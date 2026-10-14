"""Bounded SHA256d batches; ctypes releases the GIL during native scans."""
import ctypes as C
import hashlib
import platform
import struct
from array import array
from . import ROOT
from .platform_support import native_name

U80 = C.c_uint8 * 80
U32 = C.c_uint8 * 32

def hash256(data):
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()

class Hasher:
    def __init__(self, enabled=True):
        self.lib = None
        self.fill_nonces = None
        self.fill_factored = None
        self.fill_offsets = None
        self.select_samples = None
        self.source = "Python hashlib"
        self.reason = "disabled by configuration" if not enabled else "native library unavailable"
        if not enabled:
            return
        path = ROOT / "native" / native_name("libhasher_fast")
        try:
            lib = C.CDLL(str(path))
            for name in ("scan_nonces_batch", "scan_nonces_list"):
                fn = getattr(lib, name)
                fn.argtypes = [C.POINTER(C.c_uint8), C.POINTER(C.c_uint8),
                               C.c_uint32 if name.endswith("batch") else C.POINTER(C.c_uint32),
                               C.c_uint32, C.POINTER(C.c_uint32)]
                fn.restype = C.c_int
            self.lib = lib
            # Older packaged hashers can still hash using Python batch generation.
            if hasattr(lib, "fill_nonce_batch"):
                self.fill_nonces = lib.fill_nonce_batch
                self.fill_nonces.argtypes = [C.POINTER(C.c_uint32), C.c_uint32,
                                            C.c_uint32, C.POINTER(C.c_uint64),
                                            C.c_uint32, C.POINTER(C.c_uint32)]
                self.fill_nonces.restype = C.c_uint32
            if hasattr(lib, "fill_traversal_offsets"):
                self.fill_offsets=lib.fill_traversal_offsets
                self.fill_offsets.argtypes=[C.POINTER(C.c_uint16),C.c_uint32,C.c_uint32,
                                           C.c_uint32,C.POINTER(C.c_uint32)]
                self.fill_offsets.restype=None
            if hasattr(lib, "fill_factored_nonce_batch"):
                self.fill_factored=lib.fill_factored_nonce_batch
                self.fill_factored.argtypes=[C.POINTER(C.c_uint16),C.c_uint32,C.c_uint32,C.c_uint32,
                                            C.c_uint32,C.POINTER(C.c_uint64),C.c_uint32,C.POINTER(C.c_uint32)]
                self.fill_factored.restype=C.c_uint32
            if hasattr(lib, "select_sample_nonces"):
                self.select_samples = lib.select_sample_nonces
                self.select_samples.argtypes = [C.POINTER(C.c_uint32), C.c_uint32,
                                               C.c_uint32, C.POINTER(C.c_uint32)]
                self.select_samples.restype = C.c_uint32
            self.source = "ARM SHA-256" if platform.machine() == "arm64" else "Native SHA-256"
            self.reason = ""
        except (OSError, AttributeError) as e:
            self.reason = str(e)

    def project_offsets(self,residues,phase,cell_phase,prime,output):
        if self.fill_offsets is None:return False
        if len(residues)!=360 or len(output)!=144000:raise ValueError('Invalid traversal buffers')
        source=(C.c_uint16*360).from_buffer(residues)
        target=(C.c_uint32*144000).from_buffer(output)
        self.fill_offsets(source,phase,cell_phase,prime,target)
        return True

    def scan(self, header, target, start=None, count=0, nonces=None, stop=None):
        if len(header) != 80 or type(target) is not int or not 0 <= target < (1 << 256):
            raise ValueError("Invalid mining header or target")
        size = len(nonces) if nonces is not None else count
        if type(size) is not int or not 0 < size <= 1000000:
            raise ValueError("Invalid scan batch length")
        if nonces is None:
            if type(start) is not int or not 0 <= start < 1 << 32:
                raise ValueError("Scan start must be a uint32")
        elif not (isinstance(nonces, array) and nonces.typecode == "I" and nonces.itemsize == 4):
            if any(type(n) is not int or not 0 <= n < 1 << 32 for n in nonces):
                raise ValueError("Scan nonces must be uint32 integers")
        if self.lib:
            hdr, tgt, win = U80(*header), U32(*target.to_bytes(32, "little")), C.c_uint32()
            if nonces is not None:
                if isinstance(nonces, array) and nonces.typecode == "I" and nonces.itemsize == 4:
                    values = (C.c_uint32 * size).from_buffer(nonces)
                else:
                    values = (C.c_uint32 * size)(*nonces)
                found = self.lib.scan_nonces_list(hdr, tgt, values, size, C.byref(win))
                tried = nonces.index(win.value) + 1 if found else size
            else:
                found = self.lib.scan_nonces_batch(hdr, tgt, start, size, C.byref(win))
                tried = ((win.value - start) & 0xffffffff) + 1 if found else size
            return tried, win.value if found else None
        hdr = bytearray(header)
        for i in range(size):
            if i % 256 == 0 and stop and stop():
                return i, None
            nonce = nonces[i] if nonces is not None else (start + i) & 0xffffffff
            struct.pack_into("<I", hdr, 76, nonce)
            if int.from_bytes(hash256(hdr), "little") <= target:
                return i + 1, nonce
        return size, None

    def traversal_batches(self, plan, size, single=False):
        """Generate the same order as plan.batches, with no Python per-nonce loop."""
        if not isinstance(size, int) or not 1 <= size <= 1000000:
            raise ValueError("Invalid traversal batch length")
        if self.fill_factored is not None:
            labels=(C.c_uint16*360).from_buffer(plan.residues)
            cursor=C.c_uint64(0)
            capacity=1 if single else size
            while True:
                values=array('I',[0])*capacity
                buffer=(C.c_uint32*capacity).from_buffer(values)
                count=self.fill_factored(labels,plan.phase,plan.cell_phase,plan.prime,plan.first_tile,
                                         C.byref(cursor),capacity,buffer)
                del buffer
                if count==0: return
                if count<capacity: del values[count:]
                yield {'nonces':values}
                if single: return
        elif self.fill_nonces is None or plan.offsets.itemsize != 4:
            yield from plan.batches(size, single=single)
            return
        offsets = (C.c_uint32 * len(plan.offsets)).from_buffer(plan.offsets)
        cursor = C.c_uint64(0)
        capacity = 1 if single else size
        while True:
            values = array("I", [0]) * capacity
            buffer = (C.c_uint32 * capacity).from_buffer(values)
            count = self.fill_nonces(offsets, len(plan.offsets), plan.first_tile,
                                     C.byref(cursor), capacity, buffer)
            del buffer  # Release the buffer view before resizing a short last batch.
            if count == 0:
                return
            if count < capacity:
                del values[count:]
            yield {"nonces":values}
            if single:
                return

    def sampled_nonces(self, task, tried, step):
        if "nonces" not in task:
            # Engine's linear tasks do not cross the uint32 boundary.
            first = task["start"] + (-task["start"] % step)
            return range(first, task["start"]+tried, step)
        nonces = task["nonces"]
        if (self.select_samples and isinstance(nonces,array) and
                nonces.typecode == "I" and nonces.itemsize == 4):
            values = (C.c_uint32 * len(nonces)).from_buffer(nonces)
            result = array("I", [0]) * tried
            output = (C.c_uint32 * tried).from_buffer(result)
            count = self.select_samples(values,tried,step,output)
            del output
            del result[count:]
            return result
        return [nonce for nonce in nonces[:tried] if nonce % step == 0]
