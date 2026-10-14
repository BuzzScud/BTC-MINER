"""Verify a Core-accepted block against the exact work submitted by this miner."""
import hashlib
from .serialization import _bits_to_target


def sha256d(data):
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def merkle_root(leaves):
    leaves = list(leaves)
    if not leaves or any(len(leaf) != 32 for leaf in leaves):
        raise ValueError('Invalid transaction hash list')
    while len(leaves) > 1:
        if len(leaves) % 2:
            leaves.append(leaves[-1])
        leaves = [sha256d(leaves[i] + leaves[i + 1]) for i in range(0, len(leaves), 2)]
    return leaves[0]


def verify_accepted_block(rpc, work, nonce):
    """Read back exact bytes and commitments; Core validates transaction scripts.

    Positive confirmations mean active-chain membership at the observation time,
    not permanent finality. RPC failure or inconsistent evidence must not be
    counted as success, even after submitblock returned null.
    """
    header = work.header[:76] + nonce.to_bytes(4, 'little')
    if len(header) != 80:
        raise ValueError('Invalid submitted header length')
    target = _bits_to_target(int.from_bytes(header[72:76], 'little'))
    digest = sha256d(header)
    value = int.from_bytes(digest, 'little')
    if target != work.network_target or value > min(work.target, target):
        raise ValueError('Submitted block fails independent target verification')
    block_hash = digest[::-1].hex()
    stored = bytes.fromhex(rpc.call('getblock', [block_hash, 0]))
    if stored != header + work.data['body']:
        raise ValueError('Core block bytes differ from submitted block')
    block = rpc.call('getblock', [block_hash, 2])
    if block['hash'] != block_hash or block['height'] != work.height:
        raise ValueError('Core block identity or height differs from submitted work')
    if block.get('confirmations', -1) < 1:
        raise ValueError('Submitted block is not in the active chain at verification')
    txs = block['tx']
    if merkle_root(bytes.fromhex(tx['txid'])[::-1] for tx in txs) != header[36:68]:
        raise ValueError('Transaction Merkle root verification failed')
    coinbase = txs[0]
    commitments = []
    for output in coinbase['vout']:
        script = bytes.fromhex(output['scriptPubKey']['hex'])
        if len(script) >= 38 and script.startswith(bytes.fromhex('6a24aa21a9ed')):
            commitments.append(script[6:38])
    witness_checked = False
    if commitments:
        witness = coinbase['vin'][0].get('txinwitness', [])
        if len(witness) != 1 or len(bytes.fromhex(witness[0])) != 32:
            raise ValueError('Invalid coinbase witness reserved value')
        root = merkle_root([bytes(32)] + [bytes.fromhex(tx['hash'])[::-1] for tx in txs[1:]])
        if sha256d(root + bytes.fromhex(witness[0])) != commitments[-1]:
            raise ValueError('Witness commitment verification failed')
        witness_checked = True
    elif any(vin.get('txinwitness') for tx in txs for vin in tx['vin']):
        raise ValueError('Witness data has no witness commitment')
    return {'block_hash': block_hash, 'height': block['height'],
            'header_hex': header.hex(), 'hash_value': f'{value:064x}',
            'network_target': f'{target:064x}', 'work_target': f'{work.target:064x}',
            'exact_block_readback': True, 'sha256d_verified': True,
            'merkle_root_verified': True, 'witness_commitment_verified': witness_checked,
            'transactions': len(txs), 'confirmations_at_verification': block['confirmations'],
            'transaction_validation': 'Bitcoin Core consensus validation'}
