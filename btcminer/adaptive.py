"""Budgeted complete bucket enumeration. Only complete exclusions remove work."""
from collections import deque
import time
from .constraintmodel import z3


def retain_candidates(solver, variable, candidates, deadline, bucket_size=64, slice_ms=75):
    values = list(dict.fromkeys(candidates))
    kept = set(values)
    queue = deque(values[i:i+bucket_size] for i in range(0, len(values), bucket_size))
    checks = splits = completed = unknown = models = 0
    while queue and time.monotonic() < deadline:
        group = queue.popleft(); found = set(); complete = False
        stop = min(deadline, time.monotonic()+(slice_ms if len(group)>1 else max(slice_ms, 500))/1000)
        solver.push()
        solver.add(z3.Or(*[variable == n for n in group]))
        try:
            while time.monotonic() < stop:
                solver.set(timeout=max(1, int((stop-time.monotonic())*1000)))
                verdict = solver.check(); checks += 1
                if verdict == z3.unsat:
                    complete = True; break
                if verdict == z3.unknown:
                    break
                n = solver.model().eval(variable).as_long()
                if n not in group or n in found:
                    raise ValueError('Solver returned a value outside its bucket')
                found.add(n); models += 1
                solver.add(variable != n)
        except (z3.Z3Exception, ValueError):
            pass  # retain the whole unresolved group
        finally:
            solver.pop()
        if complete:
            kept.difference_update(set(group)-found); completed += 1
        else:
            unknown += 1
            if len(group) > 1:
                mid = len(group)//2
                queue.appendleft(group[mid:]); queue.appendleft(group[:mid]); splits += 1
    return {'keep': [n for n in candidates if n in kept], 'excluded': len(values)-len(kept),
            'unknown': bool(unknown or queue), 'solver_checks': checks, 'models_seen': models,
            'adaptive_splits': splits, 'completed_buckets': completed,
            'unprocessed_buckets': len(queue)}
