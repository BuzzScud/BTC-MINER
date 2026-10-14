#!/usr/bin/env python3
"""Exact, offline rod-capacity diagnostic; never controls a miner or node."""
import argparse
from dataclasses import asdict
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from btcminer.capacity_reals import CapacityError, CapacityReals, Expr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rods', default='11,19,73,109', help='Comma-separated pairwise coprime integers')
    parser.add_argument('--sqrt', dest='radicand', default='19', help='Exact integer or rational radicand')
    parser.add_argument('--places', type=int, default=0, help='Requested base-60 fractional places')
    parser.add_argument('--max-stages', type=int, help='Optional CPU-work budget, separate from capacity')
    args = parser.parse_args()
    try:
        service = CapacityReals(tuple(int(x) for x in args.rods.split(',')))
        expression = Expr.rational(args.radicand).sqrt()
        plan = service.plan(expression)
        result = {'expression': 'sqrt(' + args.radicand + ')', 'rods': list(service.frame.rods),
                  'precision_plan': asdict(plan), 'nonce_exclusion_authority': False,
                  'scope': 'Bounded algebraic interval diagnostic; no transcendental or provider-C claim'}
        try:
            result['reading'] = asdict(service.read(expression, args.places, args.max_stages))
        except CapacityError as exc:
            result['reading'] = {'status': 'capacity_exceeded', 'message': str(exc)}
        print(json.dumps(result, indent=2))
        return 0 if result['reading']['status'] == 'certified' else 2
    except CapacityError as exc:
        print(json.dumps({'reading': {'status': 'capacity_exceeded', 'message': str(exc)}}, indent=2))
        return 2
    except (TypeError, ValueError) as exc:
        parser.error(str(exc))


if __name__ == '__main__':
    raise SystemExit(main())
