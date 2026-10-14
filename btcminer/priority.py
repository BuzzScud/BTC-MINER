"""Experimental ordering; every rejected arithmetic candidate has a fallback.

No empirical advantage is established. Bayesian scores use actual scanned
outcomes, a uniform hash prior, and a bounded window. They never authorize
exclusion. Limits cap bookkeeping and ensure tails do not starve.
"""
from collections import defaultdict
from array import array
from fractions import Fraction
from math import gcd
from .scaled_abacus import q_codec


class Priority:
    def __init__(self, window=64):
        self.codec = q_codec(); self.clock_codec = q_codec(144000); self.window = window
        self.samples = defaultdict(lambda: [0, 0]); self.target = None
        self.tasks = self.observations = 0

    def features(self, nonce):
        code = self.codec.code(nonce)
        # Former lossy filters now supply labels, never rejection decisions.
        return (gcd(nonce, 30) == 1, gcd(nonce, 210) == 1,
                self.codec.clocks[code] if code is not None else 0,
                self.clock_codec.code(nonce) is not None)

    def score(self, features, target):
        count, hits = self.samples[features]
        prior = Fraction(target+1, 1 << 256)
        return (1024*prior+hits)/(1024+count)

    def order(self, work, task):
        if self.target != work.target:
            self.samples.clear(); self.target = work.target
        size = len(task['nonces']) if 'nonces' in task else task['count']
        if size == 0:
            return task
        source = task['nonces'] if 'nonces' in task else range(task['start'], task['start']+size)
        head = [n & 0xffffffff for n in source[:self.window]]
        labels = {n: self.features(n) for n in head}
        # Stable ties: arithmetic preferences first, with ALL other values next.
        ordered = sorted(head, key=lambda n: (self.score(labels[n], work.target),
                         labels[n][1], labels[n][0], labels[n][3], labels[n][2] != 0), reverse=True)
        self.tasks += 1
        if head == ordered:
            return task
        if isinstance(source,array):
            output=array(source.typecode,source)
            output[:len(ordered)]=array(source.typecode,ordered)
            return {'nonces':output}
        return {'nonces': ordered + [n & 0xffffffff for n in source[self.window:]]}

    def observe(self, task, tried, hits):
        # Take only a bounded prefix whose actual results are known. No extra
        # oracle hashes, and no fabricated labels for unscanned candidates.
        values = task['nonces'] if 'nonces' in task else range(task['start'], task['start']+task['count'])
        winners = set(hits)
        for n in values[:min(self.window, tried)]:
            nonce = n & 0xffffffff
            key = self.features(nonce)
            self.samples[key][0] += 1; self.samples[key][1] += nonce in winners
            self.observations += 1

    def description(self):
        return {'enabled': True, 'window': self.window, 'tasks_ordered': self.tasks,
                'observed_hashes': self.observations, 'excluded': 0,
                'rules': ['coprime-to-30', 'coprime-to-210', 'clock-pair-products', 'scaled-Q membership',
                          'smoothed observed hit probability'],
                'fallback': 'All candidates retained; unranked tail follows each bounded window',
                'advantage_demonstrated': False}
