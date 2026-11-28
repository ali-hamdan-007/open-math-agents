"""Fixed-template search for a Graph 189 counterexample among clique blowups.

Input is a JSON object {"order": n, "edges": [[u,v], ...]}.
Requires only Python and the native libz3.so.4 shared library.
"""
from collections import deque
import ctypes as ct
import itertools as it
import json
from pathlib import Path
import re
import sys

Z3 = ct.CDLL('libz3.so.4')
for name, args, result in [
    ('Z3_mk_config', [], ct.c_void_p),
    ('Z3_mk_context', [ct.c_void_p], ct.c_void_p),
    ('Z3_del_config', [ct.c_void_p], None),
    ('Z3_del_context', [ct.c_void_p], None),
    ('Z3_eval_smtlib2_string', [ct.c_void_p, ct.c_char_p], ct.c_char_p),
]:
    function = getattr(Z3, name)
    function.argtypes, function.restype = args, result


class Solver:
    def __init__(self, timeout):
        config = Z3.Z3_mk_config()
        self.context = Z3.Z3_mk_context(config)
        Z3.Z3_del_config(config)
        self.run(f'(set-option :timeout {timeout})\n(set-logic QF_LIA)')

    def __enter__(self):
        return self

    def __exit__(self, *args):
        Z3.Z3_del_context(self.context)

    def run(self, program):
        answer = Z3.Z3_eval_smtlib2_string(self.context, program.encode()).decode().strip()
        if answer.startswith('(error'):
            raise ValueError(answer)
        return answer

    def values(self, *names):
        values = self.run(f'(get-value ({" ".join(names)}))')
        found = {name:int(number) for name,number in re.findall(r'\((\w+) (\d+)\)', values)}
        return [found[name] for name in names]


def aggregate(op, terms, empty='0'):
    terms = list(terms)
    if not terms:
        return empty
    if len(terms) == 1:
        return terms[0]
    return f'({op} {" ".join(terms)})'


def total(terms):
    return aggregate('+', terms)


def disjunction(terms):
    return aggregate('or', terms, 'false')


def integer(name, low, high=None):
    yield f'(declare-const {name} Int)'
    yield f'(assert (>= {name} {low}))'
    if high is not None:
        yield f'(assert (<= {name} {high}))'


def distances(adj, root):
    dist = {root: 0}
    queue = deque([root])
    while queue:
        v = queue.popleft()
        for u in adj[v]:
            if u not in dist:
                dist[u] = dist[v]+1
                queue.append(u)
    if len(dist) != len(adj):
        raise ValueError('template must be connected')
    return dist


class Template:
    def __init__(self, order, edges):
        if order < 2:
            raise ValueError('template needs at least two vertices')
        self.n = order
        self.vertices = tuple(range(order))
        self.edges = tuple(sorted({tuple(sorted(e)) for e in edges}))
        self.adj = [set() for _ in self.vertices]
        for x, y in self.edges:
            if not 0 <= x < y < order:
                raise ValueError(f'invalid edge {(x,y)}')
            self.adj[x].add(y)
            self.adj[y].add(x)
        self.dist = [distances(self.adj, v) for v in self.vertices]
        self.even = [[u for u,d in row.items() if d and d % 2 == 0] for row in self.dist]

    def verify_metric(self, weights, threshold):
        degree_counts = sorted((weights[v]-1+sum(weights[u] for u in self.adj[v]), weights[v])
                               for v in self.vertices)
        min_degree, min_count = degree_counts[0]
        second_degree = min_degree if min_count >= 2 else degree_counts[1][0]
        even = max(sum(weights[u] for u in self.even[v]) for v in self.vertices)
        assert second_degree == threshold
        assert even <= threshold
        assert sum(weights) > 3*threshold + 2
        return even

    def metric_model(self, upper=None):
        yield from integer('k',1)
        for v in self.vertices:
            yield from integer(f'w{v}',1,None if upper is None else upper[v])
        for v in self.vertices:
            degree = total(f'w{u}' for u in [v,*sorted(self.adj[v])])
            yield f'(define-fun D{v} () Int (- {degree} 1))'
            yield f'(assert (=> (< D{v} k) (= w{v} 1)))'
            metric = total(f'w{u}' for u in self.even[v])
            yield f'(assert (<= {metric} k))'
        for x,y in it.combinations(self.vertices,2):
            yield f'(assert (or (>= D{x} k) (>= D{y} k)))'
        two_at_most = [f'(and (<= D{v} k) (>= w{v} 2))' for v in self.vertices]
        two_at_most += [f'(and (<= D{x} k) (<= D{y} k))'
                        for x,y in it.combinations(self.vertices,2)]
        yield f'(assert {disjunction(two_at_most)})'
        yield f'(assert (> {total(f"w{v}" for v in self.vertices)} (+ (* 3 k) 2)))'

    def routing_model(self, weights):
        for x,y in self.edges:
            yield from integer(f'm{x}_{y}',0,2)
            yield from integer(f'f{x}_{y}',0,self.n-1)
            yield from integer(f'f{y}_{x}',0,self.n-1)
            yield f'(assert (=> (= m{x}_{y} 0) (= (+ f{x}_{y} f{y}_{x}) 0)))'
        for v in self.vertices:
            yield from integer(f'r{v}',1,min(weights[v],len(self.adj[v])))
            yield from integer(f'o{v}',0,1)
            degree = total(f'm{min(u,v)}_{max(u,v)}' for u in sorted(self.adj[v]))
            yield f'(assert (= {degree} (- (* 2 r{v}) o{v})))'
            entering = total(f'f{u}_{v}' for u in sorted(self.adj[v]))
            leaving = total(f'f{v}_{u}' for u in sorted(self.adj[v]))
            if v == 0:
                yield f'(assert (= {leaving} (+ {entering} {self.n - 1})))'
            else:
                yield f'(assert (= {entering} (+ {leaving} 1)))'
        yield f'(assert (= {total(f"o{v}" for v in self.vertices)} 2))'

    def check_route(self, visits, degrees, odd, mult, weights):
        support = [set() for _ in self.vertices]
        counts = [0] * self.n
        for (x,y), copies in zip(self.edges,mult):
            assert copies in (0,1,2)
            if copies:
                support[x].add(y)
                support[y].add(x)
                counts[x] += copies
                counts[y] += copies
        distances(support,0)
        assert counts == degrees
        assert sum(odd) == 2 and all((d % 2) == o for d,o in zip(degrees,odd))
        assert all((d+o)//2 == v <= w for d,o,v,w in zip(degrees,odd,visits,weights))

    def route(self, weights, timeout):
        with Solver(timeout) as model:
            status = model.run('\n'.join(self.routing_model(weights))+'\n(check-sat)')
            if status != 'sat':
                return status,None
            visits = model.values(*(f'r{v}' for v in self.vertices))
            odd = model.values(*(f'o{v}' for v in self.vertices))
            mult = model.values(*(f'm{x}_{y}' for x,y in self.edges))
            degrees = [2*r-o for r,o in zip(visits,odd)]
            self.check_route(visits,degrees,odd,mult,weights)
            return status,visits

    def search(self, timeout=4000, budget=1000, upper=None):
        blocked = []
        with Solver(timeout) as metric:
            metric.run('\n'.join(self.metric_model(upper)))
            for iteration in range(budget):
                status = metric.run('(check-sat)')
                if status != 'sat':
                    return {'status':status, 'routes_blocked':blocked}
                threshold,*weights = metric.values('k',*(f'w{v}' for v in self.vertices))
                even = self.verify_metric(weights,threshold)
                status,visits = self.route(weights,timeout)
                if status != 'sat':
                    return {'status':'counterexample' if status == 'unsat' else 'route-unknown',
                            'k':threshold, 'weights':weights, 'maximum_positive_even':even,
                            'routes_blocked':blocked}
                if visits in blocked:
                    raise AssertionError('blocking inequality failed')
                blocked.append(visits)
                clause = disjunction(f'(< w{v} {visits[v]})' for v in self.vertices
                                     if visits[v]>1)
                metric.run(f'(assert {clause})')
            return {'status':'budget', 'routes_blocked':blocked}


if __name__ == '__main__':
    item = json.loads(Path(sys.argv[1]).read_text())
    template = Template(item['order'],item['edges'])
    print(json.dumps(template.search(int(sys.argv[2]) if len(sys.argv)>2 else 4000,
                                     int(sys.argv[3]) if len(sys.argv)>3 else 1000,
                                     item.get('upper')), indent=2))
