"""Replay the deterministic examples from clique-blowup-routing.md."""
import importlib.util
import json
from pathlib import Path

folder = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('clique_routing', folder/'clique-blowup-routing.py')
routing = importlib.util.module_from_spec(spec)
spec.loader.exec_module(routing)

c7 = routing.Template(7, [(i, (i+1)%7) for i in range(7)])
for t in (1,2,16):
    sizes = [1+t*i for i in (2,2,3,4,4,3,2)]
    assert c7.verify_metric(sizes,6*t+2) == 6*t+2
assert c7.route([1]*7,10000) == ('sat',[1]*7)
cycle = c7.search(timeout=10000)
assert cycle['status']=='unsat' and cycle['routes_blocked'], cycle
print('C7: checked qualifying examples and excluded all nontraceable clique sizes')

star = routing.Template(4,[(0,i) for i in range(1,4)])
assert star.route([1]*4,10000) == ('unsat',None)
assert star.route([2,1,1,1],10000) == ('sat',[2,1,1,1])
print('K1,3: verified the singleton obstruction and its center-size-two routing')

for name in ('pps','pss'):
    for hub in (0,1):
        path = folder/f'blowup-{name}-{hub}.json'
        instance = json.loads(path.read_text())
        template = routing.Template(instance['order'],instance['edges'])
        result = template.search(timeout=10000,upper=instance['upper'])
        assert result == {'status':'unsat','routes_blocked':[]},(path.name,result)
        print(f'{path.name}: exact metric system UNSAT')
