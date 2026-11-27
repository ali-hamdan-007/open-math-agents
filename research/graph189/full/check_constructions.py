"""Build both Asratian–Granholm gadgets and check actual distance layers."""
from collections import Counter, deque

def edge(g,a,b):
    g.setdefault(a,set()).add(b)
    g.setdefault(b,set()).add(a)

def clique(g,A):
    for a in A:g.setdefault(a,set())
    for i,a in enumerate(A):
        for b in A[i+1:]:
            edge(g,a,b)

def layers(g,x):
    dist={x:0};q=deque([x])
    while q:
        a=q.popleft()
        for b in g[a]:
            if b not in dist:
                dist[b]=dist[a]+1
                q.append(b)
    return dist

def theta(parts):
    k=sum(parts);g={};hubs=[];paths=[]
    for side in (0,1):
        A=[[(side,'hub',i,j) for j in range(t)] for i,t in enumerate(parts)]
        hubs.append(A)
        clique(g,[v for group in A for v in group])
    for i,t in enumerate(parts):
        cliques=[]
        for side in (0,1):
            U=[(side,'U',i,j) for j in range(k-t)]
            V=[(side,'V',i,j) for j in range(t)]
            w=(side,'w',i)
            clique(g,U+V)
            for v in U+hubs[side][i]:edge(g,v,w)
            cliques.append((U,V,w))
        U,V,w=cliques[0]
        T,Z,z=cliques[1]
        for v,p in zip(V,Z):edge(g,v,p)
        paths.append([w]+U+V[1:]+[V[0],Z[0]]+Z[1:]+T+[z])
    path=[]
    for i,arm in enumerate(paths):
        side=i%2
        path.extend(hubs[side][i])
        path.extend(arm if side==0 else arm[::-1])
        path.extend(hubs[1-side][i])
    assert len(path)==len(g)==len(set(path))
    assert all(b in g[a] for a,b in zip(path,path[1:]))
    assert set(map(len,g.values()))=={k}
    m=len(parts)
    for i in range(m):
        d=Counter(layers(g,hubs[0][i][0]).values())
        assert d[2]==k-parts[i]+m-1
        assert d[4]==k
        assert d[6]==1+(m-2)*k+parts[i]
        assert d[8]==k-parts[i]
        assert sum(n for j,n in d.items() if j and j%2==0)==(m+1)*k-parts[i]+m
        t=parts[i]
        expected={
            'w':(k,(m-1)*k,k,m-1),
            'U':(2*t,m,2*(k-t),(m-2)*k+t),
            'V':(k,k,(m-2)*k+t+m-1,k-t),
        }
        for typ,actual in expected.items():
            u=(0,typ,i) if typ=='w' else (0,typ,i,0)
            counts=Counter(layers(g,u).values())
            assert tuple(counts[h] for h in (2,4,6,8))==actual
    return g

def source():
    A=[('a',j) for j in range(4)]
    scaffold=[(0,2),(0,3),(1,2),(1,3),(0,2),(1,3)]
    g={}
    for i,(a,b) in enumerate(scaffold):
        for u in range(8):
            for j in range(3):
                v=u^(1<<j)
                if {u,v}!={0,1}:edge(g,('Q',i,u),('Q',i,v))
        edge(g,A[a],('Q',i,0));edge(g,A[b],('Q',i,1))
    assert set(map(len,g.values()))=={3}
    assert len(layers(g,A[0]))==len(g)
    assert all(len(layers({u:vs-{w} for u,vs in g.items() if u!=w},
                          next(u for u in g if u!=w)))==len(g)-1 for w in g)
    rem={u:vs-set(A) for u,vs in g.items() if u not in A}
    components=[]
    while rem:
        block=set(layers(rem,next(iter(rem))))
        components.append(block)
        rem={u:vs for u,vs in rem.items() if u not in block}
    assert sorted(map(len,components))==[8]*6
    return g

def reduce(source):
    dist=layers(source,next(iter(source)))
    X={v for v,d in dist.items() if d%2==0}
    Y=set(source)-X
    assert all((v in X)!=(u in X) for v in source for u in source[v])
    g={}
    for x in X:clique(g,[('U',x,j) for j in range(4)])
    for y in Y:
        portals=[('V',y,j) for j in range(6)]
        clique(g,portals)
        for j,x in enumerate(sorted(source[y])):
            w=('w',x,y)
            for u in [('U',x,i) for i in range(4)]+portals[2*j:2*j+2]:edge(g,w,u)
    for x in X:
        d=Counter(layers(g,('U',x,0)).values())
        assert (d[2],d[4])==(6,6)
    assert set(map(len,g.values()))=={6}
    return g

def report(name,g):
    D=[Counter(layers(g,x).values()) for x in g]
    even=[sum(v for k,v in d.items() if k and k%2==0) for d in D]
    print(name,'n',len(g),'degree',len(next(iter(g.values()))),'diameter',max(max(d) for d in D),
          'max N2',max(d[2] for d in D),'positive even range',min(even),max(even))

if __name__=='__main__':
    for parts in [(2,2,2),(2,5,7),(3,3,3,3),(4,4,4,4,4)]:
        report(f'Theta {parts}',theta(parts))
    g=source()
    print('Source n',len(g), 'removed anchors',4,'components',6)
    report('Source image',reduce(g))
