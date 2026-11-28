"""Sound partial-graph exclusions for a candidate longest-path attachment pattern."""
from functools import lru_cache


def bits(mask):
    while mask:
        flag = mask & -mask
        yield flag.bit_length()-1
        mask ^= flag


def connected_after_deletion(rows, skip):
    remaining = (1<<len(rows))-1
    if skip >= 0:
        remaining ^= 1<<skip
    start=remaining & -remaining
    visited=start
    front=start
    while front:
        new=0
        for i in bits(front):
            new |= rows[i]
        front=new & remaining & ~visited
        visited |= front
    return visited==remaining


def enough_path(rows,target,allowed):
    @lru_cache(maxsize=None)
    def extend(v,used):
        if used.bit_count()>=target:
            return True
        return any(extend(w,used | (1<<w)) for w in bits(rows[v] & allowed & ~used))
    return any(extend(v,1<<v) for v in bits(allowed))


def exclude(rows, p, k, h):
    n=len(rows)
    all_vertices=(1<<n)-1
    high_vertices=all_vertices ^ (1<<(n-1))
    opt=[(i,j) for j in range(n) for i in range(j) if not (rows[i] & (1<<j))
         and ((j<p) or j==n-1)]
    def add(graph,i,j):
        graph[i]|=1<<j
        graph[j]|=1<<i
    def too_long(graph):
        return enough_path(graph,n-h-1,all_vertices) or enough_path(graph,p+1,high_vertices)
    low = list(rows)
    options = opt
    while True:
        if too_long(low):
            return True
        remaining=[]
        upper=low.copy()
        for i,j in options:
            if low[i] & (1<<j):
                continue
            add(low,i,j)
            blocked=too_long(low)
            low[i]^=1<<j
            low[j]^=1<<i
            if not blocked:
                remaining.append((i,j))
                add(upper,i,j)
        caps=[k]*(n-1)+[2]
        if any(upper[i].bit_count()<caps[i] for i in range(n)):
            return True
        if any(not connected_after_deletion(upper,i) for i in range(n)):
            return True
        for i in range(n):
            known=0
            for j in bits(low[i]):
                known |= low[j]
            if (known & ~upper[i] & ~(1<<i)).bit_count()>k:
                return True
        forced=False
        for i,j in remaining:
            if upper[i].bit_count()==caps[i] or upper[j].bit_count()==caps[j]:
                add(low,i,j)
                forced=True
        if not forced:
            return False
        options=remaining

