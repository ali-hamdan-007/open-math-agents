"""Certify a Graph 189 instance at a supplied separator, using only Python."""
import itertools
import json
import sys
from collections.abc import Iterable


def vertices(mask: int) -> Iterable[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def ball_layers(adj: list[int], start: int, allowed: int) -> Iterable[int]:
    frontier = 1 << start
    remaining = allowed ^ frontier
    while frontier:
        yield frontier
        reached = 0
        for v in vertices(frontier):
            reached |= adj[v]
        frontier = reached & remaining
        remaining ^= frontier


def components(adj: list[int], allowed: int) -> list[int]:
    parts = []
    while allowed:
        start = (allowed & -allowed).bit_length() - 1
        part = 0
        for layer in ball_layers(adj, start, allowed):
            part |= layer
        parts.append(part)
        allowed ^= part
    return parts


def cycle_from_closure(adj: list[int]) -> list[int] | None:
    graph = adj.copy()
    n = len(graph)
    all_vertices = (1 << n) - 1
    additions = []
    updated = True
    while updated:
        updated = False
        for u, neighbors in enumerate(graph):
            for v in vertices(all_vertices & ~neighbors & ~((2 << u) - 1)):
                if graph[u].bit_count() + graph[v].bit_count() >= n:
                    graph[u] |= 1 << v
                    graph[v] |= 1 << u
                    additions.append((u, v))
                    updated = True
    if any(row.bit_count() != n-1 for row in graph):
        return None
    cycle = list(range(n))
    for u, v in reversed(additions):
        graph[u] ^= 1 << v
        graph[v] ^= 1 << u
        start = cycle.index(u)
        if cycle[(start+1) % n] == v:
            step = -1
        elif cycle[(start-1) % n] == v:
            step = 1
        else:
            continue
        walk = [cycle[(start+j*step) % n] for j in range(n)]
        # u,v have total degree at least n before this closure edge was added.
        # Some successor of a v-neighbor on the spanning u-v path meets u.
        pivot = next(i for i in range(1,n-1) if (graph[v] >> walk[i]) & 1
                     and (graph[u] >> walk[i+1]) & 1)
        cycle = [u, *walk[pivot+1:], *reversed(walk[1:pivot+1])]
    return cycle


def clique_partition(adj: list[int], order: Iterable[int]) -> list[int]:
    classes = []
    for v in order:
        for i, group in enumerate(classes):
            if group & ~adj[v] == 0:
                classes[i] |= 1 << v
                break
        else:
            classes.append(1 << v)
    return classes


def short_link_connectivity(adj: list[int], target: int) -> bool:
    """Certify connectivity by disjoint paths of lengths two and three."""
    degrees = [row.bit_count() for row in adj]
    if min(degrees) < target:
        return False
    for u,v in itertools.combinations(range(len(adj)),2):
        if adj[u] & (1 << v):
            continue
        shared = adj[u] & adj[v]
        need = target-shared.bit_count()
        if need <= 0:
            continue
        left = adj[u] & ~shared
        right = adj[v] & ~shared
        partners = {}

        def augment(x: int, visited: set[int]) -> bool:
            for y in vertices(adj[x] & right):
                if y in visited:
                    continue
                visited.add(y)
                if y not in partners or augment(partners[y],visited):
                    partners[y] = x
                    return True
            return False

        for x in vertices(left):
            augment(x,set())
            if len(partners)>=need:
                break
        if len(partners)<need:
            return False
    return True


def circumference(adj: list[int]) -> dict:
    n = len(adj)
    whole = (1 << n)-1
    if n < 3:
        return {"bound": 0, "test": "no cycle"}
    cycle = cycle_from_closure(adj)
    if cycle is not None:
        return {"bound": n, "test": "Bondy-Chvatal closure", "cycle": cycle}
    if any(len(components(adj, whole ^ (1 << v))) != 1 for v in range(n)):
        return {"bound": 0, "test": "not 2-connected"}
    degrees = [row.bit_count() for row in adj]
    fan = min(max(degrees[u], degrees[v]) for u, v in itertools.combinations(range(n), 2)
              if not (adj[u] >> v) & 1 and adj[u] & adj[v])
    best = {"bound": min(n, 2*fan), "test": "Fan", "degree_threshold": fan}
    if best["bound"] == n:
        return best
    orders = [range(n), sorted(range(n), key=degrees.__getitem__),
              sorted(range(n), key=degrees.__getitem__, reverse=True)]
    groups = min((clique_partition(adj, order) for order in orders), key=len)
    if short_link_connectivity(adj,len(groups)):
        return {"bound":n,"test":"Chvatal-Erdos via short disjoint paths",
                "connectivity_lower_bound":len(groups),"clique_cover":[list(vertices(g)) for g in groups]}
    sigma = None
    for u, v in itertools.combinations(range(n), 2):
        if adj[u] & (1 << v):
            continue
        candidates = whole & ~(adj[u] | adj[v]) & ~((2 << v)-1)
        for w in vertices(candidates):
            total = degrees[u]+degrees[v]+degrees[w]
            sigma = total if sigma is None else min(sigma, total)
    if sigma is None:
        return {"bound": n, "test": "Chvatal-Erdos", "independence_upper_bound": 2}
    if sigma >= n+2:
        lower = min(n, n+(sigma+2)//3-len(groups))
        if lower > best["bound"]:
            best = {"bound": lower, "test": "Bauer et al. circumference",
                    "sigma_three": sigma, "clique_cover": [list(vertices(g)) for g in groups]}
    return best


def rooted_ore_path(adj: list[int], root: int) -> list[int]:
    """Extend a concrete rooted path by the four moves in the local Ore proof."""
    path = [root]
    whole = (1 << len(adj))-1
    while len(path) < len(adj):
        used = sum(1 << v for v in path)
        retained = len(path)
        for u in vertices(whole ^ used):
            if adj[u] & (1 << path[-1]):
                path.append(u)
                break
            marks = [i for i,v in enumerate(path) if adj[u] & (1 << v)]
            for i in marks:
                successor = path[i+1]
                if adj[u] & (1 << successor):
                    path[i+1:i+1] = [u]
                    break
                outside = adj[u] & adj[successor] & ~used
                if outside:
                    path[i+1:i+1] = [u,next(vertices(outside))]
                    break
            if len(path)>retained:
                break
            for i,j in itertools.combinations(marks,2):
                if adj[path[i+1]] & (1 << path[j+1]):
                    path = path[:i+1]+[u]+list(reversed(path[i+1:j+1]))+path[j+1:]
                    break
            if len(path)>retained:
                break
        if len(path)==retained:
            break
    return path


def block_chain(adj: list[int], allowed: int, genuine: int) -> dict:
    """Combine independently certified terminal routes in one block-tree branch."""
    pending = [allowed]
    blocks = []
    while pending:
        region = pending.pop()
        for cut in vertices(region):
            pieces = components(adj, region ^ (1 << cut))
            if len(pieces) > 1:
                pending.extend(piece | (1 << cut) for piece in pieces)
                break
        else:
            blocks.append(region)
    if len(blocks) <= 1:
        return {"length": 0}

    memberships = {v: [] for v in vertices(allowed)}
    details = []
    for index, block in enumerate(blocks):
        labels = list(vertices(block))
        local = [sum(1 << j for j,w in enumerate(labels) if adj[v] & (1 << w))
                 for v in labels]
        details.append((labels, local, circumference(local)))
        for v in labels:
            memberships[v].append(index)

    pair_cache = {}

    def terminal_route(index: int, start: int, end: int) -> dict:
        key = (index, start, end)
        if key in pair_cache:
            return pair_cache[key]
        labels, local, base = details[index]
        size = len(labels)
        if size == 2:
            route = {"length": 2, "test": "bridge", "path": [start,end]}
        else:
            x, y = labels.index(start), labels.index(end)
            marked = (1 << x) | (1 << y)
            torso = [row | ((1 << size) if marked & (1 << i) else 0)
                     for i,row in enumerate(local)] + [marked]
            full = circumference(torso)
            if full["bound"] == size+1:
                route = {"length": size, "test": "terminal marker", "cycle": full}
                if "cycle" in full:
                    cycle = full["cycle"]
                    m = cycle.index(size)
                    path = [labels[i] for i in cycle[m+1:]+cycle[:m]]
                    route["path"] = path if path[0] == start else list(reversed(path))
            else:
                # Two vertex-disjoint links from x,y to a cycle suffice.
                route = {"length": (base["bound"]+1)//2+1, "test": "longer block arc", "cycle": base}
                if "cycle" in base:
                    cycle = base["cycle"]
                    m = cycle.index(x)
                    oriented = cycle[m:]+cycle[:m]
                    break_at = oriented.index(y)
                    arcs = [oriented[:break_at+1], [x,*reversed(oriented[break_at:])]]
                    path = max(arcs, key=len)
                    route["path"] = [labels[i] for i in path]
                    route["length"] = len(path)
        route["entry"] = start
        route["exit"] = end
        route["block_vertices"] = labels
        pair_cache[key] = route
        return route

    best = {"length": 0}
    for root in vertices(genuine):
        stack = [(root,-1,1,[],[root])]
        while stack:
            current, previous, length, chain, path = stack.pop()
            if length > best["length"]:
                best = {"length": length, "test": "block chain", "chain": chain}
                if path is not None:
                    best["path"] = path
            for index in memberships[current]:
                if index == previous:
                    continue
                for end in vertices(blocks[index] ^ (1 << current)):
                    route = terminal_route(index,current,end)
                    joined = None
                    if path is not None and "path" in route:
                        joined = path+route["path"][1:]
                    stack.append((end,index,length+route["length"]-1,chain+[route],joined))
        if best["length"] == allowed.bit_count():
            break
    return best


def side_bound(adj: list[int], neighbors: int, allowed: int) -> dict:
    labels = list(vertices(allowed))
    if not labels or len(components(adj, allowed)) != 1:
        return {"length": 0}
    genuine = neighbors & allowed
    if not genuine:
        return {"length": 0}
    local = [sum(1 << j for j, w in enumerate(labels) if adj[v] & (1 << w))
             for v in labels]
    marker = len(labels)
    port_mask = sum(1 << j for j, v in enumerate(labels) if genuine & (1 << v))
    # The auxiliary root uses genuine edges only in this explicit route.
    rooted = [row | ((1 << marker) if port_mask & (1 << i) else 0)
              for i, row in enumerate(local)] + [port_mask]
    path = [labels[i] for i in rooted_ore_path(rooted,marker)[1:]]
    best = {"length": len(path), "test": "rooted Ore extensions", "path": path}
    if best["length"] == marker:
        return best
    for extra in [None, *[i for i in range(marker) if not port_mask & (1 << i)]]:
        marked = port_mask if extra is None else port_mask | (1 << extra)
        augmented = [row | ((1 << marker) if marked & (1 << i) else 0)
                     for i, row in enumerate(local)] + [marked]
        proof = circumference(augmented)
        if proof["bound"]-1 > best["length"]:
            best = {"length": proof["bound"]-1, "side_vertices": labels,
                    "artificial_contact": None if extra is None else labels[extra],
                    "cycle": proof}
            if "cycle" in proof:
                cycle = proof["cycle"]
                i = cycle.index(marker)
                path = [labels[j] for j in cycle[i+1:]+cycle[:i]]
                if not genuine & (1 << path[0]):
                    path.reverse()
                best["path"] = path
        if best["length"] == marker:
            break
    if best["length"] < marker:
        # Any ordinary side path on more vertices than the noncontacts meets a port.
        universal = [row | (1 << marker) for row in local] + [(1 << marker)-1]
        proof = circumference(universal)
        ordinary = proof["bound"]-1
        noncontacts = marker-genuine.bit_count()
        if "cycle" in proof:
            cycle = proof["cycle"]
            i = cycle.index(marker)
            path = [labels[j] for j in cycle[i+1:]+cycle[:i]]
            left = next(j for j,v in enumerate(path) if genuine & (1<<v))
            right = next(j for j,v in enumerate(reversed(path)) if genuine & (1<<v))
            kept = path[left:] if left<=right else list(reversed(path))[right:]
            if len(kept)>best["length"]:
                best={"length":len(kept),"test":"trimmed ordinary closure path","path":kept}
        elif ordinary>noncontacts and ordinary-noncontacts//2>best["length"]:
            best={"length":ordinary-noncontacts//2,"test":"trimmed ordinary path",
                  "side_vertices":labels,"noncontacts":noncontacts,"cycle":proof}
    if best["length"] < marker:
        chain = block_chain(adj, allowed, genuine)
        if chain["length"] > best["length"]:
            best = chain
    return best


def certificate(data: dict) -> dict:
    n = data["n"]
    if not isinstance(n, int) or n < 2:
        raise ValueError("n must be an integer at least two")
    adj = [0]*n
    for u, v in data["edges"]:
        if not 0 <= u < n or not 0 <= v < n or u == v:
            raise ValueError("invalid simple edge")
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    S = list(data["separator"])
    if len(S) != len(set(S)) or not S or any(not 0 <= u < n for u in S):
        raise ValueError("invalid separator")
    whole = (1 << n)-1
    if len(components(adj, whole)) != 1:
        raise ValueError("the graph must be connected")
    parts = components(adj, whole ^ sum(1 << u for u in S))
    if len(parts) != 2:
        raise ValueError("the supplied separator must leave exactly two components")
    k = sorted(row.bit_count() for row in adj)[1]
    even_max = max(sum(layer.bit_count() for i, layer in enumerate(ball_layers(adj,u,whole))
                       if i > 0 and i % 2 == 0) for u in range(n))
    cap = even_max <= k
    threshold = n-((k+1)//2+1) if cap else n
    best = {"length": 0}
    for anchor in S:
        cache = {}
        others = [v for v in S if v != anchor]
        for assignment in itertools.product(range(3), repeat=len(others)):
            masks = parts.copy()
            for v, choice in zip(others, assignment):
                if choice < 2:
                    masks[choice] |= 1 << v
            for mask in masks:
                if mask not in cache:
                    cache[mask] = side_bound(adj, adj[anchor], mask)
            left, right = (cache[mask] for mask in masks)
            if min(left["length"],right["length"]) == 0:
                continue
            length = left["length"]+1+right["length"]
            if length > best["length"]:
                best = {"length": length, "anchor": anchor, "side_sets": [list(vertices(m)) for m in masks],
                        "sides": [left, right]}
                if "path" in left and "path" in right:
                    best["path"] = [*reversed(left["path"]), anchor, *right["path"]]
            if length >= threshold:
                break
        if best["length"] >= threshold and best["length"] > 0:
            break
    if best["length"] < threshold:
        # A union of contacts can certify that some anchor works even when
        # individual contact sets fail to pass a circumference test.
        s_count = len(S)
        full_mask = (1 << s_count)-1
        tables = [{}, {}]
        caches = [{}, {}]
        for subset in range(full_mask+1):
            neighbors = 0
            for i in vertices(subset):
                neighbors |= adj[S[i]]
            for side, region in enumerate(parts):
                genuine = neighbors & region
                if genuine not in caches[side]:
                    caches[side][genuine] = side_bound(adj, genuine, region)
                tables[side][subset] = caches[side][genuine]
        scores = sorted({item["length"] for item in tables[0].values()} - {0}, reverse=True)
        for p in scores:
            q = max(1,threshold-1-p)
            # L is a proposed set containing all A-eligible anchors and none
            # of the B-eligible anchors. A positive disjunct excludes this L.
            rows = []
            for L in range(full_mask+1):
                complement = full_mask ^ L
                if tables[0][complement]["length"] >= p:
                    rows.append((0,complement))
                elif tables[1][L]["length"] >= q:
                    rows.append((1,L))
                else:
                    break
            if len(rows) == full_mask+1:
                proofs = [{}, {}]
                for side, subset in rows:
                    proofs[side][subset] = tables[side][subset]
                best = {"length": p+q+1, "test": "anchor partitions",
                        "anchor_labels": S, "side_sets": [list(vertices(m)) for m in parts],
                        "required_side_lengths": [p,q], "partition_witnesses": rows,
                        "subset_route_proofs": proofs}
                break
    return {"certified_traceable": best["length"] >= threshold and best["length"] > 0,
            "k": k, "max_positive_even": even_max, "qualifies": cap,
            "needed_path_order": threshold, "path_certificate": best}


if __name__ == "__main__":
    with open(sys.argv[1]) as source:
        print(json.dumps(certificate(json.load(source)), indent=2))
