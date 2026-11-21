import random
import itertools
from collections import deque

def is_connected(adj, excluded=set()):
    nodes = [v for v in adj if v not in excluded]
    if not nodes:
        return True
    start = nodes[0]
    seen = {start}
    q = deque([start])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if w not in excluded and w not in seen:
                seen.add(w)
                q.append(w)
    return len(seen) == len(nodes)

def find_good_triple_cubic(adj):
    for v, nbrs in adj.items():
        for i in range(3):
            u1 = nbrs[i]
            u2, u3 = nbrs[(i+1)%3], nbrs[(i+2)%3]
            if is_connected(adj, {v, u2, u3}):
                return v, u1, u2, u3
    raise AssertionError("No good triple found!")

def edge_key(u, v):
    return (u, v) if u < v else (v, u)

def vertex_seq(v, adj, color, order_list, final_block_edge=None):
    pos = {e: idx for idx, e in enumerate(order_list)}
    inc = [edge_key(v, u) for u in adj[v] if edge_key(v, u) in pos]
    inc.sort(key=lambda e: pos[e])
    seq = [color[e] for e in inc]
    if final_block_edge is not None:
        seq.append(color[final_block_edge])
    return tuple(seq)

def solve_regular_2conn(adj, color, d):
    if d == 3:
        v, u1, u2, u3 = find_good_triple_cubic(adj)
        c1, c2, c3 = color[edge_key(v, u1)], color[edge_key(v, u2)], color[edge_key(v, u3)]
        final_edge_of = {u2: edge_key(v, u2), u3: edge_key(v, u3)}
        excl = {v, u2, u3}
        parent = {u1: None}
        bfs_order = [u1]
        q = deque([u1])
        while q:
            curr = q.popleft()
            for nxt in adj[curr]:
                if nxt not in excl and nxt not in parent:
                    parent[nxt] = curr
                    bfs_order.append(nxt)
                    q.append(nxt)
        proc_order = [u2, u3] + list(reversed(bfs_order[1:]))
        order_list = []
        processed = set()
        # Step 1: u2 -> want (c3, c1, c2)
        e2_c3 = [edge_key(u2, w) for w in adj[u2] if w != v and color[edge_key(u2, w)] == c3][0]
        e2_c1 = [edge_key(u2, w) for w in adj[u2] if w != v and color[edge_key(u2, w)] == c1][0]
        order_list = [e2_c3, e2_c1]
        processed.add(u2)
        # Step 2: u3 -> want (c2, c1, c3)
        e3_c2 = [edge_key(u3, w) for w in adj[u3] if w != v and color[edge_key(u3, w)] == c2][0]
        e3_c1 = [edge_key(u3, w) for w in adj[u3] if w != v and color[edge_key(u3, w)] == c1][0]
        if e3_c1 not in order_list:
            order_list.append(e3_c1)
        assert e3_c2 not in order_list
        idx_c1 = order_list.index(e3_c1)
        order_list.insert(idx_c1, e3_c2)
        processed.add(u3)
        rest = proc_order[2:]
    else:
        v = next(iter(adj))
        nbrs = list(adj[v])
        u1 = nbrs[0]
        final_edge_of = {u: edge_key(v, u) for u in nbrs[1:]}
        excl = {v}
        parent = {u1: None}
        bfs_order = [u1]
        q = deque([u1])
        while q:
            curr = q.popleft()
            for nxt in adj[curr]:
                if nxt not in excl and nxt not in parent:
                    parent[nxt] = curr
                    bfs_order.append(nxt)
                    q.append(nxt)
        order_list = []
        processed = set()
        rest = list(reversed(bfs_order[1:]))

    for x in rest:
        inc_H = [edge_key(x, w) for w in adj[x] if w != v]
        unord = [e for e in inc_H if e not in order_list]
        assert len(unord) >= 1
        e_star = unord.pop()
        for e in unord:
            order_list.append(e)
        forb = {vertex_seq(y, adj, color, order_list, final_edge_of.get(y))
                for y in adj[x] if y in processed}
        found = False
        for pos in range(len(order_list) + 1):
            order_list.insert(pos, e_star)
            seq_x = vertex_seq(x, adj, color, order_list, final_edge_of.get(x))
            if seq_x not in forb:
                found = True
                break
            order_list.pop(pos)
        assert found, f"Failed at vertex {x}"
        processed.add(x)

    e_vu1 = edge_key(v, u1)
    forb_u1 = {vertex_seq(y, adj, color, order_list, final_edge_of.get(y))
               for y in adj[u1] if y != v}
    found = False
    for pos in range(len(order_list) + 1):
        order_list.insert(pos, e_vu1)
        seq_u1 = vertex_seq(u1, adj, color, order_list, None)
        if seq_u1 not in forb_u1:
            found = True
            break
        order_list.pop(pos)
    assert found, "Failed at u1"

    rem_edges = [edge_key(v, u) for u in adj[v] if u != u1]
    forb_v = {vertex_seq(u, adj, color, order_list, final_edge_of.get(u)) for u in adj[v]}
    found = False
    for perm in itertools.permutations(rem_edges):
        cand = order_list + list(perm)
        seq_v = vertex_seq(v, adj, color, cand, None)
        if seq_v not in forb_v:
            order_list = cand
            found = True
            break
    assert found, f"Failed at v for d={d}!"

    assert len(order_list) == len(color)
    assert set(order_list) == set(color.keys())
    seqs = {u: vertex_seq(u, adj, color, order_list) for u in adj}
    for u in adj:
        for w in adj[u]:
            assert seqs[u] != seqs[w], f"Collision on edge ({u},{w}): {seqs[u]}"
    return True

def gen_d_regular_bipartite_colored(m, d):
    for _ in range(200):
        adj = {i: [] for i in range(2*m)}
        color = {}
        ok = True
        for c in range(1, d+1):
            perm = list(range(m, 2*m))
            random.shuffle(perm)
            for i in range(m):
                u, v = i, perm[i]
                ek = edge_key(u, v)
                if ek in color:
                    ok = False
                    break
                color[ek] = c
                adj[u].append(v)
                adj[v].append(u)
            if not ok:
                break
        if ok and is_connected(adj) and all(is_connected(adj, {v}) for v in adj):
            return adj, color
    return None

K4 = {0:[1,2,3], 1:[0,2,3], 2:[0,1,3], 3:[0,1,2]}
K4_col = {(0,1):1, (2,3):1, (0,2):2, (1,3):2, (0,3):3, (1,2):3}
assert solve_regular_2conn(K4, K4_col, 3)

prism = {0:[1,2,3], 1:[0,2,4], 2:[0,1,5], 3:[0,4,5], 4:[1,3,5], 5:[2,3,4]}
prism_col = {(0,1):1,(1,2):2,(0,2):3, (3,4):1,(4,5):2,(3,5):3, (0,3):2,(1,4):3,(2,5):1}
assert solve_regular_2conn(prism, prism_col, 3)

K6 = {i:[j for j in range(6) if j != i] for i in range(6)}
K6_col = {}
for c in range(5):
    K6_col[edge_key(c, 5)] = c + 1
    K6_col[edge_key((c+1)%5, (c+4)%5)] = c + 1
    K6_col[edge_key((c+2)%5, (c+3)%5)] = c + 1
assert solve_regular_2conn(K6, K6_col, 5)

tested = 0
for d in [3, 4, 5, 6]:
    for m in [d, d+2, d+5, d+10]:
        for _ in range(30):
            res = gen_d_regular_bipartite_colored(m, d)
            if res:
                adj, col = res
                assert solve_regular_2conn(adj, col, d)
                tested += 1

print(f"ALL {tested + 3} TESTS PASSED WITH ZERO ERRORS!")
