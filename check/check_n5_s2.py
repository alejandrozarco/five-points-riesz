"""Independent exact checker for cert_n5_s2.json (N = 5 points on S^2, Riesz s = 2).

Reads only the JSON and recomputes everything exactly: rational arithmetic (sympy polynomial rings over QQ,
python-flint), and an exact principal-minor PSD test in the uniqueness enumeration. It does not import the code
that produced the certificate. All checks are assertions; the script refuses to run with python -O.

Claim checked (A)-(C):
  (A) polynomial identity in Q[u,v,t]:
        (H(u)+H(v)+H(t))/3 - e/10 - R(u,v,t) = sum_r g_r * z_r^T B_r z_r,
        R = (n-2) S(u,v,t) + S(u,u,1) + S(v,v,1) + S(t,t,1) + S(1,1,1)/(n-1),
        S = sum_k sum_{a,b} F_k[a,b] Sym(u^a v^b Q_k(u,v,t)),  Sym = average over the 6 permutations of (u,v,t),
        Q_0 = 1, Q_1 = t - uv, Q_{k+1} = 2 (t - uv) Q_k - (1-u^2)(1-v^2) Q_{k-1},
        F_k = N_k F'_k N_k^T, B_r = M_r B'_r M_r^T, e = 17/4;
  (B) every F'_k and B'_r is positive definite (exact leading principal minors), so F_k, B_r are PSD;
  (C) phi(t) - H(t) >= 0 on [-1, 1), phi(t) = 1/(2-2t), with equality exactly at t in {-1, -1/2, 0}.
Then, for any 5 distinct points with Gram entries t_ij: g_r >= 0 on Gram-feasible triples, the Bachoc-Vallentin
positivity sum_{i,j,l} S(t_ij, t_il, t_jl) >= 0, and sum over the 10 triples of R = (1/2) sum_{i,j,l} S give
sum_{i<j} H(t_ij) >= e; with (C), E_2 = sum phi(t_ij) >= 17/4 = E_2(TBP).
(D) uniqueness: equality forces every t_ij in {-1, -1/2, 0}; enumerate all such Gram matrices that are PSD of rank
    <= 3 and check that energy 17/4 occurs only for the TBP Gram matrix up to relabelling.
"""
import json, sys, itertools, time
from fractions import Fraction as Fr
from sympy import QQ, Rational, Matrix, symbols, Poly, div, expand
from sympy.polys.rings import ring

if not __debug__:
    raise SystemExit("assertions are disabled (python -O / PYTHONOPTIMIZE): refusing to run")
t0 = time.time()
C = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "cert_n5_s2.json"))
q = lambda s: QQ(Fr(s).numerator, Fr(s).denominator)
R3, u, v, t = ring("u,v,t", QQ)
n = C["n"]; e = q(C["e"]); D = C["D"]
assert n == 5 and e == QQ(17, 4) and D == 10
# structure of the certificate (so that no block can be silently dropped by zip/truncation)
assert len(C["H_chebyshev"]) == D + 1
assert len(C["F_reducers"]) == len(C["F_reduced"]) == 4
assert C["sos_degrees"] == [5, 4, 4, 4, 4, 4, 4, 3]
assert len(C["sos_reducers"]) == len(C["sos_reduced"]) == 8
def nmon(d): return len([m for m in itertools.product(range(d + 1), repeat=3) if sum(m) <= d])
for k, (N, Fp) in enumerate(zip(C["F_reducers"], C["F_reduced"])):
    assert len(N) == D // 2 + 1 - k and all(len(row) == len(Fp) for row in N) and all(len(row) == len(Fp) for row in Fp)
for d, M, Bp in zip(C["sos_degrees"], C["sos_reducers"], C["sos_reduced"]):
    assert len(M) == nmon(d) and all(len(row) == len(Bp) for row in M) and all(len(row) == len(Bp) for row in Bp)

def cheb(j, x):
    a, b = R3(1), x
    if j == 0: return a
    for _ in range(j - 1): a, b = b, 2 * x * b - a
    return b
H = lambda x: sum((q(c) * cheb(j, x) for j, c in enumerate(C["H_chebyshev"])), R3(0))
Q = [R3(1), t - u * v]
W = (1 - u ** 2) * (1 - v ** 2)
while len(Q) < len(C["F_reduced"]) + 1: Q.append(2 * (t - u * v) * Q[-1] - W * Q[-2])
def Sym(p):
    out = R3(0)
    for perm in itertools.permutations((u, v, t)):
        out += p.compose([(u, perm[0]), (v, perm[1]), (t, perm[2])])
    return out * QQ(1, 6)
def matmul3(N, Fp):  # N F' N^T, exact
    Nm = [[q(x) for x in row] for row in N]; Fm = [[q(x) for x in row] for row in Fp]
    m, r = len(Nm), len(Fm)
    NF = [[sum((Nm[i][k] * Fm[k][j] for k in range(r)), QQ(0)) for j in range(r)] for i in range(m)]
    return [[sum((NF[i][k] * Nm[j][k] for k in range(r)), QQ(0)) for j in range(m)] for i in range(m)]
def leading_minors_positive(Fp):
    """positive definite <=> symmetric and all leading principal minors > 0 (Sylvester)."""
    assert all(len(row) == len(Fp) for row in Fp)
    assert all(Fr(Fp[i][j]) == Fr(Fp[j][i]) for i in range(len(Fp)) for j in range(i)), "matrix not symmetric"
    M = Matrix([[Rational(Fr(x).numerator, Fr(x).denominator) for x in row] for row in Fp])
    from flint import fmpq_mat, fmpq
    m = M.shape[0]; Qm = fmpq_mat(m, m)
    for i in range(m):
        for j in range(m): Qm[i, j] = fmpq(int(M[i, j].p), int(M[i, j].q))
    return all(fmpq_mat([[Qm[i, j] for j in range(k)] for i in range(k)]).det() > 0 for k in range(1, m + 1))

# (B) positive definiteness
for k, Fp in enumerate(C["F_reduced"]):
    assert leading_minors_positive(Fp), f"F'_{k} not PD"
for r, Bp in enumerate(C["sos_reduced"]):
    assert leading_minors_positive(Bp), f"B'_{r} not PD"
print(f"(B) all {len(C['F_reduced'])} F' and {len(C['sos_reduced'])} B' blocks positive definite ({time.time()-t0:.0f}s)", flush=True)

# (A) identity
S = R3(0)
for k, (N, Fp) in enumerate(zip(C["F_reducers"], C["F_reduced"])):
    F = matmul3(N, Fp); m = len(F)
    for a in range(m):
        for b in range(m):
            if F[a][b] != 0: S += F[a][b] * Sym(u ** a * v ** b * Q[k])
def sub(p, a, b, c): return p.compose([(u, a), (v, b), (t, c)])
Rp = (n - 2) * S + sub(S, u, u, R3(1)) + sub(S, v, v, R3(1)) + sub(S, t, t, R3(1)) + sub(S, R3(1), R3(1), R3(1)) * QQ(1, n - 1)
lhs = (H(u) + H(v) + H(t)) * QQ(1, 3) - e * QQ(1, 10) - Rp
gs = [R3(1), 1 + u, 1 + v, 1 + t, 1 - u, 1 - v, 1 - t, 1 + 2 * u * v * t - u ** 2 - v ** 2 - t ** 2]
rhs = R3(0)
for r, (g, d, M, Bp) in enumerate(zip(gs, C["sos_degrees"], C["sos_reducers"], C["sos_reduced"])):
    mons = [m for m in itertools.product(range(d + 1), repeat=3) if sum(m) <= d]
    B = matmul3(M, Bp)
    z = [u ** a * v ** b * t ** c for (a, b, c) in mons]
    acc = R3(0)
    for i in range(len(z)):
        row = sum((B[i][j] * z[j] for j in range(len(z)) if B[i][j] != 0), R3(0))
        acc += z[i] * row
    rhs += g * acc
assert lhs == rhs, "identity fails"
print(f"(A) identity holds exactly in Q[u,v,t] ({time.time()-t0:.0f}s)", flush=True)

# (C) phi - H >= 0 on [-1, 1), touching exactly at -1, -1/2, 0
x = symbols("x")
Hx = sum(Rational(Fr(c).numerator, Fr(c).denominator) * __import__("sympy").chebyshevt(j, x) for j, c in enumerate(C["H_chebyshev"]))
pnum = Poly(expand(1 - (2 - 2 * x) * Hx), x)          # = (2-2x)(phi - H)
quo, rem = div(pnum, Poly((x + 1) * (2 * x + 1) ** 2 * x ** 2, x))
assert rem.is_zero and quo.count_roots(-1, 1) == 0 and quo.eval(0) > 0
print(f"(C) 1-(2-2x)H(x) = (x+1)(2x+1)^2 x^2 q(x), q > 0 on [-1,1] (deg q = {quo.degree()})", flush=True)

def psd_exact(G):
    """exact: a real symmetric matrix is PSD iff all its principal minors are >= 0."""
    m = G.shape[0]
    return all(G.extract(list(S_), list(S_)).det() >= 0 for r_ in range(1, m + 1) for S_ in itertools.combinations(range(m), r_))
# (D) uniqueness by enumeration of Gram matrices with entries in {-1, -1/2, 0}
vals = [Fr(-1), Fr(-1, 2), Fr(0)]; phi = {Fr(-1): Fr(1, 4), Fr(-1, 2): Fr(1, 3), Fr(0): Fr(1, 2)}
pairs = list(itertools.combinations(range(5), 2)); found = []; feasible = 0
for combo in itertools.product(vals, repeat=10):
    G = [[Fr(1) if i == j else Fr(0) for j in range(5)] for i in range(5)]
    for (i, j), c in zip(pairs, combo): G[i][j] = G[j][i] = c
    M = Matrix(5, 5, lambda i, j: Rational(G[i][j].numerator, G[i][j].denominator))
    if M.rank() > 3: continue
    if not psd_exact(M): continue                                  # PSD (exact rational principal minors)
    feasible += 1
    E = sum(phi[c] for c in combo)
    if E <= Fr(17, 4): found.append((E, combo))
print(f"(D) PSD rank<=3 Gram matrices with entries in {{-1,-1/2,0}}: {feasible}; with energy <= 17/4: {len(found)}")
assert feasible == 25 and len(found) == 10
tbp_multiset = sorted([Fr(-1)] + [Fr(0)] * 6 + [Fr(-1, 2)] * 3)
assert all(E == Fr(17, 4) and sorted(c) == tbp_multiset for E, c in found)
# all found Gram matrices are TBP up to relabelling: one antipodal pair, the other three mutually at -1/2
for E, combo in found:
    G = {p: c for p, c in zip(pairs, combo)}
    anti = [p for p, c in G.items() if c == -1]; assert len(anti) == 1
    rest = [i for i in range(5) if i not in anti[0]]
    assert all(G[tuple(sorted(pq))] == Fr(-1, 2) for pq in itertools.combinations(rest, 2))
print(f"    all {len(found)} minimisers are the TBP Gram matrix up to relabelling ({time.time()-t0:.0f}s)")
print("CERTIFICATE VERIFIED")
