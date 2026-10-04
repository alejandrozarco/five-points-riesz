"""Stage 3 of 3: exact checks on the projected solution (Sylvester minors; phi - H factorisation) and writing of
certificate/cert_n5_s<s>.json (s even). Reads stage.pkl and stage2.pkl."""
import pickle, json, time
from fractions import Fraction as Fr
import sympy as sy
from flint import fmpq_mat, fmpq
t0 = time.time()
d = pickle.load(open('stage.pkl', 'rb')); x = pickle.load(open('stage2.pkl', 'rb'))['x']
cols = d['cols']; D = d.get('D', 10); RS = d.get('RS', 2); KS = RS // 2; E_TBP = Fr(d.get('E_TBP', '17/4'))
def unpack(kind, blk):
    idx = [(ci, p, q) for ci, (kk, bb, p, q) in enumerate(cols) if kk == kind and bb == blk]
    m = max(max(p, q) for _, p, q in idx) + 1
    M = [[Fr(0)] * m for _ in range(m)]
    for ci, p, q in idx: M[p][q] = M[q][p] = x[ci]
    return M
def sylvester_min(M):
    """all leading principal minors > 0 <=> positive definite (exact); returns list of minors' signs + min value."""
    m = len(M); Q = fmpq_mat(m, m)
    for i in range(m):
        for j in range(m): Q[i, j] = fmpq(M[i][j].numerator, M[i][j].denominator)
    mins = []
    for k in range(1, m + 1):
        sub = fmpq_mat([[Q[i, j] for j in range(k)] for i in range(k)])
        mins.append(sub.det())
    return all(v > 0 for v in mins), None
res = {}
Fblocks = sorted({bb for kk, bb, p, q in cols if kk == "F"})
Bblocks = sorted({bb for kk, bb, p, q in cols if kk == "B"})
mats = {}
for k in Fblocks:
    M = unpack("F", k); ok, mn = sylvester_min(M); res[f"F{k}"] = ok; mats[f"F{k}"] = M
for r in Bblocks:
    M = unpack("B", r); ok, mn = sylvester_min(M); res[f"B{r}"] = ok; mats[f"B{r}"] = M
print("positive definite (exact Sylvester):", res, f"({time.time()-t0:.1f}s)", flush=True)
assert all(res.values())
# H <= phi = (2-2t)^(-KS) on [-1, 1)
t = sy.symbols('t')
H = sum(sy.Rational(x[j].numerator, x[j].denominator) * sy.chebyshevt(j, t) for j in range(D + 1))
p = sy.Poly(sy.expand(1 - (2 - 2 * t) ** KS * H), t)
q, rem = sy.div(p, sy.Poly((t + 1) * (2 * t + 1) ** 2 * t ** 2, t))
print("remainder zero:", rem.is_zero, " quotient deg", q.degree(), " roots of quotient in [-1,1]:", q.count_roots(-1, 1),
      " q(0) =", float(q.eval(0)), " min q on grid =", min(float(q.eval(sy.Rational(i, 200))) for i in range(-200, 201)))
assert rem.is_zero and q.count_roots(-1, 1) == 0 and q.eval(0) > 0
def s(v): return f"{v.numerator}/{v.denominator}" if v.denominator != 1 else str(v.numerator)
phis = "1/(2-2t)" if KS == 1 else f"1/(2-2t)^{KS}"
cert = dict(
    description=(f"N = 5 points on S^2, Riesz s = {RS} (phi(t) = {phis}, t = <x_i,x_j>): exact three-point certificate. "
                 "Identity: (H(u)+H(v)+H(t))/3 - e/10 - R(u,v,t) = sum_r g_r(u,v,t) z_r^T B_r z_r, where "
                 "R = 3 s(u,v,t) + s(u,u,1) + s(v,v,1) + s(t,t,1) + s(1,1,1)/4 and s = sum_k <F_k, Sym(u^a v^b Q_k(u,v,t))>; "
                 "F_k = N_k F'_k N_k^T, B_r = M_r B'_r M_r^T. AI-produced, not peer reviewed."),
    D=D, n=5, e=s(E_TBP), H_chebyshev=[s(x[j]) for j in range(D + 1)],
    F_sizes=[len(d['Fred'][k]) for k in Fblocks],
    F_reducers=d['Fred'], F_reduced=[[[s(v) for v in row] for row in mats[f"F{k}"]] for k in Fblocks],
    sos_g=["1", "1+u", "1+v", "1+t", "1-u", "1-v", "1-t", "detG=1+2uvt-u^2-v^2-t^2"], sos_degrees=[D // 2] + [D // 2 - 1] * 6 + [D // 2 - 2],
    sos_monomials="all (a,b,c) with a+b+c <= d, in itertools.product order",
    sos_reducers=d['SRED'], sos_reduced=[[[s(v) for v in row] for row in mats[f"B{r}"]] for r in Bblocks])
out = f'cert_n5_s{RS}.json'
json.dump(cert, open(out, 'w'))
import os; print("wrote", out, os.path.getsize(out) // 1024, "KB", f"({time.time()-t0:.1f}s)")
