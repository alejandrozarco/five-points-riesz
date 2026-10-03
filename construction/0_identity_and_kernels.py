"""Preliminary checks for N = 5: (a) the sum over unordered triples of R equals 1/2 of the sum over all ordered
(i, j, l) of S, for a random configuration and random PSD F_k; (b) ranks of the kernel matrices Z_k at the TBP."""
import numpy as np, itertools
from polyk import *
n = 5
def sym_s_poly(F_list):
    sform = np.zeros(N3)
    for k, F in enumerate(F_list):
        m = F.shape[0]
        sform = sform + SYM_AVG @ Yk_columns(k, m) @ F.reshape(-1)
    return sform
def R_poly(sform):
    s_uu1 = subst_matrix((0, 0, 1.0)) @ sform; s_vv1 = subst_matrix((1, 1, 1.0)) @ sform
    s_tt1 = subst_matrix((2, 2, 1.0)) @ sform; s_111 = subst_matrix((1.0, 1.0, 1.0)) @ sform
    return (n - 2) * sform + s_uu1 + s_vv1 + s_tt1 + s_111 * (1.0 / (n - 1))
rng = np.random.default_rng(3)
sizes = [6, 5, 4, 3]
F = [(lambda A: A @ A.T)(rng.normal(size=(m, m))) for m in sizes]
sp_ = sym_s_poly(F); Rp = R_poly(sp_)
X = rng.normal(size=(n, 3)); X /= np.linalg.norm(X, axis=1, keepdims=True); G = X @ X.T
sumR = sum(peval(Rp, G[i, j], G[i, l], G[j, l]) for i, j, l in itertools.combinations(range(n), 3))
sumall = sum(peval(sp_, G[i, j], G[i, l], G[j, l]) for i in range(n) for j in range(n) for l in range(n))
print("sum_triples R =", sumR, " sum_all s =", sumall, " ratio =", sumR / sumall)
# TBP
TBP = np.array([[0, 0, 1], [0, 0, -1]] + [[np.cos(2*np.pi*j/3), np.sin(2*np.pi*j/3), 0] for j in range(3)])
GT = np.round(TBP @ TBP.T, 12)
print(GT)
for k, m in enumerate(sizes + [2, 1]):
    Q = Qk(k)[k]
    Z = np.zeros((m, m))
    for i in range(n):
        for j in range(n):
            for l in range(n):
                u, v, t = GT[i, j], GT[i, l], GT[j, l]
                q = peval(Q, u, v, t)
                for a in range(m):
                    for b in range(m):
                        Z[a, b] += u**a * v**b * q
    ev = np.linalg.eigvalsh(Z)
    print(f"k={k} m={m} rank Z_k = {int((ev > 1e-9*max(1,ev.max())).sum())}  eig = {np.round(ev, 6)}")
