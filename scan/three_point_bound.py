"""Floating-point three-point bound for N = 5 (the same SDP as construction/1_build_sdp.py, without facial reduction
and without touching conditions): maximise e subject to the identity and H <= phi on [a, 1), phi(t) = (2-2t)^(-s/2)
(s = 0: -log(2-2t)/2), sampled densely. With a = -1 there is no cut. Degree D from the environment variable POLYD.
Returns e, the margin e - E_s(TBP), the identity residual and the PSD defect of the solver's solution.

usage: POLYD=10 python3 three_point_bound.py S A [K]      (Riesz s; A = -1 for no cut; K = number of kernel blocks)
"""
import sys, time, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "construction"))
import numpy as np
from numpy.polynomial import chebyshev as C
from polyk import *
from kernels import phi, EP

n = 5; NP = n*(n-1)//2


def run(s, a, K=4, sizes=None, nsamp=20001, verbose=False, solver='CLARABEL', cap=None):
    sizes = sizes or [6 - k for k in range(K)]
    pr = SOSProblem()
    # s(u,v,t) = sum_k <F_k, S_k>
    sform = LinPoly()
    for k, m in enumerate(sizes):
        pr.psd(f"F{k}", m)
        sform = sform + LinPoly({f"F{k}": np.asarray(SYM_AVG @ Yk_columns(k, m))})
    s_uu1 = sform.apply(subst_matrix((0, 0, 1.0)))
    s_vv1 = sform.apply(subst_matrix((1, 1, 1.0)))
    s_tt1 = sform.apply(subst_matrix((2, 2, 1.0)))
    s_111 = sform.apply(subst_matrix((1.0, 1.0, 1.0)))
    R = (n - 2) * sform + s_uu1 + s_vv1 + s_tt1 + s_111 * (1.0 / (n - 1))
    pr.free("hc", D + 1); pr.free("e", 1)
    Hsum = LinPoly({"hc": (univ_embed(0) + univ_embed(1) + univ_embed(2)) @ cheb2mono() / 3.0})
    eterm = LinPoly({"e": -pconst(1.0 / NP)[:, None]})
    slack = Hsum + eterm - R
    detG = ONE + 2 * pmul(pmul(U, V), T) - pmul(U, U) - pmul(V, V) - pmul(T, T)
    d0, d1, d2 = D // 2, D // 2 - 1, D // 2 - 2     # SOS multiplier degrees grow with D (5, 4, 3 at D = 10)
    blocks = [(ONE, d0), (U - a * ONE, d1), (V - a * ONE, d1), (T - a * ONE, d1), (ONE - U, d1), (ONE - V, d1),
              (ONE - T, d1), (detG, d2)]
    pr.add_identity(slack, blocks, "slack")
    # H <= phi on [a, 1): dense sampling (cosine-clustered + uniform)
    f = phi(s)
    ts = np.unique(np.concatenate([np.linspace(a, 0.9999, nsamp),
                                   (a + 1) / 2 + (1 - a) / 2 * np.cos(np.linspace(0, np.pi, 4001))[1:]]))
    ts = ts[ts < 1]
    Vd = C.chebvander(ts, D)
    fv = f(ts)
    if cap is not None: fv = np.minimum(fv, cap)       # H <= min(phi, cap) is stronger than H <= phi (conditioning)
    pr.cons.append(Vd @ pr.vars["hc"] <= fv)
    t0 = time.time()
    prob = pr.solve(pr.vars["e"][0], solver=solver, verbose=verbose)
    dt = time.time() - t0
    xs = pr.xs()
    e = float(xs["e"][0])
    # post-validation of H <= phi on a fine grid
    tf = np.concatenate([np.linspace(a, 1 - 1e-4, 2_000_001), 1 - np.logspace(-4, -12, 2000)])
    viol = max(0.0, float((C.chebval(tf, xs["hc"]) - f(tf)).max()))
    res = pr.residual_report()["slack"]
    Fneg = min(0.0, min(np.linalg.eigvalsh(xs[f"F{k}"])[0] for k in range(len(sizes))))
    # conservative correction: slack >= -(l1 resid + defect) on domain -> sum H >= e - 21*(...)
    e_corr = e - NP * viol - NP * (res[0] + res[1])
    EPs = EP(s)
    return dict(s=s, a=a, sizes=sizes, status=prob.status, e=e, margin=e - EPs, viol=viol,
                resid=res[0], defect=res[1], Fneg=Fneg, margin_corr=e_corr - EPs, time=dt,
                hc=xs["hc"])


if __name__ == "__main__":
    s = float(sys.argv[1]); a = float(sys.argv[2]); K = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    r = run(s, a, K)
    print(f"s={s} a={a} K={K} status={r['status']} e={r['e']:.12f} margin={r['margin']:+.4e} "
          f"H-viol={r['viol']:.1e} resid_l1={r['resid']:.1e} psd_def={r['defect']:.1e} "
          f"Fneg={r['Fneg']:.1e} margin_corr={r['margin_corr']:+.4e} ({r['time']:.1f}s)")
