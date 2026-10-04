"""phi_s(t) = (2-2t)^(-s/2) (s = 0: -log(2-2t)/2) and E_s(TBP) (TBP inner products: -1 once, 0 six times, -1/2 three times)."""
import numpy as np, mpmath as mp
mp.mp.dps = 40
def phi(s):
    s = float(s)
    if s == 0: return lambda t: -0.5*np.log(2-2*np.asarray(t, float))
    return lambda t: (2-2*np.asarray(t, float))**(-s/2)
def phi_mp(s, t):
    t = mp.mpf(t); return -mp.log(2-2*t)/2 if s == 0 else (2-2*t)**(-mp.mpf(s)/2)
def EP(s):
    return float(phi_mp(s, -1) + 6*phi_mp(s, 0) + 3*phi_mp(s, mp.mpf(-1)/2))
