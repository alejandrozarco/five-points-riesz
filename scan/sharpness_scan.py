"""Sharpness scan of the uncut degree-D three-point bound for N = 5 (TBP) over the Riesz exponent s (floating point).
margin = e - E_s(TBP): ~0 (|margin| below solver accuracy) = numerically sharp; clearly negative = not sharp.
H <= min(phi, cap) with cap = 20 |E_s(TBP)| + 10 (a stronger constraint than H <= phi; it improves conditioning). The
results are numerical estimates of a capped, sampled SDP, not certified lower bounds.
usage: POLYD=10 python3 sharpness_scan.py S1 S2 ...     (appends JSON lines to $OUT, default sharpness_scan.jsonl)
CAPF=k multiplies the cap by k (default 1; rows with k != 1 record "capf" and "maxH_over_cap")."""
import sys, json, os, numpy as np
import three_point_bound as c
from kernels import EP
out = open(os.environ.get("OUT", "sharpness_scan.jsonl"), "a")
for s in [float(x) for x in sys.argv[1:]]:
    capf = float(os.environ.get("CAPF", "1")); E = EP(s); cap = capf * (20 * abs(E) + 10)
    try:
        r = c.run(s, -1.0, 4, sizes=[c.D // 2 + 1 - k for k in range(4)], cap=cap)
        rec = dict(s=s, D=c.D, status=r["status"], e=r["e"], E_TBP=E, margin=r["margin"], rel=r["margin"] / abs(E),
                   resid=r["resid"], defect=r["defect"])
        if capf != 1:
            from numpy.polynomial import chebyshev as C
            ts = np.linspace(-1, 0.9999, 200001)
            rec.update(capf=capf, maxH_over_cap=float(C.chebval(ts, r["hc"]).max() / cap))
    except BaseException as ex:  # Clarabel SVD panics are BaseException
        if isinstance(ex, KeyboardInterrupt): raise
        rec = dict(s=s, D=c.D, error=str(ex)[:120])
    print(json.dumps(rec), flush=True); out.write(json.dumps(rec) + "\n"); out.flush()
