"""Stage 2 of 3: exact least-norm projection of the float SDP solution onto the affine space of exact certificates
(identity with e = E_s(TBP) and the touching conditions), using a common dyadic denominator. Reads stage.pkl, writes stage2.pkl."""
import pickle, time, sys
from fractions import Fraction as Fr
from flint import fmpq_mat, fmpq, fmpz_mat, fmpz
t0 = time.time()
d = pickle.load(open('stage.pkl', 'rb'))
A, b, x0, nrow, ncol = d['A'], d['b'], d['x0'], d['nrow'], d['ncol']
SH = 2 ** 50
xt = [Fr(round(v * SH), SH) for v in x0]
# independent rows via rref of A^T (exact, small entries)
Am = fmpq_mat(nrow, ncol)
for i in range(nrow):
    for c, v in A[i].items(): Am[i, c] = fmpq(v.numerator, v.denominator)
rr, rank = Am.transpose().rref()
I = []
for i in range(rank):
    for c in range(nrow):
        if rr[i, c] != 0: I.append(c); break
print("rank", rank, f"({time.time()-t0:.1f}s)", flush=True)
# integer scaling: A_I has denominators | 8 ; residual r = A_I xt - b_I has denominator | 8*2^50
import math
S = 1
for i in I:
    for v in A[i].values(): S = S * v.denominator // math.gcd(S, v.denominator)
for i in I: S = S * b[i].denominator // math.gcd(S, b[i].denominator)
print('S =', S)
AiZ = fmpz_mat(len(I), ncol)
for a, i in enumerate(I):
    for c, v in A[i].items():
        w = v * S; assert w.denominator == 1; AiZ[a, c] = int(w)
X = [int(v * SH) for v in xt]
# r_scaled = S*SH*(A_I xt - b_I) is an integer vector
rZ = []
for i in I:
    acc = sum(v * S * X[c] for c, v in A[i].items()) - b[i] * S * SH
    assert acc.denominator == 1; rZ.append(int(acc))
print("max |r| (scaled back):", max(abs(v) for v in rZ) / (S * SH), f"({time.time()-t0:.1f}s)", flush=True)
# solve (Ai Ai^T) y = r  with Ai = S*A_I :   A_I xt - b_I = r/(S*SH) ;  correction x -= A_I^T y'  where
# (A_I A_I^T) y' = r/(S*SH)  <=>  (Ai Ai^T) y' = S*r/SH ... use rational solve on the integer Gram matrix
GZ = AiZ * AiZ.transpose()
print("Gram built", f"({time.time()-t0:.1f}s)", flush=True)
Gq = fmpq_mat(GZ); rhs = fmpq_mat(len(I), 1)
for a in range(len(I)): rhs[a, 0] = fmpq(rZ[a] * S, S * SH)       # = S * (A_I xt - b_I)... see below
# (A_I A_I^T) y' = res  with A_I = Ai/S  ->  (Ai Ai^T) y' = S^2 res ; res = rZ/(S*SH)  -> rhs = S * rZ / SH
for a in range(len(I)): rhs[a, 0] = fmpq(rZ[a] * S, SH)
y = Gq.solve(rhs)
print("solved", f"({time.time()-t0:.1f}s)", flush=True)
# x = xt - A_I^T y'
corr = [Fr(0)] * ncol
yv = [Fr(int(y[a, 0].p), int(y[a, 0].q)) for a in range(len(I))]
for a, i in enumerate(I):
    if yv[a] == 0: continue
    for c, v in A[i].items(): corr[c] += v * yv[a]
x = [xt[c] - corr[c] for c in range(ncol)]
bad = 0
for i in range(nrow):
    if sum(v * x[c] for c, v in A[i].items()) != b[i]: bad += 1
print("rows violated:", bad, " max|corr| =", float(max(abs(c) for c in corr)), f"({time.time()-t0:.1f}s)", flush=True)
assert bad == 0, 'exact system not satisfied'
pickle.dump(dict(x=x), open('stage2.pkl', 'wb'))
