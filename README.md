# Five points on the sphere: exact three-point certificates for the Coulomb and Riesz $`s = 2`$ energies

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23125753.svg)](https://doi.org/10.5281/zenodo.23125753)

Status: **produced by AI models under the direction of the repository owner; not peer reviewed** (see
[`AI_DISCLOSURE.md`](AI_DISCLOSURE.md)).

> [!IMPORTANT]
> This repository is an AI-produced **warrant**: computer-checked certificates that no human has digested. The
> theorems they certify are already known (Schwartz; see below). What is new here, as far as we know, is the form of
> the certificates. Corrections and comments are welcome via GitHub issues. Credit for a human-readable treatment
> belongs to whoever writes one.

## Statement

For points $`x_1, \dots, x_5`$ on the unit sphere $`S^2 \subset \mathbb{R}^3`$ and $`s > 0`$, let

```math
E_s(x) = \sum_{i < j} \lVert x_i - x_j \rVert^{-s}.
```

The two certificates in `certificate/` give, for all pairwise distinct $`x_1,\dots,x_5 \in S^2`$,

```math
E_1(x) \ \ge\ \tfrac12 + 3\sqrt2 + \sqrt3 = E_1(\mathrm{TBP}) \quad\text{(Coulomb; the five-electron Thomson problem)},
\qquad
E_2(x) \ \ge\ \tfrac{17}{4} = E_2(\mathrm{TBP}),
```

where TBP is the triangular bipyramid: two antipodal poles and an equilateral triangle on the equator. In both cases
equality holds only for the TBP, up to an orthogonal map of $`\mathbb{R}^3`$ and a relabelling of the points.

**Known results.** Schwartz established the cases $`s = 1`$ and $`s = 2`$ (*The five-electron case of Thomson's
problem*, Exp. Math. 22 (2013)). His later work establishes uniqueness of the TBP for all $`0 < s < s_*`$,
$`s_* \approx 15.048`$ (*The phase transition in 5 point energy minimization*; *Divide and conquer: a distributed
approach to five point energy minimization*, arXiv:2301.05090). The logarithmic case is Dragnev, Legg and Townsend,
Pacific J. Math. 207 (2002). Both of Schwartz's arguments are computer-assisted, by subdivision of the configuration
space.

**Form of the certificates.** For each energy, the lower bound is a single global three-point
semidefinite-programming certificate of Bachoc–Vallentin and Cohn–Woo type, of polynomial degree 10. There is no
subdivision of the configuration space, and the bound is sharp: it equals $`E_s(\mathrm{TBP})`$ exactly. Verification
uses exact arithmetic. The Coulomb checker additionally uses rational box enclosures of $`\sqrt2, \sqrt3, \sqrt6`$
and Bernstein subdivision of $`[-1, 1]`$ (both exact). Uniqueness then follows
from a finite enumeration of Gram matrices.
- For $`s = 2`$ all numbers are rational.
- For $`s = 1`$ the values of the kernel at the TBP are irrational, so the certificate's numbers lie in
  $`K = \mathbb{Q}(\sqrt2, \sqrt3)`$. They are stored exactly as $`a + b\sqrt2 + c\sqrt3 + d\sqrt6`$ with rational
  $`a, b, c, d`$.

Related computations:
- Cohn and Woo (*Three-point bounds for energy minimization*, J. Amer. Math. Soc. 25 (2012), §5.3) report that,
  apart from the two cases identified by Bachoc and Vallentin, they found no sharp three-point energy bounds on
  spheres.
- De Laat (*Moment methods in energy minimization: new bounds for Riesz minimal energy problems*, Trans. Amer. Math.
  Soc. 373 (2020), 1407–1453; arXiv:1610.04905) computed four-point bounds for five points (two truncations of his
  hierarchy) whose values agree with the TBP energy to 28 digits for $`s = 1, \dots, 7`$.

We are not aware of an earlier published exact three-point certificate for these five-point results. Pointers to
earlier work are welcome.

## Why a certificate implies the bound

Write $`t_{ij} = \langle x_i, x_j\rangle`$ and $`\varphi_s(t) = (2-2t)^{-s/2}`$, so $`E_s = \sum_{i<j} \varphi_s(t_{ij})`$. Let
$`e_s = E_s(\mathrm{TBP})`$. Each certificate consists of:
- a univariate polynomial $`H`$ of degree 10;
- positive semidefinite matrices $`F_k`$ ($`k = 0,\dots,3`$);
- positive semidefinite Gram matrices $`B_r`$.

All entries are exact: rationals for $`s = 2`$, elements of $`K`$ for $`s = 1`$. Define

- $`Q_0 = 1`$, $`Q_1 = t - uv`$, $`Q_{k+1} = 2(t-uv)Q_k - (1-u^2)(1-v^2)Q_{k-1}`$;
- $`S(u,v,t) = \sum_k \sum_{a,b} (F_k)_{ab}\,\mathrm{Sym}\big(u^a v^b Q_k(u,v,t)\big)`$, where Sym averages over the
  six permutations of $`(u,v,t)`$;
- $`R = 3S(u,v,t) + S(u,u,1) + S(v,v,1) + S(t,t,1) + \tfrac14 S(1,1,1)`$.

The checker verifies four things:

1. **Identity** in $`\mathbb{Q}[u,v,t]`$, respectively $`K[u,v,t]`$ (checked as four rational identities, one per
   $`K`$-component):
   $`\tfrac13\big(H(u)+H(v)+H(t)\big) - \tfrac{e_s}{10} - R = \sum_r g_r\, z_r^{\mathsf T} B_r z_r`$, where
   - $`g_r \in \{1,\ 1\pm u,\ 1\pm v,\ 1\pm t,\ \det G\}`$;
   - $`\det G = 1 + 2uvt - u^2 - v^2 - t^2`$;
   - $`z_r`$ are vectors of monomials.
2. **Positive definiteness.** The matrices are stored in reduced form, $`F_k = N_k F_k' N_k^{\mathsf T}`$ and
   $`B_r = M_r B_r' M_r^{\mathsf T}`$, and every $`F_k'`$ and $`B_r'`$ is symmetric and positive definite (exact
   leading principal minors). For $`s = 1`$ each reduced matrix is affine in $`(\sqrt2, \sqrt3, \sqrt6)`$. It is
   checked to be positive definite at the 8 corners of a rational box of width $`10^{-60}`$ containing that point,
   which by convexity of the positive definite cone covers the true point.
3. **$`H \le \varphi_s`$ on $`[-1,1)`$, with equality exactly at $`t \in \{-1, -\tfrac12, 0\}`$.**
   - $`s = 2`$: $`1 - (2-2t)H(t) = (t+1)(2t+1)^2 t^2\, q(t)`$ with $`q > 0`$ on $`[-1,1]`$ (exact root counting).
   - $`s = 1`$: $`H > 0`$ on $`[-1,1]`$, and $`1 - (2-2t)H(t)^2 = (t+1)(2t+1)^2 t^2\, q(t)`$ with $`q > 0`$ on
     $`[-1,1]`$. Both are shown by exact Bernstein coefficients (with exact subdivision), using an exact sign test
     for elements of $`K`$.
4. **Uniqueness enumeration.** It lists the 5×5 Gram matrices with off-diagonal entries in $`\{-1,-\tfrac12,0\}`$
   that are positive semidefinite (all principal minors $`\ge 0`$) of rank $`\le 3`$. There are 25: the TBP in 10
   labellings, and $`\{\pm e_1, \pm e_2, e_3\}`$ in 15. Energy $`e_s`$ occurs only for the 10 labellings
   of the TBP (exact comparisons, in $`K`$ for $`s = 1`$).

The argument from these checks has five steps:
- **The right-hand side is nonnegative.** For a triple of unit vectors with Gram entries $`(u,v,t)`$, every
  $`g_r \ge 0`$: $`|u|,|v|,|t| \le 1`$, and $`\det G \ge 0`$ because $`\det G`$ is a 3×3 Gram determinant. So the
  right-hand side of (1) is $`\ge 0`$ at $`(t_{ij}, t_{il}, t_{jl})`$ for every triple $`\{i,j,l\}`$.
- **Positivity of $`S`$** (Bachoc–Vallentin). Fix a centre $`x_i`$. Let $`w_j \in \mathbb{C}`$ be the projection of
  $`x_j`$ to the tangent plane at $`x_i`$, in a complex coordinate. Then
  $`Q_k(t_{ij}, t_{il}, t_{jl}) = \mathrm{Re}(w_j^k \overline{w_l^k})`$, so
  $`\sum_{j,l} \sum_{a,b} (F_k)_{ab}\, t_{ij}^a t_{il}^b Q_k = \mathrm{Re}(c^* F_k c) \ge 0`$, with
  $`c_a = \sum_j t_{ij}^a w_j^k`$. Summing over centres gives $`\sum_{i,j,l \in [5]} S(t_{ij}, t_{il}, t_{jl}) \ge 0`$;
  the symmetrisation does not change the full sum.
- **Summing over triples.** Split the full sum over $`(i,j,l)`$ by coincidences of indices. This gives
  $`\sum_{\{i,j,l\}} R = \tfrac{n-2}{6}\sum_{i,j,l} S = \tfrac12 \sum_{i,j,l} S \ge 0`$ for $`n = 5`$.
- **The bound on $`\sum H`$.** Summing (1) over the 10 triples gives
  $`\sum_{i<j} H(t_{ij}) - e_s = \sum_{\{i,j,l\}} \big(\text{RHS of (1)}\big) + \tfrac12 \sum_{i,j,l} S \ge 0`$.
- **Conclusion.** By (3), $`E_s = \sum \varphi_s(t_{ij}) \ge \sum H(t_{ij}) \ge e_s`$. Equality forces
  $`t_{ij} \in \{-1, -\tfrac12, 0\}`$ for all pairs. By (4) the configuration is then the TBP; its Gram matrix fixes
  it up to an orthogonal map.

## Verify

```sh
pip install sympy python-flint          # tested with Python 3.9, sympy 1.14.0, python-flint 0.6.0
gunzip -k certificate/cert_n5_s2.json.gz certificate/cert_n5_s1.json.gz
shasum -a 256 -c certificate/cert_n5_s2.json.sha256 certificate/cert_n5_s1.json.sha256
python3 check/check_n5_s2.py certificate/cert_n5_s2.json      # about 1 minute
python3 check/check_n5_s1.py certificate/cert_n5_s1.json      # about 4 minutes
```

Each checker reads only its JSON and recomputes (1)–(4) exactly: rational arithmetic, exact sign decisions in $`K`$,
and an exact principal-minor test for positive semidefiniteness in the enumeration. It prints `CERTIFICATE VERIFIED`, and it refuses to run
with `python -O`, which would disable its assertions. The outputs of the recorded runs are in `verification/`.

## How the certificates were found (`construction/`, not needed for verification)

| file | role |
|---|---|
| `polyk.py` | polynomial and SOS toolkit; numpy, cvxpy, Clarabel |
| `0_identity_and_kernels.py` | numerical check of the triple-sum identity; ranks of the kernel matrices at the TBP (2, 0, 1, 1) |
| `1_build_sdp.py` | exact facial reduction from sharpness at the TBP; float SDP of degree 10 in the reduced coordinates; exact constraint system → `stage.pkl` |
| `2_project_exact.py` | exact least-norm projection onto {identity with $`e = 17/4`$; $`H = \varphi`$ at $`-1, -\tfrac12, 0`$; $`H' = \varphi'`$ at $`-\tfrac12, 0`$} → `stage2.pkl` |
| `3_check_and_write.py` | exact checks, then writes `cert_n5_s2.json` |
| `1c_build_sdp_coulomb.py` | Coulomb: the same facial reduction; float SDP with every block shifted by $`2\cdot10^{-7} I`$; exact constraint system with right-hand side in $`K`$ → `stage_s1.pkl` |
| `2c_exact_coulomb.py`, `kfield.py` | Coulomb: exact least-norm projection per $`K`$-component (including the touching conditions), box-corner and Bernstein checks, enumeration, then writes `cert_n5_s1.json` |

Run, in a copy of `construction/`:
- $`s = 2`$: `POLYD=10 python3 1_build_sdp.py 4 && python3 2_project_exact.py && python3 3_check_and_write.py`
  (about 2 minutes);
- Coulomb: `POLYD=10 python3 1c_build_sdp_coulomb.py 4 && python3 2c_exact_coulomb.py` (about 5 minutes).

For the Coulomb case, Clarabel failed numerically when the irrational touching conditions were also imposed in the
float SDP, so they are imposed only in the exact projection. On the machine used (macOS arm64, Python 3.9.6, numpy
1.26.4, scipy 1.13.1, cvxpy 1.7.5, Clarabel 0.11.1, sympy 1.14.0, python-flint 0.6.0) reruns reproduced both
JSON files byte for byte (transcripts with output hashes: `verification/construction_s2.txt`,
`verification/construction_s1.txt`). The floating-point SDP step may give different exact coefficients with other
solvers or environments, so verify any regenerated JSON with the independent checker.

Numerically, the same uncut degree-10 bound also appears sharp for the logarithmic energy, to solver precision. No
certificate for that case is included: there the kernel's values at the TBP are logarithms.

## Related work and credits

- C. Bachoc, F. Vallentin, *New upper bounds for kissing numbers from semidefinite programming*, J. Amer. Math. Soc.
  21 (2008): three-point bounds on spheres.
- H. Cohn, J. Woo, *Three-point bounds for energy minimization*, J. Amer. Math. Soc. 25 (2012).
- R. E. Schwartz, *The five-electron case of Thomson's problem*, Exp. Math. 22 (2013), arXiv:1001.3702 ($`s = 1, 2`$); *The phase
  transition in 5 point energy minimization* (monograph); *Divide and conquer: a distributed approach to five point
  energy minimization*, arXiv:2301.05090.
- P. D. Dragnev, D. A. Legg, D. W. Townsend, *Discrete logarithmic energy on the sphere*, Pacific J. Math. 207 (2002),
  345–358.
- The formulation of the three-point bound follows section 5 of `paper/PAPER.md` in Hung Tran's Lean formalisation of
  the Coulomb case for seven points ([huwngtran/thomson-n7-lean](https://github.com/huwngtran/thomson-n7-lean)). That
  formalisation follows the eight-point method of L. Kryvonos, L. Liehr and M. A. Taylor (arXiv:2609.22077) and its
  Lean development by J. Tooby-Smith and A. Zughaid
  ([Thomson-N-8-Warrant](https://github.com/jstoobysmith/Thomson-N-8-Warrant)). No code from those repositories is
  included here.
- D. de Laat, *Moment methods in energy minimization: new bounds for Riesz minimal energy problems*, Trans. Amer.
  Math. Soc. 373 (2020), 1407–1453, doi:10.1090/tran/7976, arXiv:1610.04905: numerically sharp four-point bounds for
  five points.
- The question whether these methods give a simpler five-point argument was raised by Jason Rute on the Lean Zulip
  (Autoformalization > Thomson problem, 2026-09-29).
- Companion repository (seven points, logarithmic energy):
  [alejandrozarco/thomson-n7-log](https://github.com/alejandrozarco/thomson-n7-log).

## Licence

Apache License 2.0 ([`LICENSE`](LICENSE)), for all code, data and text in this repository.
