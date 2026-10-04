# AI disclosure

- **Who did the work.** AI models produced the content of this repository under the direction of the repository
  owner (alejandrozarco). Claude Opus 5.5 (Anthropic) generated the new code and adapted the attributed upstream
  code, including the Lean development; it ran the computations, produced the certificates (`cert_n5_s1.json` to `cert_n5_s6.json`, `cert_n5_s1_short.json`, `cert_n5_s2_short.json`) and
  wrote the text. Separate, read-only AI reviewers checked the package
  before each release (see below).
- **The owner's role.** The owner chose the question, after a public question on the Lean Zulip about whether the new
  seven- and eight-point methods give a simpler five-point argument. The owner directed the work and decided on
  publication. The owner did not check the mathematics or the code line by line.
- **What software checks.**
  - `check/check_n5_even.py` checks the certificates for s = 2, 4, 6 in exact rational arithmetic (sympy,
    python-flint): the polynomial identity, positive definiteness, H ≤ φ_s, and the uniqueness enumeration.
  - `check/check_n5_odd.py` checks the certificates for s = 1, 3, 5:
    - the identity, per component in K = Q(√2, √3);
    - positive definiteness at the 8 corners of a rational box of width 10⁻⁶⁰ around (√2, √3, √6), by convexity;
    - H > 0 and 1 − (2−2t)^s H² = (t+1)(2t+1)²t² q with q > 0, by exact Bernstein coefficients;
    - an exact sign test in K;
    - the uniqueness energies compared in K.
  - For s = 1 and s = 2, the Lean development in `lean/` checks the whole statement (bound, minorant, minimality and
    uniqueness) in the Lean kernel; Comparator compares its statements with `lean/N5R1/Challenge.lean` and
    `lean/N5R2/Challenge.lean`, and nanoda, an independent type checker, rechecks exports of them (records in
    `verification/lean/`). What is trusted there is
    the Lean kernel (or nanoda), the statement in `Challenge.lean`, and the definitions it imports from the
    regenerated upstream preamble.
  - Trusted beyond the Python checkers:
    - Python (including `fractions` and `math.isqrt`), sympy and python-flint;
    - the short mathematical arguments in README.md (Bachoc–Vallentin positivity, the triple-sum identity, the final
      inequalities) and in the docstring of `check_n5_odd.py` (the sign test, the box/convexity and Bernstein
      arguments).

    These arguments are written out but not formalised in Python. For s = 1 and s = 2, Lean formalises the complete
    minimality and uniqueness argument: rational certificate checks (for s = 1 per component of Q(√2, √3), with
    positivity from rational checks at the corners of a box around (√2, √3)), a Bernstein minorant lemma, and
    geometric uniqueness. For s = 3, 4, 5, 6 only the Python checkers apply.
  - The floating-point sharpness scan (`scan/`) is not checked by anything; it is reported as an observation.
- **AI reviews.**
  - **Version 1** (s = 2 only), reviewed by gpt-6-astra (OpenAI), 2026-10-03. The review found the mathematics in
    order and reran the checker. It also found:
    - the positive-definiteness test did not check symmetry, so leading minors alone do not imply definiteness;
    - the checker's assertions could be disabled with `python -O`;
    - wording problems: a byte-for-byte reproducibility claim, the description of the touching conditions, use of the
      word "proof", the novelty statement, and missing references (Schwartz 2013; de Laat).

    The certificate's matrices were symmetric, so the result stood. All of this was fixed before publication.
  - **Version 2** (Coulomb added), reviewed by gpt-6-astra and by Claude Fable 5.1 (Anthropic), independently,
    2026-10-03. Both found no soundness defect in either certificate, and both reran both checkers successfully. Fable
    also made independent spot checks of the enumeration, the identity, the triple-sum identity and the sign test.
    Findings, all addressed before publication:
    - a stale MANIFEST and a repository URL mismatch;
    - this disclosure was not updated;
    - "no interval arithmetic" needed qualifying, because the Coulomb checker uses rational box enclosures and
      Bernstein subdivision;
    - a construction comment overstated what the numerical shift guarantees;
    - K-elements lacked a length check;
    - the PSD test in the enumeration relied on sympy eigenvalues; it now uses exact principal minors;
    - corrections to the de Laat citation;
    - construction transcripts were to be archived.
  - **Version 3** (s = 3, 4, 5, 6; checkers generalised to even and odd s; Lean formalisation for s = 2; sharpness
    scan), reviewed by Claude Fable 5.1 and by gpt-6-astra, independently, 2026-10-04. Neither found a soundness defect
    in the checkers, the README argument, or the Lean statement and formalisation; both reran checkers (Fable: s = 3, 4 and
    the short s = 2 certificate, plus its own negative tests; Astra: s = 5), and Astra independently rechecked the
    touching values of all six certificates. Findings, all addressed before publication:
    - the short s = 2 certificate used by the Lean development was excluded by `.gitignore`;
    - the scan: the solver's H reaches the stabilising cap at larger s, so the solver's accuracy there is lower
      than first stated (Fable); the degree-12 and degree-14 runs kept the sum-of-squares degrees of degree 10, i.e.
      tested a restricted SDP (Astra). Those runs were redone with the fix; the solver failed on almost all of them,
      so the scan now reports degree 10 only, with weaker wording ("growing numerical discrepancies", no threshold);
      the earlier runs are kept in `scan/` as superseded;
    - missing attribution notes on Lean declarations adapted from huwngtran/thomson-n7-lean, and a sentence saying
      no upstream code was included; stale paths in generated file headers; the package name in the lake manifest;
    - wording: the scope of the Lean formalisation, the licence scope for adapted upstream material, the role of
      the AI model in adapting code, and the manifest.
  - **Version 4** (Lean formalisation of the Coulomb case s = 1), reviewed by Claude Fable 5.1 and by gpt-6-astra,
    independently, 2026-10-04. Both reviewed the sources and data; neither found a soundness defect. Both checked the
    statement in `lean/N5R1/Challenge.lean` against upstream's `coulombEnergy` and `SphereConfig`, the link in Lean
    between the corner matrices and the component matrices, the vanishing √6 components of the certificate, the box
    bounds, the minorant and the uniqueness argument (Astra rechecked all 27 equator cases and the factorisation
    identities independently); both reran `check_n5_odd.py` on `cert_n5_s1_short.json` (verified) and the emitter's
    check, and Fable regenerated the Lean data byte for byte and compiled `Main.lean` and the axiom check. The Lean
    build, Comparator and nanoda runs were done separately (`verification/lean/record_v4_2026-10-04.txt`); the reviewers
    assessed their records. Findings, all addressed before publication:
    - the short s = 1 certificate used by the Lean development was excluded by `.gitignore` (Fable);
    - the attribution scanner did not scan the N5R1/N5R2 directories by default; MANIFEST; a stale cross-check in
      `gen_minor_s1.py`; README credit details (Fable);
    - the nanoda negative control accepted any failure as a rejection; it now requires the type checker's error (the
      archived controls show that error); licence scope stated in CITATION.cff and .zenodo.json; this entry; a comment
      in `Cert3K.lean` (Astra).
- **Status.** AI reviews are not peer review. No human expert has checked this work.
