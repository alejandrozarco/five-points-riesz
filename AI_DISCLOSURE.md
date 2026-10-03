# AI disclosure

- **Who did the work.** AI models produced the content of this repository under the direction of the repository
  owner (alejandrozarco). Claude Opus 5.5 (Anthropic) wrote all code, ran the computations, produced both certificates
  (`cert_n5_s2.json` and `cert_n5_s1.json`) and wrote the text. Separate, read-only AI reviewers checked the package
  before each release (see below).
- **The owner's role.** The owner chose the question, after a public question on the Lean Zulip about whether the new
  seven- and eight-point methods give a simpler five-point argument. The owner directed the work and decided on
  publication. The owner did not check the mathematics or the code line by line.
- **What software checks.**
  - `check/check_n5_s2.py` checks the s = 2 certificate in exact rational arithmetic (sympy, python-flint): the
    polynomial identity, positive definiteness, H ≤ φ₂, and the uniqueness enumeration.
  - `check/check_n5_s1.py` checks the Coulomb certificate:
    - the identity, per component in K = Q(√2, √3);
    - positive definiteness at the 8 corners of a rational box of width 10⁻⁶⁰ around (√2, √3, √6), by convexity;
    - H > 0 and 1 − (2−2t)H² = (t+1)(2t+1)²t² q with q > 0, by exact Bernstein coefficients;
    - an exact sign test in K;
    - the uniqueness energies compared in K.
  - Trusted beyond the checkers:
    - Python (including `fractions` and `math.isqrt`), sympy and python-flint;
    - the short mathematical arguments in README.md (Bachoc–Vallentin positivity, the triple-sum identity, the final
      inequalities) and in the docstring of `check_n5_s1.py` (the sign test, the box/convexity and Bernstein
      arguments).

    These arguments are written out but not formalised.
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
- **Status.** AI reviews are not peer review. No human expert has checked this work.
