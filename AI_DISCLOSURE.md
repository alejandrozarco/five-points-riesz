# AI disclosure

- **Who did the work.** AI models produced the content of this repository under the direction of the repository
  owner (alejandrozarco):
  - Claude Opus 5.5 (Anthropic) wrote the code, ran the computations, produced the certificate and wrote the text;
  - gpt-6-astra (OpenAI), as a separate read-only reviewer, reviewed the package before publication.
- **The owner's role.** The owner chose the question, after a public question on the Lean Zulip about whether the new
  seven- and eight-point methods give a simpler five-point argument. The owner directed the work and decided on
  publication. The owner did not check the mathematics or the code line by line.
- **What software checks.**
  - `check/check_n5_s2.py` checks the certificate in exact rational arithmetic (sympy, python-flint): the polynomial
    identity, positive definiteness, the inequality H ≤ φ, and the uniqueness enumeration.
  - Trusted beyond the checker: Python, sympy and python-flint, and the short mathematical argument in README.md
    (Bachoc–Vallentin positivity, the triple-sum identity and the final inequalities). That argument is written out
    but not formalised.
- **Findings of the AI review** (gpt-6-astra, 2026-10-03, before publication). The review found the mathematics and
  the certificate in order and reran the checker. It also found:
  - the checker's positive-definiteness test did not check symmetry, so leading minors alone do not imply
    definiteness. The certificate's matrices are symmetric, so the result stands; the check is now added;
  - the checker's assertions could be disabled with `python -O`; the checker now refuses to run in that mode;
  - wording: a byte-for-byte reproducibility claim, the description of the touching conditions, use of the word
    "proof", the novelty statement, and missing references (Schwartz 2013 for s = 2; de Laat's numerically sharp
    four-point bounds). These were corrected before the first publication.
- **Status.** AI reviews are not peer review. No human expert has checked this work.
