# KempnerResearch

Research artifact for the sharp coprime-fiber obstruction for the
Kempner/Smarandache function.

## Main result

For

\[
S(n)=\min\{m\ge 1:n\mid m!\},
\qquad
E(z)=\max_{p\mid z}v_p(z),
\]

if `x,y > 1` are coprime and `S(x) = S(y) = m`, then

\[
m+\min\{E(x),E(y)\}\le E(x)E(y).
\]

The inequality is sharp for infinitely many coprime pairs. The report also
derives a smooth-number restriction on hypothetical counterexamples to the
Tuţescu consecutive-value conjecture. It does **not** prove that conjecture.

## Status

The core inequality has a kernel-checked Lean/Mathlib formalization. The
ordinary proof, literature claims, and surrounding consequences have not yet
received independent expert peer review. The MathSciNet/zbMATH audit found no
equivalent result in the searches described in the report; that supports
"apparently novel," not certified novelty.

The fixed-fiber search framework itself is not claimed as new: a September
2004 contribution by T. D. Noe already described searching a common Kempner
value through activating prime powers and a linear Diophantine equation on
[PrimePuzzles Conjecture 37](https://www.primepuzzles.net/conjectures/conj_037.htm).
The claimed contribution here is the sharp quantitative obstruction and its
consequences.

OpenAI Codex assisted with exploratory proof search, literature-query
formulation, computation, Lean formalization, and drafting. A human author
must independently verify and take responsibility for the work before journal
submission.

## Contents

- [REPORT.md](REPORT.md): theorem, ordinary proof, Tutescu reduction,
  computation, digestion, and novelty audit.
- [output/pdf/kempner_coprime_fiber_result.pdf](output/pdf/kempner_coprime_fiber_result.pdf):
  self-contained, text-extractable handoff for an independent reviewer or LLM.
- [KempnerResearch/Basic.lean](KempnerResearch/Basic.lean): Mathlib
  formalization of the theorem.
- [scripts/audit_activations.py](scripts/audit_activations.py): exhaustive
  local activation audit.
- [scripts/search_consecutive.cpp](scripts/search_consecutive.cpp): direct
  consecutive-value and structural-survivor sieve.

## Verification

```bash
lake build
python3 scripts/audit_activations.py --max-value 1000000
g++ -O3 -std=c++20 -Wall -Wextra -Wpedantic \
  scripts/search_consecutive.cpp -o /tmp/search_consecutive
/tmp/search_consecutive --limit 100000000
```

## Regenerate the PDF

```bash
uv run --with reportlab python scripts/make_result_pdf.py
```
