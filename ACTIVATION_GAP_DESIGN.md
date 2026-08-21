# Activation-gap rigidity and the `c = 1` reduction audit

Date: 2026-08-21

Status: the proposed fixed-shift activation theorem is valid as ordinary
mathematics, survived the audits below, and its finite arithmetic core is now
kernel-checked in `KempnerResearch/ActivationGap.lean`,
`KempnerResearch/ResidualCofactor.lean`, and
`KempnerResearch/ResidualComplement.lean`.  The stronger claim that a
hypothetical Tutescu counterexample must have `c = 1` has **not** been proved.
What is now proved exactly is both the strict controller-defect classification
and a five-branch factorization of every possible `c >= 2` case.  Coprimality
and equal Kempner value alone do not eliminate any of those five branches;
the consecutive equation and the full factorial exponent caps are
indispensable.

## Conventions and domain corrections

For a nonzero integer `h`, the notation in the research brief is interpreted as

\[
H(h)=\max_{p\mid |h|}p\,v_p(|h|), \qquad H(1)=H(-1)=0.
\]

The comma in the pasted formula must be multiplication.  The fixed-shift count
is over positive integers `n` satisfying `n+h>1`:

\[
C_h(X)=\#\{n\le X:n>1,\ n+h>1,\ S(n)=S(n+h)\}.
\]

These conventions are necessary when `h<0` and do not change the argument.

## Exact ordinary theorem

Let `h != 0`, let `x,y=x+h>1`, and suppose

\[
S(x)=S(y)=m.
\]

Choose controlling prime powers `p^a || x` and `q^b || y`, meaning

\[
S(p^a)=S(q^b)=m.
\]

### Shared controller

If `p=q`, put

\[
e_0=v_p((m-1)!)+1.
\]

Both controller exponents are at least `e_0`, so `p^{e_0}` divides both
inputs and hence divides `h`.  Activation at `m` also forces `p | m`: if
`p` did not divide `m`, multiplication by `m` would not change the
`p`-valuation of the factorial.  Write `m=pt`.  Then

\[
e_0\ge \left\lfloor\frac{m-1}{p}\right\rfloor+1=t,
\]

and therefore

\[
m\le p e_0\le p v_p(|h|)\le H(h).
\]

This part does not require `gcd(x,y)=1`.

### Distinct controllers

Suppose `p != q`, order them so that `p<q`, orient the two inputs
accordingly, and write

\[
m=pqc,\qquad c\ge1.
\]

For every integer `N>=1`, Legendre's formula gives

\[
v_p((pN-1)!)=N-1+v_p((N-1)!).
\]

Taking `N=qc` and using activation yields the exact lower threshold

\[
a\ge qc+v_p((qc-1)!).
\]

The same calculation for `q`, with `N=pc`, gives

\[
b\ge pc+v_q((pc-1)!).
\]

Let `A=E(x_p)` on the `p`-controller side and `B=E(x_q)` on the
`q`-controller side.  Since `qc-1>=p`,

\[
A\ge qc+1,\qquad B\ge pc.
\]

Thus the integers

\[
r=A-(qc+1),\qquad s=B-pc
\]

are nonnegative.  Direct expansion, with no inequality step, gives

\[
\boxed{(A-1)B-m=m(c-1)+qc\,s+pc\,r+rs.}
\]

Equivalently `(A-1)B` is at least `cm`, and hence

\[
\boxed{cm+\min(A,B)\le AB.}
\]

The right side of the defect identity vanishes exactly when

\[
c=1,\qquad r=0,\qquad s=0.
\]

Then `A=q+1` and `B=p`.  The exact activation threshold forces
`v_p((q-1)!)=1`, which for primes `p<q` is equivalent to `q<2p`.  This is
the existing sharp controller regime.  Conversely, primes `p<q<2p` give
the sharp pure-power pair `p^{q+1},q^p` at common value `pq`.

### Fixed-shift count

In the shared-controller case, `m<=H(h)`.  For each fixed `m`, every element
of the fiber divides `m!`, so these finitely many values contribute
`O_h(1)` pairs.

In the distinct-controller case, the displayed inequality implies `m<=AB`.
For `n<=X`, both inputs are at most `X+|h|`, so

\[
A,B\le\log_2(X+|h|),
\]

so `m=O_h((log X)^2)`.  Every prime factor of `n` is at most `m`, because
`n | m!`.  The standard estimate for smooth numbers therefore gives

\[
C_h(X)\le \Psi(X,O_h((\log X)^2))+O_h(1)
       =X^{1/2+o(1)}+O_h(1).
\]

This is an upper bound, not an asymptotic formula.

## What the first `c = 1` objective establishes

### Controller exponents are automatically near their exact threshold

If `p^a` activates at `m`, then

\[
v_p((m-1)!)<a\le v_p(m!)
             =v_p((m-1)!)+v_p(m).
\]

Consequently there is a unique integer `alpha` such that

\[
a=v_p((m-1)!)+1+\alpha,
\qquad 0\le\alpha<v_p(m).
\]

Thus "near-minimal exponent" is automatic in the exact activation sense:
there are precisely `v_p(m)` possible activating exponents.  For distinct
controllers and `m=pqc`, this sharpens to

\[
a=qc+v_p((qc-1)!)+\alpha,
\qquad 0\le\alpha\le v_p(c),
\]

and similarly

\[
b=pc+v_q((pc-1)!)+\beta,
\qquad 0\le\beta\le v_q(c).
\]

Consequently, if `c` is coprime to `pq`, both controller exponents are
exactly minimal even when `c>1`.  This is the strongest unconditional
"near-minimal exponent" reduction obtained here.

If `c=1`, then `m=pq` is squarefree at both controller primes, so both
activation slacks vanish:

\[
a=q+v_p((q-1)!),\qquad b=p.
\]

The still sharper exponents `a=q+1,b=p` occur exactly when `q<2p`.
Therefore there are two separate reductions to prove:

1. force the common value to be a squarefree semiprime (`c=1`);
2. inside that regime, force or control the Legendre tail
   `v_p((q-1)!)-1`.

The first step is currently missing.  The activation identity only says

\[
c\ge2\quad\Longrightarrow\quad (A-1)B-m\ge m.
\]

No upper bound below `m` follows from adjacency by the present argument.
Such an upper bound, or an equivalent elimination of all large-defect
factorial-divisor solutions, would prove the desired `c=1` reduction.

There is an exact way to state that missing upper bound.  Use the controller
exponents themselves and put

\[
D_{\rm ctrl}=(a-1)b-m.
\]

The same defect identity applies with
`r_0=a-(qc+1)` and `s_0=b-pc`.  If `c>=2`, it gives
`D_ctrl>=m`.  If `c=1`, the activation intervals above collapse to

\[
b=p,\qquad a=q+v_p((q-1)!),
\]

and hence

\[
D_{\rm ctrl}=p\bigl(v_p((q-1)!)-1\bigr)<pq=m.
\]

The strict inequality follows from
`v_p((q-1)!) <= (q-1)/(p-1) <= q-1`.  Therefore

\[
\boxed{c=1\quad\Longleftrightarrow\quad 0\le D_{\rm ctrl}<m.}
\]

This is a classification, not yet a reduction: proving that adjacency forces
`D_ctrl<m` is precisely the new pointwise lemma still required.  The Lean
theorem `controller_defect_lt_value_iff_cofactor_eq_one` checks both directions
for the actual controller exponents `a,b`.  It must not be generalized to
arbitrary exponent bounds `A,B`; those can contain unrelated slack.

### Exact consecutive-divisor reformulation

A common-fiber pair at value `m` is equivalently a positive integer `n`
satisfying

\[
n(n+1)\mid m!,\qquad
n\nmid(m-1)!,\qquad
n+1\nmid(m-1)!.
\]

The forward implication uses `gcd(n,n+1)=1`; the reverse implication is
the definition of `S`.

For any divisor `z | m!`, define its last-step residual by

\[
R_m(z)=\frac{z}{\gcd(z,(m-1)!)}.
\]

Then `R_m(z)|m`.  In a counterexample, `R_m(n)` and `R_m(n+1)` are
coprime nontrivial divisors of `m`, so

\[
R_m(n)R_m(n+1)\mid m.
\]

This packages exactly how the final multiplier `m` supplies both
activations.  A possible next rigidity lemma would have to show that the
unused part of this last-step budget cannot coexist with a gap of one.  No
such lemma is currently known here.

There is a dual unused-budget statement.  If `z|m!` contains an activated
controller `p` to its exact exponent `a`, and

\[
K=\frac{m!}{z},
\]

then

\[
v_p(K)=v_p(m!)-a<v_p(m).
\]

Thus if `p` occurs only once in `m`, the factorial complement contains no
copy of `p`.  This is kernel-checked as
`ActivatesAt.factorization_factorialComplement_lt_value`; it is useful
bookkeeping, but still does not force the adjacent gap to exceed one.

Equivalently, after choosing controllers one has

\[
n=p^a u,\qquad n+1=q^b v,\qquad q^b v-p^a u=1
\]

up to reversing the orientation, with exact prime-support separation and

\[
u\mid m!/p^a,\qquad v\mid m!/q^b.
\]

The linear Diophantine equation alone always has integer solutions because
`gcd(p^a,q^b)=1`.  The hard conditions are positivity, exact valuations,
disjoint supports, and the factorial exponent caps on `u,v`.

The controller exponent may be chosen to be the input's *full* `p`-valuation,
not merely an arbitrary activating sub-power.  For such exact controllers,
write the activation slacks as `alpha,beta`.  If

\[
r=R_m(x),\qquad s=R_m(y),\qquad m=pqc,
\]

then

\[
v_p(r)=1+\alpha,\qquad v_q(s)=1+\beta.
\]

Writing `m=r*s*ell` and removing those mandatory controller powers gives
positive `p,q`-free coprime factors `u,v` such that

\[
\boxed{
r=p^{1+\alpha}u,\qquad
s=q^{1+\beta}v,\qquad
c=p^\alpha q^\beta uv\ell.}
\]

This is kernel-checked by
`ordered_exact_controllers_cofactor_partition`.  Its endpoint is exact:

\[
c=1\iff \alpha=\beta=0\ \text{ and }\ u=v=\ell=1.
\]

Consequently the entire `c>=2` branch is the exhaustive split

\[
\alpha>0\ \lor\ \beta>0\ \lor\ u>1\ \lor\ v>1\ \lor\ \ell>1.
\]

There is also a stronger factorial-complement parametrization.  Put

\[
F=(m-1)!,\qquad
K=\frac{m!}{xy},\qquad
d=\frac{m}{R_m(x)R_m(y)}.
\]

For coprime divisors `x,y` of `m!`, there are positive `A,B,L` with

\[
\boxed{
x=R_m(x)A,\quad y=R_m(y)B,\quad
K=dL,\quad ABL=F,}
\]

and

\[
\gcd(R_m(x),BL)=\gcd(R_m(y),AL)=1.
\]

Thus `d|K`.  For consecutive `y=x+1`, the remaining pointwise equation is

\[
\boxed{R_m(y)B-R_m(x)A=1.}
\]

The theorem `coprime_factorial_divisors_exact_complement` kernel-checks all
of this except the final displayed subtraction, which follows immediately
after substituting `y=x+1`.  This is the exact factorial-capped `S`-unit
problem that a general `c>=2` proof must solve.

## Falsified strengthenings and smallest witnesses

- **Coprime equal fibers force `c=1`: false.**
  `S(243)=S(512)=12`; the numbers are coprime.  With ordered controllers
  `p=2,q=3`, one has `c=2`, `a=A=9`, `b=B=5`, `r=2`, `s=1`, and
  `(A-1)B-m=28`.
- **The distinct-controller theorem needs coprimality: false.**
  `S(486)=S(512)=12` with gap `26`; this pair is not coprime and has the
  same ordered controller data `c=2,r=2,s=1`.
- **`c=1` forces the crude minimal exponents: false.**
  `S(25)=S(256)=10`.  Here `p=2,q=5,c=1`, but the forced controller
  exponents are `a=8,b=2`, not `q+1=6,b=2`.  The Legendre-tail slack is
  `r=2`.
- **Adjacency as a congruence forces `c=1`: unsupported.**
  For the first `c=2` configuration `m=12,p=2,q=3,a=9,b=5`, even the exact
  controller valuations and adjacency equation are realized by
  `2^9*271+1=3^5*571`.  The cofactors have primes larger than `12`, so the
  pair fails factorial support.  The global caps, not the congruence alone,
  do the eliminating.
- **Minimal slacks force the cofactor to remain unused: false.**
  At `m=12`, the coprime common-fiber pair `(512,243)=(2^9,3^5)` has residuals
  `2,3` and leftover `2`, whereas `(1024,243)` has residuals `4,3` and
  leftover `1`.  At `m=30,p=2,q=3,c=5`, both `(2^26,3^14)` and
  `(2^26*5^7,3^14)` have minimal controller slacks; the first leaves `5`
  unused and the second puts `5` into a residual.  Hence residual-budget
  identities alone cannot eliminate any allocation of `c`.

None of these examples is a Tutescu counterexample.  They delimit which
hypotheses a future `c=1` proof must use.

## Reproducible computation

All runs used exact integer arithmetic.

1. `python3 scripts/audit_activations.py --max-value 1000000`
   enumerated all 5,004,826 activating-prime configurations with common
   value `m<=10^6`.  It found zero failures of the exact thresholds, slack
   intervals, defect identity, coprime-fiber bound, or sharp
   classification.  It also found zero mismatches in the exact test
   `c=1` iff `0<=D_ctrl<m`.  It found 8,097 zero-defect configurations, all in the
   classified `c=1,p<q<2p` regime.  The scan reached `c=166666`,
   `r=499992`, and `s=166658`, showing that activation itself permits very
   non-sharp configurations.
2. `python3 scripts/audit_fixed_shifts.py --max-x 300000 --max-gap 256`
   checked every positive gap `1<=h<=256` for `2<=x<=300000`, including
   non-coprime pairs and every available controller choice.  It found
   68,860 equal-fiber pairs, 68,732 shared-controller configurations, 143
   distinct-controller configurations, and zero theorem violations.  The
   first `c>1` example inside the gap window was `(486,512)`.  An additional
   all-gap pass over computed values found `(243,512)` as the first `c>1`
   distinct-controller collision by larger member.
3. `python3 scripts/audit_factorial_fibers.py --max-value 36` used the exact
   consecutive-divisor reformulation.  It inspected 36,790,221 divisors at
   or below `sqrt(m!)` across every `m<=36`, found 4,768 pairs `d,d+1` that
   both divide the relevant factorial, and found zero pairs for which both
   first enter at `m`.
4. `python3 scripts/verify_luca_najman_table.py` downloaded the corrected
   Luca--Najman table of all odd `x` for which `P^+(x^2-1)<100`, verified its
   SHA-256
   `035f2e7342d11bb86d4b7dacad611e7adb5601f8e5352a1e525e0646ad0f4380`,
   checked all 13,374 entries, factored both `(x-1)/2` and `(x+1)/2` over the
   primes below 100, and recomputed their exact Kempner values by Legendre
   inversion.  It found zero equal-value pairs.  Conditional only on the
   published completeness proof/table, this excludes every common value
   `m<=100`, regardless of the size of `n`.  Since a consecutive common fiber
   needs two distinct prime divisors of `m`, prime-power `m=101` is also
   impossible; hence any counterexample has `m>=102`.
5. `python3 scripts/verify_berger_113_table.py` downloaded the public
   `twin_smooths_113_sorted_full.txt` artifact at repository commit
   `6fc4c364ee995a6aef5f788e29cdfc307d37f9a5`, verified SHA-256
   `9ad599518af925638f1c72e6bdcc3cfd7a3c26554a6cca3c44930689bee7f43d`,
   checked strict ordering and all 33,233 entries, independently factored
   both neighbors over primes at most 113, and recomputed every exact Kempner
   value.  It found zero equal-value pairs; the largest recomputed value was
   452.  Since the next prime after 113 is 127, conditional on the external
   completeness of the Størmer/Lehmer output this excludes every common value
   `m<127`.  The kernel-checked prime-power theorem then excludes `m=127` and
   `m=128`, so any counterexample has `m>=129`.  At `m=129=3*43`, two distinct
   controllers force `c=1`; hence the `c>=2` branch starts at `m>=130`.
6. `python3 scripts/search_c_ge_two.py --max-value 80
   --cross-check-through 36` exhaustively enumerated every ordered controller
   pair, both orientations, and every exact activation exponent for `c>=2`.
   A meet-in-the-middle residue index compressed a summed unpruned space of
   1,921,437,349,488 divisor choices to 311,547 modular-adjacency survivors.
   All survivors failed smoothness of the opposite cofactor; none reached the
   full factorial caps.  The modular enumeration was independently compared
   with naive divisor enumeration through `m=36`.  This is an exact finite
   audit through `m=80`, although item 5 already gives a stronger externally
   complete value bound.
7. The existing independent direct sieve `scripts/search_consecutive` was
   previously run through `n=10^8`; it found no equality.  PrimePuzzles
   reports an older direct verification through `10^9`, so neither bound is
   a record.

Items 1-3, 6, and 7 are internal finite computations.  Items 4 and 5 are
reproducible post-processing certificates whose uniform conclusions still
depend on the external Størmer/Pell completeness theorem and the provenance
of the published tables; Lean does not claim either enumeration's
completeness.

## Prior-art audit

### Kempner fibers and fixed shifts

- Prodanescu and Tutescu, *On a conjecture concerning the Smarandache
  function*, MR1650388 / Zbl 1008.11508, proves only that an input `a>=2`
  and `S(a)` share a prime factor; the paper explicitly says this does not
  solve the conjecture.
- Mullin, *On the Smarandache function and the fixed-point theory of
  numbers*, MR1416986 / Zbl 0885.11012, explicitly poses finiteness for
  shifts `2` and `3` and nonexistence for shift `1`; it gives no fiber
  bound.
- T. D. Noe's September 2004 PrimePuzzles contribution already fixes a
  common value `M`, enumerates its activating prime powers, and solves
  `y q^b-x p^a=1` with factorial-divisor tests.  This fixed-fiber search
  framework and Diophantine equation are prior art.
- The public MathSciNet MR Lookup was queried on 2026-08-20 with title
  combinations using `Smarandache function` and `consecutive`, `equal
  values`, `shift`, `coprime`, and `fixed-point theory`, plus author
  `Tutescu` and title `Kempner function`.  The targeted consecutive,
  equal-value, and shift conjunctions returned no title records.  The
  Tutescu query returned the original conjecture paper; the fixed-point
  query returned Mullin's note.  MR Lookup is title/metadata limited and is
  not a substitute for subscriber full-text searching.
- Targeted zbMATH Open searches for `S(n+h)`, fixed shift, equal/same
  values, fiber/preimage, neighbor, coprime, and gcd found no
  fixed-shift theorem or gcd-sensitive fiber bound.  The relevant indexed
  records were the same Prodanescu--Tutescu, Ashbacher, and Mullin sources;
  several lexical hits concerned unrelated Smarandache-type functions.

The activation-gap identity may be apparently new, but this audit cannot
certify novelty and the result should not yet be advertised as novel without
expert review.

### Neighboring smooth numbers and factorial divisors

- Størmer's theorem, in its modern Pell-equation form, makes the set of
  consecutive `B`-smooth pairs finite for each fixed `B`.  Buzek et al.,
  *Finding twin smooth integers by solving Pell equations*
  (arXiv:2211.04315), explains that complete enumeration becomes
  exponential/prohibitive as `B` grows.  Here the smoothness bound is the
  unknown common value `m`, so fixed-`B` finiteness is not uniform enough.
- [Luca and Najman, *On the largest prime factor of
  `x^2-1`](https://arxiv.org/abs/1005.1533), together with their published
  corrected table, completely enumerates the case `P^+(x^2-1)<100`.  The
  Kempner filter described above is new post-processing of that enumeration,
  not a new completeness proof.  Later work reports that the complete
  `B=113` computation contains 33,233 pairs.  A matching full artifact is now
  public in [Daniel Berger's infrastructure repository at the pinned
  commit](https://github.com/db711/infrastructure/blob/6fc4c364ee995a6aef5f788e29cdfc307d37f9a5/data/twin_smooths_113_sorted_full.txt):
  it has exactly that count and the same reported largest pair.  See
  [Cryptographic Smooth Neighbors](https://eprint.iacr.org/2022/1439.pdf) and
  [Towards Optimally Small Smoothness
  Bounds](https://eprint.iacr.org/2023/1576.pdf).  The byte/factorization audit
  here still does not independently rerun the exhaustive Pell computation.
- Heath-Brown, *The Differences Between Consecutive Smooth Numbers*
  (arXiv:1808.02947), treats the frequency of large gaps and explicitly
  notes that the method breaks down for gaps at most about `x^{1/3}`.  It
  does not reach the fixed gap `1` needed here.
- [Berend and Harmse, *Gaps between consecutive divisors of
  factorials*](https://www.numdam.org/item/AIF_1993__43_3_569_0/),
  Ann. Inst. Fourier 43 (1993), 569-583, studies the ordered divisors of
  `m!`.  Direct inspection of Theorems 2-4 confirms the mismatch: Theorem 2
  gives a divisor near a target, while the central lower-gap conclusions are
  density or infinitely-often statements.  None is a pointwise theorem that
  excludes adjacent divisors both entering for the first time at step `m`.

These are plausible toolkits for computation or average estimates, not a
known route to the required pointwise `c=1` elimination.

### AI-assisted proof methodology audit

The useful lesson from successful AI-assisted mathematics is a verified
counterexample loop, not an unsupported end-to-end proof draft.  The workflow
adopted here follows four precedents:

- [FunSearch](https://www.nature.com/articles/s41586-023-06924-6) used a
  deterministic evaluator to select generated constructions;
- [AlphaGeometry](https://www.nature.com/articles/s41586-023-06747-5) searched
  for auxiliary objects before returning to symbolic deduction;
- [AlphaProof](https://www.nature.com/articles/s41586-025-09833-y) used
  target-specific curricula of simpler and generalized problems;
- the AI-assisted formalization of
  [Erdős Problem 728](https://arxiv.org/abs/2601.07421) is the closest
  factorial-divisibility precedent: it decomposes the argument into named
  valuation lemmas and maps each one to a Lean declaration.

For this project the corresponding independent search islands are controller
defect, residual/factorial budget, modular or `S`-unit obstructions, and prime
support.  Every proposed inequality is tested against exact activations and
smallest witnesses before it is offered to Lean.  These systems solve hard
known problems or find verified constructions; none supplies a reason to
claim that an open conjecture has been proved.

## Lean formalization status

Reusable declarations in `KempnerResearch/Basic.lean`:

- `IsKempnerValue.exists_activating_prime_power`;
- `ActivatesAt.prime_dvd_value` and `ActivatesAt.value_pos`;
- `ActivatesAt.value_le_exponent_mul_prime`;
- `ActivatesAt.quotient_le_exponent` and
  `ActivatesAt.quotient_add_one_le_exponent`;
- `activation_primes_ne_of_coprime` for the `h=1` specialization;
- `orderedControllers_of_activations`, `ordered_controller_bound`, and
  `ordered_controller_bound_sub`;
- `maxPrimeExponent`, `factorization_le_maxPrimeExponent`, and the existing
  coprime-fiber theorems.

`KempnerResearch/ActivationGap.lean` now kernel-checks, in dependency order:

1. `factorization_factorial_mul_sub_one`, the exact identity
   `v_p((p*N-1)!) = N-1 + v_p((N-1)!)`;
2. `ActivatesAt.exists_bounded_activation_slack`,
   `exists_exact_quotient_slack`, and
   `activation_exact_slacks_of_ordered_activations`;
3. `shared_controller_pow_dvd_dist` and its positive-gap specialization;
4. `ActivationGapData.defect_add`, `defect_sub`, and `controller_bound`;
5. `activation_gap_dichotomy` and `kempner_fiber_activation_gap`, with no
   coprimality assumption;
6. `controller_defect_lt_value_iff_cofactor_eq_one`, the exact first-objective
   classification for actual controller exponents;
7. `consecutive_common_fiber_iff` and the last-step-residual package,
   culminating in `coprime_kempner_fiber_lastStepResidual` and
   `ActivatesAt.prime_dvd_lastStepResidual`;
8. `factorialComplement` and
   `ActivatesAt.factorization_factorialComplement_lt_value`, plus the
   prime-power exclusion `not_consecutive_common_fiber_at_prime_power`.
9. `IsKempnerValue.exists_exact_activating_prime_power`, exact residual
   valuations, the residual/controller-core factorization, and
   `ordered_exact_controllers_cofactor_partition` in
   `ResidualCofactor.lean`; `cofactor_partition_cases_of_two_le` is the
   exhaustive five-branch split.
10. `cofactor_partition_eq_one_iff` and
    `coprime_factorial_divisors_exact_complement` in
    `ResidualComplement.lean`, giving the exact endpoint and the
    `A*B*L=(m-1)!`, `K=d*L` parametrization.

The file deliberately does **not** contain a theorem saying adjacency implies
`D_ctrl<m`; that remains the missing mathematical lemma rather than a Lean
engineering task.

The analytic `X^{1/2+o(1)}` consequence should remain a documented paper
corollary unless an appropriate smooth-number asymptotic library is added;
the finite arithmetic core is the appropriate Lean target.

Trust policy remains unchanged: no `sorry`, no project-defined axioms, no
`native_decide`, and no `unsafe`.  External audits are falsification tools,
not proof terms.

## Decision and next proof route

Do **not** assume `c=1` in a proof of Tutescu's conjecture.  What is justified
now is:

\[
\text{all controller exponents lie in exact short activation intervals,}
\]

and

\[
c\ge2\Longrightarrow\text{oriented defect at least }m.
\]

Moreover the exact activation slacks satisfy

\[
0\le\alpha\le v_p(c),\qquad 0\le\beta\le v_q(c),
\]

so minimal or near-minimal exponents are already automatic.  The public
113-smooth artifact and the prime-power exclusion give the
external-completeness-backed finite lower bound `m>=129` for any hypothetical
counterexample, and `m>=130` in the `c>=2` branch.

The new exact cofactor identity determines what a `c=1` reduction would have
to prove: adjacency must rule out each of

\[
\alpha>0,\quad\beta>0,\quad u>1,\quad v>1,\quad\ell>1.
\]

Actual coprime equal-fiber examples realize both residual-allocation extremes,
so no residual-budget inequality alone can do this.  The pure-controller-power
subfamily is excluded by [Mihăilescu's
theorem](https://doi.org/10.1515/crll.2004.048): the only consecutive perfect
powers with both exponents greater than one are `8,9`, and their Kempner
values are `4,6`.  This does not address factorial-smooth cofactors.

The next useful attack is the exact constrained equation

\[
sB-rA=1,\qquad ABL=(m-1)!,
\]

with its cross-coprimality and cofactor-allocation conditions.  A productive
split is:

- `c>=2` or positive Legendre-tail defect: seek a factorial-budget or
  anti-sieve contradiction;
- `c=1,q<2p`: analyze the exact endpoint
  `p^{q+1}u` and `q^p v`;
- `c=1,q>=2p`: retain the explicit Legendre tail rather than calling the
  exponents minimal.

The first target not covered by the 113-smooth artifact in the `c>=2` branch
is `m=130`.  Its controller exponents are forced to `128,32,10`, but the
current Python meet-in-the-middle halves would require between roughly 525
million and 1.85 billion materialized integers per controller pair, beyond
the 15 GiB host.  A complete `m=130` certificate therefore needs either a
targeted parallel Størmer/Pell computation or a substantially stronger
factorial-capped `S`-unit solver; merely raising the script limit is not a
credible verification plan.

For computation beyond the current certificates, the most concrete route is a
factorial-capped `S`-unit solver.  It should enumerate only the exact exponent
intervals above, enforce disjoint prime support, apply modular sieves and
real/`p`-adic LLL, and emit small factorization or residue certificates for an
independent checker.  Generic `S`-unit finiteness is insufficient because the
prime set grows with `m`; smooth-number and anti-sieve theorems currently give
average rather than pointwise control.

Until the first branch is eliminated, reducing all hypothetical
counterexamples to the near-sharp endpoint is an open intermediate lemma,
not an established consequence of activation-gap rigidity.
