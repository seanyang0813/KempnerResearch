# A sharp coprime-fiber obstruction for the Kempner function

Date of audit: 2026-08-20

## Result

For (z>1), write

\[
E(z):=\max_{\ell\mid z}v_\ell(z),
\qquad P(z):=P^+(z).
\]

Here and below the maximum in (E) is over prime divisors. The following is
the main result.

**Coprime-fiber theorem.** Let (x,y>1) be coprime and suppose

\[
S(x)=S(y)=m.
\]

Then

\[
\boxed{m+\min\{E(x),E(y)\}\le E(x)E(y).}\tag{1}
\]

Consequently,

\[
\boxed{\max\{P(x),P(y)\}+\min\{E(x),E(y)\}
       \le E(x)E(y).}\tag{2}
\]

There is a sharper local form. Choose prime powers (p^a\parallel x) and
(q^b\parallel y) that control the common value, so

\[
S(p^a)=S(q^b)=m.
\]

The primes are distinct. If (p<q), write (m=pqc). Then

\[
\boxed{a\ge qc+1,\qquad b\ge pc.}\tag{3}
\]

If the smaller controlling prime belongs to (y), the same statement holds
after interchanging (x,y).

The bound (1) is best possible. For every pair of primes (p<q<2p),

\[
S\left(p^{q+1}\right)=S\left(q^p\right)=pq
\]

and equality holds in (1). In particular, choosing (q) to be the next prime
after (p) gives infinitely many sharp coprime pairs by Bertrand's theorem.

## Proof

The identity

\[
S(z)=\max_{\ell^e\parallel z}S(\ell^e)
\]

supplies controlling prime powers (p^a\parallel x) and
(q^b\parallel y). Minimality of (m=S(p^a)) says

\[
v_p((m-1)!)<a\le v_p(m!).
\]

Thus (p\mid m): otherwise multiplication by (m) would not change the
(p)-adic valuation. Similarly (q\mid m). Coprimality of (x,y) gives
(p\ne q), so (pq\mid m).

Assume (p<q) and put (m=pqc). Legendre's formula gives

\[
\begin{aligned}
v_p((m-1)!)
&\ge \left\lfloor\frac{m-1}{p}\right\rfloor
   +\left\lfloor\frac{m-1}{p^2}\right\rfloor \\
&\ge (qc-1)+1=qc,
\end{aligned}
\]

where (p^2<m) follows from (p<q) and (c\ge1). Hence (a\ge qc+1).
Likewise,

\[
v_q((m-1)!)\ge\left\lfloor\frac{m-1}{q}\right\rfloor=pc-1,
\]

so (b\ge pc). This proves (3).

Set (A=E(x)), (B=E(y)). In the present orientation (A\ge qc+1) and
(B\ge pc). Therefore

\[
(A-1)B\ge(qc)(pc)=pqc^2=mc\ge m.
\]

It follows that (m+B\le AB), and replacing (B) on the left by
(min(A,B)) proves (1). The other orientation is symmetric.

Finally, every prime factor of (x) or (y) is at most (m), since both
integers divide (m!). Combining this observation with (1) proves (2).

For sharpness, suppose (p<q<2p). Legendre's formula gives

\[
v_p((pq-1)!)=q,\qquad v_q((pq-1)!)=p-1.
\]

Multiplication by (pq) adds one copy of each prime. Hence
(S(p^{q+1})=S(q^p)=pq), and

\[
pq+\min(q+1,p)=pq+p=(q+1)p.
\]

This also classifies equality at the controller level. Equality forces
(c=1), the two relevant maximal exponents to be (q+1) and (p), and
(q<2p); each condition is necessary in the chain above and the displayed
construction proves sufficiency.

## Consequence for the Tutescu conjecture

Since consecutive integers are coprime, a hypothetical counterexample must
satisfy

\[
\boxed{
\max\{P(n),P(n+1)\}
\le E(n)E(n+1)-\min\{E(n),E(n+1)\}.
}\tag{4}

It must also contain, on opposite sides, controlling powers satisfying (3).
In particular one neighbor is divisible by a fourth power and the other by a
square. Thus the theorem includes all pairs with one squarefree member and
all pairs for which both members are fourth-power-free, but (4) is usually
far stronger than those elementary cases.

There is a quantitative consequence. Let (C(X)) be the number of
hypothetical Tutescu counterexamples (n\le X). Since

\[
E(n),E(n+1)\le \log_2(X+1),
\]

(4) makes both (n) and (n+1) (Y)-smooth for

\[
Y=(\log_2(X+1))^2.
\]

Therefore

\[
C(X)\le \Psi(X,Y)=X^{1/2+o(1)}.\tag{5}
\]

The last equality is the standard smooth-number estimate

\[
\Psi(X,(\log X)^\alpha)=X^{1-1/\alpha+o(1)}\qquad(\alpha>1)
\]

with (alpha=2). Alternatively, the upper bound needed in (5) follows
directly from Rankin's method at exponent (1/2), together with
(sum_{p\le Y}p^{-1/2}=O(\sqrt Y/\log Y)).

This is a power-saving structural reduction. Merely using the classical fact
that (S(n)=P(n)) for almost all (n) puts counterexamples in a density-zero
set; the known exceptional-set estimate is of size

\[
X\exp\!\left(-(\sqrt2+o(1))\sqrt{\log X\log\log X}\right)=X^{1-o(1)},
\]

whereas (5) is (X^{1/2+o(1)}).

## Computation and falsification

The proof is independent of computation. Two independent audits were run.

1. `scripts/audit_activations.py --max-value 1000000` enumerated all
   (5,004,826) pairs of activating prime-power configurations with common
   value (m\le10^6). It found no violation of (3) or (1). It found 8,097
   equality configurations, all and only those described by
   (c=1, p<q<2p, a=q+1, b=p).
2. `scripts/search_consecutive --limit 100000000` computed (S(n)) from the
   prime-power max formula for every (n\le10^8+1). It found no Tutescu
   equality. More importantly for this theorem, only 30 of the (10^8)
   consecutive pairs survived the factorization-only necessary condition
   (4); direct Kempner values eliminated all 30. This is a validation run,
   not a record: an older published web reference already reports direct
   verification through (10^9).

Candidate strengthenings were actively falsified:

- Strict inequality in (1) is false: (x=16,y=9,m=6) is sharp.
- Replacing the right side by ((E(x)-1)(E(y)-1)) is false for the same pair.
- Replacing (qc+1) in (3) by (qc+2) is false for (p=2,q=3,c=1).
- The arithmetic smoothness condition (4) is not itself impossible for
  consecutive integers: (8,9) satisfies it, although (S(8)=4\ne6=S(9)).

## Lean verification

`KempnerResearch/Basic.lean` formalizes:

- the graph predicate for the Kempner function;
- existence of an activating prime-power component from a fiber witness;
- the valuation jump and cross-exponent bounds;
- the sharp coprime-fiber inequality in both addition and subtraction forms;
- the prime-factor version underlying (4).

From the repository root, the checked command is:

```bash
lake build
```

It succeeds with Lean `v4.34.0-rc1` and the Mathlib revision pinned in
`lake-manifest.json`.

## Prior-art and novelty audit

### MathSciNet and zbMATH (Zentralblatt) database audit (2026-08-20)

The two principal mathematical reviewing databases were checked separately.
The scope and access limitations matter:

- The zbMATH Open API allowed direct searches of titles, reviews/summaries,
  metadata, and indexed reference text. The exact phrase `"Smarandache
  function"` occurs in 257 records overall, 155 title records, and 174
  review/summary records. Searching `Tutescu` or `Tuţescu` returned seven
  records; only one of them is the number-theoretic conjecture paper, Zbl
  1008.11508.
- All 12 review/summary records containing both `"Smarandache function"`
  and `"S(n+1)"` were screened. The relevant ones formulate the consecutive
  problem, study other recurrences among consecutive values, or discuss
  Radu's different prime-between-values problem. None states a bound on a
  coprime fiber.
- Additional zbMATH review/summary searches combined `"Smarandache
  function"` with `Legendre`, `valuation`, `p-adic`, `exponent`, `prime
  power`, `same value`, `equal values`, `fiber`, `preimage`, `inverse
  image`, `smooth`, `coprime`, `maximal exponent`, and `maximum exponent`.
  The few hits were inspected. They concern computation of prime-power
  values, unrelated p-adic generalizations, the normal order of the
  function, or a separately defined coprime characteristic function. No
  hit contains (1)--(3), an equivalent exponent-product obstruction, or
  the smooth-number consequence (5).
- The zbMATH reference-text index returned no record citing Prodanescu,
  Tutescu, or the exact title *On a conjecture concerning the Smarandache
  function*. This is supporting evidence only: reference-list coverage is
  incomplete, particularly for the small journals and books in this
  literature.
- Full MathSciNet `Anywhere`, `Review Text`, and `References` searching
  requires institutional authentication and was not available from this
  environment. The public MR Lookup service was therefore searched instead.
  To mitigate its limit of three regular results per query, the title phrase
  `Smarandache function` was queried separately for every year from 1980
  through 2026, yielding 51 distinct MR records, and was supplemented by
  targeted title conjunctions with `consecutive`, `equal`, `equality`,
  `coprime`, `inverse`, `fiber`, `values`, `conjecture`, `prime` plus
  `power`, and `exponent`. Exact searches were also run for `Kempner
  function`, `Kempner` plus `factorial`, the principal authors, and the
  known candidate titles. There were no title hits for the consecutive,
  equal-value, fiber, inverse-image, or exponent formulations. The three
  `coprime` hits concern a different 0--1 characteristic function, not
  coprime arguments in a Kempner fiber.

The principal records cross-checked between the databases are:

- Prodanescu--Tutescu: MR1650388, Zbl 1008.11508;
- Ashbacher's *An Introduction to the Smarandache Function*: MR1364859,
  Zbl 0834.11002;
- Mullin's explicit restatement of the consecutive conjecture: MR1416986,
  Zbl 0885.11012;
- the prime-power calculation paper of Sutton: MR1294796, with the related
  zbMATH prime-power records Zbl 1043.11503--04;
- the standard max-over-prime-powers discussion of Andrei et al.:
  MR1294791, MR1361855, MR1398974 and Zbl 0812.11002, 0874.11009,
  0865.11002;
- Ivić's largest-prime-factor paper: Zbl 1098.11046.

Thus this audit materially strengthens the prior-art check, but it does not
turn novelty into a formally certified fact. In particular, it is not an
exhaustive full-text MathSciNet search, and neither database can rule out an
unindexed or differently phrased result.

The following sources were searched for the theorem, equivalent
max-exponent statements, coprime-fiber bounds, Tutescu reductions, and
stronger results:

- Prodanescu and Tutescu, *On a Conjecture Concerning the Smarandache
  Function*;
- Ashbacher, *An Introduction to the Smarandache Function*, especially its
  discussion of the consecutive-value problem;
- Liu, *A Survey on Smarandache Notions in Number Theory I*;
- Ivić, *On a Problem of Erdős Involving the Largest Prime Factor of n*;
- the Kempner-function and Tutescu-related OEIS entries A002034, A099120,
  and A099143;
- the indexed Kempner/Smarandache-function bibliography and targeted web
  searches for equal values, coprime arguments, fibers, maximal exponents,
  and smooth counterexamples.

The nearest prior observation found is Ashbacher's: writing the two common
values as (kp=rq), coprimality forces (q\mid k) and (p\mid r). The
original Prodanescu--Tutescu note proves the still weaker fact that an
argument and its Kempner value share a prime divisor. I found no source that
adds the extra Legendre copy for the smaller prime, derives (1) or (2),
classifies sharpness, or obtains the (X^{1/2+o(1)}) reduction.

Accordingly, the theorem is **proved** (including a kernel-checked Lean
formalization) and the expanded database audit supports the description
**apparently novel**. Novelty is still not certified: full subscriber-level
MathSciNet searching and, more importantly, an expert referee could still
locate an unindexed or differently phrased equivalent.

Links used in the audit:

- [Prodanescu--Tutescu note](https://fs.unm.edu/SNJ/OnAConjectureConcerning-9.pdf)
- [Ashbacher's introduction](https://fs.unm.edu/SF/AnIntroduction.pdf)
- [Liu's 2017 survey](https://fs.unm.edu/SF/ASurveyOnSmarandacheNotions1.pdf)
- [Ivić's paper (arXiv)](https://arxiv.org/abs/math/0311056)
- [Hildebrand--Tenenbaum on smooth numbers](https://jtnb.centre-mersenne.org/articles/10.5802/jtnb.101/)
- [OEIS A002034](https://oeis.org/A002034),
  [A099120](https://oeis.org/A099120), and
  [A099143](https://oeis.org/A099143)
- [zbMATH Open document search](https://zbmath.org/)
- [MathSciNet MR Lookup](https://mathscinet.ams.org/mrlookup)

## Digestion

The conceptual mechanism is shorter than the discovery path:

1. Equal values on coprime inputs require different activating primes.
2. Both primes divide the common value.
3. Legendre's formula couples each prime to the *other* prime's quotient;
   the smaller prime gets one unavoidable extra copy from its square.
4. Multiplying the two cross-bounds yields the sharp global obstruction.
5. Since all input primes lie below the common value, the obstruction turns
   immediately into a polylogarithmic smoothness condition and a
   square-root-scale counting bound.

No uniqueness assumption on a controlling prime power is needed, adjacency
is used only through coprimality, and the `+ min` term cannot be improved
uniformly because of the infinite sharp family above.
