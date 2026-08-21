/-
Copyright (c) 2026 The KempnerResearch Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Yang, OpenAI Codex
-/
import KempnerResearch.Basic

/-!
# Activation-gap rigidity for Kempner fibers

This file strengthens the local controller estimates in `Basic.lean`.
It formalizes:

* the exact factorial valuation immediately before a multiple of a prime;
* the exact activation threshold and bounded activation slack;
* the divisibility of the distance when two inputs share a controller;
* the `c, r, s` oriented-defect identity for distinct controllers; and
* the strengthened bound `c * m + min A B ≤ A * B`.

Only finite arithmetic is formalized here.  The smooth-number asymptotic used
for the fixed-shift counting corollary remains an external paper consequence.
-/

open Finset List Finsupp

namespace KempnerResearch

/-- No new copy of `p` enters the factorial between `p*k` and
`p*k+n` when `n<p`. -/
theorem factorization_factorial_mul_add_of_lt
    {p k n : ℕ} (hn : n < p) :
    (p * k + n).factorial.factorization p =
      (p * k).factorial.factorization p := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn' : n < p := lt_trans (Nat.lt_succ_self n) hn
      have hnot_small : ¬p ∣ n + 1 :=
        Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n) hn
      have hnot : ¬p ∣ p * k + (n + 1) := by
        intro hdvd
        have hp_mul : p ∣ p * k := dvd_mul_right p k
        exact hnot_small ((Nat.dvd_add_iff_right hp_mul).mpr hdvd)
      rw [Nat.add_succ, Nat.factorial_succ,
        Nat.factorization_mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _),
        Finsupp.coe_add, Pi.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.add_assoc] using hnot),
        ih hn']
      simp

/-- Exact Legendre step immediately before a positive multiple of `p`:

`v_p((p*N-1)!) = (N-1) + v_p((N-1)!)`.
-/
theorem factorization_factorial_mul_sub_one
    {p N : ℕ} (hp : p.Prime) (hN : 0 < N) :
    (p * N - 1).factorial.factorization p =
      (N - 1).factorial.factorization p + (N - 1) := by
  have hp_pos : 0 < p := hp.pos
  have hp_pred_lt : p - 1 < p := Nat.sub_lt hp_pos (by omega)
  have hN_repr : N = (N - 1) + 1 := by omega
  have hmul : p * N = p * (N - 1) + p := by
    calc
      p * N = p * ((N - 1) + 1) := by rw [← hN_repr]
      _ = p * (N - 1) + p := by ring
  have hindex : p * N - 1 = p * (N - 1) + (p - 1) := by
    rw [hmul, Nat.add_sub_assoc hp.one_le]
  rw [hindex, factorization_factorial_mul_add_of_lt hp_pred_lt,
    Nat.factorization_factorial_mul hp]

/-- The exponent of an activated prime power is strictly above the
`p`-factorization of the previous factorial. -/
theorem ActivatesAt.prev_factorization_lt_exponent
    {p a m : ℕ} (h : ActivatesAt p a m) :
    (m - 1).factorial.factorization p < a := by
  by_contra hnot
  have ha : a ≤ (m - 1).factorial.factorization p := Nat.le_of_not_gt hnot
  exact h.not_dvd_prev_factorial
    ((h.prime.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mpr ha)

/-- The exponent of an activated prime power is at most the corresponding
factorization of the current factorial. -/
theorem ActivatesAt.exponent_le_factorization
    {p a m : ℕ} (h : ActivatesAt p a m) :
    a ≤ m.factorial.factorization p :=
  (h.prime.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp
    h.dvd_factorial

/-- At a positive factorial step, the `p`-factorization increases by exactly
the `p`-factorization of the new factor. -/
theorem ActivatesAt.factorization_factorial_eq_prev_add_value
    {p a m : ℕ} (h : ActivatesAt p a m) :
    m.factorial.factorization p =
      (m - 1).factorial.factorization p + m.factorization p := by
  have hm0 : m ≠ 0 := h.value_pos.ne'
  have hm : (m - 1) + 1 = m := Nat.sub_add_cancel h.value_pos
  have hfac : m.factorial = m * (m - 1).factorial := by
    calc
      m.factorial = ((m - 1) + 1).factorial := by rw [hm]
      _ = ((m - 1) + 1) * (m - 1).factorial := Nat.factorial_succ _
      _ = m * (m - 1).factorial := by rw [hm]
  rw [hfac, Nat.factorization_mul hm0 (Nat.factorial_ne_zero _),
    Finsupp.coe_add, Pi.add_apply, add_comm]

/-- Every activated exponent is the exact minimum plus a slack strictly
smaller than the valuation jump supplied by the new factor `m`. -/
theorem ActivatesAt.exists_bounded_activation_slack
    {p a m : ℕ} (h : ActivatesAt p a m) :
    ∃ α, α < m.factorization p ∧
      a = (m - 1).factorial.factorization p + 1 + α := by
  have hlower : (m - 1).factorial.factorization p + 1 ≤ a :=
    Nat.succ_le_iff.mpr h.prev_factorization_lt_exponent
  obtain ⟨α, ha⟩ := Nat.exists_eq_add_of_le hlower
  refine ⟨α, ?_, ha⟩
  have hupper := h.exponent_le_factorization
  rw [h.factorization_factorial_eq_prev_add_value] at hupper
  omega

/-- If an activation value is `m=p*k`, then the `p`-factorization supplied
by the final factor is exactly one more than the `p`-factorization of `k`. -/
theorem ActivatesAt.factorization_value_eq_quotient_add_one
    {p a m k : ℕ} (h : ActivatesAt p a m) (hm : m = p * k) :
    m.factorization p = k.factorization p + 1 := by
  have hk0 : k ≠ 0 := by
    intro hk
    rw [hk, mul_zero] at hm
    exact h.value_pos.ne' hm
  rw [hm, Nat.factorization_mul h.prime.ne_zero hk0,
    Finsupp.coe_add, Pi.add_apply, h.prime.factorization_self]
  omega

/-- Quotient form of the exact activation interval.  The slack above the
Legendre threshold is bounded by the `p`-factorization of the quotient. -/
theorem ActivatesAt.exists_exact_quotient_slack
    {p a m k : ℕ} (h : ActivatesAt p a m) (hm : m = p * k) :
    ∃ α, α ≤ k.factorization p ∧
      a = k + (k - 1).factorial.factorization p + α := by
  obtain ⟨α, hαlt, ha⟩ := h.exists_bounded_activation_slack
  have hk_pos : 0 < k := by
    have hm_pos := h.value_pos
    rw [hm] at hm_pos
    exact Nat.pos_of_mul_pos_left hm_pos
  have hjump := h.factorization_value_eq_quotient_add_one hm
  have hαle : α ≤ k.factorization p := by omega
  refine ⟨α, hαle, ?_⟩
  rw [hm, factorization_factorial_mul_sub_one h.prime hk_pos] at ha
  omega

/-- If the controller prime does not divide the quotient `k`, the activation
exponent is forced to its unique minimal value. -/
theorem ActivatesAt.exact_quotient_exponent_of_not_dvd
    {p a m k : ℕ} (h : ActivatesAt p a m) (hm : m = p * k)
    (hpk : ¬ p ∣ k) :
    a = k + (k - 1).factorial.factorization p := by
  obtain ⟨α, hα, ha⟩ := h.exists_exact_quotient_slack hm
  rw [Nat.factorization_eq_zero_of_not_dvd hpk] at hα
  omega

/-- Multiplying by a nonzero cofactor does not add any `p`-factorization
through a distinct prime `q`. -/
theorem factorization_distinct_prime_mul
    {p q c : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hc : c ≠ 0) :
    (q * c).factorization p = c.factorization p := by
  have hnot : ¬ p ∣ q := by
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
  rw [Nat.factorization_mul hq.ne_zero hc,
    Finsupp.coe_add, Pi.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnot]
  simp

/-- If an activation value is written as `m=p*k`, this is the exact
Legendre lower threshold for its exponent. -/
theorem ActivatesAt.exact_quotient_threshold_le_exponent
    {p a m k : ℕ} (h : ActivatesAt p a m) (hm : m = p * k) :
    k + (k - 1).factorial.factorization p ≤ a := by
  have hk_pos : 0 < k := by
    have hm_pos := h.value_pos
    rw [hm] at hm_pos
    exact Nat.pos_of_mul_pos_left hm_pos
  have hlt := h.prev_factorization_lt_exponent
  rw [hm, factorization_factorial_mul_sub_one h.prime hk_pos] at hlt
  omega

/-- The exact threshold power itself divides every number containing an
activated `p^a`. -/
theorem ActivatesAt.threshold_pow_dvd
    {p a m x : ℕ} (h : ActivatesAt p a m) (hpx : p ^ a ∣ x) :
    p ^ ((m - 1).factorial.factorization p + 1) ∣ x := by
  have hle : (m - 1).factorial.factorization p + 1 ≤ a :=
    Nat.succ_le_iff.mpr h.prev_factorization_lt_exponent
  exact (pow_dvd_pow p hle).trans hpx

/-- If two fiber inputs use the same activating prime, its exact threshold
power divides their natural distance. -/
theorem shared_controller_pow_dvd_dist
    {x y m p a b : ℕ}
    (hx : ActivatesAt p a m) (hy : ActivatesAt p b m)
    (hpx : p ^ a ∣ x) (hpy : p ^ b ∣ y) :
    p ^ ((m - 1).factorial.factorization p + 1) ∣ Nat.dist x y := by
  have hdx := hx.threshold_pow_dvd hpx
  have hdy := hy.threshold_pow_dvd hpy
  rcases le_total x y with hxy | hyx
  · rw [Nat.dist_eq_sub_of_le hxy]
    exact Nat.dvd_sub hdy hdx
  · rw [Nat.dist_eq_sub_of_le_right hyx]
    exact Nat.dvd_sub hdx hdy

/-- Quantitative shared-controller consequence: for distinct inputs, the
common activation value is at most `p` times the `p`-factorization of their
distance. -/
theorem shared_controller_value_le_prime_mul_factorization_dist
    {x y m p a b : ℕ}
    (hx : ActivatesAt p a m) (hy : ActivatesAt p b m)
    (hpx : p ^ a ∣ x) (hpy : p ^ b ∣ y)
    (hxy : x ≠ y) :
    m ≤ p * (Nat.dist x y).factorization p := by
  let e := (m - 1).factorial.factorization p + 1
  have hpow : p ^ e ∣ Nat.dist x y := by
    simpa [e] using shared_controller_pow_dvd_dist hx hy hpx hpy
  have hdist0 : Nat.dist x y ≠ 0 := (Nat.dist_pos_of_ne hxy).ne'
  have he_dist : e ≤ (Nat.dist x y).factorization p :=
    (hx.prime.pow_dvd_iff_le_factorization hdist0).mp hpow
  obtain ⟨k, hm⟩ := hx.prime_dvd_value
  have hk_pos : 0 < k := by
    have hm_pos := hx.value_pos
    rw [hm] at hm_pos
    exact Nat.pos_of_mul_pos_left hm_pos
  have he_formula : e = k + (k - 1).factorial.factorization p := by
    simp only [e]
    rw [hm, factorization_factorial_mul_sub_one hx.prime hk_pos]
    omega
  have hk_e : k ≤ e := by rw [he_formula]; omega
  calc
    m = p * k := hm
    _ ≤ p * e := Nat.mul_le_mul_left p hk_e
    _ ≤ p * (Nat.dist x y).factorization p :=
      Nat.mul_le_mul_left p he_dist

/-- Nonnegative slack data obtained after orienting two distinct controllers
so that `p<q`.  Here `c` is the cofactor in `m=p*q*c`; `A,B` are the two
chosen exponent bounds, and `r,s` are their exact slacks from `q*c+1` and
`p*c`. -/
structure ActivationGapData (m p q c A B r s : ℕ) : Prop where
  value_eq : m = p * q * c
  p_pos : 0 < p
  primes_ordered : p < q
  cofactor_pos : 0 < c
  small_max_eq : A = q * c + 1 + r
  large_max_eq : B = p * c + s

/-- An `OrderedControllers` witness and upper exponent bounds determine
nonnegative activation-gap slacks. -/
theorem ActivationGapData.of_orderedControllers
    {m p q c a b A B : ℕ}
    (h : OrderedControllers m p q c a b)
    (haA : a ≤ A) (hbB : b ≤ B) :
    ∃ r s, ActivationGapData m p q c A B r s := by
  have hsmall : q * c + 1 ≤ A := h.small_exponent.trans haA
  have hlarge : p * c ≤ B := h.large_exponent.trans hbB
  obtain ⟨r, hA⟩ := Nat.exists_eq_add_of_le hsmall
  obtain ⟨s, hB⟩ := Nat.exists_eq_add_of_le hlarge
  exact ⟨r, s, ⟨h.value_eq, h.p_pos, h.primes_ordered, h.cofactor_pos, hA, hB⟩⟩

/-- Ordered activations supply both the old `OrderedControllers` data and
the exact Legendre lower thresholds requested by the fixed-shift theorem. -/
theorem activationGapData_of_activations
    {m p q a b A B : ℕ}
    (hp : ActivatesAt p a m) (hq : ActivatesAt q b m)
    (hpq : p < q) (haA : a ≤ A) (hbB : b ≤ B) :
    ∃ c r s,
      ActivationGapData m p q c A B r s ∧
      q * c + (q * c - 1).factorial.factorization p ≤ a ∧
      p * c + (p * c - 1).factorial.factorization q ≤ b := by
  obtain ⟨c, hcontrollers⟩ := orderedControllers_of_activations hp hq hpq
  obtain ⟨r, s, hgap⟩ :=
    ActivationGapData.of_orderedControllers hcontrollers haA hbB
  have hm_p : m = p * (q * c) := by
    rw [hcontrollers.value_eq]
    ring
  have hm_q : m = q * (p * c) := by
    rw [hcontrollers.value_eq]
    ring
  exact ⟨c, r, s, hgap,
    hp.exact_quotient_threshold_le_exponent hm_p,
    hq.exact_quotient_threshold_le_exponent hm_q⟩

/-- Exact controller exponents after writing `m=p*q*c`.  Their activation
slacks are bounded solely by the multiplicities of the controller primes
inside `c`.  In particular, when `c` is coprime to `p*q`, both exponents
are forced to their exact minimal thresholds. -/
theorem activation_exact_slacks_of_ordered_activations
    {m p q a b : ℕ}
    (hp : ActivatesAt p a m) (hq : ActivatesAt q b m)
    (hpq : p < q) :
    ∃ c α β,
      m = p * q * c ∧ 0 < c ∧
      α ≤ c.factorization p ∧ β ≤ c.factorization q ∧
      a = q * c + (q * c - 1).factorial.factorization p + α ∧
      b = p * c + (p * c - 1).factorial.factorization q + β := by
  obtain ⟨c, hcontrollers⟩ := orderedControllers_of_activations hp hq hpq
  have hc0 : c ≠ 0 := hcontrollers.cofactor_pos.ne'
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have hm_p : m = p * (q * c) := by
    rw [hcontrollers.value_eq]
    ring
  have hm_q : m = q * (p * c) := by
    rw [hcontrollers.value_eq]
    ring
  obtain ⟨α, hα, ha⟩ := hp.exists_exact_quotient_slack hm_p
  obtain ⟨β, hβ, hb⟩ := hq.exists_exact_quotient_slack hm_q
  have hqc : (q * c).factorization p = c.factorization p :=
    factorization_distinct_prime_mul hp.prime hq.prime hpq_ne hc0
  have hpc : (p * c).factorization q = c.factorization q :=
    factorization_distinct_prime_mul hq.prime hp.prime (ne_of_gt hpq) hc0
  rw [hqc] at hα
  rw [hpc] at hβ
  exact ⟨c, α, β, hcontrollers.value_eq, hcontrollers.cofactor_pos,
    hα, hβ, ha, hb⟩

/-- Subtraction-free form of the exact oriented-defect identity. -/
theorem ActivationGapData.defect_add
    {m p q c A B r s : ℕ} (h : ActivationGapData m p q c A B r s) :
    m + (m * (c - 1) + q * c * s + p * c * r + r * s) =
      (A - 1) * B := by
  have hA_pred : q * c + 1 + r - 1 = q * c + r := by omega
  have hc_id : c + c * (c - 1) = c * c := by
    calc
      c + c * (c - 1) = c * ((c - 1) + 1) := by ring
      _ = c * c := by rw [Nat.sub_add_cancel h.cofactor_pos]
  rw [h.value_eq, h.small_max_eq, h.large_max_eq, hA_pred]
  calc
    p * q * c +
          (p * q * c * (c - 1) + q * c * s + p * c * r + r * s) =
        p * q * (c + c * (c - 1)) + q * c * s + p * c * r + r * s := by ring
    _ = p * q * (c * c) + q * c * s + p * c * r + r * s := by rw [hc_id]
    _ = (q * c + r) * (p * c + s) := by ring

/-- Exact displayed oriented-defect identity over the natural numbers. -/
theorem ActivationGapData.defect_sub
    {m p q c A B r s : ℕ} (h : ActivationGapData m p q c A B r s) :
    (A - 1) * B - m =
      m * (c - 1) + q * c * s + p * c * r + r * s := by
  have hadd := h.defect_add
  exact (Nat.sub_eq_iff_eq_add (by omega)).2 (by omega)

/-- The defect identity implies `(A-1)B ≥ c*m`. -/
theorem ActivationGapData.c_mul_value_le_pred_mul
    {m p q c A B r s : ℕ} (h : ActivationGapData m p q c A B r s) :
    c * m ≤ (A - 1) * B := by
  have hc_split : c * m = m + m * (c - 1) := by
    calc
      c * m = ((c - 1) + 1) * m := by rw [Nat.sub_add_cancel h.cofactor_pos]
      _ = m + m * (c - 1) := by ring
  rw [hc_split]
  calc
    m + m * (c - 1) ≤
        m + (m * (c - 1) + q * c * s + p * c * r + r * s) := by omega
    _ = (A - 1) * B := h.defect_add

/-- Strengthened distinct-controller bound:

`c*m + min A B ≤ A*B`.
-/
theorem ActivationGapData.controller_bound
    {m p q c A B r s : ℕ} (h : ActivationGapData m p q c A B r s) :
    c * m + min A B ≤ A * B := by
  have hA_pos : 0 < A := by rw [h.small_max_eq]; omega
  have hAB : (A - 1) * B + B = A * B := by
    calc
      (A - 1) * B + B = ((A - 1) + 1) * B := by ring
      _ = A * B := by rw [Nat.sub_add_cancel hA_pos]
  calc
    c * m + min A B ≤ c * m + B :=
      Nat.add_le_add_left (min_le_right A B) _
    _ ≤ (A - 1) * B + B :=
      Nat.add_le_add_right h.c_mul_value_le_pred_mul B
    _ = A * B := hAB

/-- The nonnegative defect terms vanish exactly in the endpoint
`c=1, r=0, s=0`. -/
theorem ActivationGapData.defect_terms_eq_zero_iff
    {m p q c A B r s : ℕ} (h : ActivationGapData m p q c A B r s) :
    m * (c - 1) + q * c * s + p * c * r + r * s = 0 ↔
      c = 1 ∧ r = 0 ∧ s = 0 := by
  constructor
  · intro hz
    have hq_pos : 0 < q := h.p_pos.trans h.primes_ordered
    have hc_pos : 0 < c := h.cofactor_pos
    have hm_pos : 0 < m := by
      rw [h.value_eq]
      exact Nat.mul_pos (Nat.mul_pos h.p_pos hq_pos) h.cofactor_pos
    have hmc : m * (c - 1) = 0 := by omega
    have hqcs : q * c * s = 0 := by omega
    have hpcr : p * c * r = 0 := by omega
    simp only [Nat.mul_eq_zero] at hmc hqcs hpcr
    have hc_one : c = 1 := by
      rcases hmc with hm_zero | hc_pred_zero
      · exact (hm_pos.ne' hm_zero).elim
      · omega
    have hs_zero : s = 0 := by
      rcases hqcs with (hq_zero | hc_zero) | hs_zero
      · exact (hq_pos.ne' hq_zero).elim
      · exact (h.cofactor_pos.ne' hc_zero).elim
      · exact hs_zero
    have hr_zero : r = 0 := by
      rcases hpcr with (hp_zero | hc_zero) | hr_zero
      · exact (h.p_pos.ne' hp_zero).elim
      · exact (h.cofactor_pos.ne' hc_zero).elim
      · exact hr_zero
    exact ⟨hc_one, hr_zero, hs_zero⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

/-- The displayed oriented defect is zero exactly at
`c=1, r=0, s=0`. -/
theorem ActivationGapData.defect_eq_zero_iff
    {m p q c A B r s : ℕ} (h : ActivationGapData m p q c A B r s) :
    (A - 1) * B - m = 0 ↔ c = 1 ∧ r = 0 ∧ s = 0 := by
  rw [h.defect_sub, h.defect_terms_eq_zero_iff]

/-- The factorization of a product of two distinct primes at the first
prime is exactly one. -/
theorem factorization_mul_distinct_primes_left
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (p * q).factorization p = 1 := by
  have hnot : ¬ p ∣ q := by
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
  rw [Nat.factorization_mul hp.ne_zero hq.ne_zero,
    Finsupp.coe_add, Pi.add_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hnot]

/-- For actual activating exponents, the endpoint `c=1` has controller
defect strictly below the common value.  This uses the collapse of both
exact activation slacks at the squarefree semiprime value `m=p*q`. -/
theorem controller_defect_lt_of_cofactor_eq_one
    {m p q a b A B r s : ℕ}
    (hp : ActivatesAt p a m) (hq : ActivatesAt q b m)
    (hpq : p < q)
    (hgap : ActivationGapData m p q 1 A B r s)
    (hAa : A = a) (hBb : B = b) :
    (A - 1) * B - m < m := by
  have hm : m = p * q := by simpa using hgap.value_eq
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have hmfactp : m.factorization p = 1 := by
    rw [hm]
    exact factorization_mul_distinct_primes_left hp.prime hq.prime hpq_ne
  obtain ⟨α, hαlt, ha⟩ := hp.exists_bounded_activation_slack
  have hαzero : α = 0 := by rw [hmfactp] at hαlt; omega
  have ha_exact : a = q + (q - 1).factorial.factorization p := by
    calc
      a = (m - 1).factorial.factorization p + 1 + α := ha
      _ = ((q - 1).factorial.factorization p + (q - 1)) + 1 + 0 := by
        rw [hm, factorization_factorial_mul_sub_one hp.prime hq.prime.pos,
          hαzero]
      _ = q + (q - 1).factorial.factorization p := by omega
  have hm' : m = q * p := by rw [hm, Nat.mul_comm]
  have hmfactq : m.factorization q = 1 := by
    rw [hm', factorization_mul_distinct_primes_left hq.prime hp.prime
      (ne_of_gt hpq)]
  obtain ⟨β, hβlt, hb⟩ := hq.exists_bounded_activation_slack
  have hβzero : β = 0 := by rw [hmfactq] at hβlt; omega
  have hpred_lt : p - 1 < q := by omega
  have hzero : (p - 1).factorial.factorization q = 0 :=
    Nat.factorization_factorial_eq_zero_of_lt hpred_lt
  have hb_exact : b = p := by
    calc
      b = (m - 1).factorial.factorization q + 1 + β := hb
      _ = ((p - 1).factorial.factorization q + (p - 1)) + 1 + 0 := by
        rw [hm', factorization_factorial_mul_sub_one hq.prime hp.prime.pos,
          hβzero]
      _ = p := by
        simpa [hzero] using (Nat.sub_add_cancel hp.prime.one_le)
  let v := (q - 1).factorial.factorization p
  have hv_bound : v ≤ q - 1 := by
    exact (Nat.factorization_factorial_le_div_pred hp.prime (q - 1)).trans
      (Nat.div_le_self _ _)
  have hp_le_pred : p ≤ q - 1 := by omega
  have hp_dvd : p ∣ (q - 1).factorial := hp.prime.dvd_factorial.mpr hp_le_pred
  have hv_one : 1 ≤ v :=
    (hp.prime.dvd_iff_one_le_factorization (Nat.factorial_ne_zero _)).mp hp_dvd
  have hdef : (q + v - 1) * p - p * q = p * (v - 1) := by
    rw [Nat.add_sub_assoc hv_one]
    have heq : (q + (v - 1)) * p = p * q + p * (v - 1) := by ring
    rw [heq, Nat.add_sub_cancel_left]
  rw [hAa, hBb, ha_exact, hb_exact, hm]
  rw [hdef]
  exact (Nat.mul_lt_mul_left hp.prime.pos).2 (by omega)

/-- Any controller defect below the common value forces `c=1`; this is the
purely algebraic direction of the controller-regime classification. -/
theorem ActivationGapData.cofactor_eq_one_of_controller_defect_lt
    {m p q c A B r s : ℕ} (h : ActivationGapData m p q c A B r s)
    (hlt : (A - 1) * B - m < m) :
    c = 1 := by
  rw [h.defect_sub] at hlt
  by_contra hc
  have hc_pred : 1 ≤ c - 1 := by
    have hc_pos := h.cofactor_pos
    omega
  have hm_le : m ≤ m * (c - 1) := by
    simpa using Nat.mul_le_mul_left m hc_pred
  have hterm_le : m * (c - 1) ≤
      m * (c - 1) + q * c * s + p * c * r + r * s := by omega
  exact (not_lt_of_ge (hm_le.trans hterm_le)) hlt

/-- Exact classification of the near-sharp controller regime for the
actual activating exponents:

`c=1` if and only if `D_ctrl=(a-1)b-m` lies in `[0,m)`.

The difficult conjectural step is therefore to derive the displayed strict
upper bound from adjacency and the remaining factorial-divisor conditions. -/
theorem controller_defect_lt_value_iff_cofactor_eq_one
    {m p q c a b r s : ℕ}
    (hp : ActivatesAt p a m) (hq : ActivatesAt q b m)
    (hpq : p < q)
    (hgap : ActivationGapData m p q c a b r s) :
    (a - 1) * b - m < m ↔ c = 1 := by
  constructor
  · exact hgap.cofactor_eq_one_of_controller_defect_lt
  · intro hc
    subst c
    exact controller_defect_lt_of_cofactor_eq_one hp hq hpq hgap rfl rfl

/-- A nontrivial Kempner value has positive factorial index. -/
theorem IsKempnerValue.value_pos
    {z m : ℕ} (h : IsKempnerValue z m) (hz : 1 < z) :
    0 < m := by
  by_contra hm
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
  rw [hm0] at h
  have hz1 : z = 1 := Nat.dvd_one.mp (by simpa [IsKempnerValue] using h.1)
  omega

/-- For a positive index, minimality of a Kempner value is equivalent to
failure of divisibility at the immediately preceding factorial. -/
theorem isKempnerValue_iff_dvd_factorial_not_dvd_prev
    {z m : ℕ} (hm : 0 < m) :
    IsKempnerValue z m ↔
      z ∣ m.factorial ∧ ¬ z ∣ (m - 1).factorial := by
  constructor
  · intro h
    exact ⟨h.1, h.2 (m - 1) (Nat.sub_lt hm (by omega))⟩
  · rintro ⟨hnow, hprev⟩
    refine ⟨hnow, ?_⟩
    intro k hk hk_dvd
    have hk_pred : k ≤ m - 1 := by omega
    exact hprev (hk_dvd.trans (Nat.factorial_dvd_factorial hk_pred))

/-- Exact factorial-divisor reformulation of a consecutive common fiber. -/
theorem consecutive_common_fiber_iff
    {n m : ℕ} (hm : 0 < m) :
    IsKempnerValue n m ∧ IsKempnerValue (n + 1) m ↔
      n * (n + 1) ∣ m.factorial ∧
      ¬ n ∣ (m - 1).factorial ∧
      ¬ n + 1 ∣ (m - 1).factorial := by
  have hcop : n.Coprime (n + 1) := by
    rw [Nat.coprime_self_add_right]
    simp
  constructor
  · rintro ⟨hn, hsucc⟩
    have hn' := (isKempnerValue_iff_dvd_factorial_not_dvd_prev hm).mp hn
    have hsucc' :=
      (isKempnerValue_iff_dvd_factorial_not_dvd_prev hm).mp hsucc
    exact ⟨hcop.mul_dvd_of_dvd_of_dvd hn'.1 hsucc'.1, hn'.2, hsucc'.2⟩
  · rintro ⟨hprod, hnprev, hsuccprev⟩
    have hnnow : n ∣ m.factorial := (dvd_mul_right n (n + 1)).trans hprod
    have hsuccnow : n + 1 ∣ m.factorial :=
      (dvd_mul_left (n + 1) n).trans hprod
    exact ⟨
      (isKempnerValue_iff_dvd_factorial_not_dvd_prev hm).mpr
        ⟨hnnow, hnprev⟩,
      (isKempnerValue_iff_dvd_factorial_not_dvd_prev hm).mpr
        ⟨hsuccnow, hsuccprev⟩⟩

/-- The part of `z` supplied for the first time by the final factorial
factor `m`. -/
def lastStepResidual (m z : ℕ) : ℕ :=
  z / z.gcd (m - 1).factorial

/-- GCD cancellation lemma underlying the last-step residual method. -/
theorem div_gcd_dvd_of_dvd_mul
    {z f m : ℕ} (hf : 0 < f) (hz : z ∣ m * f) :
    z / z.gcd f ∣ m := by
  let g := z.gcd f
  have hg_pos : 0 < g := by
    simpa [g] using Nat.gcd_pos_of_pos_right z hf
  have hg_z : g ∣ z := by simpa [g] using Nat.gcd_dvd_left z f
  have hg_f : g ∣ f := by simpa [g] using Nat.gcd_dvd_right z f
  have hcop : (z / g).Coprime (f / g) := by
    simpa [g] using Nat.coprime_div_gcd_div_gcd hg_pos
  apply hcop.dvd_of_dvd_mul_right
  have hz_eq : g * (z / g) = z := Nat.mul_div_cancel' hg_z
  have hf_eq : g * (f / g) = f := Nat.mul_div_cancel' hg_f
  have hcancel : g * (z / g) ∣ g * (m * (f / g)) := by
    rw [hz_eq]
    simpa only [hf_eq, mul_assoc, mul_comm, mul_left_comm] using hz
  exact Nat.dvd_of_mul_dvd_mul_left hg_pos hcancel

theorem lastStepResidual_dvd_self (m z : ℕ) :
    lastStepResidual m z ∣ z :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left z (m - 1).factorial)

/-- If `z∣m!`, then its last-step residual divides the final factor `m`. -/
theorem lastStepResidual_dvd_value
    {m z : ℕ} (hm : 0 < m) (hz : z ∣ m.factorial) :
    lastStepResidual m z ∣ m := by
  have hm_eq : (m - 1) + 1 = m := Nat.sub_add_cancel hm
  have hfac : m.factorial = m * (m - 1).factorial := by
    calc
      m.factorial = ((m - 1) + 1).factorial := by rw [hm_eq]
      _ = ((m - 1) + 1) * (m - 1).factorial := Nat.factorial_succ _
      _ = m * (m - 1).factorial := by rw [hm_eq]
  apply div_gcd_dvd_of_dvd_mul (Nat.factorial_pos _)
  simpa only [hfac] using hz

/-- Last-step residuals inherit coprimality from their inputs. -/
theorem lastStepResidual_coprime
    {m x y : ℕ} (hxy : x.Coprime y) :
    (lastStepResidual m x).Coprime (lastStepResidual m y) :=
  Nat.Coprime.of_dvd (lastStepResidual_dvd_self m x)
    (lastStepResidual_dvd_self m y) hxy

/-- Coprime divisors of `m!` consume disjoint parts of the final-factor
budget: the product of their residuals divides `m`. -/
theorem lastStepResidual_mul_dvd_value
    {m x y : ℕ}
    (hm : 0 < m) (hx : x ∣ m.factorial) (hy : y ∣ m.factorial)
    (hxy : x.Coprime y) :
    lastStepResidual m x * lastStepResidual m y ∣ m := by
  exact (lastStepResidual_coprime hxy).mul_dvd_of_dvd_of_dvd
    (lastStepResidual_dvd_value hm hx) (lastStepResidual_dvd_value hm hy)

/-- A positive divisor has residual one exactly when it was already
present in the previous factorial. -/
theorem lastStepResidual_eq_one_iff_dvd_prev
    {m z : ℕ} (hz : 0 < z) :
    lastStepResidual m z = 1 ↔ z ∣ (m - 1).factorial := by
  constructor
  · intro hone
    have hg : z.gcd (m - 1).factorial ∣ z := Nat.gcd_dvd_left _ _
    have hz_eq : z.gcd (m - 1).factorial * lastStepResidual m z = z := by
      simpa [lastStepResidual] using Nat.mul_div_cancel' hg
    rw [hone, mul_one] at hz_eq
    rw [← hz_eq]
    exact Nat.gcd_dvd_right _ _
  · intro hdvd
    rw [lastStepResidual, (Nat.gcd_eq_left_iff_dvd).2 hdvd,
      Nat.div_self hz]

/-- A nontrivial element of a Kempner fiber has a nontrivial last-step
residual. -/
theorem IsKempnerValue.one_lt_lastStepResidual
    {m z : ℕ} (h : IsKempnerValue z m) (hz : 1 < z) :
    1 < lastStepResidual m z := by
  have hm_pos := h.value_pos hz
  have hnot : ¬ z ∣ (m - 1).factorial :=
    h.2 (m - 1) (Nat.sub_lt hm_pos (by omega))
  have hne_one : lastStepResidual m z ≠ 1 := by
    intro hone
    exact hnot ((lastStepResidual_eq_one_iff_dvd_prev
      (zero_lt_one.trans hz)).mp hone)
  have hg_pos : 0 < z.gcd (m - 1).factorial :=
    Nat.gcd_pos_of_pos_left _ (zero_lt_one.trans hz)
  have hg_le : z.gcd (m - 1).factorial ≤ z :=
    Nat.gcd_le_left _ (zero_lt_one.trans hz)
  have hres_pos : 0 < lastStepResidual m z := by
    exact Nat.div_pos hg_le hg_pos
  omega

/-- Exact prime-factorization formula for the last-step residual. -/
theorem factorization_lastStepResidual
    {m z p : ℕ} (hz : z ≠ 0) :
    (lastStepResidual m z).factorization p =
      z.factorization p - (m - 1).factorial.factorization p := by
  rw [lastStepResidual,
    Nat.factorization_div (Nat.gcd_dvd_left _ _),
    Nat.factorization_gcd hz (Nat.factorial_ne_zero _),
    Finsupp.coe_tsub, Pi.sub_apply]
  change z.factorization p - min (z.factorization p)
      ((m - 1).factorial.factorization p) = _
  exact tsub_min

/-- The unused part of the factorial after removing a divisor `z`. -/
def factorialComplement (m z : ℕ) : ℕ :=
  m.factorial / z

theorem factorization_factorialComplement
    {m z p : ℕ} (hz : z ∣ m.factorial) :
    (factorialComplement m z).factorization p =
      m.factorial.factorization p - z.factorization p := by
  rw [factorialComplement, Nat.factorization_div hz,
    Finsupp.coe_tsub, Pi.sub_apply]

/-- If `z` uses an activating exponent exactly, its unused factorial
complement contains fewer copies of the controller prime than the final factor
`m` itself. -/
theorem ActivatesAt.factorization_factorialComplement_lt_value
    {p a m z : ℕ} (h : ActivatesAt p a m)
    (hz : z ∣ m.factorial) (hza : z.factorization p = a) :
    (factorialComplement m z).factorization p < m.factorization p := by
  rw [factorization_factorialComplement hz, hza]
  have hcurrent := h.factorization_factorial_eq_prev_add_value
  have hprev := h.prev_factorization_lt_exponent
  have hupper := h.exponent_le_factorization
  omega

/-- Every activating controller present in `z` survives in the last-step
residual. -/
theorem ActivatesAt.prime_dvd_lastStepResidual
    {p a m z : ℕ} (h : ActivatesAt p a m)
    (hpz : p ^ a ∣ z) (hz : z ≠ 0) :
    p ∣ lastStepResidual m z := by
  have ha_z : a ≤ z.factorization p :=
    (h.prime.pow_dvd_iff_le_factorization hz).mp hpz
  have hone : 1 ≤ z.factorization p -
      (m - 1).factorial.factorization p := by
    have hprev := h.prev_factorization_lt_exponent
    omega
  have hres0 : lastStepResidual m z ≠ 0 := by
    have hg_pos : 0 < z.gcd (m - 1).factorial :=
      Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hz)
    have hg_le : z.gcd (m - 1).factorial ≤ z :=
      Nat.gcd_le_left _ (Nat.pos_of_ne_zero hz)
    exact (Nat.div_pos hg_le hg_pos).ne'
  apply (h.prime.dvd_iff_one_le_factorization hres0).mpr
  rw [factorization_lastStepResidual hz]
  exact hone

/-- Residual package for two nontrivial coprime elements in one Kempner
fiber. -/
theorem coprime_kempner_fiber_lastStepResidual
    {x y m : ℕ}
    (hx : 1 < x) (hy : 1 < y)
    (hxm : IsKempnerValue x m) (hym : IsKempnerValue y m)
    (hxy : x.Coprime y) :
    1 < lastStepResidual m x ∧
      1 < lastStepResidual m y ∧
      lastStepResidual m x * lastStepResidual m y ∣ m := by
  have hm_pos := hxm.value_pos hx
  exact ⟨hxm.one_lt_lastStepResidual hx,
    hym.one_lt_lastStepResidual hy,
    lastStepResidual_mul_dvd_value hm_pos hxm.1 hym.1 hxy⟩

/-- A nontrivial consecutive common fiber forces two distinct prime divisors
of its common value. -/
theorem consecutive_common_fiber_has_distinct_prime_divisors
    {n m : ℕ} (hn : 1 < n)
    (hnm : IsKempnerValue n m)
    (hsuccm : IsKempnerValue (n + 1) m) :
    ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ m ∧ q ∣ m := by
  obtain ⟨p, a, hp, hpn⟩ := hnm.exists_activating_prime_power hn
  have hsucc : 1 < n + 1 := by omega
  obtain ⟨q, b, hq, hqsucc⟩ :=
    hsuccm.exists_activating_prime_power hsucc
  have hcop : n.Coprime (n + 1) := by
    rw [Nat.coprime_self_add_right]
    simp
  have hpq : p ≠ q := activation_primes_ne_of_coprime
    hp.prime hq.prime hp.exponent_pos hq.exponent_pos hpn hqsucc hcop
  exact ⟨p, q, hp.prime, hq.prime, hpq,
    hp.prime_dvd_value, hq.prime_dvd_value⟩

/-- In particular, a prime-power common value cannot occur for consecutive
nontrivial inputs. -/
theorem not_consecutive_common_fiber_at_prime_power
    {n m ℓ k : ℕ} (hn : 1 < n) (hℓ : ℓ.Prime) (hm : m = ℓ ^ k) :
    ¬ (IsKempnerValue n m ∧ IsKempnerValue (n + 1) m) := by
  rintro ⟨hnm, hsuccm⟩
  obtain ⟨p, q, hp, hq, hpq, hpm, hqm⟩ :=
    consecutive_common_fiber_has_distinct_prime_divisors hn hnm hsuccm
  rw [hm] at hpm hqm
  have hpℓ : p = ℓ :=
    (Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hpm)
  have hqℓ : q = ℓ :=
    (Nat.prime_dvd_prime_iff_eq hq hℓ).mp (hq.dvd_of_dvd_pow hqm)
  exact hpq (hpℓ.trans hqℓ.symm)

/-- The full local activation-gap dichotomy, including both possible
orientations of distinct controller primes. -/
inductive ActivationGapDichotomy
    (x y m p q a b A B : ℕ) : Prop
  | shared
      (bases_eq : p = q)
      (threshold_dvd :
        p ^ ((m - 1).factorial.factorization p + 1) ∣ Nat.dist x y)
  | forward
      {c r s : ℕ}
      (gap : ActivationGapData m p q c A B r s)
      (small_exact :
        q * c + (q * c - 1).factorial.factorization p ≤ a)
      (large_exact :
        p * c + (p * c - 1).factorial.factorization q ≤ b)
  | reverse
      {c r s : ℕ}
      (gap : ActivationGapData m q p c B A r s)
      (small_exact :
        p * c + (p * c - 1).factorial.factorization q ≤ b)
      (large_exact :
        q * c + (q * c - 1).factorial.factorization p ≤ a)

/-- Chosen activating prime powers at a common value satisfy the complete
activation-gap dichotomy. -/
theorem activation_gap_dichotomy
    {x y m p q a b A B : ℕ}
    (hp : ActivatesAt p a m) (hq : ActivatesAt q b m)
    (hpx : p ^ a ∣ x) (hqy : q ^ b ∣ y)
    (haA : a ≤ A) (hbB : b ≤ B) :
    ActivationGapDichotomy x y m p q a b A B := by
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · obtain ⟨c, r, s, hgap, ha, hb⟩ :=
      activationGapData_of_activations hp hq hpq haA hbB
    exact .forward hgap ha hb
  · subst q
    exact .shared rfl (shared_controller_pow_dvd_dist hp hq hpx hqy)
  · obtain ⟨c, r, s, hgap, hb, ha⟩ :=
      activationGapData_of_activations hq hp hqp hbB haA
    exact .reverse hgap hb ha

/-- Every pair of nontrivial elements in a common Kempner fiber admits
controllers satisfying `ActivationGapDichotomy`, with the two exponent bounds
chosen to be the actual maximal prime exponents of the inputs.  No
coprimality assumption is needed. -/
theorem kempner_fiber_activation_gap
    {x y m : ℕ}
    (hx : 1 < x) (hy : 1 < y)
    (hxm : IsKempnerValue x m) (hym : IsKempnerValue y m) :
    ∃ p a q b,
      ActivatesAt p a m ∧ p ^ a ∣ x ∧
      ActivatesAt q b m ∧ q ^ b ∣ y ∧
      ActivationGapDichotomy x y m p q a b
        (maxPrimeExponent x) (maxPrimeExponent y) := by
  obtain ⟨p, a, hp, hpx⟩ := hxm.exists_activating_prime_power hx
  obtain ⟨q, b, hq, hqy⟩ := hym.exists_activating_prime_power hy
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hy0 : y ≠ 0 := ne_of_gt (zero_lt_one.trans hy)
  have haE : a ≤ maxPrimeExponent x :=
    ((hp.prime.pow_dvd_iff_le_factorization hx0).mp hpx).trans
      (factorization_le_maxPrimeExponent x p)
  have hbE : b ≤ maxPrimeExponent y :=
    ((hq.prime.pow_dvd_iff_le_factorization hy0).mp hqy).trans
      (factorization_le_maxPrimeExponent y q)
  exact ⟨p, a, q, b, hp, hpx, hq, hqy,
    activation_gap_dichotomy hp hq hpx hqy haE hbE⟩

/-- Positive fixed-shift form of the shared-controller divisibility result. -/
theorem shared_controller_pow_dvd_gap
    {x h m p a b : ℕ}
    (hx : ActivatesAt p a m) (hy : ActivatesAt p b m)
    (hpx : p ^ a ∣ x) (hpy : p ^ b ∣ x + h) :
    p ^ ((m - 1).factorial.factorization p + 1) ∣ h := by
  have hdist := shared_controller_pow_dvd_dist hx hy hpx hpy
  simpa [Nat.dist_eq_sub_of_le (Nat.le_add_right x h)] using hdist

/-- Positive fixed-shift quantitative bound for a shared controller. -/
theorem shared_controller_value_le_prime_mul_factorization_gap
    {x h m p a b : ℕ}
    (hx : ActivatesAt p a m) (hy : ActivatesAt p b m)
    (hpx : p ^ a ∣ x) (hpy : p ^ b ∣ x + h)
    (hh : 0 < h) :
    m ≤ p * h.factorization p := by
  have hne : x ≠ x + h := by omega
  have hbound :=
    shared_controller_value_le_prime_mul_factorization_dist
      hx hy hpx hpy hne
  simpa [Nat.dist_eq_sub_of_le (Nat.le_add_right x h)] using hbound

end KempnerResearch
