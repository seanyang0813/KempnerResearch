/-
Copyright (c) 2026 The KempnerResearch Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Yang, OpenAI Codex
-/
import Mathlib

/-!
# Coprime fibers of the Kempner function: arithmetic core

This file kernel-checks the arithmetic step in the coprime-fiber theorem.
The number-theoretic input is encoded by `OrderedControllers`: if distinct
primes `p < q` activate the common Kempner value `m`, write `m = p*q*r`.
Legendre's formula gives `q*r + 1 ≤ a` and `p*r ≤ b` for the activating
exponents. The theorem below turns those sharp local bounds into the
uniform max-exponent obstruction used in the report.
-/

namespace KempnerResearch

/-- `IsKempnerValue x m` says directly that `m` is the least factorial
index whose factorial is divisible by `x`. It is the graph formulation of
the Kempner function and avoids committing to a particular implementation
of a minimization operator. -/
def IsKempnerValue (x m : ℕ) : Prop :=
  x ∣ m.factorial ∧ ∀ k < m, ¬x ∣ k.factorial

/-- Every prime factor of a fiber element is at most its Kempner value. -/
theorem IsKempnerValue.prime_factor_le
    {x m p : ℕ} (hxm : IsKempnerValue x m) (hp : p.Prime) (hpx : p ∣ x) :
    p ≤ m := by
  exact hp.dvd_factorial.mp (hpx.trans hxm.1)

/-- A prime power is *activated at* `m` when it divides `m!` but did not
divide `(m-1)!`. This is exactly the local datum supplied by a prime-power
component that controls a Kempner value `m`. -/
structure ActivatesAt (p a m : ℕ) : Prop where
  prime : p.Prime
  exponent_pos : 0 < a
  dvd_factorial : p ^ a ∣ m.factorial
  not_dvd_prev_factorial : ¬p ^ a ∣ (m - 1).factorial

theorem ActivatesAt.value_pos {p a m : ℕ} (h : ActivatesAt p a m) : 0 < m := by
  by_contra hm
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
  subst m
  exact h.not_dvd_prev_factorial (by simpa using h.dvd_factorial)

/-- Every nontrivial Kempner-fiber element has an activating prime-power
component. This is the formal version of
`S(x)=max_{p^a ‖ x} S(p^a)`. -/
theorem IsKempnerValue.exists_activating_prime_power
    {x m : ℕ} (hxm : IsKempnerValue x m) (hx : 1 < x) :
    ∃ p a, ActivatesAt p a m ∧ p ^ a ∣ x := by
  classical
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hm_pos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    rw [hm0] at hxm
    have hx1 : x = 1 := Nat.dvd_one.mp (by simpa [IsKempnerValue] using hxm.1)
    omega
  have hnot : ¬x ∣ (m - 1).factorial :=
    hxm.2 (m - 1) (Nat.sub_lt hm_pos (by omega))
  have hnotle : ¬∀ p : ℕ, p.Prime →
      x.factorization p ≤ (m - 1).factorial.factorization p := by
    intro hall
    exact hnot ((Nat.factorization_prime_le_iff_dvd hx0 (Nat.factorial_ne_zero _)).mp hall)
  push Not at hnotle
  obtain ⟨p, hp, hfactor⟩ := hnotle
  let a := x.factorization p
  have ha_pos : 0 < a := lt_of_le_of_lt (Nat.zero_le _) hfactor
  have hpow_x : p ^ a ∣ x :=
    (hp.pow_dvd_iff_le_factorization hx0).mpr (by simp [a])
  have hpow_now : p ^ a ∣ m.factorial := hpow_x.trans hxm.1
  have hpow_not_prev : ¬p ^ a ∣ (m - 1).factorial := by
    intro hpow
    have hle := (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp hpow
    exact (not_le_of_gt hfactor) hle
  exact ⟨p, a, ⟨hp, ha_pos, hpow_now, hpow_not_prev⟩, hpow_x⟩

/-- The jump activating a `p`-power can only occur at a multiple of `p`. -/
theorem ActivatesAt.prime_dvd_value {p a m : ℕ} (h : ActivatesAt p a m) : p ∣ m := by
  by_contra hpm
  have hcop : (p ^ a).Coprime m :=
    (h.prime.coprime_iff_not_dvd.mpr hpm).pow_left a
  have hm : (m - 1) + 1 = m := Nat.sub_add_cancel h.value_pos
  have hfac : m.factorial = m * (m - 1).factorial := by
    calc
      m.factorial = ((m - 1) + 1).factorial := by rw [hm]
      _ = ((m - 1) + 1) * (m - 1).factorial := Nat.factorial_succ _
      _ = m * (m - 1).factorial := by rw [hm]
  apply h.not_dvd_prev_factorial
  exact hcop.dvd_of_dvd_mul_left (hfac ▸ h.dvd_factorial)

/-- There are at least `k` copies of `p` in `(p*k)!`. -/
theorem prime_pow_dvd_factorial_mul {p k : ℕ} (hp : p.Prime) :
    p ^ k ∣ (p * k).factorial := by
  apply (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mpr
  rw [Nat.factorization_factorial_mul hp]
  omega

/-- If `p ≤ k`, the copies of `p` inside `k!` provide one extra copy in
`(p*k)!`. -/
theorem prime_pow_succ_dvd_factorial_mul {p k : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    p ^ (k + 1) ∣ (p * k).factorial := by
  apply (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mpr
  rw [Nat.factorization_factorial_mul hp]
  have hpdvd : p ∣ k.factorial := Nat.dvd_factorial hp.pos hpk
  have hone : 1 ≤ k.factorial.factorization p :=
    (hp.dvd_iff_one_le_factorization (Nat.factorial_ne_zero _)).mp hpdvd
  omega

/-- The elementary universal upper bound for an activated prime power. -/
theorem ActivatesAt.value_le_exponent_mul_prime {p a m : ℕ} (h : ActivatesAt p a m) :
    m ≤ a * p := by
  by_contra hle
  have hlt : a * p < m := Nat.lt_of_not_ge hle
  have hindex : p * a ≤ m - 1 := by
    rw [mul_comm]
    omega
  have hpow : p ^ a ∣ (p * a).factorial := prime_pow_dvd_factorial_mul h.prime
  exact h.not_dvd_prev_factorial
    (hpow.trans (Nat.factorial_dvd_factorial hindex))

/-- If an activated value factors as `m = p*k`, then the activating
exponent is at least `k`. -/
theorem ActivatesAt.quotient_le_exponent
    {p a m k : ℕ} (h : ActivatesAt p a m) (hm : m = p * k) : k ≤ a := by
  by_contra hka
  have ha : a ≤ k - 1 := by omega
  have hk_pos : 0 < k := by
    have hm_pos := h.value_pos
    rw [hm] at hm_pos
    exact Nat.pos_of_mul_pos_left hm_pos
  have hindex : p * (k - 1) ≤ m - 1 := by
    rw [hm]
    have hp_pos := h.prime.pos
    have hkpred : k - 1 < k := Nat.sub_lt hk_pos (by omega)
    have hmul : p * (k - 1) < p * k := Nat.mul_lt_mul_of_pos_left hkpred hp_pos
    omega
  have hpow : p ^ (k - 1) ∣ (p * (k - 1)).factorial :=
    prime_pow_dvd_factorial_mul h.prime
  have hpa : p ^ a ∣ p ^ (k - 1) := pow_dvd_pow p ha
  exact h.not_dvd_prev_factorial
    (hpa.trans <| hpow.trans <| Nat.factorial_dvd_factorial hindex)

/-- If additionally `p < k`, the internal multiple `p^2` forces one more
copy, so the lower bound becomes `k+1`. -/
theorem ActivatesAt.quotient_add_one_le_exponent
    {p a m k : ℕ} (h : ActivatesAt p a m) (hm : m = p * k) (hpk : p < k) :
    k + 1 ≤ a := by
  by_contra hka
  have ha : a ≤ k := by omega
  have hindex : p * (k - 1) ≤ m - 1 := by
    rw [hm]
    have hp_pos := h.prime.pos
    have hk_pos : 0 < k := by omega
    have hkpred : k - 1 < k := Nat.sub_lt hk_pos (by omega)
    have hmul : p * (k - 1) < p * k := Nat.mul_lt_mul_of_pos_left hkpred hp_pos
    omega
  have hp_le : p ≤ k - 1 := by omega
  have hpow : p ^ k ∣ (p * (k - 1)).factorial := by
    have hk_one : 1 ≤ k := by omega
    have hbase := prime_pow_succ_dvd_factorial_mul h.prime hp_le
    rwa [Nat.sub_add_cancel hk_one] at hbase
  have hpa : p ^ a ∣ p ^ k := pow_dvd_pow p ha
  exact h.not_dvd_prev_factorial
    (hpa.trans <| hpow.trans <| Nat.factorial_dvd_factorial hindex)

/-- Arithmetic data forced by two ordered activating prime powers in a
common Kempner fiber. -/
structure OrderedControllers (m p q r a b : ℕ) : Prop where
  value_eq : m = p * q * r
  p_pos : 0 < p
  primes_ordered : p < q
  cofactor_pos : 0 < r
  small_exponent : q * r + 1 ≤ a
  large_exponent : p * r ≤ b

/-- Sharp arithmetic core of the two-point coprime-fiber theorem.

`A` and `B` are arbitrary upper bounds for the two activating exponents
(in the application they are the largest prime exponents of the two
arguments). The subtraction-free conclusion is equivalent to
`m ≤ A * B - min A B` over the natural numbers. -/
theorem ordered_controller_bound
    {m p q r a b A B : ℕ}
    (h : OrderedControllers m p q r a b)
    (haA : a ≤ A) (hbB : b ≤ B) :
    m + min A B ≤ A * B := by
  have hqrA : q * r + 1 ≤ A := h.small_exponent.trans haA
  have hprB : p * r ≤ B := h.large_exponent.trans hbB
  have hr1 : 1 ≤ r := h.cofactor_pos
  have hminB : min A B ≤ B := min_le_right A B
  rw [h.value_eq]
  have hm_le_square : p * q * r ≤ (q * r) * (p * r) := by
    calc
      p * q * r = (p * q * r) * 1 := by simp
      _ ≤ (p * q * r) * r := Nat.mul_le_mul_left (p * q * r) hr1
      _ = (q * r) * (p * r) := by ring
  have hm_le_qrB : p * q * r ≤ (q * r) * B :=
    hm_le_square.trans (Nat.mul_le_mul_left (q * r) hprB)
  calc
    p * q * r + min A B ≤ p * q * r + B := Nat.add_le_add_left hminB _
    _ ≤ (q * r) * B + B := Nat.add_le_add_right hm_le_qrB B
    _ = (q * r + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right B hqrA

/-- The displayed form used in the mathematical statement. -/
theorem ordered_controller_bound_sub
    {m p q r a b A B : ℕ}
    (h : OrderedControllers m p q r a b)
    (haA : a ≤ A) (hbB : b ≤ B) :
    m ≤ A * B - min A B := by
  exact Nat.le_sub_of_add_le (ordered_controller_bound h haA hbB)

/-- Activating prime powers belonging to coprime arguments have distinct
prime bases. -/
theorem activation_primes_ne_of_coprime
    {x y p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hpx : p ^ a ∣ x) (hqy : q ^ b ∣ y)
    (hxy : x.Coprime y) : p ≠ q := by
  intro hpq
  subst q
  have hp_dvd_x : p ∣ x := (dvd_pow_self p ha_pos.ne').trans hpx
  have hp_dvd_y : p ∣ y := (dvd_pow_self p hb_pos.ne').trans hqy
  have hp_dvd_gcd : p ∣ x.gcd y := Nat.dvd_gcd hp_dvd_x hp_dvd_y
  rw [hxy.gcd_eq_one] at hp_dvd_gcd
  exact hp.not_dvd_one hp_dvd_gcd

/-- Two ordered activations of the same value supply all fields of
`OrderedControllers`. -/
theorem orderedControllers_of_activations
    {m p q a b : ℕ}
    (hp : ActivatesAt p a m) (hq : ActivatesAt q b m)
    (hpq : p < q) :
    ∃ r, OrderedControllers m p q r a b := by
  have hp_ne_q : p ≠ q := ne_of_lt hpq
  have hpq_coprime : p.Coprime q := (Nat.coprime_primes hp.prime hq.prime).mpr hp_ne_q
  have hpq_dvd : p * q ∣ m := hpq_coprime.mul_dvd_of_dvd_of_dvd
    hp.prime_dvd_value hq.prime_dvd_value
  obtain ⟨r, hm⟩ := hpq_dvd
  have hr_pos : 0 < r := by
    have hm_pos := hp.value_pos
    rw [hm] at hm_pos
    exact Nat.pos_of_mul_pos_left hm_pos
  have hp_lt_qr : p < q * r := by
    exact hpq.trans_le (Nat.le_mul_of_pos_right q hr_pos)
  have ha_lower : q * r + 1 ≤ a := by
    apply hp.quotient_add_one_le_exponent (k := q * r)
    · rw [hm]
      ring
    · exact hp_lt_qr
  have hb_lower : p * r ≤ b := by
    apply hq.quotient_le_exponent (k := p * r)
    rw [hm]
    ring
  exact ⟨r, ⟨hm, hp.prime.pos, hpq, hr_pos, ha_lower, hb_lower⟩⟩

/-- **Sharp coprime-fiber obstruction, in activated-prime-power form.**

If coprime integers `x,y` contain prime powers activated at the same value
`m`, and `A,B` bound those exponents, then

`m + min A B ≤ A*B`.

For actual Kempner-fiber elements, the max formula supplies such an
activated prime power on each side, and one takes `A=E(x), B=E(y)`. -/
theorem coprime_activated_fiber_bound
    {x y m p q a b A B : ℕ}
    (hp : ActivatesAt p a m) (hq : ActivatesAt q b m)
    (hpx : p ^ a ∣ x) (hqy : q ^ b ∣ y)
    (hxy : x.Coprime y)
    (haA : a ≤ A) (hbB : b ≤ B) :
    m + min A B ≤ A * B := by
  have hp_ne_q := activation_primes_ne_of_coprime hp.prime hq.prime
    hp.exponent_pos hq.exponent_pos hpx hqy hxy
  rcases lt_or_gt_of_ne hp_ne_q with hpq | hqp
  · obtain ⟨r, hcontrollers⟩ := orderedControllers_of_activations hp hq hpq
    exact ordered_controller_bound hcontrollers haA hbB
  · obtain ⟨r, hcontrollers⟩ := orderedControllers_of_activations hq hp hqp
    simpa only [min_comm, mul_comm] using
      (ordered_controller_bound hcontrollers hbB haA)

/-- Subtraction form of `coprime_activated_fiber_bound`. -/
theorem coprime_activated_fiber_bound_sub
    {x y m p q a b A B : ℕ}
    (hp : ActivatesAt p a m) (hq : ActivatesAt q b m)
    (hpx : p ^ a ∣ x) (hqy : q ^ b ∣ y)
    (hxy : x.Coprime y)
    (haA : a ≤ A) (hbB : b ≤ B) :
    m ≤ A * B - min A B := by
  exact Nat.le_sub_of_add_le
    (coprime_activated_fiber_bound hp hq hpx hqy hxy haA hbB)

/-- Largest exponent occurring in the canonical prime factorization. -/
def maxPrimeExponent (n : ℕ) : ℕ :=
  n.factorization.support.sup fun p => n.factorization p

theorem factorization_le_maxPrimeExponent (n p : ℕ) :
    n.factorization p ≤ maxPrimeExponent n := by
  by_cases hp0 : n.factorization p = 0
  · simp [hp0]
  · exact Finset.le_sup (Finsupp.mem_support_iff.mpr hp0)

/-- **Sharp coprime-fiber theorem for the Kempner function.**

If two nontrivial coprime integers have common Kempner value `m`, then

`m + min (E x) (E y) ≤ E x * E y`,

where `E` is the largest prime exponent. -/
theorem coprime_kempner_fiber_bound
    {x y m : ℕ}
    (hx : 1 < x) (hy : 1 < y)
    (hxm : IsKempnerValue x m) (hym : IsKempnerValue y m)
    (hxy : x.Coprime y) :
    m + min (maxPrimeExponent x) (maxPrimeExponent y) ≤
      maxPrimeExponent x * maxPrimeExponent y := by
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
  exact coprime_activated_fiber_bound hp hq hpx hqy hxy
    haE hbE

/-- Displayed subtraction form of the sharp coprime-fiber theorem. -/
theorem coprime_kempner_fiber_bound_sub
    {x y m : ℕ}
    (hx : 1 < x) (hy : 1 < y)
    (hxm : IsKempnerValue x m) (hym : IsKempnerValue y m)
    (hxy : x.Coprime y) :
    m ≤ maxPrimeExponent x * maxPrimeExponent y -
      min (maxPrimeExponent x) (maxPrimeExponent y) := by
  exact Nat.le_sub_of_add_le (coprime_kempner_fiber_bound hx hy hxm hym hxy)

/-- Prime-factor form used for the Tutescu reduction. Every prime factor
of either coprime argument obeys the same sharp exponent-product bound. -/
theorem prime_factor_add_min_le_exponent_product
    {x y m ℓ : ℕ}
    (hx : 1 < x) (hy : 1 < y)
    (hxm : IsKempnerValue x m) (hym : IsKempnerValue y m)
    (hxy : x.Coprime y)
    (hℓ : ℓ.Prime) (hℓxy : ℓ ∣ x ∨ ℓ ∣ y) :
    ℓ + min (maxPrimeExponent x) (maxPrimeExponent y) ≤
      maxPrimeExponent x * maxPrimeExponent y := by
  have hℓm : ℓ ≤ m := hℓxy.elim
    (fun hℓx => hxm.prime_factor_le hℓ hℓx)
    (fun hℓy => hym.prime_factor_le hℓ hℓy)
  exact (Nat.add_le_add_right hℓm _).trans
    (coprime_kempner_fiber_bound hx hy hxm hym hxy)

/-- The unsharpened two-point fiber inequality has a particularly simple
arithmetic form. If `p*q ∣ m` and the activating exponents satisfy the
standard upper estimates `m ≤ a*p` and `m ≤ b*q`, then `m ≤ a*b`. -/
theorem two_controller_product_bound
    {m p q a b : ℕ}
    (hm_pos : 0 < m)
    (hpq_dvd : p * q ∣ m)
    (hpa : m ≤ a * p)
    (hqb : m ≤ b * q) :
    m ≤ a * b := by
  obtain ⟨r, rfl⟩ := hpq_dvd
  have hpq_pos : 0 < p * q := by
    by_contra hz
    simp only [not_lt, nonpos_iff_eq_zero] at hz
    simp [hz] at hm_pos
  have hr_pos : 0 < r := Nat.pos_of_mul_pos_left hm_pos
  have hp_pos : 0 < p := Nat.pos_of_mul_pos_right hpq_pos
  have hqr_a : q * r ≤ a := by
    apply Nat.le_of_mul_le_mul_left (c := p) _ hp_pos
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hpa
  have hp_b : p ≤ b := by
    have hpr_b : p * r ≤ b := by
      have hq_pos : 0 < q := Nat.pos_of_mul_pos_left hpq_pos
      apply Nat.le_of_mul_le_mul_right (c := q) _ hq_pos
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hqb
    exact (Nat.le_mul_of_pos_right p hr_pos).trans hpr_b
  calc
    p * q * r = (q * r) * p := by ring
    _ ≤ a * b := Nat.mul_le_mul hqr_a hp_b

end KempnerResearch
