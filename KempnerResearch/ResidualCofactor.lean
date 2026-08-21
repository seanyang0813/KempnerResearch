/-
Copyright (c) 2026 The KempnerResearch Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Yang, OpenAI Codex
-/
import KempnerResearch.ActivationGap

/-!
# Last-step residuals and the controller cofactor

This file refines the last-step residual package from `ActivationGap.lean`.
For two coprime inputs with ordered exact controllers, it removes the mandatory
controller powers from their residuals and proves that the remaining factors,
the activation slacks, and an unused leftover partition the controller
cofactor `c` exactly.  The resulting five-way split states the precise cases
that a proof eliminating `c ≥ 2` still has to rule out.
-/

open Finset List Finsupp

namespace KempnerResearch

/-- An activating controller can be chosen at its input's full prime
factorization, rather than at an arbitrary smaller activating exponent. -/
theorem IsKempnerValue.exists_exact_activating_prime_power
    {x m : ℕ} (hxm : IsKempnerValue x m) (hx : 1 < x) :
    ∃ p, ActivatesAt p (x.factorization p) m ∧
      p ^ x.factorization p ∣ x := by
  obtain ⟨p, a, hp, hpa⟩ := hxm.exists_activating_prime_power hx
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have ha_le : a ≤ x.factorization p :=
    (hp.prime.pow_dvd_iff_le_factorization hx0).mp hpa
  have he_pos : 0 < x.factorization p :=
    hp.exponent_pos.trans_le ha_le
  have he_dvd_x : p ^ x.factorization p ∣ x :=
    (hp.prime.pow_dvd_iff_le_factorization hx0).mpr le_rfl
  have he_not_prev : ¬p ^ x.factorization p ∣ (m - 1).factorial := by
    intro he
    exact hp.not_dvd_prev_factorial ((pow_dvd_pow p ha_le).trans he)
  exact ⟨p, ⟨hp.prime, he_pos, he_dvd_x.trans hxm.1, he_not_prev⟩,
    he_dvd_x⟩

/-- A nonzero input has a positive last-step residual. -/
theorem lastStepResidual_pos
    {m z : ℕ} (hz : z ≠ 0) : 0 < lastStepResidual m z := by
  have hg_pos : 0 < z.gcd (m - 1).factorial :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hz)
  have hg_le : z.gcd (m - 1).factorial ≤ z :=
    Nat.gcd_le_left _ (Nat.pos_of_ne_zero hz)
  exact Nat.div_pos hg_le hg_pos

/-- Exact residual valuation attached to a specified activation slack. -/
theorem factorization_lastStepResidual_eq_slack_add_one
    {p a m z α : ℕ} (hz : z ≠ 0)
    (hza : z.factorization p = a)
    (ha : a = (m - 1).factorial.factorization p + 1 + α) :
    (lastStepResidual m z).factorization p = α + 1 := by
  rw [factorization_lastStepResidual hz, hza, ha]
  omega

/-- Exact quotient-slack form of the residual valuation. -/
theorem ActivatesAt.exists_quotient_slack_with_residual_factorization
    {p a m k z : ℕ} (h : ActivatesAt p a m) (hm : m = p * k)
    (hz : z ≠ 0) (hza : z.factorization p = a) :
    ∃ α, α ≤ k.factorization p ∧
      (lastStepResidual m z).factorization p = α + 1 := by
  obtain ⟨α, hα, ha⟩ := h.exists_exact_quotient_slack hm
  refine ⟨α, hα, ?_⟩
  have hk_pos : 0 < k := by
    have hm_pos := h.value_pos
    rw [hm] at hm_pos
    exact Nat.pos_of_mul_pos_left hm_pos
  rw [factorization_lastStepResidual hz, hza, ha, hm,
    factorization_factorial_mul_sub_one h.prime hk_pos]
  omega

/-- The controller power occurring in the residual is exact. -/
theorem ActivatesAt.residual_controller_pow_exact
    {p a m z α : ℕ} (h : ActivatesAt p a m) (hz : z ≠ 0)
    (hza : z.factorization p = a)
    (ha : a = (m - 1).factorial.factorization p + 1 + α) :
    p ^ (α + 1) ∣ lastStepResidual m z ∧
      ¬p ^ (α + 2) ∣ lastStepResidual m z := by
  have hres0 : lastStepResidual m z ≠ 0 :=
    (lastStepResidual_pos hz).ne'
  have hfac :=
    factorization_lastStepResidual_eq_slack_add_one hz hza ha
  constructor
  · exact (h.prime.pow_dvd_iff_le_factorization hres0).mpr (by omega)
  · intro hpow
    have hle := (h.prime.pow_dvd_iff_le_factorization hres0).mp hpow
    omega

/-- Canonical unused last-step factor after the two coprime residuals. -/
def lastStepLeftover (m x y : ℕ) : ℕ :=
  m / (lastStepResidual m x * lastStepResidual m y)

/-- The two residuals and their canonical leftover multiply back to `m`. -/
theorem lastStepResidual_mul_leftover_eq_value
    {m x y : ℕ}
    (hm : 0 < m) (hx : x ∣ m.factorial) (hy : y ∣ m.factorial)
    (hxy : x.Coprime y) :
    lastStepResidual m x * lastStepResidual m y *
        lastStepLeftover m x y = m := by
  exact Nat.mul_div_cancel'
    (lastStepResidual_mul_dvd_value hm hx hy hxy)

/-- Clean existential partition for a nontrivial coprime common fiber. -/
theorem coprime_kempner_fiber_exists_lastStepResidual_partition
    {x y m : ℕ}
    (hx : 1 < x) (hy : 1 < y)
    (hxm : IsKempnerValue x m) (hym : IsKempnerValue y m)
    (hxy : x.Coprime y) :
    ∃ ℓ,
      m = lastStepResidual m x * lastStepResidual m y * ℓ ∧
      (lastStepResidual m x).Coprime (lastStepResidual m y) ∧
      1 < lastStepResidual m x ∧
      1 < lastStepResidual m y := by
  obtain ⟨hxres, hyres, hprod⟩ :=
    coprime_kempner_fiber_lastStepResidual hx hy hxm hym hxy
  obtain ⟨ℓ, hℓ⟩ := hprod
  exact ⟨ℓ, hℓ, lastStepResidual_coprime hxy, hxres, hyres⟩

/-- Ordered exact controllers expose their complete residual powers together
with the common residual partition. -/
theorem ordered_exact_controllers_residual_partition
    {x y m p q a b : ℕ}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hp : ActivatesAt p a m) (hq : ActivatesAt q b m)
    (hpq : p < q)
    (hxa : x.factorization p = a) (hyb : y.factorization q = b)
    (hxm : x ∣ m.factorial) (hym : y ∣ m.factorial)
    (hxy : x.Coprime y) :
    ∃ c α β ℓ,
      m = p * q * c ∧ 0 < c ∧
      α ≤ c.factorization p ∧ β ≤ c.factorization q ∧
      (lastStepResidual m x).factorization p = α + 1 ∧
      (lastStepResidual m y).factorization q = β + 1 ∧
      p ^ (α + 1) ∣ lastStepResidual m x ∧
      q ^ (β + 1) ∣ lastStepResidual m y ∧
      m = lastStepResidual m x * lastStepResidual m y * ℓ ∧
      (lastStepResidual m x).Coprime (lastStepResidual m y) := by
  obtain ⟨c, α, β, hm, hc, hα, hβ, ha, hb⟩ :=
    activation_exact_slacks_of_ordered_activations hp hq hpq
  have hqc_pos : 0 < q * c :=
    Nat.mul_pos hq.prime.pos hc
  have hpc_pos : 0 < p * c :=
    Nat.mul_pos hp.prime.pos hc
  have hm_p : m = p * (q * c) := by rw [hm]; ring
  have hm_q : m = q * (p * c) := by rw [hm]; ring
  have hres_p : (lastStepResidual m x).factorization p = α + 1 := by
    rw [factorization_lastStepResidual hx0, hxa, ha, hm_p,
      factorization_factorial_mul_sub_one hp.prime hqc_pos]
    omega
  have hres_q : (lastStepResidual m y).factorization q = β + 1 := by
    rw [factorization_lastStepResidual hy0, hyb, hb, hm_q,
      factorization_factorial_mul_sub_one hq.prime hpc_pos]
    omega
  have hxres0 : lastStepResidual m x ≠ 0 :=
    (lastStepResidual_pos hx0).ne'
  have hyres0 : lastStepResidual m y ≠ 0 :=
    (lastStepResidual_pos hy0).ne'
  have hp_pow : p ^ (α + 1) ∣ lastStepResidual m x :=
    (hp.prime.pow_dvd_iff_le_factorization hxres0).mpr (by omega)
  have hq_pow : q ^ (β + 1) ∣ lastStepResidual m y :=
    (hq.prime.pow_dvd_iff_le_factorization hyres0).mpr (by omega)
  have hprod := lastStepResidual_mul_dvd_value hp.value_pos hxm hym hxy
  obtain ⟨ℓ, hℓ⟩ := hprod
  exact ⟨c, α, β, ℓ, hm, hc, hα, hβ, hres_p, hres_q,
    hp_pow, hq_pow, hℓ, lastStepResidual_coprime hxy⟩

/-- Exact controller valuations left in the third factor of a residual
partition.  The third factor need not be coprime to either residual. -/
theorem residual_partition_leftover_factorizations
    {x y m p q c α β ℓ : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hc : c ≠ 0)
    (hm : m = p * q * c)
    (hxres0 : lastStepResidual m x ≠ 0)
    (hyres0 : lastStepResidual m y ≠ 0)
    (hres_p : (lastStepResidual m x).factorization p = α + 1)
    (hres_q : (lastStepResidual m y).factorization q = β + 1)
    (hcop : (lastStepResidual m x).Coprime (lastStepResidual m y))
    (hpart : m = lastStepResidual m x * lastStepResidual m y * ℓ) :
    ℓ.factorization p = c.factorization p - α ∧
      ℓ.factorization q = c.factorization q - β := by
  let rx := lastStepResidual m x
  let ry := lastStepResidual m y
  have hm0 : m ≠ 0 := by
    rw [hm]
    exact mul_ne_zero (mul_ne_zero hp.ne_zero hq.ne_zero) hc
  have hℓ0 : ℓ ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hpart
    exact hm0 hpart
  have hp_rx : p ∣ rx := by
    apply (hp.dvd_iff_one_le_factorization hxres0).mpr
    have hrx : rx.factorization p = α + 1 := by simpa only [rx] using hres_p
    rw [hrx]
    omega
  have hq_ry : q ∣ ry := by
    apply (hq.dvd_iff_one_le_factorization hyres0).mpr
    have hry : ry.factorization q = β + 1 := by simpa only [ry] using hres_q
    rw [hry]
    omega
  have hp_not_ry : ¬p ∣ ry :=
    hp.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hp_rx hcop)
  have hq_not_rx : ¬q ∣ rx :=
    hq.coprime_iff_not_dvd.mp
      (Nat.Coprime.of_dvd_left hq_ry hcop.symm)
  have hfac_ry_p : ry.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hp_not_ry
  have hfac_rx_q : rx.factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hq_not_rx
  have hqc0 : q * c ≠ 0 := mul_ne_zero hq.ne_zero hc
  have hpc0 : p * c ≠ 0 := mul_ne_zero hp.ne_zero hc
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have hqc : (q * c).factorization p = c.factorization p :=
    factorization_distinct_prime_mul hp hq hpq_ne hc
  have hpc : (p * c).factorization q = c.factorization q :=
    factorization_distinct_prime_mul hq hp (ne_of_gt hpq) hc
  have hmf_p : m.factorization p = c.factorization p + 1 := by
    have hm_p : m = p * (q * c) := by rw [hm]; ring
    rw [hm_p, Nat.factorization_mul hp.ne_zero hqc0,
      Finsupp.coe_add, Pi.add_apply, hp.factorization_self, hqc]
    omega
  have hmf_q : m.factorization q = c.factorization q + 1 := by
    have hm_q : m = q * (p * c) := by rw [hm]; ring
    rw [hm_q, Nat.factorization_mul hq.ne_zero hpc0,
      Finsupp.coe_add, Pi.add_apply, hq.factorization_self, hpc]
    omega
  have hpart_p : m.factorization p =
      rx.factorization p + ry.factorization p + ℓ.factorization p := by
    rw [hpart, Nat.factorization_mul
      (mul_ne_zero hxres0 hyres0) hℓ0,
      Nat.factorization_mul hxres0 hyres0,
      Finsupp.coe_add, Pi.add_apply, Finsupp.coe_add, Pi.add_apply]
  have hpart_q : m.factorization q =
      rx.factorization q + ry.factorization q + ℓ.factorization q := by
    rw [hpart, Nat.factorization_mul
      (mul_ne_zero hxres0 hyres0) hℓ0,
      Nat.factorization_mul hxres0 hyres0,
      Finsupp.coe_add, Pi.add_apply, Finsupp.coe_add, Pi.add_apply]
  change ℓ.factorization p = c.factorization p - α ∧
    ℓ.factorization q = c.factorization q - β
  change rx.factorization p = α + 1 at hres_p
  change ry.factorization q = β + 1 at hres_q
  omega

/-- After removing the exact controller powers from the residuals, the
remaining cores and the leftover partition the cofactor `c` itself. -/
theorem residual_controller_cores_partition_cofactor
    {x y m p q c α β ℓ : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hm : m = p * q * c) (hc : c ≠ 0)
    (hxres0 : lastStepResidual m x ≠ 0)
    (hyres0 : lastStepResidual m y ≠ 0)
    (hres_p : (lastStepResidual m x).factorization p = α + 1)
    (hres_q : (lastStepResidual m y).factorization q = β + 1)
    (hcop : (lastStepResidual m x).Coprime (lastStepResidual m y))
    (hpart : m = lastStepResidual m x * lastStepResidual m y * ℓ) :
    ∃ u v,
      lastStepResidual m x = p ^ (α + 1) * u ∧
      lastStepResidual m y = q ^ (β + 1) * v ∧
      c = p ^ α * q ^ β * u * v * ℓ ∧
      0 < u ∧ 0 < v ∧ 0 < ℓ ∧
      ¬p ∣ u ∧ ¬p ∣ v ∧ ¬q ∣ u ∧ ¬q ∣ v ∧
      u.Coprime v := by
  let rx := lastStepResidual m x
  let ry := lastStepResidual m y
  have hp_pow : p ^ (α + 1) ∣ rx := by
    apply (hp.pow_dvd_iff_le_factorization hxres0).mpr
    omega
  have hq_pow : q ^ (β + 1) ∣ ry := by
    apply (hq.pow_dvd_iff_le_factorization hyres0).mpr
    omega
  obtain ⟨u, hu⟩ := hp_pow
  obtain ⟨v, hv⟩ := hq_pow
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hu
    exact hxres0 hu
  have hv0 : v ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hv
    exact hyres0 hv
  have hm0 : m ≠ 0 := by
    rw [hm]
    exact mul_ne_zero (mul_ne_zero hp.ne_zero hq.ne_zero) hc
  have hℓ0 : ℓ ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hpart
    exact hm0 hpart
  have hufac : u.factorization p = 0 := by
    have hfac : rx.factorization p = α + 1 + u.factorization p := by
      rw [hu, Nat.factorization_mul
        (Nat.pow_pos hp.pos).ne' hu0,
        Finsupp.coe_add, Pi.add_apply,
        Nat.factorization_pow_self hp]
    change (lastStepResidual m x).factorization p =
      α + 1 + u.factorization p at hfac
    omega
  have hvfac : v.factorization q = 0 := by
    have hfac : ry.factorization q = β + 1 + v.factorization q := by
      rw [hv, Nat.factorization_mul
        (Nat.pow_pos hq.pos).ne' hv0,
        Finsupp.coe_add, Pi.add_apply,
        Nat.factorization_pow_self hq]
    change (lastStepResidual m y).factorization q =
      β + 1 + v.factorization q at hfac
    omega
  have hp_not_u : ¬p ∣ u := by
    intro hdvd
    have hone := (hp.dvd_iff_one_le_factorization hu0).mp hdvd
    omega
  have hq_not_v : ¬q ∣ v := by
    intro hdvd
    have hone := (hq.dvd_iff_one_le_factorization hv0).mp hdvd
    omega
  have hu_dvd_rx : u ∣ rx := by
    rw [hu]
    exact dvd_mul_left u _
  have hv_dvd_ry : v ∣ ry := by
    rw [hv]
    exact dvd_mul_left v _
  have hp_rx : p ∣ rx :=
    (dvd_pow_self p (by omega)).trans ⟨u, hu⟩
  have hq_ry : q ∣ ry :=
    (dvd_pow_self q (by omega)).trans ⟨v, hv⟩
  have hp_not_ry : ¬p ∣ ry :=
    hp.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hp_rx hcop)
  have hq_not_rx : ¬q ∣ rx :=
    hq.coprime_iff_not_dvd.mp
      (Nat.Coprime.of_dvd_left hq_ry hcop.symm)
  have hp_not_v : ¬p ∣ v := fun hdvd ↦ hp_not_ry (hdvd.trans hv_dvd_ry)
  have hq_not_u : ¬q ∣ u := fun hdvd ↦ hq_not_rx (hdvd.trans hu_dvd_rx)
  have huv : u.Coprime v :=
    Nat.Coprime.of_dvd hu_dvd_rx hv_dvd_ry hcop
  have hpq_pos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hcancel : p * q * c =
      p * q * (p ^ α * q ^ β * u * v * ℓ) := by
    calc
      p * q * c = m := hm.symm
      _ = rx * ry * ℓ := hpart
      _ = (p ^ (α + 1) * u) * (q ^ (β + 1) * v) * ℓ := by
        rw [← hu, ← hv]
      _ = p * q * (p ^ α * q ^ β * u * v * ℓ) := by
        rw [pow_succ, pow_succ]
        ring
  have hc_eq : c = p ^ α * q ^ β * u * v * ℓ :=
    Nat.eq_of_mul_eq_mul_left hpq_pos hcancel
  exact ⟨u, v, hu, hv, hc_eq, Nat.pos_of_ne_zero hu0,
    Nat.pos_of_ne_zero hv0, Nat.pos_of_ne_zero hℓ0, hp_not_u, hp_not_v,
    hq_not_u, hq_not_v, huv⟩

/-- One-shot form used by the `c ≥ 2` attack: exact controllers split the
cofactor into their activation-slack powers, two controller-free coprime
residual cores, and the unrestricted leftover. -/
theorem ordered_exact_controllers_cofactor_partition
    {x y m p q a b : ℕ}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hp : ActivatesAt p a m) (hq : ActivatesAt q b m)
    (hpq : p < q)
    (hxa : x.factorization p = a) (hyb : y.factorization q = b)
    (hxm : x ∣ m.factorial) (hym : y ∣ m.factorial)
    (hxy : x.Coprime y) :
    ∃ c α β ℓ u v,
      m = p * q * c ∧ 0 < c ∧
      α ≤ c.factorization p ∧ β ≤ c.factorization q ∧
      lastStepResidual m x = p ^ (α + 1) * u ∧
      lastStepResidual m y = q ^ (β + 1) * v ∧
      c = p ^ α * q ^ β * u * v * ℓ ∧
      0 < u ∧ 0 < v ∧ 0 < ℓ ∧
      ¬p ∣ u ∧ ¬p ∣ v ∧ ¬q ∣ u ∧ ¬q ∣ v ∧
      u.Coprime v := by
  obtain ⟨c, α, β, ℓ, hm, hc, hα, hβ, hres_p, hres_q,
      hp_pow, hq_pow, hpart, hcop⟩ :=
    ordered_exact_controllers_residual_partition hx0 hy0 hp hq hpq
      hxa hyb hxm hym hxy
  obtain ⟨u, v, hu, hv, hcpart, hu_pos, hv_pos, hℓ_pos,
      hp_not_u, hp_not_v, hq_not_u, hq_not_v, huv⟩ :=
    residual_controller_cores_partition_cofactor hp.prime hq.prime hm hc.ne'
      (lastStepResidual_pos hx0).ne' (lastStepResidual_pos hy0).ne'
      hres_p hres_q hcop hpart
  exact ⟨c, α, β, ℓ, u, v, hm, hc, hα, hβ, hu, hv, hcpart,
    hu_pos, hv_pos, hℓ_pos, hp_not_u, hp_not_v, hq_not_u, hq_not_v, huv⟩

/-- Exhaustive first split for the `c ≥ 2` branch of a cofactor partition. -/
theorem cofactor_partition_cases_of_two_le
    {p q c α β u v ℓ : ℕ}
    (hc : c = p ^ α * q ^ β * u * v * ℓ)
    (hu : 0 < u) (hv : 0 < v) (hℓ : 0 < ℓ) (hc2 : 2 ≤ c) :
    0 < α ∨ 0 < β ∨ 1 < u ∨ 1 < v ∨ 1 < ℓ := by
  by_contra hall
  push Not at hall
  obtain ⟨hα, hβ, hu_le, hv_le, hℓ_le⟩ := hall
  have hα0 : α = 0 := by omega
  have hβ0 : β = 0 := by omega
  have hu1 : u = 1 := by omega
  have hv1 : v = 1 := by omega
  have hℓ1 : ℓ = 1 := by omega
  simp [hα0, hβ0, hu1, hv1, hℓ1] at hc
  omega

end KempnerResearch
