/-
Copyright (c) 2026 The KempnerResearch Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Yang, OpenAI Codex
-/
import KempnerResearch.ResidualCofactor

/-!
# Exact complement factorization for last-step residuals

This file identifies the `c = 1` endpoint of the controller-cofactor
partition and gives an exact factorial-complement parametrization.  For two
coprime divisors of `m!`, their last-step residuals split the final factor
`m`, while three remaining factors split `(m - 1)!` with cross-coprimality.
-/

namespace KempnerResearch

/-- The cofactor partition reaches its sharp endpoint exactly when every
exponent and positive residual factor is trivial. -/
theorem cofactor_partition_eq_one_iff
    {p q c α β u v ℓ : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hc : c = p ^ α * q ^ β * u * v * ℓ)
    (_hu : 0 < u) (_hv : 0 < v) (_hℓ : 0 < ℓ) :
    c = 1 ↔ α = 0 ∧ β = 0 ∧ u = 1 ∧ v = 1 ∧ ℓ = 1 := by
  constructor
  · intro hc1
    have hprod : p ^ α * q ^ β * u * v * ℓ = 1 := hc.symm.trans hc1
    have hℓ1 : ℓ = 1 := Nat.eq_one_of_mul_eq_one_left hprod
    have hprev : p ^ α * q ^ β * u * v = 1 :=
      Nat.eq_one_of_mul_eq_one_right hprod
    have hv1 : v = 1 := Nat.eq_one_of_mul_eq_one_left hprev
    have hprev : p ^ α * q ^ β * u = 1 :=
      Nat.eq_one_of_mul_eq_one_right hprev
    have hu1 : u = 1 := Nat.eq_one_of_mul_eq_one_left hprev
    have hprev : p ^ α * q ^ β = 1 :=
      Nat.eq_one_of_mul_eq_one_right hprev
    have hqβ1 : q ^ β = 1 := Nat.eq_one_of_mul_eq_one_left hprev
    have hpα1 : p ^ α = 1 := Nat.eq_one_of_mul_eq_one_right hprev
    have hα0 : α = 0 :=
      (Nat.pow_eq_one.mp hpα1).resolve_left hp.ne_one
    have hβ0 : β = 0 :=
      (Nat.pow_eq_one.mp hqβ1).resolve_left hq.ne_one
    exact ⟨hα0, hβ0, hu1, hv1, hℓ1⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    simpa using hc

/-- Exact complement bookkeeping for two coprime divisors of `m!`.

The last-step residuals consume a factor of `m`; its quotient divides the
unused factorial complement.  After extracting it, the remaining factor
partitions `(m - 1)!`, with the indicated cross-coprimality. -/
theorem coprime_factorial_divisors_exact_complement
    {m x y : ℕ}
    (hm : 0 < m) (hx : x ∣ m.factorial) (hy : y ∣ m.factorial)
    (hxy : x.Coprime y) :
    ∃ A B L,
      x = lastStepResidual m x * A ∧
      y = lastStepResidual m y * B ∧
      lastStepLeftover m x y ∣ factorialComplement m (x * y) ∧
      factorialComplement m (x * y) = lastStepLeftover m x y * L ∧
      A * B * L = (m - 1).factorial ∧
      (lastStepResidual m x).Coprime (B * L) ∧
      (lastStepResidual m y).Coprime (A * L) := by
  let F := (m - 1).factorial
  let A := x.gcd F
  let B := y.gcd F
  let L := F / (A * B)
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    exact Nat.factorial_ne_zero m (by simpa using hx)
  have hy0 : y ≠ 0 := by
    intro hzero
    subst y
    exact Nat.factorial_ne_zero m (by simpa using hy)
  have hA_pos : 0 < A := by
    simpa [A, F] using Nat.gcd_pos_of_pos_right x (Nat.factorial_pos (m - 1))
  have hB_pos : 0 < B := by
    simpa [B, F] using Nat.gcd_pos_of_pos_right y (Nat.factorial_pos (m - 1))
  have hA_dvd_x : A ∣ x := by
    simpa [A, F] using Nat.gcd_dvd_left x F
  have hB_dvd_y : B ∣ y := by
    simpa [B, F] using Nat.gcd_dvd_left y F
  have hA_dvd_F : A ∣ F := by
    simpa [A] using Nat.gcd_dvd_right x F
  have hB_dvd_F : B ∣ F := by
    simpa [B] using Nat.gcd_dvd_right y F
  have hAB_coprime : A.Coprime B :=
    Nat.Coprime.of_dvd hA_dvd_x hB_dvd_y hxy
  have hAB_dvd_F : A * B ∣ F :=
    hAB_coprime.mul_dvd_of_dvd_of_dvd hA_dvd_F hB_dvd_F
  have hx_split : x = lastStepResidual m x * A := by
    symm
    simpa [lastStepResidual, A, F] using Nat.div_mul_cancel hA_dvd_x
  have hy_split : y = lastStepResidual m y * B := by
    symm
    simpa [lastStepResidual, B, F] using Nat.div_mul_cancel hB_dvd_y
  have hF_split : A * B * L = F := by
    simpa [L] using Nat.mul_div_cancel' hAB_dvd_F
  have hm_split :
      lastStepResidual m x * lastStepResidual m y *
          lastStepLeftover m x y = m :=
    lastStepResidual_mul_leftover_eq_value hm hx hy hxy
  have hm_factorial : m.factorial = m * F := by
    have hm_eq : (m - 1) + 1 = m := Nat.sub_add_cancel hm
    calc
      m.factorial = ((m - 1) + 1).factorial := by rw [hm_eq]
      _ = ((m - 1) + 1) * (m - 1).factorial := Nat.factorial_succ _
      _ = m * F := by rw [hm_eq]
  have hxy_split :
      x * y =
        (lastStepResidual m x * lastStepResidual m y) * (A * B) := by
    calc
      x * y =
          (lastStepResidual m x * A) * (lastStepResidual m y * B) :=
            congrArg₂ (fun a b : ℕ => a * b) hx_split hy_split
      _ = (lastStepResidual m x * lastStepResidual m y) * (A * B) := by
        ring
  have hproduct :
      x * y * (lastStepLeftover m x y * L) = m.factorial := by
    calc
      x * y * (lastStepLeftover m x y * L) =
          (lastStepResidual m x * lastStepResidual m y *
            lastStepLeftover m x y) * (A * B * L) := by
              rw [hxy_split]
              ring
      _ = m * F := by rw [hm_split, hF_split]
      _ = m.factorial := hm_factorial.symm
  have hcomplement :
      factorialComplement m (x * y) = lastStepLeftover m x y * L := by
    symm
    simpa [factorialComplement] using
      Nat.eq_div_of_mul_eq_right (mul_ne_zero hx0 hy0) hproduct
  have hr_coprime_FdivA :
      (lastStepResidual m x).Coprime (F / A) := by
    simpa [lastStepResidual, A, F] using
      Nat.coprime_div_gcd_div_gcd hA_pos
  have hs_coprime_FdivB :
      (lastStepResidual m y).Coprime (F / B) := by
    simpa [lastStepResidual, B, F] using
      Nat.coprime_div_gcd_div_gcd hB_pos
  have hBL : B * L = F / A := by
    apply Nat.eq_div_of_mul_eq_right hA_pos.ne'
    calc
      A * (B * L) = A * B * L := by ring
      _ = F := hF_split
  have hAL : A * L = F / B := by
    apply Nat.eq_div_of_mul_eq_right hB_pos.ne'
    calc
      B * (A * L) = A * B * L := by ring
      _ = F := hF_split
  refine ⟨A, B, L, hx_split, hy_split, ?_, hcomplement, ?_, ?_, ?_⟩
  · exact ⟨L, hcomplement⟩
  · simpa [F] using hF_split
  · simpa [hBL] using hr_coprime_FdivA
  · simpa [hAL] using hs_coprime_FdivB

end KempnerResearch
