/-
Algebraic residual certificates for positive fractional powers.

A "certificate" for the positive real `T` is the pair `(a, b)` with
`x^a * T^b = 1`, i.e. `T = x^(-a/b)`.  Everything here is stated with
natural-number powers only (no `Real.rpow`), so any generator — binomial
slices, Poisson kernels, or otherwise — that produces bracketing values
`L, U` with `x^a L^b ≤ 1 ≤ x^a U^b` can use the same certification
interface.  The final example certifies `√10` numerically.

This module is deliberately independent of the residue-slice development.
-/
import Mathlib

open scoped BigOperators

namespace ResidualCertificate

/-- Lower order certificate: if `A` undershoots the unit residual, then
`A ≤ T`. -/
theorem residual_order_lower {x A T : ℝ} {a b : ℕ}
    (hx : 0 < x) (_hA : 0 < A) (hT : 0 < T) (hb : 0 < b)
    (hT1 : x ^ a * T ^ b = 1) (hA1 : x ^ a * A ^ b ≤ 1) :
    A ≤ T := by
  have hxa : 0 < x ^ a := pow_pos hx a
  have hle : x ^ a * A ^ b ≤ x ^ a * T ^ b := by rw [hT1]; exact hA1
  have hAT : A ^ b ≤ T ^ b := le_of_mul_le_mul_left hle hxa
  exact le_of_pow_le_pow_left₀ hb.ne' hT.le hAT

/-- Upper order certificate: if `A` overshoots the unit residual, then
`T ≤ A`. -/
theorem residual_order_upper {x A T : ℝ} {a b : ℕ}
    (hx : 0 < x) (hA : 0 < A) (_hT : 0 < T) (hb : 0 < b)
    (hT1 : x ^ a * T ^ b = 1) (hA1 : 1 ≤ x ^ a * A ^ b) :
    T ≤ A := by
  have hxa : 0 < x ^ a := pow_pos hx a
  have hle : x ^ a * T ^ b ≤ x ^ a * A ^ b := by rw [hT1]; exact hA1
  have hTA : T ^ b ≤ A ^ b := le_of_mul_le_mul_left hle hxa
  exact le_of_pow_le_pow_left₀ hb.ne' hA.le hTA

/-- A two-sided bracket certificate: undershoot below, overshoot above. -/
theorem residual_bracket {x L U T : ℝ} {a b : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hU : 0 < U) (hT : 0 < T) (hb : 0 < b)
    (hT1 : x ^ a * T ^ b = 1)
    (hLb : x ^ a * L ^ b ≤ 1) (hUb : 1 ≤ x ^ a * U ^ b) :
    L ≤ T ∧ T ≤ U :=
  ⟨residual_order_lower hx hL hT hb hT1 hLb,
   residual_order_upper hx hU hT hb hT1 hUb⟩

/-- Intersecting two bracketing intervals sharpens both bounds. -/
theorem residual_pair_intersection {T L₁ U₁ L₂ U₂ : ℝ}
    (h1 : L₁ ≤ T ∧ T ≤ U₁) (h2 : L₂ ≤ T ∧ T ≤ U₂) :
    max L₁ L₂ ≤ T ∧ T ≤ min U₁ U₂ :=
  ⟨max_le h1.1 h2.1, le_min h1.2 h2.2⟩

/-- Intersecting a nonempty finite family of bracketing intervals.  The
`Finset.Nonempty` hypothesis rules out the empty collection, for which no
`sup'`/`inf'` is defined. -/
theorem residual_finset_intersection {ι : Type*} {T : ℝ} {L U : ι → ℝ}
    {s : Finset ι} (hs : s.Nonempty)
    (hlo : ∀ i ∈ s, L i ≤ T) (hhi : ∀ i ∈ s, T ≤ U i) :
    s.sup' hs L ≤ T ∧ T ≤ s.inf' hs U :=
  ⟨Finset.sup'_le hs L hlo, Finset.le_inf' hs U hhi⟩

/-- Exact rational certificate for `√10`: `(79/25)^2 ≤ 10 ≤ (16/5)^2`, hence
`79/25 ≤ √10 ≤ 16/5`. -/
theorem sqrt_ten_certificate :
    ((79 : ℝ) / 25) ^ 2 ≤ 10 ∧ (10 : ℝ) ≤ ((16 : ℝ) / 5) ^ 2 ∧
      (79 : ℝ) / 25 ≤ Real.sqrt 10 ∧ Real.sqrt 10 ≤ (16 : ℝ) / 5 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (79 : ℝ) / 25 = Real.sqrt ((79 / 25) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  · rw [show (16 : ℝ) / 5 = Real.sqrt ((16 / 5) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)

end ResidualCertificate
