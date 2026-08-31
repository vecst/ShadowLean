/-
Cubic-silver finite-row crossover, Phase B4B5: real quadratic branch
classification, including the negative-channel boundary.

Classifies the real roots of the two limiting crossover quadratics.
Positive channel `y^2 - lambda*y - 1`: exactly the two displayed distinct real
roots for every real `lambda`. Negative channel `y^2 - lambda*y + 1`: no real
root when `|lambda| < 2`; exactly one double real root `lambda/2` when
`|lambda| = 2` (there the derivative factor `2*y - lambda` vanishes, so the
simple-root branch selection cannot apply); exactly the two displayed distinct
real roots when `2 < |lambda|`. This is a statement about the limiting
quadratics only: no finite-row root existence or convergence is asserted at the
double-root boundary, and no cofinality of either selected center-error sign is
claimed.
-/
import RequestProject.SilverFiniteRowExplicitCrossoverBranches

open scoped Real

namespace SilverFiniteRow

theorem positiveCrossoverRootMinus_lt_plus (lambda : Real) :
    positiveCrossoverRootMinus lambda < positiveCrossoverRootPlus lambda := by
  have hs0 : 0 < Real.sqrt (lambda ^ 2 + 4) :=
    Real.sqrt_pos.mpr (SilverCrossover.positive_error_discriminant lambda)
  unfold positiveCrossoverRootMinus positiveCrossoverRootPlus
  linarith

theorem positive_crossover_eq_zero_iff (lambda y : Real) :
    y ^ 2 - lambda * y - 1 = 0 ↔
      y = positiveCrossoverRootMinus lambda ∨
      y = positiveCrossoverRootPlus lambda := by
  have hs2 : Real.sqrt (lambda ^ 2 + 4) ^ 2 = lambda ^ 2 + 4 :=
    Real.sq_sqrt (by positivity)
  have hfac : y ^ 2 - lambda * y - 1 =
      (y - positiveCrossoverRootMinus lambda) *
        (y - positiveCrossoverRootPlus lambda) := by
    unfold positiveCrossoverRootMinus positiveCrossoverRootPlus
    linear_combination (1 / 4 : Real) * hs2
  constructor
  · intro h
    rw [hfac, mul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl | rfl)
    · exact (positiveCrossoverRootMinus_spec lambda).1
    · exact (positiveCrossoverRootPlus_spec lambda).1

theorem negative_crossover_ne_zero_of_abs_lt_two
    {lambda : Real} (hlambda : |lambda| < 2) (y : Real) :
    y ^ 2 - lambda * y + 1 ≠ 0 := by
  intro h
  have hd : lambda ^ 2 - 4 < 0 :=
    SilverCrossover.negative_discriminant_of_abs_lt_two hlambda
  nlinarith [sq_nonneg (2 * y - lambda)]

theorem negative_crossover_boundary_root_and_not_simple
    {lambda : Real} (hlambda : |lambda| = 2) :
    (lambda / 2) ^ 2 - lambda * (lambda / 2) + 1 = 0 ∧
      2 * (lambda / 2) - lambda = 0 := by
  have hd0 : lambda ^ 2 - 4 = 0 :=
    SilverCrossover.negative_discriminant_eq_zero_of_abs_eq_two hlambda
  refine ⟨?_, by ring⟩
  linear_combination (-1 / 4 : Real) * hd0

theorem negative_crossover_eq_zero_iff_of_abs_eq_two
    {lambda : Real} (hlambda : |lambda| = 2) (y : Real) :
    y ^ 2 - lambda * y + 1 = 0 ↔ y = lambda / 2 := by
  have hd0 : lambda ^ 2 - 4 = 0 :=
    SilverCrossover.negative_discriminant_eq_zero_of_abs_eq_two hlambda
  constructor
  · intro h
    have hsq : (2 * y - lambda) ^ 2 = 0 := by linear_combination 4 * h + hd0
    have hlin : 2 * y - lambda = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linarith
  · rintro rfl
    exact (negative_crossover_boundary_root_and_not_simple hlambda).1

theorem negativeCrossoverRoots_eq_half_of_abs_eq_two
    {lambda : Real} (hlambda : |lambda| = 2) :
    negativeCrossoverRootPlus lambda = lambda / 2 ∧
      negativeCrossoverRootMinus lambda = lambda / 2 := by
  have hd0 : lambda ^ 2 - 4 = 0 :=
    SilverCrossover.negative_discriminant_eq_zero_of_abs_eq_two hlambda
  have hs : Real.sqrt (lambda ^ 2 - 4) = 0 := by
    rw [hd0, Real.sqrt_zero]
  constructor
  · unfold negativeCrossoverRootPlus
    rw [hs]
    ring
  · unfold negativeCrossoverRootMinus
    rw [hs]
    ring

theorem negativeCrossoverRootMinus_lt_plus_of_two_lt_abs
    {lambda : Real} (hlambda : 2 < |lambda|) :
    negativeCrossoverRootMinus lambda < negativeCrossoverRootPlus lambda := by
  have hs0 : 0 < Real.sqrt (lambda ^ 2 - 4) :=
    Real.sqrt_pos.mpr (SilverCrossover.positive_discriminant_of_two_lt_abs hlambda)
  unfold negativeCrossoverRootMinus negativeCrossoverRootPlus
  linarith

theorem negative_crossover_eq_zero_iff_of_two_lt_abs
    {lambda : Real} (hlambda : 2 < |lambda|) (y : Real) :
    y ^ 2 - lambda * y + 1 = 0 ↔
      y = negativeCrossoverRootMinus lambda ∨
      y = negativeCrossoverRootPlus lambda := by
  have hs2 : Real.sqrt (lambda ^ 2 - 4) ^ 2 = lambda ^ 2 - 4 :=
    Real.sq_sqrt (SilverCrossover.positive_discriminant_of_two_lt_abs hlambda).le
  have hfac : y ^ 2 - lambda * y + 1 =
      (y - negativeCrossoverRootMinus lambda) *
        (y - negativeCrossoverRootPlus lambda) := by
    unfold negativeCrossoverRootMinus negativeCrossoverRootPlus
    linear_combination (1 / 4 : Real) * hs2
  constructor
  · intro h
    rw [hfac, mul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl | rfl)
    · exact (negativeCrossoverRootMinus_spec_of_two_lt_abs hlambda).1
    · exact (negativeCrossoverRootPlus_spec_of_two_lt_abs hlambda).1

end SilverFiniteRow
