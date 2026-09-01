/-
Cubic-silver finite-row crossover, Phase B4B6: exact double-root Taylor-discriminant
algebra.

An exact algebraic scaffold for the double-root problem; it proves no new packet
derivative/second-derivative theorem and no finite-row root existence/convergence
theorem. `endpointTaylorSlope lambda t d = d + lambda*t*(1+d)` is the exact center
slope; `endpointTaylorCurvature` rescales an abstract center curvature by the same
affine factor `(1+lambda*t)^2`; `endpointTaylorDiscriminant` is the quadratic
Taylor discriminant for center residual `-epsilon`. At `lambda = +-2` the
difference isolates the exact driver `d*(1+d) + 2*epsilon*c` while the sum is the
symmetry defect; if `|D_2 + D_{-2}| < |D_2 - D_{-2}|` then `D_2` and `D_{-2}` have
opposite signs, and the final two theorems orient them using positivity of `t` and
the driver. The separation hypothesis is not claimed for the actual packet data
here, and `d` alone does not control the sign (the curvature term can dominate when
`d` is near zero).
-/
import RequestProject.SilverFiniteRowCrossoverRealClassification

open scoped Real

namespace SilverFiniteRow

def endpointTaylorSlope
    (lambda t derivativeError : Real) : Real :=
  derivativeError + lambda * t * (1 + derivativeError)

def endpointTaylorCurvature
    (lambda t curvature : Real) : Real :=
  (1 + lambda * t) ^ 2 * curvature

def endpointTaylorDiscriminant
    (lambda t derivativeError curvature epsilon : Real) : Real :=
  endpointTaylorSlope lambda t derivativeError ^ 2 +
    2 * epsilon * endpointTaylorCurvature lambda t curvature

theorem endpointTaylorDiscriminant_eq_packet_data
    (lambda t A p q epsilon : Real) :
    endpointTaylorDiscriminant lambda t (A * p - 1) (A ^ 2 * q) epsilon =
      (A * (1 + lambda * t) * p - 1) ^ 2 +
        2 * epsilon * (A * (1 + lambda * t)) ^ 2 * q := by
  simp only [endpointTaylorDiscriminant, endpointTaylorSlope,
    endpointTaylorCurvature]
  ring

theorem endpointTaylorDiscriminant_two_sub_neg_two
    (t derivativeError curvature epsilon : Real) :
    endpointTaylorDiscriminant 2 t derivativeError curvature epsilon -
        endpointTaylorDiscriminant (-2) t derivativeError curvature epsilon =
      8 * t *
        (derivativeError * (1 + derivativeError) +
          2 * epsilon * curvature) := by
  simp only [endpointTaylorDiscriminant, endpointTaylorSlope,
    endpointTaylorCurvature]
  ring

theorem endpointTaylorDiscriminant_two_add_neg_two
    (t derivativeError curvature epsilon : Real) :
    endpointTaylorDiscriminant 2 t derivativeError curvature epsilon +
        endpointTaylorDiscriminant (-2) t derivativeError curvature epsilon =
      2 * derivativeError ^ 2 +
        8 * t ^ 2 * (1 + derivativeError) ^ 2 +
        4 * epsilon * curvature * (1 + 4 * t ^ 2) := by
  simp only [endpointTaylorDiscriminant, endpointTaylorSlope,
    endpointTaylorCurvature]
  ring

theorem mul_neg_of_abs_add_lt_abs_sub
    {a b : Real} (hsep : |a + b| < |a - b|) :
    a * b < 0 := by
  have h2 : (a + b) ^ 2 < (a - b) ^ 2 := by
    have h1 : |a + b| ^ 2 < |a - b| ^ 2 := by
      nlinarith [abs_nonneg (a + b), abs_nonneg (a - b), hsep]
    rwa [sq_abs, sq_abs] at h1
  nlinarith [h2]

theorem endpointTaylorDiscriminants_mul_neg_of_separated
    {t derivativeError curvature epsilon : Real}
    (hsep :
      |endpointTaylorDiscriminant 2 t derivativeError curvature epsilon +
          endpointTaylorDiscriminant (-2) t derivativeError curvature epsilon| <
        |endpointTaylorDiscriminant 2 t derivativeError curvature epsilon -
          endpointTaylorDiscriminant (-2) t derivativeError curvature epsilon|) :
    endpointTaylorDiscriminant 2 t derivativeError curvature epsilon *
        endpointTaylorDiscriminant (-2) t derivativeError curvature epsilon < 0 := by
  exact mul_neg_of_abs_add_lt_abs_sub hsep

theorem endpointTaylorDiscriminant_signs_of_driver_pos
    {t derivativeError curvature epsilon : Real} (ht : 0 < t)
    (hdriver :
      0 < derivativeError * (1 + derivativeError) +
        2 * epsilon * curvature)
    (hsep :
      |endpointTaylorDiscriminant 2 t derivativeError curvature epsilon +
          endpointTaylorDiscriminant (-2) t derivativeError curvature epsilon| <
        |endpointTaylorDiscriminant 2 t derivativeError curvature epsilon -
          endpointTaylorDiscriminant (-2) t derivativeError curvature epsilon|) :
    0 < endpointTaylorDiscriminant 2 t derivativeError curvature epsilon ∧
      endpointTaylorDiscriminant (-2) t derivativeError curvature epsilon < 0 := by
  have hprod := endpointTaylorDiscriminants_mul_neg_of_separated hsep
  have hdiff := endpointTaylorDiscriminant_two_sub_neg_two t derivativeError curvature epsilon
  have hpos : 0 < 8 * t * (derivativeError * (1 + derivativeError) + 2 * epsilon * curvature) := by
    have : (0:Real) < 8 * t := by linarith
    exact mul_pos this hdriver
  constructor
  · nlinarith [hprod, hdiff, hpos]
  · nlinarith [hprod, hdiff, hpos]

theorem endpointTaylorDiscriminant_signs_of_driver_neg
    {t derivativeError curvature epsilon : Real} (ht : 0 < t)
    (hdriver :
      derivativeError * (1 + derivativeError) +
          2 * epsilon * curvature < 0)
    (hsep :
      |endpointTaylorDiscriminant 2 t derivativeError curvature epsilon +
          endpointTaylorDiscriminant (-2) t derivativeError curvature epsilon| <
        |endpointTaylorDiscriminant 2 t derivativeError curvature epsilon -
          endpointTaylorDiscriminant (-2) t derivativeError curvature epsilon|) :
    endpointTaylorDiscriminant 2 t derivativeError curvature epsilon < 0 ∧
      0 < endpointTaylorDiscriminant (-2) t derivativeError curvature epsilon := by
  have hprod := endpointTaylorDiscriminants_mul_neg_of_separated hsep
  have hdiff := endpointTaylorDiscriminant_two_sub_neg_two t derivativeError curvature epsilon
  have hneg : 8 * t * (derivativeError * (1 + derivativeError) + 2 * epsilon * curvature) < 0 := by
    have h8 : (0:Real) < 8 * t := by linarith
    exact mul_neg_of_pos_of_neg h8 hdriver
  constructor
  · nlinarith [hprod, hdiff, hneg]
  · nlinarith [hprod, hdiff, hneg]

end SilverFiniteRow
