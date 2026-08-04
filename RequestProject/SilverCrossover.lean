/-
Silver-ratio crossover algebra for the cubic residual `z^3 - (b + m z)` of the
metallic packet, and the normalized quadratic `y^2 - λ y - σ` obtained after
rescaling by `crossoverScale = √(α·|packetError|)`. Elementary real/complex
algebra only — no analysis beyond one polynomial derivative, no packet/Fourier
dependencies (imports Mathlib only).

Proof routes (every target is provable; close all, keep statements verbatim):
- cubicResidual_add_displacement / cubicResidual_neutral: unfold the defs, `ring`.
- cubicResidual_neutral_hasDerivAt: with μ = 1 the residual is
  `z^3 - 3α²·z + 2α³`, derivative `3z² - 3α²`, which vanishes at `z = α`;
  build the `HasDerivAt` for the polynomial and evaluate (double root at α).
- crossoverScale_sq: `Real.sq_sqrt` with `0 ≤ α·|packetError|` from `0 ≤ α`.
- quadraticCrossover_rescale_pos/neg: unfold, substitute `crossoverScale² = α·|e|`,
  split on the sign of `packetError` to rewrite `|e|` (= e when `0 < e`,
  = -e when `e < 0`), then `ring`/`field_simp` (`α ≠ 0`).
- normalizedRootPlus/Minus_isRoot: quadratic formula; `Complex.sq_sqrt` gives
  `Complex.sqrt d ^ 2 = d` unconditionally over ℂ, then `ring`.
- discriminant lemmas: `λ² - 4` sign from `|λ|` vs 2 (three cases) and
  `0 < λ² + 4` always; `nlinarith`/`sq_abs`/`abs_lt`/`lt_abs` as needed.
Certification: keep every target an active declaration; if any cannot close,
omit it and report which — do not weaken a statement to make it pass.
-/
import Mathlib

open scoped Real

namespace SilverCrossover

def affineSlope (alpha mu : Real) : Real :=
  3 * mu * alpha ^ 2

def affineIntercept (alpha mu : Real) : Real :=
  alpha ^ 3 - affineSlope alpha mu * alpha

def cubicResidual (alpha mu z : Real) : Real :=
  z ^ 3 - (affineIntercept alpha mu + affineSlope alpha mu * z)

def quadraticCrossover (alpha packetError muShift delta : Real) : Real :=
  delta ^ 2 - alpha * muShift * delta - alpha * packetError

noncomputable def crossoverScale (alpha packetError : Real) : Real :=
  Real.sqrt (alpha * |packetError|)

def normalizedPoly (lambda sigma y : Complex) : Complex :=
  y ^ 2 - lambda * y - sigma

noncomputable def normalizedRootPlus (lambda sigma : Complex) : Complex :=
  (lambda + Complex.sqrt (lambda ^ 2 + 4 * sigma)) / 2

noncomputable def normalizedRootMinus (lambda sigma : Complex) : Complex :=
  (lambda - Complex.sqrt (lambda ^ 2 + 4 * sigma)) / 2

theorem cubicResidual_add_displacement (alpha mu delta : Real) :
    cubicResidual alpha mu (alpha + delta) =
      delta ^ 3 + 3 * alpha * delta ^ 2 + 3 * alpha ^ 2 * (1 - mu) * delta := by
  unfold cubicResidual affineIntercept affineSlope
  ring

theorem cubicResidual_neutral (alpha delta : Real) :
    cubicResidual alpha 1 (alpha + delta) =
      delta ^ 2 * (delta + 3 * alpha) := by
  unfold cubicResidual affineIntercept affineSlope
  ring

theorem cubicResidual_neutral_hasDerivAt (alpha : Real) :
    HasDerivAt (fun z => cubicResidual alpha 1 z) 0 alpha := by
  have h : HasDerivAt (fun z : Real => z ^ 3 - (affineIntercept alpha 1 + affineSlope alpha 1 * z))
      ((3 : ℕ) * alpha ^ (3 - 1) - (0 + affineSlope alpha 1 * 1)) alpha :=
    (hasDerivAt_pow 3 alpha).sub
      ((hasDerivAt_const alpha _).add ((hasDerivAt_id alpha).const_mul _))
  have he : ((3 : ℕ) : ℝ) * alpha ^ (3 - 1) - (0 + affineSlope alpha 1 * 1) = 0 := by
    simp [affineSlope]
  rw [he] at h
  exact h

theorem crossoverScale_sq {alpha packetError : Real} (halpha : 0 <= alpha) :
    crossoverScale alpha packetError ^ 2 = alpha * |packetError| :=
  Real.sq_sqrt (mul_nonneg halpha (abs_nonneg _))

theorem quadraticCrossover_rescale_pos {alpha packetError lambda y : Real}
    (halpha : 0 < alpha) (herror : 0 < packetError) :
    quadraticCrossover alpha packetError
        (lambda * crossoverScale alpha packetError / alpha)
        (crossoverScale alpha packetError * y) =
      alpha * packetError * (y ^ 2 - lambda * y - 1) := by
  have hs : crossoverScale alpha packetError ^ 2 = alpha * packetError := by
    rw [crossoverScale_sq halpha.le, abs_of_pos herror]
  unfold quadraticCrossover
  field_simp
  linear_combination (y * (y - lambda)) * hs

theorem quadraticCrossover_rescale_neg {alpha packetError lambda y : Real}
    (halpha : 0 < alpha) (herror : packetError < 0) :
    quadraticCrossover alpha packetError
        (lambda * crossoverScale alpha packetError / alpha)
        (crossoverScale alpha packetError * y) =
      alpha * (-packetError) * (y ^ 2 - lambda * y + 1) := by
  have hs : crossoverScale alpha packetError ^ 2 = alpha * (-packetError) := by
    rw [crossoverScale_sq halpha.le, abs_of_neg herror]
  unfold quadraticCrossover
  field_simp
  linear_combination (y * (y - lambda)) * hs

/-- `Complex.sqrt` squares back to its argument (it is defined as the principal
`z ^ (2⁻¹ : ℂ)`, so this holds unconditionally). -/
theorem complex_sq_sqrt (z : Complex) : Complex.sqrt z ^ 2 = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have h1 := Complex.neg_pi_lt_log_im z
    have h2 := Complex.log_im_le_pi z
    have hpi := Real.pi_pos
    rw [Complex.sqrt, ← Complex.cpow_natCast (z ^ (2⁻¹ : Complex)) 2, ← Complex.cpow_mul] <;>
      simp <;> linarith

theorem normalizedRootPlus_isRoot (lambda sigma : Complex) :
    normalizedPoly lambda sigma (normalizedRootPlus lambda sigma) = 0 := by
  have h := complex_sq_sqrt (lambda ^ 2 + 4 * sigma)
  unfold normalizedPoly normalizedRootPlus
  field_simp
  linear_combination h

theorem normalizedRootMinus_isRoot (lambda sigma : Complex) :
    normalizedPoly lambda sigma (normalizedRootMinus lambda sigma) = 0 := by
  have h := complex_sq_sqrt (lambda ^ 2 + 4 * sigma)
  unfold normalizedPoly normalizedRootMinus
  field_simp
  linear_combination h

theorem negative_discriminant_of_abs_lt_two {lambda : Real} (hlambda : |lambda| < 2) :
    lambda ^ 2 - 4 < 0 := by
  nlinarith [sq_abs lambda, abs_nonneg lambda]

theorem negative_discriminant_eq_zero_of_abs_eq_two {lambda : Real} (hlambda : |lambda| = 2) :
    lambda ^ 2 - 4 = 0 := by
  nlinarith [sq_abs lambda]

theorem positive_discriminant_of_two_lt_abs {lambda : Real} (hlambda : 2 < |lambda|) :
    0 < lambda ^ 2 - 4 := by
  nlinarith [sq_abs lambda, abs_nonneg lambda]

theorem positive_error_discriminant (lambda : Real) :
    0 < lambda ^ 2 + 4 := by
  positivity

end SilverCrossover
