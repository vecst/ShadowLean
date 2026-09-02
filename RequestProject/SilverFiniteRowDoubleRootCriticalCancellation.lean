/-
Cubic-silver finite-row crossover, Phase B4B8: critical curvature-cancellation and
quantitative separation interface.

The limiting cube-root quotient has center curvature -2/alpha after multiplication
by (3*alpha^2)^2, so the quantity that decays spectrally is
`centerCurvatureDefect = centerPacketCurvature + 2/alpha`. Exact differentiation of
`centerDerivativeError` gives the bridge
`centerCurvatureDefect = centerDerivativeErrorDerivative - (2/alpha)*centerDerivativeError`.
At the negative-error double-root scale `epsilon = alpha*t^2`, recentering the
actual curvature cancels the limiting curvature terms, yielding the exact critical
driver and symmetry defect; the two `centerEndpointTaylorDiscriminant` identities
instantiate the B4B6 endpoint difference/sum with the actual B4B7 packet data. The
last two theorems are a SUFFICIENT-BOUND interface only: a positive lower bound on
the absolute critical driver together with an upper bound on the absolute critical
symmetry defect, with `symmetryUpper < 8*t*driverLower`, force strict endpoint
separation and hence a negative product. No unconditional all-row separation or
derivative-noncancellation lower bound is claimed (real single-row cancellations
exist); this phase proves no spectral rate, no selected-error sign cofinality, and
no finite-row double-root existence or convergence theorem.
-/
import RequestProject.SilverFiniteRowDoubleRootSecondDerivativeBridge

open scoped Real

namespace SilverFiniteRow

/-- Derivative, with respect to the center parameter, of the center slope error. -/
noncomputable def centerDerivativeErrorDerivative
    (N : Nat) (alpha : Real) : Real :=
  6 * alpha * packetRatioDerivative N (alpha ^ 3) +
    9 * alpha ^ 4 * packetRatioSecondDerivative N (alpha ^ 3)

/-- The packet curvature after subtracting the limiting cube-root curvature. -/
noncomputable def centerCurvatureDefect
    (N : Nat) (alpha : Real) : Real :=
  centerPacketCurvature N alpha + 2 / alpha

/-- The endpoint-splitting driver after the critical curvature cancellation. -/
def criticalEndpointDriver
    (alpha t derivativeError curvatureDefect : Real) : Real :=
  derivativeError * (1 + derivativeError) - 4 * t ^ 2 +
    2 * alpha * t ^ 2 * curvatureDefect

/-- The endpoint-symmetry defect after the critical curvature cancellation. -/
def criticalEndpointSymmetryDefect
    (alpha t derivativeError curvatureDefect : Real) : Real :=
  2 * derivativeError ^ 2 + 16 * t ^ 2 * derivativeError +
    8 * t ^ 2 * derivativeError ^ 2 - 32 * t ^ 4 +
    4 * alpha * t ^ 2 * curvatureDefect * (1 + 4 * t ^ 2)

theorem hasDerivAt_centerDerivativeError
    (N : Nat) {alpha : Real} (halpha : 0 < alpha) :
    HasDerivAt (fun beta : Real => centerDerivativeError N beta)
      (centerDerivativeErrorDerivative N alpha) alpha := by
  have hcube : HasDerivAt (fun beta : Real => beta ^ 3) (3 * alpha ^ 2) alpha := by
    simpa using hasDerivAt_pow 3 alpha
  have hcubepos : (0 : Real) < alpha ^ 3 := by positivity
  have hcomp :=
    HasDerivAt.comp (h := fun beta : Real => beta ^ 3) (h₂ := packetRatioDerivative N)
      alpha (hasDerivAt_packetRatioDerivative N hcubepos) hcube
  have hP' : HasDerivAt (fun beta : Real => packetRatioDerivative N (beta ^ 3))
      (packetRatioSecondDerivative N (alpha ^ 3) * (3 * alpha ^ 2)) alpha := hcomp
  have hsq : HasDerivAt (fun beta : Real => 3 * beta ^ 2) (3 * (2 * alpha)) alpha := by
    have : HasDerivAt (fun beta : Real => beta ^ 2) (2 * alpha) alpha := by
      simpa using hasDerivAt_pow 2 alpha
    simpa using this.const_mul (3 : Real)
  have hmul := (hsq.mul hP').sub_const (1 : Real)
  have hval :
      3 * (2 * alpha) * packetRatioDerivative N (alpha ^ 3) +
          3 * alpha ^ 2 * (packetRatioSecondDerivative N (alpha ^ 3) * (3 * alpha ^ 2)) =
        centerDerivativeErrorDerivative N alpha := by
    unfold centerDerivativeErrorDerivative
    ring
  have hfun : (fun beta : Real => centerDerivativeError N beta) =
      fun beta : Real => 3 * beta ^ 2 * packetRatioDerivative N (beta ^ 3) - 1 := rfl
  rw [hfun, ← hval]
  exact hmul

theorem centerCurvatureDefect_eq_derivative_bridge
    (N : Nat) {alpha : Real} (halpha : 0 < alpha) :
    centerCurvatureDefect N alpha =
      centerDerivativeErrorDerivative N alpha -
        (2 / alpha) * centerDerivativeError N alpha := by
  unfold centerCurvatureDefect centerPacketCurvature centerDerivativeErrorDerivative
    centerDerivativeError
  field_simp [halpha.ne']
  ring

theorem endpointDriver_eq_critical
    {alpha t derivativeError curvatureDefect : Real} (halpha : alpha ≠ 0) :
    derivativeError * (1 + derivativeError) +
        2 * (alpha * t ^ 2) * (curvatureDefect - 2 / alpha) =
      criticalEndpointDriver alpha t derivativeError curvatureDefect := by
  unfold criticalEndpointDriver
  field_simp [halpha]
  ring

theorem endpointSymmetryDefect_eq_critical
    {alpha t derivativeError curvatureDefect : Real} (halpha : alpha ≠ 0) :
    2 * derivativeError ^ 2 +
        8 * t ^ 2 * (1 + derivativeError) ^ 2 +
        4 * (alpha * t ^ 2) * (curvatureDefect - 2 / alpha) *
          (1 + 4 * t ^ 2) =
      criticalEndpointSymmetryDefect alpha t derivativeError curvatureDefect := by
  unfold criticalEndpointSymmetryDefect
  field_simp [halpha]
  ring

theorem centerEndpointTaylorDiscriminant_two_sub_neg_two_critical
    (N : Nat) {alpha : Real} (halpha : 0 < alpha) (t : Real) :
    centerEndpointTaylorDiscriminant N alpha 2 t (alpha * t ^ 2) -
        centerEndpointTaylorDiscriminant N alpha (-2) t (alpha * t ^ 2) =
      8 * t * criticalEndpointDriver alpha t
        (centerDerivativeError N alpha) (centerCurvatureDefect N alpha) := by
  rw [centerEndpointTaylorDiscriminant_eq_abstract,
    centerEndpointTaylorDiscriminant_eq_abstract,
    endpointTaylorDiscriminant_two_sub_neg_two, ← endpointDriver_eq_critical
      (t := t) (derivativeError := centerDerivativeError N alpha)
      (curvatureDefect := centerCurvatureDefect N alpha) halpha.ne']
  unfold centerCurvatureDefect
  ring

theorem centerEndpointTaylorDiscriminant_two_add_neg_two_critical
    (N : Nat) {alpha : Real} (halpha : 0 < alpha) (t : Real) :
    centerEndpointTaylorDiscriminant N alpha 2 t (alpha * t ^ 2) +
        centerEndpointTaylorDiscriminant N alpha (-2) t (alpha * t ^ 2) =
      criticalEndpointSymmetryDefect alpha t
        (centerDerivativeError N alpha) (centerCurvatureDefect N alpha) := by
  rw [centerEndpointTaylorDiscriminant_eq_abstract,
    centerEndpointTaylorDiscriminant_eq_abstract,
    endpointTaylorDiscriminant_two_add_neg_two, ← endpointSymmetryDefect_eq_critical
      (t := t) (derivativeError := centerDerivativeError N alpha)
      (curvatureDefect := centerCurvatureDefect N alpha) halpha.ne']
  unfold centerCurvatureDefect
  ring

theorem centerEndpointTaylorDiscriminants_separated_of_critical_bounds
    (N : Nat) {alpha t driverLower symmetryUpper : Real}
    (halpha : 0 < alpha) (ht : 0 < t)
    (hdriverLower : 0 <= driverLower)
    (hdriver : driverLower <=
      |criticalEndpointDriver alpha t
        (centerDerivativeError N alpha) (centerCurvatureDefect N alpha)|)
    (hsymmetry :
      |criticalEndpointSymmetryDefect alpha t
        (centerDerivativeError N alpha) (centerCurvatureDefect N alpha)| <=
          symmetryUpper)
    (hdominates : symmetryUpper < 8 * t * driverLower) :
    |centerEndpointTaylorDiscriminant N alpha 2 t (alpha * t ^ 2) +
        centerEndpointTaylorDiscriminant N alpha (-2) t (alpha * t ^ 2)| <
      |centerEndpointTaylorDiscriminant N alpha 2 t (alpha * t ^ 2) -
        centerEndpointTaylorDiscriminant N alpha (-2) t (alpha * t ^ 2)| := by
  have h8t : (0 : Real) < 8 * t := by linarith
  have hdiff :
      |centerEndpointTaylorDiscriminant N alpha 2 t (alpha * t ^ 2) -
          centerEndpointTaylorDiscriminant N alpha (-2) t (alpha * t ^ 2)| =
        8 * t * |criticalEndpointDriver alpha t
          (centerDerivativeError N alpha) (centerCurvatureDefect N alpha)| := by
    rw [centerEndpointTaylorDiscriminant_two_sub_neg_two_critical N halpha t, abs_mul,
      abs_of_pos h8t]
  have hsum :
      |centerEndpointTaylorDiscriminant N alpha 2 t (alpha * t ^ 2) +
          centerEndpointTaylorDiscriminant N alpha (-2) t (alpha * t ^ 2)| =
        |criticalEndpointSymmetryDefect alpha t
          (centerDerivativeError N alpha) (centerCurvatureDefect N alpha)| := by
    rw [centerEndpointTaylorDiscriminant_two_add_neg_two_critical N halpha t]
  have hlower : 8 * t * driverLower <=
      8 * t * |criticalEndpointDriver alpha t
        (centerDerivativeError N alpha) (centerCurvatureDefect N alpha)| :=
    mul_le_mul_of_nonneg_left hdriver (le_of_lt h8t)
  have hnonneg : (0 : Real) <= 8 * t * driverLower := mul_nonneg h8t.le hdriverLower
  rw [hsum, hdiff]
  linarith [hsymmetry, hdominates, hlower, hnonneg]

theorem centerEndpointTaylorDiscriminants_mul_neg_of_critical_bounds
    (N : Nat) {alpha t driverLower symmetryUpper : Real}
    (halpha : 0 < alpha) (ht : 0 < t)
    (hdriverLower : 0 <= driverLower)
    (hdriver : driverLower <=
      |criticalEndpointDriver alpha t
        (centerDerivativeError N alpha) (centerCurvatureDefect N alpha)|)
    (hsymmetry :
      |criticalEndpointSymmetryDefect alpha t
        (centerDerivativeError N alpha) (centerCurvatureDefect N alpha)| <=
          symmetryUpper)
    (hdominates : symmetryUpper < 8 * t * driverLower) :
    centerEndpointTaylorDiscriminant N alpha 2 t (alpha * t ^ 2) *
        centerEndpointTaylorDiscriminant N alpha (-2) t (alpha * t ^ 2) < 0 := by
  exact mul_neg_of_abs_add_lt_abs_sub
    (centerEndpointTaylorDiscriminants_separated_of_critical_bounds N halpha ht
      hdriverLower hdriver hsymmetry hdominates)

end SilverFiniteRow
