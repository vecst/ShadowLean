/-
Cubic-silver finite-row crossover, Phase B4B7: exact packet second-derivative and
center-discriminant bridge.

An exact differential bridge: `packetRatioSecondDerivative` is the actual second
derivative of the Wronskian quotient `W_N(x)/Q_N(x)^2`, written
`(W_N'(x) Q_N(x) - 2 W_N(x) Q_N'(x)) / Q_N(x)^3`; `finiteResidual = finiteMap - id`
has exact first/second derivatives on positive affine input. At `z = alpha` the
center evaluations preserve the exact factors `3*mu*alpha^2` and its square, and
the last two theorems identify the actual center Taylor discriminant with the
B4B6 abstract object (curvature variable `(3*alpha^2)^2 * P_N''(alpha^3)`) and with
the expanded packet-derivative data. This proves no spectral rate, no separation
inequality, no endpoint sign theorem for packet data, and no finite-row
double-root existence or convergence theorem.
-/
import RequestProject.SilverFiniteRowDoubleRootTaylorAlgebra

open scoped Real

namespace SilverFiniteRow

noncomputable def packetRatioSecondDerivative (N : Nat) (x : Real) : Real :=
  ((Polynomial.derivative (rowWronskian N)).eval x *
        ResidueSlices.revA 3 0 N x -
      2 * (rowWronskian N).eval x *
        (Polynomial.derivative (rowPoly N 0)).eval x) /
    (ResidueSlices.revA 3 0 N x) ^ 3

noncomputable def finiteResidual
    (N : Nat) (alpha mu z : Real) : Real :=
  finiteMap N alpha mu z - z

noncomputable def finiteResidualDerivative
    (N : Nat) (alpha mu z : Real) : Real :=
  SilverCrossover.affineSlope alpha mu *
      packetRatioDerivative N (affineInput alpha mu z) - 1

noncomputable def finiteResidualSecondDerivative
    (N : Nat) (alpha mu z : Real) : Real :=
  SilverCrossover.affineSlope alpha mu ^ 2 *
    packetRatioSecondDerivative N (affineInput alpha mu z)

noncomputable def centerDerivativeError
    (N : Nat) (alpha : Real) : Real :=
  3 * alpha ^ 2 * packetRatioDerivative N (alpha ^ 3) - 1

noncomputable def centerPacketCurvature
    (N : Nat) (alpha : Real) : Real :=
  (3 * alpha ^ 2) ^ 2 * packetRatioSecondDerivative N (alpha ^ 3)

noncomputable def centerEndpointTaylorDiscriminant
    (N : Nat) (alpha lambda t epsilon : Real) : Real :=
  finiteResidualDerivative N alpha (1 + lambda * t) alpha ^ 2 +
    2 * epsilon *
      finiteResidualSecondDerivative N alpha (1 + lambda * t) alpha

theorem hasDerivAt_packetRatioDerivative
    (N : Nat) {x : Real} (hx : 0 < x) :
    HasDerivAt (packetRatioDerivative N)
      (packetRatioSecondDerivative N x) x := by
  have hQpos : 0 < ResidueSlices.revA 3 0 N x := packetRatio_den_pos N hx
  have hQne : ResidueSlices.revA 3 0 N x ≠ 0 := ne_of_gt hQpos
  have hW : HasDerivAt (fun y : Real => (rowWronskian N).eval y)
      ((Polynomial.derivative (rowWronskian N)).eval x) x :=
    (rowWronskian N).hasDerivAt x
  have hQ : HasDerivAt (fun y : Real => ResidueSlices.revA 3 0 N y)
      ((Polynomial.derivative (rowPoly N 0)).eval x) x := by
    have := (rowPoly N 0).hasDerivAt x
    simpa [rowPoly_eval] using this
  have hQ2 := hQ.mul hQ
  have hQ2ne :
      ResidueSlices.revA 3 0 N x * ResidueSlices.revA 3 0 N x ≠ 0 :=
    mul_ne_zero hQne hQne
  have hdiv := hW.div hQ2 hQ2ne
  have heq :
      ((Polynomial.derivative (rowWronskian N)).eval x *
            (ResidueSlices.revA 3 0 N x * ResidueSlices.revA 3 0 N x) -
          (rowWronskian N).eval x *
            ((Polynomial.derivative (rowPoly N 0)).eval x *
                ResidueSlices.revA 3 0 N x +
              ResidueSlices.revA 3 0 N x *
                (Polynomial.derivative (rowPoly N 0)).eval x)) /
        (ResidueSlices.revA 3 0 N x * ResidueSlices.revA 3 0 N x) ^ 2
      = packetRatioSecondDerivative N x := by
    rw [packetRatioSecondDerivative]
    field_simp
    ring
  have hfun : packetRatioDerivative N
      = fun y : Real => (rowWronskian N).eval y /
          (ResidueSlices.revA 3 0 N y * ResidueSlices.revA 3 0 N y) := by
    funext y
    rw [packetRatioDerivative, pow_two]
  rw [hfun]
  exact heq ▸ hdiv

theorem hasDerivAt_finiteResidual
    (N : Nat) (alpha mu : Real) {z : Real}
    (hinput : 0 < affineInput alpha mu z) :
    HasDerivAt (finiteResidual N alpha mu)
      (finiteResidualDerivative N alpha mu z) z := by
  have haff : HasDerivAt (fun w : Real => affineInput alpha mu w)
      (SilverCrossover.affineSlope alpha mu) z := by
    have h : HasDerivAt (fun w : Real =>
        SilverCrossover.affineIntercept alpha mu +
          SilverCrossover.affineSlope alpha mu * w)
        (0 + SilverCrossover.affineSlope alpha mu * 1) z :=
      (hasDerivAt_const z (SilverCrossover.affineIntercept alpha mu)).add
        ((hasDerivAt_id z).const_mul (SilverCrossover.affineSlope alpha mu))
    simpa [affineInput] using h
  have hcomp := (hasDerivAt_packetRatio N hinput).comp z haff
  have hsub := hcomp.sub (hasDerivAt_id z)
  have hfun : finiteResidual N alpha mu
      = fun w : Real => packetRatio N (affineInput alpha mu w) - w := rfl
  rw [hfun, finiteResidualDerivative, mul_comm]
  exact hsub

theorem hasDerivAt_finiteResidualDerivative
    (N : Nat) (alpha mu : Real) {z : Real}
    (hinput : 0 < affineInput alpha mu z) :
    HasDerivAt (finiteResidualDerivative N alpha mu)
      (finiteResidualSecondDerivative N alpha mu z) z := by
  have haff : HasDerivAt (fun w : Real => affineInput alpha mu w)
      (SilverCrossover.affineSlope alpha mu) z := by
    have h : HasDerivAt (fun w : Real =>
        SilverCrossover.affineIntercept alpha mu +
          SilverCrossover.affineSlope alpha mu * w)
        (0 + SilverCrossover.affineSlope alpha mu * 1) z :=
      (hasDerivAt_const z (SilverCrossover.affineIntercept alpha mu)).add
        ((hasDerivAt_id z).const_mul (SilverCrossover.affineSlope alpha mu))
    simpa [affineInput] using h
  have hcomp := (hasDerivAt_packetRatioDerivative N hinput).comp z haff
  have hmul := hcomp.const_mul (SilverCrossover.affineSlope alpha mu)
  have hres := hmul.sub_const (1 : Real)
  have hfun : finiteResidualDerivative N alpha mu
      = fun w : Real => SilverCrossover.affineSlope alpha mu *
          packetRatioDerivative N (affineInput alpha mu w) - 1 := rfl
  have hval : SilverCrossover.affineSlope alpha mu ^ 2 *
        packetRatioSecondDerivative N (affineInput alpha mu z)
      = SilverCrossover.affineSlope alpha mu *
        (packetRatioSecondDerivative N (affineInput alpha mu z) *
          SilverCrossover.affineSlope alpha mu) := by
    ring
  rw [hfun, finiteResidualSecondDerivative, hval]
  exact hres

theorem finiteResidualDerivative_center
    (N : Nat) (alpha mu : Real) :
    finiteResidualDerivative N alpha mu alpha =
      3 * mu * alpha ^ 2 * packetRatioDerivative N (alpha ^ 3) - 1 := by
  rw [finiteResidualDerivative, affineInput_center, SilverCrossover.affineSlope]

theorem finiteResidualSecondDerivative_center
    (N : Nat) (alpha mu : Real) :
    finiteResidualSecondDerivative N alpha mu alpha =
      (3 * mu * alpha ^ 2) ^ 2 *
        packetRatioSecondDerivative N (alpha ^ 3) := by
  rw [finiteResidualSecondDerivative, affineInput_center, SilverCrossover.affineSlope]

theorem centerEndpointTaylorDiscriminant_eq_abstract
    (N : Nat) (alpha lambda t epsilon : Real) :
    centerEndpointTaylorDiscriminant N alpha lambda t epsilon =
      endpointTaylorDiscriminant lambda t
        (centerDerivativeError N alpha)
        (centerPacketCurvature N alpha) epsilon := by
  rw [centerEndpointTaylorDiscriminant, finiteResidualDerivative_center,
    finiteResidualSecondDerivative_center, endpointTaylorDiscriminant,
    endpointTaylorSlope, endpointTaylorCurvature, centerDerivativeError,
    centerPacketCurvature]
  ring

theorem centerEndpointTaylorDiscriminant_eq_packet_data
    (N : Nat) (alpha lambda t epsilon : Real) :
    centerEndpointTaylorDiscriminant N alpha lambda t epsilon =
      (3 * alpha ^ 2 * (1 + lambda * t) *
          packetRatioDerivative N (alpha ^ 3) - 1) ^ 2 +
        2 * epsilon *
          (3 * alpha ^ 2 * (1 + lambda * t)) ^ 2 *
            packetRatioSecondDerivative N (alpha ^ 3) := by
  rw [centerEndpointTaylorDiscriminant, finiteResidualDerivative_center,
    finiteResidualSecondDerivative_center]
  ring

end SilverFiniteRow
