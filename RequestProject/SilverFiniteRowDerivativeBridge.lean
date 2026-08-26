/-
Cubic-silver finite-row crossover: exact derivative bridge.

This module exposes the exact derivative objects needed for the local
spectral-Lipschitz step: the derivative of the packet quotient (via the row
Wronskian), the derivative of the positive-axis real cube-root branch, their
difference (the packet-error derivative), and the identification of packet
deviation / deviation variation with packet-error increments, plus a chain-rule
derivative and a derivative-level mean-value interface.

Algebraic/differential only: NO asymptotic derivative rate, relative error
estimate, fixed-point displacement, or noncancellation result is claimed here.
The later analytic estimates (~ N*rho^N, N^2*rho^N*h^2) are deliberately NOT
targets; this module only exposes the exact derivative objects.
-/
import RequestProject.SilverFiniteRowRemainder
import RequestProject.SilverFiniteRowElasticity

open scoped Topology

namespace SilverFiniteRow

noncomputable def packetRatioDerivative (N : Nat) (x : Real) : Real :=
  (rowWronskian N).eval x /
    (ResidueSlices.revA 3 0 N x) ^ 2

noncomputable def cubeRootDerivative (x : Real) : Real :=
  ((3 : Real)⁻¹) *
    x ^ (((3 : Real)⁻¹) - 1)

noncomputable def packetErrorFunction (N : Nat) (x : Real) : Real :=
  packetRatio N x - x ^ ((3 : Real)⁻¹)

noncomputable def packetErrorDerivative (N : Nat) (x : Real) : Real :=
  packetRatioDerivative N x - cubeRootDerivative x

theorem hasDerivAt_packetRatio
    (N : Nat) {x : Real} (hx : 0 < x) :
    HasDerivAt (packetRatio N) (packetRatioDerivative N x) x := by
  have hQpos : 0 < ResidueSlices.revA 3 0 N x := packetRatio_den_pos N hx
  have hP : HasDerivAt (fun y : Real => ResidueSlices.revA 3 1 N y)
      ((Polynomial.derivative (rowPoly N 1)).eval x) x := by
    have := (rowPoly N 1).hasDerivAt x
    simpa [rowPoly_eval] using this
  have hQ : HasDerivAt (fun y : Real => ResidueSlices.revA 3 0 N y)
      ((Polynomial.derivative (rowPoly N 0)).eval x) x := by
    have := (rowPoly N 0).hasDerivAt x
    simpa [rowPoly_eval] using this
  have hdiv := hP.div hQ hQpos.ne'
  have heq : ((Polynomial.derivative (rowPoly N 1)).eval x * ResidueSlices.revA 3 0 N x
        - ResidueSlices.revA 3 1 N x * (Polynomial.derivative (rowPoly N 0)).eval x)
      / (ResidueSlices.revA 3 0 N x) ^ 2
      = packetRatioDerivative N x := by
    rw [packetRatioDerivative, rowWronskian]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, rowPoly_eval]
  exact heq ▸ hdiv

theorem hasDerivAt_cubeRoot
    {x : Real} (hx : 0 < x) :
    HasDerivAt
      (fun y : Real => y ^ ((3 : Real)⁻¹))
      (cubeRootDerivative x) x := by
  rw [cubeRootDerivative]
  exact Real.hasDerivAt_rpow_const (Or.inl hx.ne')

theorem hasDerivAt_packetErrorFunction
    (N : Nat) {x : Real} (hx : 0 < x) :
    HasDerivAt (packetErrorFunction N)
      (packetErrorDerivative N x) x := by
  exact (hasDerivAt_packetRatio N hx).sub (hasDerivAt_cubeRoot hx)

theorem packetDeviation_eq_packetErrorFunction
    (N : Nat) (alpha mu z : Real) :
    packetDeviation N alpha mu z =
      packetErrorFunction N (affineInput alpha mu z) := by
  rfl

theorem deviationVariation_eq_packetErrorFunction_sub
    (N : Nat) {alpha : Real} (halpha : 0 < alpha)
    (mu delta : Real) :
    deviationVariation N alpha mu delta =
      packetErrorFunction N (affineInput alpha mu (alpha + delta)) -
        packetErrorFunction N (alpha ^ 3) := by
  have hval : (alpha ^ 3 : Real) ^ ((3 : Real)⁻¹) = alpha := by
    rw [show (alpha ^ 3 : Real) = alpha ^ ((3 : ℕ) : Real) by rw [Real.rpow_natCast]]
    rw [← Real.rpow_mul halpha.le]
    norm_num
  have hcenter : packetErrorFunction N (alpha ^ 3) = centerError N alpha := by
    rw [packetErrorFunction, centerError, hval]
  rw [deviationVariation, packetDeviation_eq_packetErrorFunction, hcenter]

theorem hasDerivAt_packetDeviation
    (N : Nat) (alpha mu : Real) {z : Real}
    (hinput : 0 < affineInput alpha mu z) :
    HasDerivAt
      (fun w : Real => packetDeviation N alpha mu w)
      (SilverCrossover.affineSlope alpha mu *
        packetErrorDerivative N (affineInput alpha mu z)) z := by
  have haff : HasDerivAt (fun w : Real => affineInput alpha mu w)
      (SilverCrossover.affineSlope alpha mu) z := by
    have h : HasDerivAt (fun w : Real =>
        SilverCrossover.affineIntercept alpha mu +
          SilverCrossover.affineSlope alpha mu * w)
        (0 + SilverCrossover.affineSlope alpha mu * 1) z :=
      (hasDerivAt_const z (SilverCrossover.affineIntercept alpha mu)).add
        ((hasDerivAt_id z).const_mul (SilverCrossover.affineSlope alpha mu))
    simpa [affineInput] using h
  have hcomp := (hasDerivAt_packetErrorFunction N hinput).comp z haff
  have heq : (fun w : Real => packetDeviation N alpha mu w)
      = (fun w : Real => packetErrorFunction N (affineInput alpha mu w)) := by
    funext w
    exact packetDeviation_eq_packetErrorFunction N alpha mu w
  rw [heq, mul_comm]
  exact hcomp

theorem deviationVariation_eq_deriv_mul
    (N : Nat) {alpha mu delta : Real}
    (halpha : 0 < alpha)
    (hsegment : ∀ x : Real,
      x ∈ Set.uIcc (alpha ^ 3) (affineInput alpha mu (alpha + delta)) →
        0 < x) :
    ∃ xi : Real,
      xi ∈ Set.uIcc (alpha ^ 3)
          (affineInput alpha mu (alpha + delta)) ∧
      deviationVariation N alpha mu delta =
        packetErrorDerivative N xi *
          (affineInput alpha mu (alpha + delta) - alpha ^ 3) := by
  set a : Real := alpha ^ 3
  set b : Real := affineInput alpha mu (alpha + delta)
  have hmain : ∀ x : Real, x ∈ Set.uIcc a b →
      HasDerivAt (packetErrorFunction N) (packetErrorDerivative N x) x :=
    fun x hx => hasDerivAt_packetErrorFunction N (hsegment x hx)
  have key : ∃ xi : Real, xi ∈ Set.uIcc a b ∧
      packetErrorFunction N b - packetErrorFunction N a
        = packetErrorDerivative N xi * (b - a) := by
    rcases lt_trichotomy a b with hab | hab | hab
    · have hsub : Set.Icc a b = Set.uIcc a b := (Set.uIcc_of_le hab.le).symm
      have hcont : ContinuousOn (packetErrorFunction N) (Set.Icc a b) := by
        intro x hx
        exact (hmain x (hsub ▸ hx)).continuousAt.continuousWithinAt
      have hderiv : ∀ x ∈ Set.Ioo a b,
          HasDerivAt (packetErrorFunction N) (packetErrorDerivative N x) x := by
        intro x hx
        exact hmain x (hsub ▸ (Set.Ioo_subset_Icc_self hx))
      obtain ⟨c, hc, hceq⟩ :=
        exists_hasDerivAt_eq_slope (packetErrorFunction N) (packetErrorDerivative N)
          hab hcont hderiv
      refine ⟨c, hsub ▸ (Set.Ioo_subset_Icc_self hc), ?_⟩
      rw [hceq]
      field_simp
    · exact ⟨a, Set.left_mem_uIcc, by rw [← hab]; ring⟩
    · have hsub : Set.Icc b a = Set.uIcc a b := by
        rw [Set.uIcc_of_ge hab.le]
      have hcont : ContinuousOn (packetErrorFunction N) (Set.Icc b a) := by
        intro x hx
        exact (hmain x (hsub ▸ hx)).continuousAt.continuousWithinAt
      have hderiv : ∀ x ∈ Set.Ioo b a,
          HasDerivAt (packetErrorFunction N) (packetErrorDerivative N x) x := by
        intro x hx
        exact hmain x (hsub ▸ (Set.Ioo_subset_Icc_self hx))
      obtain ⟨c, hc, hceq⟩ :=
        exists_hasDerivAt_eq_slope (packetErrorFunction N) (packetErrorDerivative N)
          hab hcont hderiv
      refine ⟨c, hsub ▸ (Set.Ioo_subset_Icc_self hc), ?_⟩
      rw [hceq]
      have hne : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
      field_simp
      ring
  obtain ⟨xi, hxi, hval⟩ := key
  exact ⟨xi, hxi, by
    rw [deviationVariation_eq_packetErrorFunction_sub N halpha mu delta]
    exact hval⟩

end SilverFiniteRow
