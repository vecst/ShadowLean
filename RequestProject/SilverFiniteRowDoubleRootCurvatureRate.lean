/-
Cubic-silver finite-row crossover, Phase B4B10: spectral upper bound for the
recentered center curvature defect.

Differentiating the center error `E = alpha*U/D` twice and applying the exact
`+2/alpha` recentering (`centerCurvatureDefect = E'' - (2/alpha)*E'`) cancels the
raw `2*U'/D` and `2*U*D'/D^2` terms, leaving the exact four-term identity
`centerCurvatureDefect = alpha*U''/D - 2*U/(alpha*D) - alpha*(2*U'*D' + U*D'')/D^2
+ 2*alpha*U*(D')^2/D^3`. With the second-channel derivatives
`q'' = -2*(1-omega)/(beta+1)^3`, `r'' = 2/(beta+1)^3` and the fixed-parameter
bounds `‖q''‖ ≤ 2*‖1-omega‖`, `|r''| ≤ 2`, each term is `O((N+1)^2*rho^N)`
(0<rho<1, endpoint channel subordinate), giving an eventual spectral upper bound
`|centerCurvatureDefect N| ≤ C*(N+1)^2*rho^N` and hence convergence to zero, on all
sufficiently large rows and along the B4B9 derivative selector. The polynomial
factor `(N+1)^2` is essential: the normalized value oscillates rather than tending
to zero, so no `O(rho^N)` bound holds. This proves no curvature lower bound, no
joint negative-error/derivative row, no adaptiveRow agreement, and no endpoint
separation, root existence, or convergence at `|lambda| = 2`.
-/
import RequestProject.SilverFiniteRowDoubleRootDerivativeGuard

open scoped Real Topology BigOperators
open Filter

namespace SilverFiniteRow

noncomputable def centerChannelSecondDeriv (beta : Real) : Complex :=
  -2 * (1 - centerOmega) / ((beta : Complex) + 1) ^ 3

noncomputable def centerEndpointRateSecondDeriv (beta : Real) : Real :=
  2 * (((beta + 1) ^ 3)⁻¹)

noncomputable def centerChannelPowerSecondDeriv
    (N : Nat) (beta : Real) : Complex :=
  (N : Complex) * ((N - 1 : Nat) : Complex) *
      centerChannel beta ^ (N - 2) * centerChannelDeriv beta ^ 2 +
    (N : Complex) * centerChannel beta ^ (N - 1) *
      centerChannelSecondDeriv beta

noncomputable def centerEndpointRatePowerSecondDeriv
    (N : Nat) (beta : Real) : Real :=
  (N : Real) * ((N - 1 : Nat) : Real) *
      centerEndpointRate beta ^ (N - 2) * centerEndpointRateDeriv beta ^ 2 +
    (N : Real) * centerEndpointRate beta ^ (N - 1) *
      centerEndpointRateSecondDeriv beta

noncomputable def centerEndpointTermSecondDeriv
    (N : Nat) (beta : Real) : Real :=
  3 * ResidueSlices.epsIdx 3 N *
    centerEndpointRatePowerSecondDeriv N beta

noncomputable def centerNumeratorTermSecondDeriv
    (N : Nat) (beta : Real) : Real :=
  2 * Complex.re
      ((centerOmega ^ 2 - 1) * centerChannelPowerSecondDeriv N beta) +
    centerEndpointTermSecondDeriv N beta

noncomputable def centerDenominatorWaveSecondDeriv
    (N : Nat) (beta : Real) : Real :=
  2 * Complex.re (centerChannelPowerSecondDeriv N beta) -
    centerEndpointTermSecondDeriv N beta

theorem hasDerivAt_centerChannelDeriv
    {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt centerChannelDeriv (centerChannelSecondDeriv beta) beta := by
  have hb : ((beta : Complex) + 1) ≠ 0 := centerOfReal_add_one_ne_zero hbeta
  have h1 : HasDerivAt (fun b : Real => ((b : Complex) + 1)) 1 beta := by
    simpa using ((hasDerivAt_id beta).ofReal_comp).add_const (1 : Complex)
  have h2 : HasDerivAt (fun b : Real => ((b : Complex) + 1) * ((b : Complex) + 1))
      (1 * ((beta : Complex) + 1) + ((beta : Complex) + 1) * 1) beta := h1.mul h1
  have h3 := (hasDerivAt_const beta (1 - centerOmega)).div h2 (mul_ne_zero hb hb)
  have hfun : centerChannelDeriv =
      fun b : Real => (1 - centerOmega) / (((b : Complex) + 1) * ((b : Complex) + 1)) := by
    funext b
    unfold centerChannelDeriv
    ring
  rw [hfun]
  refine h3.congr_deriv ?_
  unfold centerChannelSecondDeriv
  field_simp
  ring

theorem hasDerivAt_centerEndpointRateDeriv
    {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt centerEndpointRateDeriv
      (centerEndpointRateSecondDeriv beta) beta := by
  have hb : (0 : Real) < beta + 1 := by linarith
  have h1 : HasDerivAt (fun b : Real => b + 1) 1 beta := (hasDerivAt_id beta).add_const 1
  have h2 : HasDerivAt (fun b : Real => (b + 1) * (b + 1))
      (1 * (beta + 1) + (beta + 1) * 1) beta := h1.mul h1
  have hne : (beta + 1) * (beta + 1) ≠ 0 := by positivity
  have h3 := (h2.inv hne).neg
  have hfun : centerEndpointRateDeriv = fun b : Real => -(((b + 1) * (b + 1))⁻¹) := by
    funext b
    unfold centerEndpointRateDeriv
    ring_nf
  rw [hfun]
  refine h3.congr_deriv ?_
  unfold centerEndpointRateSecondDeriv
  field_simp
  ring

theorem hasDerivAt_centerChannelPowerDeriv
    (N : Nat) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt
      (fun b : Real =>
        (N : Complex) * centerChannel b ^ (N - 1) * centerChannelDeriv b)
      (centerChannelPowerSecondDeriv N beta) beta := by
  have hexp : N - 1 - 1 = N - 2 := by omega
  have hp := hasDerivAt_centerChannel_pow (N - 1) hbeta
  rw [hexp] at hp
  have hd := hasDerivAt_centerChannelDeriv hbeta
  have h := (hp.mul hd).const_mul ((N : Complex))
  have hfun :
      (fun b : Real =>
        (N : Complex) * centerChannel b ^ (N - 1) * centerChannelDeriv b) =
      fun b : Real =>
        (N : Complex) * (centerChannel b ^ (N - 1) * centerChannelDeriv b) := by
    funext b; ring
  rw [hfun]
  refine h.congr_deriv ?_
  unfold centerChannelPowerSecondDeriv
  ring

theorem hasDerivAt_centerEndpointRatePowerDeriv
    (N : Nat) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt
      (fun b : Real =>
        (N : Real) * centerEndpointRate b ^ (N - 1) *
          centerEndpointRateDeriv b)
      (centerEndpointRatePowerSecondDeriv N beta) beta := by
  have hexp : N - 1 - 1 = N - 2 := by omega
  have hp := hasDerivAt_centerEndpointRate_pow (N - 1) hbeta
  rw [hexp] at hp
  have hd := hasDerivAt_centerEndpointRateDeriv hbeta
  have h := (hp.mul hd).const_mul ((N : Real))
  have hfun :
      (fun b : Real =>
        (N : Real) * centerEndpointRate b ^ (N - 1) * centerEndpointRateDeriv b) =
      fun b : Real =>
        (N : Real) * (centerEndpointRate b ^ (N - 1) * centerEndpointRateDeriv b) := by
    funext b; ring
  rw [hfun]
  refine h.congr_deriv ?_
  unfold centerEndpointRatePowerSecondDeriv
  ring

theorem hasDerivAt_centerEndpointTermDeriv
    (N : Nat) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt (fun b : Real => centerEndpointTermDeriv N b)
      (centerEndpointTermSecondDeriv N beta) beta := by
  have h := (hasDerivAt_centerEndpointRatePowerDeriv N hbeta).const_mul
    (3 * ResidueSlices.epsIdx 3 N)
  unfold centerEndpointTermDeriv
  refine h.congr_deriv ?_
  unfold centerEndpointTermSecondDeriv
  ring

theorem hasDerivAt_centerNumeratorTermDeriv
    (N : Nat) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt (fun b : Real => centerNumeratorTermDeriv N b)
      (centerNumeratorTermSecondDeriv N beta) beta := by
  have hP := hasDerivAt_centerChannelPowerDeriv N hbeta
  have hA := hP.const_mul (centerOmega ^ 2 - 1)
  have hRe := (hasDerivAt_complexRe hA).const_mul (2 : Real)
  have h := hRe.add (hasDerivAt_centerEndpointTermDeriv N hbeta)
  unfold centerNumeratorTermDeriv
  refine h.congr_deriv ?_
  unfold centerNumeratorTermSecondDeriv
  ring

theorem hasDerivAt_centerDenominatorWaveDeriv
    (N : Nat) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt (fun b : Real => centerDenominatorWaveDeriv N b)
      (centerDenominatorWaveSecondDeriv N beta) beta := by
  have hP := hasDerivAt_centerChannelPowerDeriv N hbeta
  have hRe := (hasDerivAt_complexRe hP).const_mul (2 : Real)
  have h := hRe.sub (hasDerivAt_centerEndpointTermDeriv N hbeta)
  unfold centerDenominatorWaveDeriv
  refine h.congr_deriv ?_
  unfold centerDenominatorWaveSecondDeriv
  ring

/-- Second-order quotient derivative of the exact center error parameter derivative. -/
private theorem hasDerivAt_centerErrorParameterDeriv
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    HasDerivAt (fun b : Real => centerErrorParameterDeriv N b)
      ((((2 * centerNumeratorTermDeriv N alpha +
              alpha * centerNumeratorTermSecondDeriv N alpha) *
            centerDenominatorWave N alpha -
          alpha * centerNumeratorTerm N alpha *
            centerDenominatorWaveSecondDeriv N alpha) *
          centerDenominatorWave N alpha -
        2 * centerDenominatorWaveDeriv N alpha *
          ((centerNumeratorTerm N alpha + alpha * centerNumeratorTermDeriv N alpha) *
              centerDenominatorWave N alpha -
            alpha * centerNumeratorTerm N alpha * centerDenominatorWaveDeriv N alpha)) /
        centerDenominatorWave N alpha ^ 3) alpha := by
  have hDpos : 0 < centerDenominatorWave N alpha := centerDenominatorWave_pos hN halpha
  have hDne : centerDenominatorWave N alpha ≠ 0 := ne_of_gt hDpos
  have hU := hasDerivAt_centerNumeratorTerm N halpha
  have hU' := hasDerivAt_centerNumeratorTermDeriv N halpha
  have hD := hasDerivAt_centerDenominatorWave N halpha
  have hD' := hasDerivAt_centerDenominatorWaveDeriv N halpha
  have hid := hasDerivAt_id alpha
  have hnum := ((hU.add (hid.mul hU')).mul hD).sub ((hid.mul hU).mul hD')
  have hden := hD.mul hD
  have hquot := hnum.div hden (mul_ne_zero hDne hDne)
  have hfun : (fun b : Real => centerErrorParameterDeriv N b) =
      fun b : Real =>
        ((centerNumeratorTerm N b + b * centerNumeratorTermDeriv N b) *
            centerDenominatorWave N b -
          b * centerNumeratorTerm N b * centerDenominatorWaveDeriv N b) /
          (centerDenominatorWave N b * centerDenominatorWave N b) := by
    funext b
    unfold centerErrorParameterDeriv
    ring
  rw [hfun]
  refine hquot.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
  field_simp
  ring

theorem centerCurvatureDefect_decomposition
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    centerCurvatureDefect N alpha =
      alpha * centerNumeratorTermSecondDeriv N alpha /
          centerDenominatorWave N alpha -
        2 * centerNumeratorTerm N alpha /
          (alpha * centerDenominatorWave N alpha) -
        alpha *
            (2 * centerNumeratorTermDeriv N alpha *
                centerDenominatorWaveDeriv N alpha +
              centerNumeratorTerm N alpha *
                centerDenominatorWaveSecondDeriv N alpha) /
          centerDenominatorWave N alpha ^ 2 +
        2 * alpha * centerNumeratorTerm N alpha *
            centerDenominatorWaveDeriv N alpha ^ 2 /
          centerDenominatorWave N alpha ^ 3 := by
  have hDpos : 0 < centerDenominatorWave N alpha := centerDenominatorWave_pos hN halpha
  have hDne : centerDenominatorWave N alpha ≠ 0 := ne_of_gt hDpos
  have heq : (fun b : Real => centerDerivativeError N b) =ᶠ[nhds alpha]
      fun b : Real => centerErrorParameterDeriv N b := by
    filter_upwards [eventually_gt_nhds halpha] with b hb
    exact centerDerivativeError_eq_centerErrorParameterDeriv hN hb
  have h1 := (hasDerivAt_centerErrorParameterDeriv hN halpha).congr_of_eventuallyEq heq
  have h3 := (hasDerivAt_centerDerivativeError N halpha).unique h1
  rw [centerCurvatureDefect_eq_derivative_bridge N halpha, h3,
    centerDerivativeError_eq_centerErrorParameterDeriv hN halpha]
  unfold centerErrorParameterDeriv
  field_simp
  ring

/-! ### Second-channel fixed-parameter bounds -/

/-- Fixed-parameter bound on the second derivative of the center channel. -/
private theorem norm_centerChannelSecondDeriv_le {beta : Real} (hbeta : 1 < beta) :
    ‖centerChannelSecondDeriv beta‖ ≤ 2 * ‖1 - centerOmega‖ := by
  have hb0 : (0 : Real) < beta := lt_trans one_pos hbeta
  have hnorm : ‖((beta : Complex) + 1) ^ 3‖ = (beta + 1) ^ 3 := by
    rw [norm_pow]
    congr 1
    rw [show ((beta : Complex) + 1) = ((beta + 1 : Real) : Complex) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hge : (1 : Real) ≤ (beta + 1) ^ 3 := one_le_pow₀ (by linarith)
  unfold centerChannelSecondDeriv
  rw [norm_div, hnorm, div_le_iff₀ (by linarith)]
  have hnum : ‖(-2 : Complex) * (1 - centerOmega)‖ = 2 * ‖1 - centerOmega‖ := by
    rw [norm_mul]
    norm_num
  rw [hnum]
  nlinarith [norm_nonneg (1 - centerOmega)]

/-- Fixed-parameter bound on the second derivative of the endpoint rate. -/
private theorem abs_centerEndpointRateSecondDeriv_le {beta : Real} (hbeta : 1 < beta) :
    |centerEndpointRateSecondDeriv beta| ≤ 2 := by
  have hge : (1 : Real) ≤ (beta + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hpos : (0 : Real) < (beta + 1) ^ 3 := by linarith
  unfold centerEndpointRateSecondDeriv
  rw [abs_of_nonneg (by positivity)]
  have hinv : ((beta + 1) ^ 3)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact hge
  linarith

/-- Second-channel block bound for the differentiated channel power. -/
private theorem norm_centerChannelPowerSecondDeriv_le (N : Nat) {beta : Real} (hbeta : 1 < beta) :
    ‖centerChannelPowerSecondDeriv N beta‖ ≤
      (‖1 - centerOmega‖ + 1) ^ 2 *
        (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2)) := by
  have hb0 : (0 : Real) < beta := lt_trans one_pos hbeta
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval hb0
  have hcast : ((N + 1 : Nat) : Real) = (N : Real) + 1 := by push_cast; ring
  rw [hcast]
  have hq' := norm_centerChannelDeriv_le hbeta
  have hq'' := norm_centerChannelSecondDeriv_le hbeta
  have hq'0 : 0 ≤ ‖centerChannelDeriv beta‖ := norm_nonneg _
  have hKq0 : 0 ≤ ‖1 - centerOmega‖ := norm_nonneg _
  have hrhoeq : ‖centerChannel beta‖ = centerRho beta := rfl
  have hp2pos : 0 < centerRho beta ^ (N - 2) := pow_pos hrho0 _
  have hp1nn : 0 ≤ centerRho beta ^ (N - 1) := pow_nonneg hrho0.le _
  have hmono : centerRho beta ^ (N - 1) ≤ centerRho beta ^ (N - 2) :=
    pow_le_pow_of_le_one hrho0.le hrho1.le (by omega)
  have hNnn : (0 : Real) ≤ (N : Real) := Nat.cast_nonneg N
  have hN1 : ((N - 1 : Nat) : Real) ≤ (N : Real) := Nat.cast_le.mpr (by omega)
  have hN1nn : (0 : Real) ≤ ((N - 1 : Nat) : Real) := Nat.cast_nonneg _
  have e1 : ‖(N : Complex) * ((N - 1 : Nat) : Complex) * centerChannel beta ^ (N - 2) *
        centerChannelDeriv beta ^ 2‖
      = (N : Real) * ((N - 1 : Nat) : Real) * centerRho beta ^ (N - 2) *
          ‖centerChannelDeriv beta‖ ^ 2 := by
    simp only [norm_mul, norm_pow, Complex.norm_natCast, hrhoeq]
  have e2 : ‖(N : Complex) * centerChannel beta ^ (N - 1) * centerChannelSecondDeriv beta‖
      = (N : Real) * centerRho beta ^ (N - 1) * ‖centerChannelSecondDeriv beta‖ := by
    simp only [norm_mul, norm_pow, Complex.norm_natCast, hrhoeq]
  have hprod : (N : Real) * ((N - 1 : Nat) : Real) ≤ ((N : Real) + 1) ^ 2 := by nlinarith
  have hsq : ‖centerChannelDeriv beta‖ ^ 2 ≤ ‖1 - centerOmega‖ ^ 2 := by nlinarith
  have b1 : (N : Real) * ((N - 1 : Nat) : Real) * centerRho beta ^ (N - 2) *
        ‖centerChannelDeriv beta‖ ^ 2
      ≤ ‖1 - centerOmega‖ ^ 2 *
        (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) := by
    calc (N : Real) * ((N - 1 : Nat) : Real) * centerRho beta ^ (N - 2) *
          ‖centerChannelDeriv beta‖ ^ 2
        = ((N : Real) * ((N - 1 : Nat) : Real)) * ‖centerChannelDeriv beta‖ ^ 2 *
            centerRho beta ^ (N - 2) := by ring
      _ ≤ (((N : Real) + 1) ^ 2) * ‖1 - centerOmega‖ ^ 2 * centerRho beta ^ (N - 2) := by
          refine mul_le_mul_of_nonneg_right ?_ hp2pos.le
          exact mul_le_mul hprod hsq (sq_nonneg _) (by positivity)
      _ = ‖1 - centerOmega‖ ^ 2 * (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) := by ring
  have hNsq : (N : Real) ≤ ((N : Real) + 1) ^ 2 := by nlinarith
  have hstep : (N : Real) * centerRho beta ^ (N - 1) ≤
      ((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2) :=
    mul_le_mul hNsq hmono hp1nn (by positivity)
  have b2 : (N : Real) * centerRho beta ^ (N - 1) * ‖centerChannelSecondDeriv beta‖
      ≤ 2 * ‖1 - centerOmega‖ *
        (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) := by
    calc (N : Real) * centerRho beta ^ (N - 1) * ‖centerChannelSecondDeriv beta‖
        ≤ (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) * (2 * ‖1 - centerOmega‖) :=
          mul_le_mul hstep hq'' (norm_nonneg _) (by positivity)
      _ = 2 * ‖1 - centerOmega‖ * (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) := by ring
  have hY0 : 0 ≤ ((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2) := by positivity
  unfold centerChannelPowerSecondDeriv
  calc ‖(N : Complex) * ((N - 1 : Nat) : Complex) * centerChannel beta ^ (N - 2) *
          centerChannelDeriv beta ^ 2 +
        (N : Complex) * centerChannel beta ^ (N - 1) * centerChannelSecondDeriv beta‖
      ≤ ‖(N : Complex) * ((N - 1 : Nat) : Complex) * centerChannel beta ^ (N - 2) *
            centerChannelDeriv beta ^ 2‖ +
          ‖(N : Complex) * centerChannel beta ^ (N - 1) * centerChannelSecondDeriv beta‖ :=
        norm_add_le _ _
    _ = (N : Real) * ((N - 1 : Nat) : Real) * centerRho beta ^ (N - 2) *
            ‖centerChannelDeriv beta‖ ^ 2 +
          (N : Real) * centerRho beta ^ (N - 1) * ‖centerChannelSecondDeriv beta‖ := by
        rw [e1, e2]
    _ ≤ ‖1 - centerOmega‖ ^ 2 * (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) +
          2 * ‖1 - centerOmega‖ * (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) := by
        linarith
    _ ≤ (‖1 - centerOmega‖ + 1) ^ 2 *
          (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) := by nlinarith [hY0]

/-- Second-channel block bound for the differentiated endpoint power. -/
private theorem abs_centerEndpointRatePowerSecondDeriv_le
    (N : Nat) {beta : Real} (hbeta : 1 < beta) :
    |centerEndpointRatePowerSecondDeriv N beta| ≤
      3 * (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2)) := by
  have hb0 : (0 : Real) < beta := lt_trans one_pos hbeta
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval hb0
  have hcast : ((N + 1 : Nat) : Real) = (N : Real) + 1 := by push_cast; ring
  rw [hcast]
  have hrnn : 0 ≤ centerEndpointRate beta := centerEndpointRate_nonneg hb0
  have hrlt : centerEndpointRate beta < centerRho beta := centerEndpointRate_lt_centerRho hbeta
  have hr' := abs_centerEndpointRateDeriv_le hbeta
  have hr'' := abs_centerEndpointRateSecondDeriv_le hbeta
  have hp2pos : 0 < centerRho beta ^ (N - 2) := pow_pos hrho0 _
  have hr2 : centerEndpointRate beta ^ (N - 2) ≤ centerRho beta ^ (N - 2) :=
    pow_le_pow_left₀ hrnn hrlt.le _
  have hr1 : centerEndpointRate beta ^ (N - 1) ≤ centerRho beta ^ (N - 1) :=
    pow_le_pow_left₀ hrnn hrlt.le _
  have hmono : centerRho beta ^ (N - 1) ≤ centerRho beta ^ (N - 2) :=
    pow_le_pow_of_le_one hrho0.le hrho1.le (by omega)
  have hr2nn : 0 ≤ centerEndpointRate beta ^ (N - 2) := pow_nonneg hrnn _
  have hr1nn : 0 ≤ centerEndpointRate beta ^ (N - 1) := pow_nonneg hrnn _
  have hNnn : (0 : Real) ≤ (N : Real) := Nat.cast_nonneg N
  have hN1 : ((N - 1 : Nat) : Real) ≤ (N : Real) := Nat.cast_le.mpr (by omega)
  have hN1nn : (0 : Real) ≤ ((N - 1 : Nat) : Real) := Nat.cast_nonneg _
  have hprod : (N : Real) * ((N - 1 : Nat) : Real) ≤ ((N : Real) + 1) ^ 2 := by nlinarith
  have hNsq : (N : Real) ≤ ((N : Real) + 1) ^ 2 := by nlinarith
  have hY0 : 0 ≤ ((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2) := by positivity
  have b1 : |(N : Real) * ((N - 1 : Nat) : Real) * centerEndpointRate beta ^ (N - 2) *
        centerEndpointRateDeriv beta ^ 2|
      ≤ ((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity), abs_pow]
    have hsq : |centerEndpointRateDeriv beta| ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg (centerEndpointRateDeriv beta)]
    calc (N : Real) * ((N - 1 : Nat) : Real) * centerEndpointRate beta ^ (N - 2) *
          |centerEndpointRateDeriv beta| ^ 2
        = ((N : Real) * ((N - 1 : Nat) : Real)) * |centerEndpointRateDeriv beta| ^ 2 *
            centerEndpointRate beta ^ (N - 2) := by ring
      _ ≤ (((N : Real) + 1) ^ 2) * 1 * centerRho beta ^ (N - 2) := by
          refine mul_le_mul (mul_le_mul hprod hsq (sq_nonneg _) (by positivity)) hr2 hr2nn
            (by positivity)
      _ = ((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2) := by ring
  have b2 : |(N : Real) * centerEndpointRate beta ^ (N - 1) *
        centerEndpointRateSecondDeriv beta|
      ≤ 2 * (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hstep : (N : Real) * centerEndpointRate beta ^ (N - 1) ≤
        ((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2) := by
      calc (N : Real) * centerEndpointRate beta ^ (N - 1)
          ≤ ((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 1) :=
            mul_le_mul hNsq (le_trans hr1 (le_refl _)) hr1nn (by positivity)
        _ ≤ ((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2) := by
            exact mul_le_mul_of_nonneg_left hmono (by positivity)
    calc (N : Real) * centerEndpointRate beta ^ (N - 1) *
          |centerEndpointRateSecondDeriv beta|
        ≤ (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) * 2 :=
          mul_le_mul hstep hr'' (abs_nonneg _) hY0
      _ = 2 * (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) := by ring
  unfold centerEndpointRatePowerSecondDeriv
  calc |(N : Real) * ((N - 1 : Nat) : Real) * centerEndpointRate beta ^ (N - 2) *
          centerEndpointRateDeriv beta ^ 2 +
        (N : Real) * centerEndpointRate beta ^ (N - 1) *
          centerEndpointRateSecondDeriv beta|
      ≤ |(N : Real) * ((N - 1 : Nat) : Real) * centerEndpointRate beta ^ (N - 2) *
            centerEndpointRateDeriv beta ^ 2| +
          |(N : Real) * centerEndpointRate beta ^ (N - 1) *
            centerEndpointRateSecondDeriv beta| := abs_add_le _ _
    _ ≤ 3 * (((N : Real) + 1) ^ 2 * centerRho beta ^ (N - 2)) := by linarith

/-- Endpoint-term second-derivative bound. -/
private theorem abs_centerEndpointTermSecondDeriv_le
    (N : Nat) {beta : Real} (hbeta : 1 < beta) :
    |centerEndpointTermSecondDeriv N beta| ≤
      9 * (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2)) := by
  obtain ⟨he0, he1⟩ := epsIdx_bounds N
  have hin := abs_centerEndpointRatePowerSecondDeriv_le N hbeta
  have hout : |3 * ResidueSlices.epsIdx 3 N| ≤ 3 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  unfold centerEndpointTermSecondDeriv
  calc |3 * ResidueSlices.epsIdx 3 N * centerEndpointRatePowerSecondDeriv N beta|
      = |3 * ResidueSlices.epsIdx 3 N| * |centerEndpointRatePowerSecondDeriv N beta| :=
        abs_mul _ _
    _ ≤ 3 * (3 * (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2))) :=
        mul_le_mul hout hin (abs_nonneg _) (by norm_num)
    _ = 9 * (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2)) := by ring

/-- Spectral bound for the numerator second derivative. -/
private theorem abs_centerNumeratorTermSecondDeriv_le
    (N : Nat) {beta : Real} (hbeta : 1 < beta) :
    |centerNumeratorTermSecondDeriv N beta| ≤
      (2 * (‖centerOmega ^ 2 - 1‖ + 1) * (‖1 - centerOmega‖ + 1) ^ 2 + 9) *
        (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2)) := by
  have hb0 : (0 : Real) < beta := lt_trans one_pos hbeta
  obtain ⟨hrho0, _⟩ := centerRho_mem_unitInterval hb0
  have hY0 : 0 ≤ ((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2) := by
    have := pow_pos hrho0 (N - 2)
    positivity
  have hP := norm_centerChannelPowerSecondDeriv_le N hbeta
  have hE := abs_centerEndpointTermSecondDeriv_le N hbeta
  have hmul : ‖(centerOmega ^ 2 - 1) * centerChannelPowerSecondDeriv N beta‖
      ≤ ‖centerOmega ^ 2 - 1‖ *
        ((‖1 - centerOmega‖ + 1) ^ 2 *
          (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2))) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hP (norm_nonneg _)
  have h2 := abs_two_mul_re_le hmul
  unfold centerNumeratorTermSecondDeriv
  calc |2 * Complex.re ((centerOmega ^ 2 - 1) * centerChannelPowerSecondDeriv N beta) +
        centerEndpointTermSecondDeriv N beta|
      ≤ |2 * Complex.re ((centerOmega ^ 2 - 1) * centerChannelPowerSecondDeriv N beta)| +
          |centerEndpointTermSecondDeriv N beta| := abs_add_le _ _
    _ ≤ 2 * (‖centerOmega ^ 2 - 1‖ *
            ((‖1 - centerOmega‖ + 1) ^ 2 *
              (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2)))) +
          9 * (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2)) := by linarith
    _ ≤ (2 * (‖centerOmega ^ 2 - 1‖ + 1) * (‖1 - centerOmega‖ + 1) ^ 2 + 9) *
          (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2)) := by
        nlinarith [mul_nonneg (sq_nonneg (‖1 - centerOmega‖ + 1)) hY0]

/-- Spectral bound for the denominator second derivative. -/
private theorem abs_centerDenominatorWaveSecondDeriv_le
    (N : Nat) {beta : Real} (hbeta : 1 < beta) :
    |centerDenominatorWaveSecondDeriv N beta| ≤
      (2 * (‖centerOmega ^ 2 - 1‖ + 1) * (‖1 - centerOmega‖ + 1) ^ 2 + 9) *
        (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2)) := by
  have hb0 : (0 : Real) < beta := lt_trans one_pos hbeta
  obtain ⟨hrho0, _⟩ := centerRho_mem_unitInterval hb0
  have hY0 : 0 ≤ ((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2) := by
    have := pow_pos hrho0 (N - 2)
    positivity
  have hP := norm_centerChannelPowerSecondDeriv_le N hbeta
  have hE := abs_centerEndpointTermSecondDeriv_le N hbeta
  have h2 := abs_two_mul_re_le hP
  unfold centerDenominatorWaveSecondDeriv
  calc |2 * Complex.re (centerChannelPowerSecondDeriv N beta) -
        centerEndpointTermSecondDeriv N beta|
      ≤ |2 * Complex.re (centerChannelPowerSecondDeriv N beta)| +
          |centerEndpointTermSecondDeriv N beta| := abs_sub_le_abs_add_abs _ _
    _ ≤ 2 * ((‖1 - centerOmega‖ + 1) ^ 2 *
            (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2))) +
          9 * (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2)) := by linarith
    _ ≤ (2 * (‖centerOmega ^ 2 - 1‖ + 1) * (‖1 - centerOmega‖ + 1) ^ 2 + 9) *
          (((N + 1 : Nat) : Real) ^ 2 * centerRho beta ^ (N - 2)) := by
        nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (centerOmega ^ 2 - 1))
          (sq_nonneg (‖1 - centerOmega‖ + 1))) hY0]

/-! ### Abstract quotient estimate for the four-term curvature decomposition -/

/-- Pure algebraic estimate behind the curvature spectral bound. -/
private theorem curvature_defect_bound_aux
    {a D U Ud Dd Udd Ddd s Y K1 K2 K3 Cs : Real}
    (ha : 0 < a) (hD : 1 / 2 < D) (hs0 : 0 < s) (hs1 : s ≤ 1) (hY0 : 0 ≤ Y)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hCs : 0 ≤ Cs)
    (hU : |U| ≤ K1 * s) (hUdDd : |Ud * Dd| ≤ K2 * K3 * Y)
    (hDd2 : |Dd| ^ 2 ≤ K3 ^ 2 * Y)
    (hUdd : |Udd| ≤ Cs * Y) (hDdd : |Ddd| ≤ Cs * Y) :
    |a * Udd / D - 2 * U / (a * D) - a * (2 * Ud * Dd + U * Ddd) / D ^ 2 +
        2 * a * U * Dd ^ 2 / D ^ 3|
      ≤ (2 * a * Cs + 4 * a * (2 * K2 * K3 + K1 * Cs) + 16 * a * K1 * K3 ^ 2) * Y +
        4 * K1 / a * s := by
  have hDpos : 0 < D := by linarith
  have hD2 : (1 : Real) / 4 < D ^ 2 := by nlinarith
  have hD3 : (1 : Real) / 8 < D ^ 3 := by nlinarith
  have hCsY : 0 ≤ Cs * Y := mul_nonneg hCs hY0
  have h1 : |a * Udd / D| ≤ 2 * a * Cs * Y := by
    rw [abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos, abs_mul, abs_of_pos ha]
    have hstep : a * |Udd| ≤ a * (Cs * Y) := mul_le_mul_of_nonneg_left hUdd ha.le
    nlinarith [mul_nonneg (mul_nonneg ha.le hCs) hY0]
  have h2 : |2 * U / (a * D)| ≤ 4 * K1 / a * s := by
    rw [abs_div, abs_of_pos (mul_pos ha hDpos), div_le_iff₀ (mul_pos ha hDpos)]
    have hrw : 4 * K1 / a * s * (a * D) = 4 * K1 * s * D := by
      field_simp
    rw [hrw, show (2 : Real) * U = 2 * U from rfl, abs_mul,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
    nlinarith [mul_nonneg hK1 hs0.le]
  have hQ0 : 0 ≤ 2 * K2 * K3 + K1 * Cs := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : Real) ≤ 2) hK2) hK3
    have := mul_nonneg hK1 hCs
    linarith
  have h3 : |a * (2 * Ud * Dd + U * Ddd) / D ^ 2| ≤
      4 * a * (2 * K2 * K3 + K1 * Cs) * Y := by
    have hUDdd : |U * Ddd| ≤ K1 * Cs * Y := by
      rw [abs_mul]
      calc |U| * |Ddd| ≤ (K1 * s) * (Cs * Y) :=
            mul_le_mul hU hDdd (abs_nonneg _) (mul_nonneg hK1 hs0.le)
        _ ≤ K1 * Cs * Y := by nlinarith [mul_nonneg (mul_nonneg hK1 hCs) hY0]
    have hinner : |2 * Ud * Dd + U * Ddd| ≤ (2 * K2 * K3 + K1 * Cs) * Y := by
      have habs2 : |2 * Ud * Dd| = 2 * |Ud * Dd| := by
        rw [show (2 : Real) * Ud * Dd = 2 * (Ud * Dd) by ring, abs_mul,
          abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
      calc |2 * Ud * Dd + U * Ddd| ≤ |2 * Ud * Dd| + |U * Ddd| := abs_add_le _ _
        _ = 2 * |Ud * Dd| + |U * Ddd| := by rw [habs2]
        _ ≤ 2 * (K2 * K3 * Y) + K1 * Cs * Y := by linarith
        _ = (2 * K2 * K3 + K1 * Cs) * Y := by ring
    rw [abs_div, abs_of_pos (by positivity : (0 : Real) < D ^ 2),
      div_le_iff₀ (by positivity : (0 : Real) < D ^ 2), abs_mul, abs_of_pos ha]
    have hstep : a * |2 * Ud * Dd + U * Ddd| ≤ a * ((2 * K2 * K3 + K1 * Cs) * Y) :=
      mul_le_mul_of_nonneg_left hinner ha.le
    nlinarith [mul_nonneg (mul_nonneg ha.le (mul_nonneg hQ0 hY0))
      (by linarith : (0 : Real) ≤ 4 * D ^ 2 - 1)]
  have h4 : |2 * a * U * Dd ^ 2 / D ^ 3| ≤ 16 * a * K1 * K3 ^ 2 * Y := by
    have hnum : |2 * a * U * Dd ^ 2| ≤ 2 * a * (K1 * K3 ^ 2 * Y) := by
      have habs : |2 * a * U * Dd ^ 2| = 2 * a * (|U| * |Dd| ^ 2) := by
        rw [show (2 : Real) * a * U * Dd ^ 2 = (2 * a) * (U * Dd ^ 2) by ring, abs_mul,
          abs_of_pos (by linarith : (0 : Real) < 2 * a), abs_mul, abs_pow]
      rw [habs]
      have hprod : |U| * |Dd| ^ 2 ≤ (K1 * s) * (K3 ^ 2 * Y) :=
        mul_le_mul hU hDd2 (by positivity) (mul_nonneg hK1 hs0.le)
      have hsimp : (K1 * s) * (K3 ^ 2 * Y) ≤ K1 * K3 ^ 2 * Y := by
        nlinarith [mul_nonneg (mul_nonneg hK1 (sq_nonneg K3)) hY0]
      nlinarith [mul_nonneg hK1 (mul_nonneg (sq_nonneg K3) hY0)]
    rw [abs_div, abs_of_pos (by positivity : (0 : Real) < D ^ 3),
      div_le_iff₀ (by positivity : (0 : Real) < D ^ 3)]
    nlinarith [mul_nonneg (mul_nonneg ha.le (mul_nonneg hK1 (mul_nonneg (sq_nonneg K3) hY0)))
      (by linarith : (0 : Real) ≤ 8 * D ^ 3 - 1)]
  calc |a * Udd / D - 2 * U / (a * D) - a * (2 * Ud * Dd + U * Ddd) / D ^ 2 +
        2 * a * U * Dd ^ 2 / D ^ 3|
      ≤ |a * Udd / D - 2 * U / (a * D) - a * (2 * Ud * Dd + U * Ddd) / D ^ 2| +
          |2 * a * U * Dd ^ 2 / D ^ 3| := abs_add_le _ _
    _ ≤ (|a * Udd / D - 2 * U / (a * D)| +
          |a * (2 * Ud * Dd + U * Ddd) / D ^ 2|) + |2 * a * U * Dd ^ 2 / D ^ 3| := by
        have := abs_sub_le_abs_add_abs (a * Udd / D - 2 * U / (a * D))
          (a * (2 * Ud * Dd + U * Ddd) / D ^ 2)
        linarith
    _ ≤ ((|a * Udd / D| + |2 * U / (a * D)|) +
          |a * (2 * Ud * Dd + U * Ddd) / D ^ 2|) + |2 * a * U * Dd ^ 2 / D ^ 3| := by
        have := abs_sub_le_abs_add_abs (a * Udd / D) (2 * U / (a * D))
        linarith
    _ ≤ (2 * a * Cs + 4 * a * (2 * K2 * K3 + K1 * Cs) + 16 * a * K1 * K3 ^ 2) * Y +
          4 * K1 / a * s := by linarith

/-- Rescaling step converting the `rho^(N-2)` bound into the `rho^N` rate. -/
private theorem curvature_scale_aux {A B P r2 n2 s : Real}
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hr2 : 0 < r2) (hn2 : r2 ≤ n2) (hs : s = P * r2) :
    A * (n2 * P) + B * s ≤ (A + B) / r2 * (n2 * s) := by
  subst hs
  have hne : r2 ≠ 0 := ne_of_gt hr2
  have hEq : (A + B) / r2 * (n2 * (P * r2)) = (A + B) * (n2 * P) := by
    field_simp
  rw [hEq]
  nlinarith [mul_nonneg (mul_nonneg hB hP) (sub_nonneg.mpr hn2)]

theorem eventually_centerCurvatureDefect_geometric_upper
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ N : Nat in Filter.atTop,
        |centerCurvatureDefect N alpha| ≤
          C * (((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ N) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  have hrnn : 0 ≤ centerEndpointRate alpha := centerEndpointRate_nonneg halpha0
  have hrlt : centerEndpointRate alpha < centerRho alpha := centerEndpointRate_lt_centerRho halpha
  obtain ⟨Kw, hKwdef⟩ : ∃ x : Real, x = ‖centerOmega ^ 2 - 1‖ := ⟨_, rfl⟩
  obtain ⟨Kq, hKqdef⟩ : ∃ x : Real, x = ‖1 - centerOmega‖ := ⟨_, rfl⟩
  have hKw0 : 0 ≤ Kw := by rw [hKwdef]; exact norm_nonneg _
  have hKq0 : 0 ≤ Kq := by rw [hKqdef]; exact norm_nonneg _
  have hK10 : (0 : Real) ≤ 2 * Kw + 3 := by linarith
  have hK20 : (0 : Real) ≤ 2 * Kw * Kq + 3 := by nlinarith
  have hK30 : (0 : Real) ≤ 2 * Kq + 3 := by linarith
  have hCs0 : (0 : Real) ≤ 2 * (Kw + 1) * (Kq + 1) ^ 2 + 9 := by
    nlinarith [sq_nonneg (Kq + 1)]
  have hrho2 : (0 : Real) < centerRho alpha ^ 2 := pow_pos hrho0 2
  obtain ⟨C, hC⟩ : ∃ x : Real, x =
      (2 * alpha * (2 * (Kw + 1) * (Kq + 1) ^ 2 + 9) +
        4 * alpha * (2 * (2 * Kw * Kq + 3) * (2 * Kq + 3) +
          (2 * Kw + 3) * (2 * (Kw + 1) * (Kq + 1) ^ 2 + 9)) +
        16 * alpha * (2 * Kw + 3) * (2 * Kq + 3) ^ 2 +
        4 * (2 * Kw + 3) / alpha) / centerRho alpha ^ 2 := ⟨_, rfl⟩
  have hCpos : 0 < C := by
    rw [hC]
    refine div_pos ?_ hrho2
    have e1 : (0 : Real) ≤ 2 * alpha * (2 * (Kw + 1) * (Kq + 1) ^ 2 + 9) :=
      mul_nonneg (by linarith) hCs0
    have e2 : (0 : Real) ≤ 4 * alpha * (2 * (2 * Kw * Kq + 3) * (2 * Kq + 3) +
        (2 * Kw + 3) * (2 * (Kw + 1) * (Kq + 1) ^ 2 + 9)) := by
      refine mul_nonneg (by linarith) ?_
      have := mul_nonneg hK20 hK30
      have := mul_nonneg hK10 hCs0
      linarith
    have e3 : (0 : Real) ≤ 16 * alpha * (2 * Kw + 3) * (2 * Kq + 3) ^ 2 :=
      mul_nonneg (mul_nonneg (by linarith) hK10) (sq_nonneg _)
    have e4 : (0 : Real) < 4 * (2 * Kw + 3) / alpha := div_pos (by linarith) halpha0
    linarith
  refine ⟨C, hCpos, ?_⟩
  have hev1 : ∀ᶠ N : Nat in atTop, (1 : Real) / 2 < centerDenominatorWave N alpha :=
    (tendsto_centerDenominatorWave halpha0).eventually
      (lt_mem_nhds (by norm_num : (1 : Real) / 2 < 1))
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev1
  rw [eventually_atTop]
  refine ⟨max N1 2, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNge1 : 1 ≤ N := by omega
  have hD : (1 : Real) / 2 < centerDenominatorWave N alpha :=
    hN1 N (le_trans (le_max_left _ _) hN)
  have hrhoN : 0 < centerRho alpha ^ N := pow_pos hrho0 N
  have hrhoN1 : centerRho alpha ^ N ≤ 1 := pow_le_one₀ hrho0.le hrho1.le
  have hP0 : 0 < centerRho alpha ^ (N - 2) := pow_pos hrho0 (N - 2)
  have hsplit : centerRho alpha ^ N = centerRho alpha ^ (N - 2) * centerRho alpha ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hn1 : (1 : Real) ≤ ((N + 1 : Nat) : Real) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hNle : (N : Real) ≤ ((N + 1 : Nat) : Real) := by exact_mod_cast Nat.le_succ N
  have hNnn : (0 : Real) ≤ (N : Real) := Nat.cast_nonneg N
  have hY0 : 0 ≤ ((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ (N - 2) :=
    mul_nonneg (sq_nonneg _) hP0.le
  -- first-order bounds
  have hU : |centerNumeratorTerm N alpha| ≤ (2 * Kw + 3) * centerRho alpha ^ N := by
    rw [hKwdef]
    exact abs_centerNumeratorTerm_le N halpha0 (le_refl _) (pow_le_pow_left₀ hrnn hrlt.le N)
  have hUd : |centerNumeratorTermDeriv N alpha| ≤
      (2 * Kw * Kq + 3) * ((N : Real) * centerRho alpha ^ (N - 1)) := by
    rw [hKwdef, hKqdef]
    exact abs_centerNumeratorTermDeriv_le N halpha (le_refl _)
      (pow_le_pow_left₀ hrnn hrlt.le _)
  have hDd : |centerDenominatorWaveDeriv N alpha| ≤
      (2 * Kq + 3) * ((N : Real) * centerRho alpha ^ (N - 1)) := by
    rw [hKqdef]
    exact abs_centerDenominatorWaveDeriv_le N halpha (le_refl _)
      (pow_le_pow_left₀ hrnn hrlt.le _)
  have hUdd : |centerNumeratorTermSecondDeriv N alpha| ≤
      (2 * (Kw + 1) * (Kq + 1) ^ 2 + 9) *
        (((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ (N - 2)) := by
    rw [hKwdef, hKqdef]
    exact abs_centerNumeratorTermSecondDeriv_le N halpha
  have hDdd : |centerDenominatorWaveSecondDeriv N alpha| ≤
      (2 * (Kw + 1) * (Kq + 1) ^ 2 + 9) *
        (((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ (N - 2)) := by
    rw [hKwdef, hKqdef]
    exact abs_centerDenominatorWaveSecondDeriv_le N halpha
  -- polynomial factor comparisons
  have hW0 : 0 ≤ (N : Real) * centerRho alpha ^ (N - 1) :=
    mul_nonneg hNnn (pow_nonneg hrho0.le _)
  have hexp : centerRho alpha ^ (N - 1) * centerRho alpha ^ (N - 1)
      = centerRho alpha ^ (N - 2) * centerRho alpha ^ N := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hW2 : ((N : Real) * centerRho alpha ^ (N - 1)) ^ 2 ≤
      ((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ (N - 2) := by
    have hstep : ((N : Real) * centerRho alpha ^ (N - 1)) ^ 2
        = (N : Real) ^ 2 * (centerRho alpha ^ (N - 2) * centerRho alpha ^ N) := by
      rw [← hexp]; ring
    rw [hstep]
    have h1 : (N : Real) ^ 2 * (centerRho alpha ^ (N - 2) * centerRho alpha ^ N)
        ≤ (N : Real) ^ 2 * (centerRho alpha ^ (N - 2) * 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hrhoN1 hP0.le
    have h2 : (N : Real) ^ 2 * (centerRho alpha ^ (N - 2) * 1)
        ≤ ((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ (N - 2) := by
      have : (N : Real) ^ 2 ≤ ((N + 1 : Nat) : Real) ^ 2 := by nlinarith
      nlinarith [hP0]
    linarith
  have hUdDd : |centerNumeratorTermDeriv N alpha * centerDenominatorWaveDeriv N alpha| ≤
      (2 * Kw * Kq + 3) * (2 * Kq + 3) *
        (((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ (N - 2)) := by
    rw [abs_mul]
    calc |centerNumeratorTermDeriv N alpha| * |centerDenominatorWaveDeriv N alpha|
        ≤ ((2 * Kw * Kq + 3) * ((N : Real) * centerRho alpha ^ (N - 1))) *
            ((2 * Kq + 3) * ((N : Real) * centerRho alpha ^ (N - 1))) :=
          mul_le_mul hUd hDd (abs_nonneg _) (mul_nonneg hK20 hW0)
      _ = (2 * Kw * Kq + 3) * (2 * Kq + 3) *
            ((N : Real) * centerRho alpha ^ (N - 1)) ^ 2 := by ring
      _ ≤ (2 * Kw * Kq + 3) * (2 * Kq + 3) *
            (((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ (N - 2)) := by
          refine mul_le_mul_of_nonneg_left hW2 ?_
          exact mul_nonneg hK20 hK30
  have hDd2 : |centerDenominatorWaveDeriv N alpha| ^ 2 ≤
      (2 * Kq + 3) ^ 2 * (((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ (N - 2)) := by
    have hsq : |centerDenominatorWaveDeriv N alpha| ^ 2 ≤
        ((2 * Kq + 3) * ((N : Real) * centerRho alpha ^ (N - 1))) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hDd 2
    calc |centerDenominatorWaveDeriv N alpha| ^ 2
        ≤ ((2 * Kq + 3) * ((N : Real) * centerRho alpha ^ (N - 1))) ^ 2 := hsq
      _ = (2 * Kq + 3) ^ 2 * ((N : Real) * centerRho alpha ^ (N - 1)) ^ 2 := by ring
      _ ≤ (2 * Kq + 3) ^ 2 * (((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ (N - 2)) :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
  have hmain := curvature_defect_bound_aux (a := alpha)
    (D := centerDenominatorWave N alpha) (U := centerNumeratorTerm N alpha)
    (Ud := centerNumeratorTermDeriv N alpha) (Dd := centerDenominatorWaveDeriv N alpha)
    (Udd := centerNumeratorTermSecondDeriv N alpha)
    (Ddd := centerDenominatorWaveSecondDeriv N alpha)
    halpha0 hD hrhoN hrhoN1 hY0 hK10 hK20 hK30 hCs0 hU hUdDd hDd2 hUdd hDdd
  rw [centerCurvatureDefect_decomposition hNge1 halpha0]
  refine le_trans hmain ?_
  have hrho2le1 : centerRho alpha ^ 2 ≤ 1 := pow_le_one₀ hrho0.le hrho1.le
  have hn2ge1 : (1 : Real) ≤ ((N + 1 : Nat) : Real) ^ 2 := one_le_pow₀ hn1
  have hn2 : centerRho alpha ^ 2 ≤ ((N + 1 : Nat) : Real) ^ 2 :=
    le_trans hrho2le1 hn2ge1
  have hB0 : (0 : Real) ≤ 4 * (2 * Kw + 3) / alpha :=
    le_of_lt (div_pos (by linarith) halpha0)
  rw [hC]
  exact curvature_scale_aux hB0 hP0.le hrho2 hn2 hsplit


/-- Polynomial-times-geometric domination with a squared polynomial factor. -/
private theorem tendsto_natSucc_sq_mul_pow {x : Real} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun N : Nat => ((N + 1 : Nat) : Real) ^ 2 * x ^ N) atTop (nhds 0) := by
  have hy0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hy1 : Real.sqrt x < 1 := by
    have := Real.sqrt_lt_sqrt hx0 hx1
    simpa using this
  have h := tendsto_natSucc_mul_pow hy0 hy1
  have h2 := h.mul h
  rw [mul_zero] at h2
  refine h2.congr ?_
  intro N
  have hsq : Real.sqrt x ^ N * Real.sqrt x ^ N = x ^ N := by
    rw [← mul_pow, Real.mul_self_sqrt hx0]
  calc ((N + 1 : Nat) : Real) * Real.sqrt x ^ N *
        (((N + 1 : Nat) : Real) * Real.sqrt x ^ N)
      = ((N + 1 : Nat) : Real) ^ 2 * (Real.sqrt x ^ N * Real.sqrt x ^ N) := by ring
    _ = ((N + 1 : Nat) : Real) ^ 2 * x ^ N := by rw [hsq]

theorem tendsto_centerCurvatureDefect
    {alpha : Real} (halpha : 1 < alpha) :
    Filter.Tendsto (fun N : Nat => centerCurvatureDefect N alpha)
      Filter.atTop (nhds 0) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  obtain ⟨C, hC0, hev⟩ := eventually_centerCurvatureDefect_geometric_upper halpha
  have hlim : Filter.Tendsto
      (fun N : Nat => C * (((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ N))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_natSucc_sq_mul_pow hrho0.le hrho1).const_mul C
    simpa using h
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hev] with N hN
  simpa [Real.norm_eq_abs] using hN

theorem eventually_adaptiveDerivativeRow_centerCurvatureDefect_geometric_upper
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ N : Nat in Filter.atTop,
        |centerCurvatureDefect (adaptiveDerivativeRow N alpha) alpha| ≤
          C *
            ((((adaptiveDerivativeRow N alpha) + 1 : Nat) : Real) ^ 2 *
              centerRho alpha ^ (adaptiveDerivativeRow N alpha)) := by
  obtain ⟨C, hC0, hev⟩ := eventually_centerCurvatureDefect_geometric_upper halpha
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  refine ⟨C, hC0, ?_⟩
  rw [eventually_atTop]
  refine ⟨N0, ?_⟩
  intro N hN
  exact hN0 (adaptiveDerivativeRow N alpha)
    (le_trans hN (le_adaptiveDerivativeRow N alpha))

theorem tendsto_adaptiveDerivativeRow_centerCurvatureDefect
    {alpha : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        centerCurvatureDefect (adaptiveDerivativeRow N alpha) alpha)
      Filter.atTop (nhds 0) := by
  have h := (tendsto_centerCurvatureDefect halpha).comp
    (tendsto_adaptiveDerivativeRow alpha)
  simpa [Function.comp_def] using h

end SilverFiniteRow
