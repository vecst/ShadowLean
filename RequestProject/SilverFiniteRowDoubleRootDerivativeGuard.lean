/-
Cubic-silver finite-row crossover, Phase B4B9: adjacent derivative-channel
noncancellation and the derivative-adaptive row selector.

The dominant differentiated channel of the real center error is
`L_N = 2*alpha*Re(A * N*q^(N-1)*q')` (A = centerOmega^2-1, q = centerChannel,
q' = centerChannelDeriv); dividing by `N*rho^N` gives the exact phase projection
`2*alpha*Re((A*q'/q)*u^N)` with `u = q/rho` on the unit circle with nonzero
imaginary part, so `adjacent_real_projection_lower` forbids simultaneous vanishing
of adjacent leading derivative projections. The normalized actual-minus-leading
remainder tends to zero (four squeeze estimates from the exact quotient-derivative
decomposition), so eventual adjacent noncancellation transfers to the actual
derivative error, and `adaptiveDerivativeRow` (whichever of N, N+1 has the larger
normalized derivative error) is a bounded-delay selector with an eventual genuine
lower bound and nonzero derivative error. This phase does NOT claim
`adaptiveDerivativeRow` preserves negative center error, agrees with `adaptiveRow`,
supplies B4B8's critical-separation hypotheses, or proves a double-root branch; it
proves no spectral bound for `centerCurvatureDefect`, no joint row, and no endpoint
sign separation, root existence, or convergence.
-/
import RequestProject.SilverFiniteRowDoubleRootCriticalCancellation

open scoped Real Topology BigOperators
open Filter

namespace SilverFiniteRow

noncomputable def centerDerivativeChannelCoefficient (alpha : Real) : Complex :=
  (centerOmega ^ 2 - 1) * centerChannelDeriv alpha / centerChannel alpha

noncomputable def centerDerivativeProjectionConstant (alpha : Real) : Real :=
  2 * alpha *
    (norm (centerDerivativeChannelCoefficient alpha) *
      |Complex.im (centerUnitChannel alpha)| / 4)

noncomputable def centerDerivativeLeadingTerm
    (N : Nat) (alpha : Real) : Real :=
  2 * alpha * Complex.re
    ((centerOmega ^ 2 - 1) *
      ((N : Complex) * centerChannel alpha ^ (N - 1) *
        centerChannelDeriv alpha))

noncomputable def normalizedCenterDerivativeError
    (N : Nat) (alpha : Real) : Real :=
  |centerDerivativeError N alpha| /
    ((N : Real) * centerRho alpha ^ N)

noncomputable def adaptiveDerivativeRow (N : Nat) (alpha : Real) : Nat :=
  if normalizedCenterDerivativeError N alpha ≤
      normalizedCenterDerivativeError (N + 1) alpha then
    N + 1
  else
    N

theorem centerDerivativeChannelCoefficient_ne_zero
    {alpha : Real} (halpha : 0 < alpha) :
    centerDerivativeChannelCoefficient alpha ≠ 0 := by
  have hA : centerOmega ^ 2 - 1 ≠ 0 := by
    have h2 : centerOmega ^ 2 ≠ 1 :=
      centerOmega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    exact sub_ne_zero.mpr h2
  have homega : centerOmega ≠ 1 := by
    have h1 : centerOmega ^ 1 ≠ 1 :=
      centerOmega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    simpa using h1
  have hone : (1 : Complex) - centerOmega ≠ 0 := sub_ne_zero.mpr (Ne.symm homega)
  have hderiv : centerChannelDeriv alpha ≠ 0 := by
    unfold centerChannelDeriv
    exact div_ne_zero hone (pow_ne_zero 2 (centerOfReal_add_one_ne_zero halpha))
  unfold centerDerivativeChannelCoefficient
  exact div_ne_zero (mul_ne_zero hA hderiv) (centerChannel_ne_zero halpha)

theorem centerDerivativeProjectionConstant_pos
    {alpha : Real} (halpha : 0 < alpha) :
    0 < centerDerivativeProjectionConstant alpha := by
  have hcoeff : 0 < norm (centerDerivativeChannelCoefficient alpha) :=
    norm_pos_iff.mpr (centerDerivativeChannelCoefficient_ne_zero halpha)
  have him : 0 < |Complex.im (centerUnitChannel alpha)| :=
    abs_pos.mpr (centerUnitChannel_im_ne_zero halpha)
  unfold centerDerivativeProjectionConstant
  positivity

theorem centerDerivativeError_eq_centerErrorParameterDeriv
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    centerDerivativeError N alpha = centerErrorParameterDeriv N alpha := by
  have hsq : (alpha : Real) ^ 2 ≠ 0 := by positivity
  have hrpow : (alpha ^ 3 : Real) ^ ((3 : Real)⁻¹ - 1) = (alpha ^ 2)⁻¹ := by
    rw [show (alpha ^ 3 : Real) = alpha ^ (((3 : Nat) : Real)) by rw [Real.rpow_natCast],
      ← Real.rpow_mul halpha.le,
      show (((3 : Nat) : Real)) * ((3 : Real)⁻¹ - 1) = -((2 : Nat) : Real) by push_cast; ring,
      Real.rpow_neg halpha.le, Real.rpow_natCast]
  have hcube : cubeRootDerivative (alpha ^ 3) = (3 : Real)⁻¹ * (alpha ^ 2)⁻¹ := by
    unfold cubeRootDerivative
    rw [hrpow]
  have hkey := packetErrorDerivative_eq_centerErrorParameterDeriv hN halpha
  unfold packetErrorDerivative at hkey
  rw [hcube] at hkey
  unfold centerDerivativeError
  calc 3 * alpha ^ 2 * packetRatioDerivative N (alpha ^ 3) - 1
      = 3 * alpha ^ 2 *
          (packetRatioDerivative N (alpha ^ 3) - (3 : Real)⁻¹ * (alpha ^ 2)⁻¹) := by
        field_simp
    _ = 3 * alpha ^ 2 * (centerErrorParameterDeriv N alpha / (3 * alpha ^ 2)) := by
        rw [hkey]
    _ = centerErrorParameterDeriv N alpha := by
        field_simp

private theorem centerDerivativeLeadingBlock_eq
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    (((N : Real) * centerRho alpha ^ N : Real) : Complex) *
        (centerDerivativeChannelCoefficient alpha *
          centerUnitChannel alpha ^ N) =
      (centerOmega ^ 2 - 1) *
        ((N : Complex) * centerChannel alpha ^ (N - 1) *
          centerChannelDeriv alpha) := by
  have hrho : 0 < centerRho alpha := centerRho_pos halpha
  have hrne : ((centerRho alpha : Real) : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hrho.ne'
  have hqne : centerChannel alpha ≠ 0 := centerChannel_ne_zero halpha
  have hpow : centerChannel alpha ^ N
      = centerChannel alpha ^ (N - 1) * centerChannel alpha := by
    conv_lhs => rw [← Nat.sub_add_cancel hN]
    rw [pow_succ]
  unfold centerDerivativeChannelCoefficient centerUnitChannel
  rw [div_pow, hpow]
  push_cast
  field_simp

theorem centerDerivativeLeadingTerm_normalized
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    centerDerivativeLeadingTerm N alpha /
        ((N : Real) * centerRho alpha ^ N) =
      2 * alpha * Complex.re
        (centerDerivativeChannelCoefficient alpha *
          centerUnitChannel alpha ^ N) := by
  have hrho : 0 < centerRho alpha := centerRho_pos halpha
  have hNpos : (0 : Real) < (N : Real) := by exact_mod_cast hN
  have hpos : (0 : Real) < (N : Real) * centerRho alpha ^ N := by positivity
  have hre : Complex.re
        ((centerOmega ^ 2 - 1) *
          ((N : Complex) * centerChannel alpha ^ (N - 1) *
            centerChannelDeriv alpha))
      = ((N : Real) * centerRho alpha ^ N) *
        Complex.re (centerDerivativeChannelCoefficient alpha *
          centerUnitChannel alpha ^ N) := by
    rw [← centerDerivativeLeadingBlock_eq hN halpha, Complex.re_ofReal_mul]
  unfold centerDerivativeLeadingTerm
  rw [hre]
  field_simp

theorem adjacent_centerDerivative_leading_lower
    (N : Nat) {alpha : Real} (halpha : 0 < alpha) :
    centerDerivativeProjectionConstant alpha ≤
      max
        |2 * alpha * Complex.re
          (centerDerivativeChannelCoefficient alpha *
            centerUnitChannel alpha ^ N)|
        |2 * alpha * Complex.re
          (centerDerivativeChannelCoefficient alpha *
            centerUnitChannel alpha ^ (N + 1))| := by
  have hu : norm (centerUnitChannel alpha) = 1 := norm_centerUnitChannel halpha
  have hz : norm (centerUnitChannel alpha ^ N) = 1 := by rw [norm_pow, hu, one_pow]
  have key := adjacent_real_projection_lower
    (A := centerDerivativeChannelCoefficient alpha)
    (u := centerUnitChannel alpha) (z := centerUnitChannel alpha ^ N) hu hz
  have he : centerDerivativeChannelCoefficient alpha * centerUnitChannel alpha ^ N *
      centerUnitChannel alpha
      = centerDerivativeChannelCoefficient alpha * centerUnitChannel alpha ^ (N + 1) := by
    rw [pow_succ]; ring
  rw [he] at key
  have h2a : (0 : Real) < 2 * alpha := by linarith
  have habs1 : |2 * alpha * Complex.re
      (centerDerivativeChannelCoefficient alpha * centerUnitChannel alpha ^ N)|
      = 2 * alpha * |Complex.re
        (centerDerivativeChannelCoefficient alpha * centerUnitChannel alpha ^ N)| := by
    rw [abs_mul, abs_of_pos h2a]
  have habs2 : |2 * alpha * Complex.re
      (centerDerivativeChannelCoefficient alpha * centerUnitChannel alpha ^ (N + 1))|
      = 2 * alpha * |Complex.re
        (centerDerivativeChannelCoefficient alpha * centerUnitChannel alpha ^ (N + 1))| := by
    rw [abs_mul, abs_of_pos h2a]
  rw [habs1, habs2, ← mul_max_of_nonneg _ _ h2a.le]
  unfold centerDerivativeProjectionConstant
  exact mul_le_mul_of_nonneg_left key h2a.le

theorem centerDerivativeError_sub_leading_decomposition
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    centerDerivativeError N alpha - centerDerivativeLeadingTerm N alpha =
      centerNumeratorTerm N alpha / centerDenominatorWave N alpha +
        alpha * centerEndpointTermDeriv N alpha /
          centerDenominatorWave N alpha -
        alpha * centerNumeratorTerm N alpha *
          centerDenominatorWaveDeriv N alpha /
          centerDenominatorWave N alpha ^ 2 +
        centerDerivativeLeadingTerm N alpha *
          (1 / centerDenominatorWave N alpha - 1) := by
  have hD : centerDenominatorWave N alpha ≠ 0 :=
    (centerDenominatorWave_pos hN halpha).ne'
  rw [centerDerivativeError_eq_centerErrorParameterDeriv hN halpha]
  unfold centerErrorParameterDeriv centerNumeratorTermDeriv centerDerivativeLeadingTerm
  field_simp
  ring

/-! ### Normalized remainder estimates -/

private theorem centerEndpointRate_pos {alpha : Real} (halpha : 0 < alpha) :
    0 < centerEndpointRate alpha := by
  rw [centerEndpointRate_eq_inv halpha]
  exact inv_pos.mpr (by linarith)

private theorem tendsto_centerNumeratorTerm_normalized
    {alpha : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        centerNumeratorTerm N alpha / ((N : Real) * centerRho alpha ^ N))
      Filter.atTop (nhds 0) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  have hr0 : (0 : Real) ≤ centerEndpointRate alpha := centerEndpointRate_nonneg halpha0
  have hlt : centerEndpointRate alpha < centerRho alpha :=
    centerEndpointRate_lt_centerRho halpha
  refine squeeze_zero_norm'
    (a := fun N : Nat => (2 * ‖centerOmega ^ 2 - 1‖ + 3) / (N : Real)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖centerOmega ^ 2 - 1‖ + 3))
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hNpos : (0 : Real) < (N : Real) := by exact_mod_cast hN
  have hppos : (0 : Real) < centerRho alpha ^ N := pow_pos hrho0 N
  have hbound : |centerNumeratorTerm N alpha|
      ≤ (2 * ‖centerOmega ^ 2 - 1‖ + 3) * centerRho alpha ^ N :=
    abs_centerNumeratorTerm_le N halpha0 le_rfl (pow_le_pow_left₀ hr0 hlt.le N)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hNpos hppos),
    div_le_div_iff₀ (mul_pos hNpos hppos) hNpos]
  nlinarith [mul_le_mul_of_nonneg_right hbound hNpos.le]

private theorem tendsto_centerEndpointTermDeriv_normalized
    {alpha : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        centerEndpointTermDeriv N alpha / ((N : Real) * centerRho alpha ^ N))
      Filter.atTop (nhds 0) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  have hrpos : 0 < centerEndpointRate alpha := centerEndpointRate_pos halpha0
  have hlt : centerEndpointRate alpha < centerRho alpha :=
    centerEndpointRate_lt_centerRho halpha
  have hq0 : (0 : Real) ≤ centerEndpointRate alpha / centerRho alpha := by positivity
  have hq1 : centerEndpointRate alpha / centerRho alpha < 1 := (div_lt_one hrho0).mpr hlt
  refine squeeze_zero_norm'
    (a := fun N : Nat => 3 / centerEndpointRate alpha *
      (centerEndpointRate alpha / centerRho alpha) ^ N) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : Real) < (N : Real) := by exact_mod_cast hN
    have hppos : (0 : Real) < centerRho alpha ^ N := pow_pos hrho0 N
    have hEd : |centerEndpointTermDeriv N alpha|
        ≤ 3 * ((N : Real) * centerEndpointRate alpha ^ (N - 1)) :=
      abs_centerEndpointTermDeriv_le N halpha le_rfl
    have hrN : centerEndpointRate alpha ^ N
        = centerEndpointRate alpha ^ (N - 1) * centerEndpointRate alpha := by
      conv_lhs => rw [← Nat.sub_add_cancel hN]
      rw [pow_succ]
    have hRHS : 3 / centerEndpointRate alpha *
        (centerEndpointRate alpha / centerRho alpha) ^ N
        = 3 * centerEndpointRate alpha ^ (N - 1) / centerRho alpha ^ N := by
      rw [div_pow, hrN]
      field_simp
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hNpos hppos), hRHS,
      div_le_div_iff₀ (mul_pos hNpos hppos) hppos]
    nlinarith [mul_le_mul_of_nonneg_right hEd hppos.le]
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul
      (3 / centerEndpointRate alpha)
    simpa using h

private theorem tendsto_centerNumeratorTerm_mul_denominatorDeriv_normalized
    {alpha : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        centerNumeratorTerm N alpha * centerDenominatorWaveDeriv N alpha /
          ((N : Real) * centerRho alpha ^ N))
      Filter.atTop (nhds 0) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  have hr0 : (0 : Real) ≤ centerEndpointRate alpha := centerEndpointRate_nonneg halpha0
  have hlt : centerEndpointRate alpha < centerRho alpha :=
    centerEndpointRate_lt_centerRho halpha
  refine squeeze_zero_norm'
    (a := fun N : Nat => (2 * ‖centerOmega ^ 2 - 1‖ + 3) * (2 * ‖1 - centerOmega‖ + 3) /
      centerRho alpha * centerRho alpha ^ N) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : Real) < (N : Real) := by exact_mod_cast hN
    have hppos : (0 : Real) < centerRho alpha ^ N := pow_pos hrho0 N
    have hppos' : (0 : Real) < centerRho alpha ^ (N - 1) := pow_pos hrho0 (N - 1)
    have hT : |centerNumeratorTerm N alpha|
        ≤ (2 * ‖centerOmega ^ 2 - 1‖ + 3) * centerRho alpha ^ N :=
      abs_centerNumeratorTerm_le N halpha0 le_rfl (pow_le_pow_left₀ hr0 hlt.le N)
    have hDd : |centerDenominatorWaveDeriv N alpha|
        ≤ (2 * ‖1 - centerOmega‖ + 3) * ((N : Real) * centerRho alpha ^ (N - 1)) :=
      abs_centerDenominatorWaveDeriv_le N halpha le_rfl
        (pow_le_pow_left₀ hr0 hlt.le (N - 1))
    have hrhoN : centerRho alpha ^ N = centerRho alpha ^ (N - 1) * centerRho alpha := by
      conv_lhs => rw [← Nat.sub_add_cancel hN]
      rw [pow_succ]
    have hRHS : (2 * ‖centerOmega ^ 2 - 1‖ + 3) * (2 * ‖1 - centerOmega‖ + 3) /
          centerRho alpha * centerRho alpha ^ N
        = (2 * ‖centerOmega ^ 2 - 1‖ + 3) * (2 * ‖1 - centerOmega‖ + 3) *
          centerRho alpha ^ (N - 1) := by
      rw [hrhoN]
      field_simp
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hNpos hppos), hRHS,
      div_le_iff₀ (mul_pos hNpos hppos), abs_mul]
    calc |centerNumeratorTerm N alpha| * |centerDenominatorWaveDeriv N alpha|
        ≤ ((2 * ‖centerOmega ^ 2 - 1‖ + 3) * centerRho alpha ^ N) *
            ((2 * ‖1 - centerOmega‖ + 3) * ((N : Real) * centerRho alpha ^ (N - 1))) :=
          mul_le_mul hT hDd (abs_nonneg _) (by positivity)
      _ = (2 * ‖centerOmega ^ 2 - 1‖ + 3) * (2 * ‖1 - centerOmega‖ + 3) *
            centerRho alpha ^ (N - 1) * ((N : Real) * centerRho alpha ^ N) := by ring
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hrho0.le hrho1).const_mul
      ((2 * ‖centerOmega ^ 2 - 1‖ + 3) * (2 * ‖1 - centerOmega‖ + 3) / centerRho alpha)
    simpa using h

private theorem abs_centerDerivativeLeadingTerm_normalized_le
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    |centerDerivativeLeadingTerm N alpha / ((N : Real) * centerRho alpha ^ N)|
      ≤ 2 * alpha * ‖centerDerivativeChannelCoefficient alpha‖ := by
  have h2a : (0 : Real) < 2 * alpha := by linarith
  have h1 : |Complex.re (centerDerivativeChannelCoefficient alpha *
      centerUnitChannel alpha ^ N)|
      ≤ ‖centerDerivativeChannelCoefficient alpha * centerUnitChannel alpha ^ N‖ :=
    Complex.abs_re_le_norm _
  have h2 : ‖centerDerivativeChannelCoefficient alpha * centerUnitChannel alpha ^ N‖
      = ‖centerDerivativeChannelCoefficient alpha‖ := by
    rw [norm_mul, norm_pow, norm_centerUnitChannel halpha, one_pow, mul_one]
  rw [centerDerivativeLeadingTerm_normalized hN halpha, abs_mul, abs_of_pos h2a]
  rw [h2] at h1
  exact mul_le_mul_of_nonneg_left h1 h2a.le

theorem tendsto_centerDerivativeError_sub_leading_normalized
    {alpha : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        (centerDerivativeError N alpha - centerDerivativeLeadingTerm N alpha) /
          ((N : Real) * centerRho alpha ^ N))
      Filter.atTop (nhds 0) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  have hD : Filter.Tendsto (fun N : Nat => centerDenominatorWave N alpha)
      Filter.atTop (nhds 1) := tendsto_centerDenominatorWave halpha0
  have hDinv : Filter.Tendsto (fun N : Nat => (centerDenominatorWave N alpha)⁻¹)
      Filter.atTop (nhds 1) := by
    simpa using hD.inv₀ one_ne_zero
  have hA := tendsto_centerNumeratorTerm_normalized halpha
  have hB := tendsto_centerEndpointTermDeriv_normalized halpha
  have hC := tendsto_centerNumeratorTerm_mul_denominatorDeriv_normalized halpha
  have h1 : Filter.Tendsto
      (fun N : Nat =>
        centerNumeratorTerm N alpha / ((N : Real) * centerRho alpha ^ N) *
          (centerDenominatorWave N alpha)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using hA.mul hDinv
  have h2 : Filter.Tendsto
      (fun N : Nat =>
        alpha * (centerEndpointTermDeriv N alpha / ((N : Real) * centerRho alpha ^ N)) *
          (centerDenominatorWave N alpha)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using (hB.const_mul alpha).mul hDinv
  have h3 : Filter.Tendsto
      (fun N : Nat =>
        alpha * (centerNumeratorTerm N alpha * centerDenominatorWaveDeriv N alpha /
            ((N : Real) * centerRho alpha ^ N)) *
          ((centerDenominatorWave N alpha)⁻¹ * (centerDenominatorWave N alpha)⁻¹))
      Filter.atTop (nhds 0) := by
    simpa using (hC.const_mul alpha).mul (hDinv.mul hDinv)
  have habs : Filter.Tendsto
      (fun N : Nat => |1 / centerDenominatorWave N alpha - 1|)
      Filter.atTop (nhds 0) := by
    have h := (hDinv.sub (tendsto_const_nhds (x := (1 : Real)))).abs
    simpa [one_div] using h
  have h4 : Filter.Tendsto
      (fun N : Nat =>
        centerDerivativeLeadingTerm N alpha / ((N : Real) * centerRho alpha ^ N) *
          (1 / centerDenominatorWave N alpha - 1))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm'
      (a := fun N : Nat => 2 * alpha * ‖centerDerivativeChannelCoefficient alpha‖ *
        |1 / centerDenominatorWave N alpha - 1|) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (abs_centerDerivativeLeadingTerm_normalized_le hN halpha0) (abs_nonneg _)
    · have h := habs.const_mul
        (2 * alpha * ‖centerDerivativeChannelCoefficient alpha‖)
      simpa using h
  have htot : Filter.Tendsto
      (fun N : Nat =>
        centerNumeratorTerm N alpha / ((N : Real) * centerRho alpha ^ N) *
            (centerDenominatorWave N alpha)⁻¹ +
          alpha * (centerEndpointTermDeriv N alpha / ((N : Real) * centerRho alpha ^ N)) *
            (centerDenominatorWave N alpha)⁻¹ -
          alpha * (centerNumeratorTerm N alpha * centerDenominatorWaveDeriv N alpha /
              ((N : Real) * centerRho alpha ^ N)) *
            ((centerDenominatorWave N alpha)⁻¹ * (centerDenominatorWave N alpha)⁻¹) +
          centerDerivativeLeadingTerm N alpha / ((N : Real) * centerRho alpha ^ N) *
            (1 / centerDenominatorWave N alpha - 1))
      Filter.atTop (nhds 0) := by
    simpa using ((h1.add h2).sub h3).add h4
  refine htot.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [centerDerivativeError_sub_leading_decomposition hN halpha0]
  ring

theorem eventually_adjacent_centerDerivativeError_guard
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ c : Real, 0 < c ∧
      ∀ᶠ N in Filter.atTop,
        c ≤ max
          (normalizedCenterDerivativeError N alpha)
          (normalizedCenterDerivativeError (N + 1) alpha) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  have hPC : 0 < centerDerivativeProjectionConstant alpha :=
    centerDerivativeProjectionConstant_pos halpha0
  have hrow : ∀ M : Nat, 1 ≤ M →
      |(centerDerivativeError M alpha - centerDerivativeLeadingTerm M alpha) /
          ((M : Real) * centerRho alpha ^ M)|
        ≤ centerDerivativeProjectionConstant alpha / 2 →
      centerDerivativeProjectionConstant alpha ≤
        |2 * alpha * Complex.re (centerDerivativeChannelCoefficient alpha *
          centerUnitChannel alpha ^ M)| →
      centerDerivativeProjectionConstant alpha / 2 ≤
        normalizedCenterDerivativeError M alpha := by
    intro M hM hR hP
    have hMpos : (0 : Real) < (M : Real) := by exact_mod_cast hM
    have hpos : (0 : Real) < (M : Real) * centerRho alpha ^ M := by positivity
    have hL := centerDerivativeLeadingTerm_normalized hM halpha0
    have hsplit : centerDerivativeError M alpha / ((M : Real) * centerRho alpha ^ M)
        = 2 * alpha * Complex.re (centerDerivativeChannelCoefficient alpha *
            centerUnitChannel alpha ^ M) +
          (centerDerivativeError M alpha - centerDerivativeLeadingTerm M alpha) /
            ((M : Real) * centerRho alpha ^ M) := by
      rw [← hL]; ring
    have hnorm : normalizedCenterDerivativeError M alpha
        = |centerDerivativeError M alpha / ((M : Real) * centerRho alpha ^ M)| := by
      unfold normalizedCenterDerivativeError
      rw [abs_div, abs_of_pos hpos]
    rw [hnorm, hsplit]
    have htri : |2 * alpha * Complex.re (centerDerivativeChannelCoefficient alpha *
          centerUnitChannel alpha ^ M)|
        ≤ |2 * alpha * Complex.re (centerDerivativeChannelCoefficient alpha *
              centerUnitChannel alpha ^ M) +
            (centerDerivativeError M alpha - centerDerivativeLeadingTerm M alpha) /
              ((M : Real) * centerRho alpha ^ M)| +
          |(centerDerivativeError M alpha - centerDerivativeLeadingTerm M alpha) /
            ((M : Real) * centerRho alpha ^ M)| := by
      calc |2 * alpha * Complex.re (centerDerivativeChannelCoefficient alpha *
              centerUnitChannel alpha ^ M)|
          = |(2 * alpha * Complex.re (centerDerivativeChannelCoefficient alpha *
                centerUnitChannel alpha ^ M) +
              (centerDerivativeError M alpha - centerDerivativeLeadingTerm M alpha) /
                ((M : Real) * centerRho alpha ^ M)) +
            (-((centerDerivativeError M alpha - centerDerivativeLeadingTerm M alpha) /
                ((M : Real) * centerRho alpha ^ M)))| := by ring_nf
        _ ≤ _ := by
            refine le_trans (abs_add_le _ _) ?_
            rw [abs_neg]
    linarith
  refine ⟨centerDerivativeProjectionConstant alpha / 2, by positivity, ?_⟩
  have hRabs : Filter.Tendsto
      (fun M : Nat =>
        |(centerDerivativeError M alpha - centerDerivativeLeadingTerm M alpha) /
          ((M : Real) * centerRho alpha ^ M)|)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_centerDerivativeError_sub_leading_normalized halpha).abs
  have hev1 : ∀ᶠ M : Nat in Filter.atTop,
      |(centerDerivativeError M alpha - centerDerivativeLeadingTerm M alpha) /
        ((M : Real) * centerRho alpha ^ M)| <
        centerDerivativeProjectionConstant alpha / 2 :=
    hRabs.eventually (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ M : Nat in Filter.atTop, 1 ≤ M :=
    Filter.eventually_atTop.mpr ⟨1, fun M hM => hM⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hev1.and hev2)
  refine Filter.eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hr1, hm1⟩ := hN₀ N hN
  obtain ⟨hr2, hm2⟩ := hN₀ (N + 1) (le_trans hN (Nat.le_succ N))
  rcases le_max_iff.mp (adjacent_centerDerivative_leading_lower N halpha0) with h | h
  · exact le_max_of_le_left (hrow N hm1 hr1.le h)
  · exact le_max_of_le_right (hrow (N + 1) hm2 hr2.le h)

theorem adaptiveDerivativeRow_eq_self_or_succ (N : Nat) (alpha : Real) :
    adaptiveDerivativeRow N alpha = N ∨
      adaptiveDerivativeRow N alpha = N + 1 := by
  unfold adaptiveDerivativeRow
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem le_adaptiveDerivativeRow (N : Nat) (alpha : Real) :
    N ≤ adaptiveDerivativeRow N alpha := by
  unfold adaptiveDerivativeRow
  split_ifs with h
  · exact Nat.le_succ N
  · exact le_rfl

theorem adaptiveDerivativeRow_le_succ (N : Nat) (alpha : Real) :
    adaptiveDerivativeRow N alpha ≤ N + 1 := by
  unfold adaptiveDerivativeRow
  split_ifs with h
  · exact le_rfl
  · exact Nat.le_succ N

theorem normalizedCenterDerivativeError_adaptiveDerivativeRow_eq_max
    (N : Nat) (alpha : Real) :
    normalizedCenterDerivativeError (adaptiveDerivativeRow N alpha) alpha =
      max (normalizedCenterDerivativeError N alpha)
        (normalizedCenterDerivativeError (N + 1) alpha) := by
  unfold adaptiveDerivativeRow
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (not_le.mp h).le).symm

theorem tendsto_adaptiveDerivativeRow (alpha : Real) :
    Filter.Tendsto
      (fun N : Nat => adaptiveDerivativeRow N alpha)
      Filter.atTop Filter.atTop := by
  exact tendsto_atTop_mono (fun N => le_adaptiveDerivativeRow N alpha) tendsto_id

theorem eventually_adaptiveDerivativeRow_normalized_guard
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ c : Real, 0 < c ∧
      ∀ᶠ N in Filter.atTop,
        c ≤ normalizedCenterDerivativeError
          (adaptiveDerivativeRow N alpha) alpha := by
  obtain ⟨c, hc, hev⟩ := eventually_adjacent_centerDerivativeError_guard halpha
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev] with N hN
  rw [normalizedCenterDerivativeError_adaptiveDerivativeRow_eq_max]
  exact hN

theorem eventually_adaptiveDerivativeRow_centerDerivativeError_lower
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ c : Real, 0 < c ∧
      ∀ᶠ N in Filter.atTop,
        c * ((adaptiveDerivativeRow N alpha : Nat) : Real) *
            centerRho alpha ^ (adaptiveDerivativeRow N alpha) ≤
          |centerDerivativeError (adaptiveDerivativeRow N alpha) alpha| := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  have hrho : 0 < centerRho alpha := centerRho_pos halpha0
  obtain ⟨c, hc, hev⟩ := eventually_adaptiveDerivativeRow_normalized_guard halpha
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with N hN hN1
  have hrow : 1 ≤ adaptiveDerivativeRow N alpha :=
    le_trans hN1 (le_adaptiveDerivativeRow N alpha)
  have hMpos : (0 : Real) < ((adaptiveDerivativeRow N alpha : Nat) : Real) := by
    exact_mod_cast hrow
  have hpos : (0 : Real) < ((adaptiveDerivativeRow N alpha : Nat) : Real) *
      centerRho alpha ^ (adaptiveDerivativeRow N alpha) := by positivity
  rw [normalizedCenterDerivativeError, le_div_iff₀ hpos] at hN
  linarith [hN]

theorem eventually_adaptiveDerivativeRow_centerDerivativeError_ne_zero
    {alpha : Real} (halpha : 1 < alpha) :
    ∀ᶠ N in Filter.atTop,
      centerDerivativeError (adaptiveDerivativeRow N alpha) alpha ≠ 0 := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  have hrho : 0 < centerRho alpha := centerRho_pos halpha0
  obtain ⟨c, hc, hev⟩ := eventually_adaptiveDerivativeRow_centerDerivativeError_lower halpha
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with N hN hN1
  have hrow : 1 ≤ adaptiveDerivativeRow N alpha :=
    le_trans hN1 (le_adaptiveDerivativeRow N alpha)
  have hMpos : (0 : Real) < ((adaptiveDerivativeRow N alpha : Nat) : Real) := by
    exact_mod_cast hrow
  have hpos : (0 : Real) < |centerDerivativeError (adaptiveDerivativeRow N alpha) alpha| :=
    lt_of_lt_of_le (by positivity) hN
  exact abs_pos.mp hpos

end SilverFiniteRow
