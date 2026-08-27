/-
Cubic-silver finite-row crossover, Phase B2B: exact center-channel
decomposition and adjacent-row noncancellation.

At the cubic center the two dominant nonprincipal roots-of-unity channels are
complex conjugates `q = (1+t*omega)/(1+t)` and its conjugate, with
`t = alpha⁻¹`, `omega = exp(2*pi*i/3)`, `rho = ‖q‖ < 1`, `r = t/(1+t)`.
Roots-of-unity filtering plus the corrected reversed `k=0` endpoint gives the
EXACT center-error identity (`centerError_channel_formula`, N ≥ 1):
  centerError N alpha
    = alpha * (2*Re((omega^2-1)*q^N) + centerEndpointTerm N alpha)
        / centerDenominatorWave N alpha.
The leading channel is oscillatory. No all-row lower bound is assumed here, and
numerical phase cancellation indicates that such a bound should not generally be
expected. The flagship
`eventually_adjacent_centerError_guard` is the constructive bounded-delay
replacement: eventually at least one of rows N, N+1 has a center error of size
at least `c = alpha*centerProjectionConstant alpha/2 > 0` times its own rho
power, since adjacent projections are separated by one fixed nonzero angle and
cannot cancel simultaneously (generic 2-D bound `adjacent_real_projection_lower`).
-/
import RequestProject.SilverFiniteRowDerivativeBridge
import RequestProject.ReversedRate

open scoped Real Topology BigOperators
open Filter

namespace SilverFiniteRow

noncomputable def centerT (alpha : Real) : Real := alpha⁻¹

noncomputable def centerOmega : Complex :=
  Complex.exp (2 * Real.pi * Complex.I / 3)

noncomputable def centerChannel (alpha : Real) : Complex :=
  (1 + (centerT alpha : Complex) * centerOmega) /
    (1 + centerT alpha)

noncomputable def centerRho (alpha : Real) : Real :=
  norm (centerChannel alpha)

noncomputable def centerEndpointRate (alpha : Real) : Real :=
  centerT alpha / (1 + centerT alpha)

noncomputable def centerEndpointTerm (N : Nat) (alpha : Real) : Real :=
  3 * ResidueSlices.epsIdx 3 N * centerEndpointRate alpha ^ N

noncomputable def centerNumeratorWave (N : Nat) (alpha : Real) : Real :=
  1 + 2 * Complex.re (centerOmega^2 * centerChannel alpha ^ N)

noncomputable def centerDenominatorWave (N : Nat) (alpha : Real) : Real :=
  1 + 2 * Complex.re (centerChannel alpha ^ N) -
    centerEndpointTerm N alpha

noncomputable def centerUnitChannel (alpha : Real) : Complex :=
  centerChannel alpha / centerRho alpha

noncomputable def centerProjectionConstant (alpha : Real) : Real :=
  norm (centerOmega^2 - 1) *
    |Complex.im (centerUnitChannel alpha)| / 4

theorem centerT_pos {alpha : Real} (halpha : 0 < alpha) :
    0 < centerT alpha := by
  unfold centerT
  positivity

theorem centerOmega_isPrimitiveRoot :
    IsPrimitiveRoot centerOmega 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  unfold centerOmega
  convert h using 2
  norm_num

theorem centerChannel_ne_zero
    {alpha : Real} (halpha : 0 < alpha) :
    centerChannel alpha ≠ 0 := by
  have ht : 0 < centerT alpha := centerT_pos halpha
  have hw3 : centerOmega ^ 3 = 1 := centerOmega_isPrimitiveRoot.pow_eq_one
  have hnum : 1 + (centerT alpha : Complex) * centerOmega ≠ 0 := by
    intro h
    have h1 : (centerT alpha : Complex) * centerOmega = -1 := by linear_combination h
    have h2 : ((centerT alpha : Complex)) ^ 3 = -1 := by
      have h5 : ((centerT alpha : Complex) * centerOmega) ^ 3 = (-1 : Complex) ^ 3 := by rw [h1]
      rw [mul_pow, hw3, mul_one] at h5
      rw [h5]; ring
    have h3 : ((centerT alpha ^ 3 : Real) : Complex) = ((-1 : Real) : Complex) := by
      push_cast; simpa using h2
    have h4 : centerT alpha ^ 3 = -1 := by exact_mod_cast h3
    nlinarith [pow_pos ht 3]
  have hden : (1 + (centerT alpha : Complex)) ≠ 0 := by
    have h6 : ((1 + centerT alpha : Real) : Complex) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    push_cast at h6
    exact h6
  exact div_ne_zero hnum hden

theorem centerRho_pos
    {alpha : Real} (halpha : 0 < alpha) :
    0 < centerRho alpha := by
  unfold centerRho
  exact norm_pos_iff.mpr (centerChannel_ne_zero halpha)

theorem packetRatio_center_numerator_wave
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    ResidueSlices.slice 3 1 N ((centerT alpha)^3) =
      (1 + centerT alpha)^N /
        (3 * centerT alpha) * centerNumeratorWave N alpha := by
  have _ : 1 ≤ N := hN
  have ht : 0 < centerT alpha := centerT_pos halpha
  set t := centerT alpha with hTdef
  have hone : centerOmega ^ 3 = 1 := centerOmega_isPrimitiveRoot.pow_eq_one
  have hw0 : centerOmega ≠ 0 := by intro h; rw [h] at hone; simp at hone
  have hnorm : norm centerOmega = 1 := by
    have h1 : norm centerOmega ^ 3 = 1 := by rw [← norm_pow, hone, norm_one]
    nlinarith [norm_nonneg centerOmega, sq_nonneg (norm centerOmega - 1),
      sq_nonneg (norm centerOmega + 1)]
  have hconj : (starRingEnd Complex) centerOmega = centerOmega ^ 2 := by
    have hns : Complex.normSq centerOmega = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
    have h2 : centerOmega * (starRingEnd Complex) centerOmega = 1 := by
      rw [Complex.mul_conj, hns, Complex.ofReal_one]
    have h3 : centerOmega * centerOmega ^ 2 = 1 := by rw [← pow_succ']; exact hone
    exact mul_left_cancel₀ hw0 (h2.trans h3.symm)
  have hw4 : centerOmega ^ 4 = centerOmega := by
    rw [show (4:Nat) = 3 + 1 from rfl, pow_succ, hone, one_mul]
  have hden : (1 : Complex) + (t : Complex) ≠ 0 := by
    have h6 : ((1 + t : Real) : Complex) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
    push_cast at h6; exact h6
  have hcpow : (1 + (t : Complex) * centerOmega)^N
      = centerChannel alpha ^ N * (1 + (t : Complex))^N := by
    unfold centerChannel
    rw [← mul_pow, div_mul_cancel₀]
    exact hden
  have hfilter := ResidueSlices.roots_of_unity_filter (g := 3) (k := 1) (N := N)
    (by norm_num) (by norm_num) centerOmega_isPrimitiveRoot ((t : Real) : Complex)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hfilter
  have e1 : centerOmega ^ (2 * (3 - 1)) = centerOmega := by
    rw [show 2 * (3 - 1) = 4 from rfl, hw4]
  have e2 : centerOmega ^ (1 * (3 - 1)) = centerOmega ^ 2 := by norm_num
  have hpair : centerOmega ^ (2 * (3 - 1)) * (1 + (t : Complex) * centerOmega ^ 2) ^ N
      = (starRingEnd Complex)
          (centerOmega ^ (1 * (3 - 1)) * (1 + (t : Complex) * centerOmega ^ 1) ^ N) := by
    rw [e1, e2, map_mul, map_pow, map_pow, map_add, map_one, map_mul, hconj, Complex.conj_ofReal,
      pow_one, show (centerOmega^2)^2 = centerOmega ^ 4 by ring, hw4, hconj]
  have hzval : centerOmega ^ (1 * (3 - 1)) * (1 + (t : Complex) * centerOmega ^ 1) ^ N
      = (((1 + t)^N : Real) : Complex) * (centerOmega ^ 2 * centerChannel alpha ^ N) := by
    rw [e2, pow_one, hcpow]
    push_cast
    ring
  have hfirst : centerOmega ^ (0 * (3 - 1)) * (1 + (t : Complex) * centerOmega ^ 0) ^ N
      = (((1 + t)^N : Real) : Complex) := by
    push_cast
    norm_num
  rw [hpair, hzval, hfirst, add_assoc, Complex.add_conj, Complex.re_ofReal_mul,
    show ((t : Complex))^3 = (((t^3 : Real)) : Complex) by push_cast; ring,
    ResidueSlices.slice_ofReal] at hfilter
  have hreal : (1 + t)^N + 2 * ((1 + t)^N * Complex.re (centerOmega ^ 2 * centerChannel alpha ^ N))
      = 3 * t * ResidueSlices.slice 3 1 N (t^3) := by
    have h7 := hfilter
    rw [pow_one] at h7
    exact_mod_cast h7
  unfold centerNumeratorWave
  field_simp
  linarith [hreal]

theorem packetRatio_center_denominator_wave
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    ResidueSlices.slice 3 0 N ((centerT alpha)^3) -
        ResidueSlices.epsIdx 3 N *
          ((centerT alpha)^3) ^ (ResidueSlices.qIdx 3 N + 1) =
      (1 + centerT alpha)^N / 3 *
        centerDenominatorWave N alpha := by
  have ht : 0 < centerT alpha := centerT_pos halpha
  set t := centerT alpha with hTdef
  have hone : centerOmega ^ 3 = 1 := centerOmega_isPrimitiveRoot.pow_eq_one
  have hw0 : centerOmega ≠ 0 := by intro h; rw [h] at hone; simp at hone
  have hnorm : norm centerOmega = 1 := by
    have h1 : norm centerOmega ^ 3 = 1 := by rw [← norm_pow, hone, norm_one]
    nlinarith [norm_nonneg centerOmega, sq_nonneg (norm centerOmega - 1),
      sq_nonneg (norm centerOmega + 1)]
  have hconj : (starRingEnd Complex) centerOmega = centerOmega ^ 2 := by
    have hns : Complex.normSq centerOmega = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
    have h2 : centerOmega * (starRingEnd Complex) centerOmega = 1 := by
      rw [Complex.mul_conj, hns, Complex.ofReal_one]
    have h3 : centerOmega * centerOmega ^ 2 = 1 := by rw [← pow_succ']; exact hone
    exact mul_left_cancel₀ hw0 (h2.trans h3.symm)
  have hden : (1 : Complex) + (t : Complex) ≠ 0 := by
    have h6 : ((1 + t : Real) : Complex) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
    push_cast at h6; exact h6
  have hcpow : (1 + (t : Complex) * centerOmega)^N
      = centerChannel alpha ^ N * (1 + (t : Complex))^N := by
    unfold centerChannel
    rw [← mul_pow, div_mul_cancel₀]
    exact hden
  have hfilter := ResidueSlices.roots_of_unity_filter (g := 3) (k := 0) (N := N)
    (by norm_num) (by norm_num) centerOmega_isPrimitiveRoot ((t : Real) : Complex)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hfilter
  have e0 : centerOmega ^ (0 * (3 - 0)) = 1 := by norm_num
  have e1 : centerOmega ^ (1 * (3 - 0)) = 1 := by
    rw [show 1 * (3 - 0) = 3 from rfl, hone]
  have e2 : centerOmega ^ (2 * (3 - 0)) = 1 := by
    rw [show 2 * (3 - 0) = 6 from rfl, show (6:Nat) = 3 * 2 from rfl, pow_mul, hone, one_pow]
  have hpair : (1 + (t : Complex) * centerOmega ^ 2) ^ N
      = (starRingEnd Complex) ((1 + (t : Complex) * centerOmega ^ 1) ^ N) := by
    rw [map_pow, map_add, map_one, map_mul, map_pow, hconj, Complex.conj_ofReal, pow_one]
  have hzval : (1 + (t : Complex) * centerOmega ^ 1) ^ N
      = (((1 + t)^N : Real) : Complex) * (centerChannel alpha ^ N) := by
    rw [pow_one, hcpow]
    push_cast
    ring
  have hfirst : (1 + (t : Complex) * 1) ^ N = (((1 + t)^N : Real) : Complex) := by
    push_cast; norm_num
  rw [e0, e1, e2, one_mul, one_mul, one_mul, hpair, hzval, hfirst, add_assoc, Complex.add_conj,
    show ((t : Complex))^3 = (((t^3 : Real)) : Complex) by push_cast; ring,
    ResidueSlices.slice_ofReal] at hfilter
  have hreal : (1 + t)^N + 2 * Complex.re ((((1 + t)^N : Real) : Complex) * centerChannel alpha ^ N)
      = 3 * ResidueSlices.slice 3 0 N (t^3) := by
    have h7 := hfilter
    rw [pow_zero, mul_one] at h7
    exact_mod_cast h7
  rw [Complex.re_ofReal_mul] at hreal
  have hendpoint : ResidueSlices.epsIdx 3 N * (t^3) ^ (ResidueSlices.qIdx 3 N + 1)
      = (1 + t)^N * (ResidueSlices.epsIdx 3 N * centerEndpointRate alpha ^ N) := by
    unfold ResidueSlices.epsIdx centerEndpointRate
    rw [← hTdef]
    split_ifs with hdvd
    · have hq : ResidueSlices.qIdx 3 N + 1 = N / 3 := by unfold ResidueSlices.qIdx; omega
      rw [hq, ← pow_mul, show 3 * (N / 3) = N by omega, div_pow]
      field_simp
    · simp
  rw [hendpoint]
  unfold centerDenominatorWave centerEndpointTerm centerEndpointRate
  rw [← hTdef]
  have hpos : (0:Real) < (1 + t)^N := by positivity
  field_simp
  linarith [hreal]

theorem centerDenominatorWave_pos
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    0 < centerDenominatorWave N alpha := by
  have ht : 0 < centerT alpha := centerT_pos halpha
  have hx : (0:Real) < alpha ^ 3 := by positivity
  have hinv : (alpha^3)⁻¹ = (centerT alpha)^3 := by unfold centerT; rw [inv_pow]
  have hrevB := ResidueSlices.revB_eq_slice (g := 3) (N := N) (by norm_num) hN hx
  rw [hinv] at hrevB
  have hrevpos : 0 < ResidueSlices.revA 3 0 N (alpha^3) := packetRatio_den_pos N hx
  have hpow : (0:Real) < (alpha^3) ^ ResidueSlices.qIdx 3 N := by positivity
  have hkey : 0 < ResidueSlices.slice 3 0 N ((centerT alpha)^3)
      - ResidueSlices.epsIdx 3 N * ((centerT alpha)^3) ^ (ResidueSlices.qIdx 3 N + 1) := by
    rw [hrevB] at hrevpos
    nlinarith [hrevpos, hpow]
  rw [packetRatio_center_denominator_wave hN halpha] at hkey
  have hpos : (0:Real) < (1 + centerT alpha)^N / 3 := by positivity
  nlinarith [hkey, hpos]

theorem packetRatio_center_channel_formula
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    packetRatio N (alpha^3) =
      alpha * centerNumeratorWave N alpha /
        centerDenominatorWave N alpha := by
  have ht : 0 < centerT alpha := centerT_pos halpha
  have hx : (0:Real) < alpha ^ 3 := by positivity
  have hinv : (alpha^3)⁻¹ = (centerT alpha)^3 := by unfold centerT; rw [inv_pow]
  have hpow : (0:Real) < (alpha^3) ^ ResidueSlices.qIdx 3 N := by positivity
  have hden : 0 < centerDenominatorWave N alpha := centerDenominatorWave_pos hN halpha
  have hat : alpha * centerT alpha = 1 := by unfold centerT; field_simp
  unfold packetRatio
  rw [ResidueSlices.revA_eq_slice (g := 3) (k := 1) (N := N) (by norm_num) (le_refl 1)
      (by norm_num) hx,
    ResidueSlices.revB_eq_slice (g := 3) (N := N) (by norm_num) hN hx, hinv,
    packetRatio_center_numerator_wave hN halpha, packetRatio_center_denominator_wave hN halpha,
    mul_div_mul_left _ _ (ne_of_gt hpow)]
  have hpos : (0:Real) < (1 + centerT alpha)^N := by positivity
  field_simp
  linear_combination (-centerNumeratorWave N alpha) * hat

theorem centerError_channel_formula
    {N : Nat} (hN : 1 ≤ N) {alpha : Real} (halpha : 0 < alpha) :
    centerError N alpha =
      alpha *
        (2 * Complex.re
            ((centerOmega^2 - 1) * centerChannel alpha ^ N) +
          centerEndpointTerm N alpha) /
        centerDenominatorWave N alpha := by
  have hden : 0 < centerDenominatorWave N alpha := centerDenominatorWave_pos hN halpha
  have hD : centerDenominatorWave N alpha ≠ 0 := ne_of_gt hden
  have hre : Complex.re ((centerOmega^2 - 1) * centerChannel alpha ^ N)
      = Complex.re (centerOmega^2 * centerChannel alpha ^ N)
        - Complex.re (centerChannel alpha ^ N) := by
    rw [sub_mul, Complex.sub_re, one_mul]
  have hnum : centerNumeratorWave N alpha - centerDenominatorWave N alpha
      = 2 * Complex.re ((centerOmega^2 - 1) * centerChannel alpha ^ N)
        + centerEndpointTerm N alpha := by
    rw [hre]
    unfold centerNumeratorWave centerDenominatorWave
    ring
  unfold centerError
  rw [packetRatio_center_channel_formula hN halpha, ← hnum]
  field_simp

theorem centerRho_mem_unitInterval
    {alpha : Real} (halpha : 0 < alpha) :
    0 < centerRho alpha ∧ centerRho alpha < 1 := by
  refine ⟨centerRho_pos halpha, ?_⟩
  have ht : 0 < centerT alpha := centerT_pos halpha
  have hw3 : centerOmega ^ 3 = 1 := centerOmega_isPrimitiveRoot.pow_eq_one
  have hnorm : norm centerOmega = 1 := by
    have h1 : norm centerOmega ^ 3 = 1 := by rw [← norm_pow, hw3, norm_one]
    nlinarith [norm_nonneg centerOmega, sq_nonneg (norm centerOmega - 1),
      sq_nonneg (norm centerOmega + 1)]
  have hne1 : centerOmega ≠ 1 := centerOmega_isPrimitiveRoot.ne_one (by norm_num)
  have key := ResidueSlices.norm_one_add_pos_mul_lt hnorm hne1 ht
  have hd : norm ((1 : Complex) + (centerT alpha : Complex)) = 1 + centerT alpha := by
    have h2 : ((1 + centerT alpha : Real) : Complex) = 1 + (centerT alpha : Complex) := by
      push_cast; ring
    rw [← h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  unfold centerRho centerChannel
  rw [Complex.norm_div, hd, div_lt_one (by positivity)]
  exact key

theorem centerEndpointRate_nonneg
    {alpha : Real} (halpha : 0 < alpha) :
    0 ≤ centerEndpointRate alpha := by
  have ht : 0 < centerT alpha := centerT_pos halpha
  unfold centerEndpointRate
  positivity

theorem centerEndpointRate_lt_one
    {alpha : Real} (halpha : 0 < alpha) :
    centerEndpointRate alpha < 1 := by
  have ht : 0 < centerT alpha := centerT_pos halpha
  unfold centerEndpointRate
  rw [div_lt_one (by positivity)]
  linarith

theorem centerEndpointRate_lt_centerRho
    {alpha : Real} (halpha : 1 < alpha) :
    centerEndpointRate alpha < centerRho alpha := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  have ht : 0 < centerT alpha := centerT_pos halpha0
  have ht1 : centerT alpha < 1 := by
    unfold centerT
    rw [inv_lt_one_iff₀]
    right
    exact halpha
  have hcomp : centerOmega.re = -(1/2) ∧ centerOmega.im = Real.sqrt 3 / 2 := by
    have h : (2 * (Real.pi : Complex) * Complex.I / 3)
        = ((2 * Real.pi / 3 : Real) : Complex) * Complex.I := by
      push_cast; ring
    unfold centerOmega
    rw [h, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    refine ⟨?_, ?_⟩
    · rw [show (2 * Real.pi / 3 : Real) = Real.pi - Real.pi/3 by ring, Real.cos_pi_sub,
        Real.cos_pi_div_three]
    · rw [show (2 * Real.pi / 3 : Real) = Real.pi - Real.pi/3 by ring, Real.sin_pi_sub,
        Real.sin_pi_div_three]
  obtain ⟨hre, him⟩ := hcomp
  set t := centerT alpha with hT
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnum2 : norm (1 + (t : Complex) * centerOmega) ^ 2 = 1 - t + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      hre, him]
    nlinarith [hs3]
  have hd : norm ((1 : Complex) + (t : Complex)) = 1 + t := by
    have h2 : ((1 + t : Real) : Complex) = 1 + (t : Complex) := by push_cast; ring
    rw [← h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hrho2 : centerRho alpha ^ 2 = (1 - t + t ^ 2) / (1 + t) ^ 2 := by
    unfold centerRho centerChannel
    rw [Complex.norm_div, div_pow, hnum2, hd]
  have hr : centerEndpointRate alpha = t / (1 + t) := rfl
  have hrnn : 0 ≤ centerEndpointRate alpha := by rw [hr]; positivity
  have hrhonn : 0 ≤ centerRho alpha := norm_nonneg _
  have hsq : centerEndpointRate alpha ^ 2 < centerRho alpha ^ 2 := by
    rw [hrho2, hr, div_pow]
    gcongr
    linarith
  nlinarith [hsq, hrnn, hrhonn]

theorem norm_centerUnitChannel
    {alpha : Real} (halpha : 0 < alpha) :
    norm (centerUnitChannel alpha) = 1 := by
  have hrho : 0 < centerRho alpha := centerRho_pos halpha
  unfold centerUnitChannel
  rw [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho]
  exact div_self hrho.ne'

theorem centerUnitChannel_im_ne_zero
    {alpha : Real} (halpha : 0 < alpha) :
    Complex.im (centerUnitChannel alpha) ≠ 0 := by
  have hrho : 0 < centerRho alpha := centerRho_pos halpha
  have ht : 0 < centerT alpha := centerT_pos halpha
  have him : centerOmega.im = Real.sqrt 3 / 2 := by
    have h : (2 * (Real.pi : Complex) * Complex.I / 3)
        = ((2 * Real.pi / 3 : Real) : Complex) * Complex.I := by
      push_cast; ring
    unfold centerOmega
    rw [h, Complex.exp_ofReal_mul_I_im,
      show (2 * Real.pi / 3 : Real) = Real.pi - Real.pi/3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  have hc : centerChannel alpha
      = (((1 + centerT alpha)⁻¹ : Real) : Complex) * (1 + (centerT alpha : Complex) * centerOmega) := by
    unfold centerChannel
    push_cast
    field_simp
  have hcim : (centerChannel alpha).im
      = (1 + centerT alpha)⁻¹ * (centerT alpha * (Real.sqrt 3 / 2)) := by
    rw [hc, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, him]
    simp
  unfold centerUnitChannel
  rw [Complex.div_ofReal_im, hcim]
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  positivity

theorem centerProjectionConstant_pos
    {alpha : Real} (halpha : 0 < alpha) :
    0 < centerProjectionConstant alpha := by
  have h1 : centerOmega ^ 2 - 1 ≠ 0 := by
    have h2 : centerOmega ^ 2 ≠ 1 :=
      centerOmega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    exact sub_ne_zero.mpr h2
  have h3 : 0 < norm (centerOmega ^ 2 - 1) := norm_pos_iff.mpr h1
  have h4 : 0 < |Complex.im (centerUnitChannel alpha)| :=
    abs_pos.mpr (centerUnitChannel_im_ne_zero halpha)
  unfold centerProjectionConstant
  positivity

theorem adjacent_real_projection_lower
    {A u z : Complex}
    (hu : norm u = 1) (hz : norm z = 1) :
    norm A * |Complex.im u| / 4 ≤
      max |Complex.re (A * z)| |Complex.re (A * z * u)| := by
  set P := max |Complex.re (A * z)| |Complex.re (A * z * u)| with hP
  have hP0 : 0 ≤ P := le_trans (abs_nonneg _) (le_max_left _ _)
  have h1 : |Complex.re (A * z)| ≤ P := le_max_left _ _
  have h2 : |Complex.re (A * z * u)| ≤ P := le_max_right _ _
  have hAz : norm (A * z) = norm A := by rw [norm_mul, hz, mul_one]
  have hsplit : norm A ≤ |(A * z).re| + |(A * z).im| := by
    rw [← hAz]; exact Complex.norm_le_abs_re_add_abs_im _
  have hur : |u.re| ≤ 1 := by rw [← hu]; exact Complex.abs_re_le_norm u
  have hui : |u.im| ≤ 1 := by rw [← hu]; exact Complex.abs_im_le_norm u
  have hmul : (A * z * u).re = (A * z).re * u.re - (A * z).im * u.im := Complex.mul_re _ _
  have hprod1 : |(A * z).re * u.re| ≤ P := by
    rw [abs_mul]
    calc |(A * z).re| * |u.re| ≤ P * 1 := mul_le_mul h1 hur (abs_nonneg _) hP0
      _ = P := mul_one P
  have hyu : |(A * z).im * u.im| ≤ 2 * P := by
    have e : (A * z).im * u.im = (A * z).re * u.re - (A * z * u).re := by rw [hmul]; ring
    calc |(A * z).im * u.im| = |(A * z).re * u.re - (A * z * u).re| := by rw [e]
      _ ≤ |(A * z).re * u.re| + |(A * z * u).re| := abs_sub _ _
      _ ≤ P + P := add_le_add hprod1 h2
      _ = 2 * P := by ring
  have hxu : |(A * z).re * u.im| ≤ P := by
    rw [abs_mul]
    calc |(A * z).re| * |u.im| ≤ P * 1 := mul_le_mul h1 hui (abs_nonneg _) hP0
      _ = P := mul_one P
  have hfinal : norm A * |u.im| ≤ 3 * P := by
    calc norm A * |u.im| ≤ (|(A * z).re| + |(A * z).im|) * |u.im| :=
          mul_le_mul_of_nonneg_right hsplit (abs_nonneg u.im)
      _ = |(A * z).re * u.im| + |(A * z).im * u.im| := by rw [abs_mul, abs_mul]; ring
      _ ≤ P + 2 * P := add_le_add hxu hyu
      _ = 3 * P := by ring
  linarith

theorem adjacent_center_projection_lower
    (N : Nat) {alpha : Real} (halpha : 0 < alpha) :
    centerProjectionConstant alpha ≤
      max
        |Complex.re
          ((centerOmega^2 - 1) * centerUnitChannel alpha ^ N)|
        |Complex.re
          ((centerOmega^2 - 1) *
            centerUnitChannel alpha ^ (N + 1))| := by
  have hu : norm (centerUnitChannel alpha) = 1 := norm_centerUnitChannel halpha
  have hz : norm (centerUnitChannel alpha ^ N) = 1 := by rw [norm_pow, hu, one_pow]
  have key := adjacent_real_projection_lower (A := centerOmega^2 - 1)
    (u := centerUnitChannel alpha) (z := centerUnitChannel alpha ^ N) hu hz
  have he : (centerOmega^2 - 1) * centerUnitChannel alpha ^ N * centerUnitChannel alpha
      = (centerOmega^2 - 1) * centerUnitChannel alpha ^ (N + 1) := by
    rw [pow_succ]; ring
  rw [he] at key
  exact key

theorem tendsto_centerDenominatorWave
    {alpha : Real} (halpha : 0 < alpha) :
    Filter.Tendsto
      (fun N : Nat => centerDenominatorWave N alpha)
      Filter.atTop (nhds 1) := by
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha
  have heps : ∀ N : Nat, 0 ≤ ResidueSlices.epsIdx 3 N ∧ ResidueSlices.epsIdx 3 N ≤ 1 := by
    intro N; unfold ResidueSlices.epsIdx; split_ifs <;> norm_num
  have hrnn : (0:Real) ≤ centerEndpointRate alpha := centerEndpointRate_nonneg halpha
  have h1 : Tendsto (fun N : Nat => Complex.re (centerChannel alpha ^ N)) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun N : Nat => centerRho alpha ^ N)
    · intro n
      rw [Real.norm_eq_abs]
      calc |Complex.re (centerChannel alpha ^ n)| ≤ norm (centerChannel alpha ^ n) :=
            Complex.abs_re_le_norm _
        _ = centerRho alpha ^ n := by rw [norm_pow]; rfl
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one hrho0.le hrho1
  have h2 : Tendsto (fun N : Nat => centerEndpointTerm N alpha) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun N : Nat => 3 * centerEndpointRate alpha ^ N)
    · intro n
      rw [Real.norm_eq_abs]
      unfold centerEndpointTerm
      have h3 : (0:Real) ≤ centerEndpointRate alpha ^ n := pow_nonneg hrnn n
      rw [abs_of_nonneg (by have := (heps n).1; positivity)]
      nlinarith [(heps n).1, (heps n).2]
    · have h4 := tendsto_pow_atTop_nhds_zero_of_lt_one hrnn (centerEndpointRate_lt_one halpha)
      simpa using h4.const_mul (3:Real)
  have h5 := ((tendsto_const_nhds (x := (1:Real)) (f := atTop (α := Nat))).add
    (h1.const_mul 2)).sub h2
  simpa [centerDenominatorWave] using h5

theorem tendsto_centerEndpointTerm_div_rho_pow
    {alpha : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        centerEndpointTerm N alpha / centerRho alpha ^ N)
      Filter.atTop (nhds 0) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  have hrnn : (0:Real) ≤ centerEndpointRate alpha := centerEndpointRate_nonneg halpha0
  have hlt : centerEndpointRate alpha < centerRho alpha := centerEndpointRate_lt_centerRho halpha
  have hq0 : (0:Real) ≤ centerEndpointRate alpha / centerRho alpha := by positivity
  have hq1 : centerEndpointRate alpha / centerRho alpha < 1 := (div_lt_one hrho0).mpr hlt
  have heps : ∀ N : Nat, 0 ≤ ResidueSlices.epsIdx 3 N ∧ ResidueSlices.epsIdx 3 N ≤ 1 := by
    intro N; unfold ResidueSlices.epsIdx; split_ifs <;> norm_num
  apply squeeze_zero_norm
    (a := fun N : Nat => 3 * (centerEndpointRate alpha / centerRho alpha) ^ N)
  · intro n
    have hrpos : (0:Real) < centerRho alpha ^ n := pow_pos hrho0 n
    have hval : centerEndpointTerm n alpha / centerRho alpha ^ n
        = 3 * ResidueSlices.epsIdx 3 n * (centerEndpointRate alpha / centerRho alpha) ^ n := by
      unfold centerEndpointTerm
      rw [div_pow]
      field_simp
    rw [Real.norm_eq_abs, hval]
    have h3 : (0:Real) ≤ (centerEndpointRate alpha / centerRho alpha) ^ n := pow_nonneg hq0 n
    rw [abs_of_nonneg (by have := (heps n).1; positivity)]
    nlinarith [(heps n).1, (heps n).2]
  · have h4 := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    simpa using h4.const_mul (3:Real)

theorem eventually_adjacent_centerError_guard
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ c : Real, 0 < c ∧
      ∀ᶠ N in Filter.atTop,
        c ≤ max
          (|centerError N alpha| / centerRho alpha ^ N)
          (|centerError (N + 1) alpha| /
            centerRho alpha ^ (N + 1)) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  have hP : 0 < centerProjectionConstant alpha := centerProjectionConstant_pos halpha0
  have hrne : ((centerRho alpha : Real) : Complex) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hrho0.ne'
  have hrow : ∀ M : Nat, 1 ≤ M → centerDenominatorWave M alpha < 2 →
      |centerEndpointTerm M alpha / centerRho alpha ^ M| < centerProjectionConstant alpha / 2 →
      centerProjectionConstant alpha
          ≤ |Complex.re ((centerOmega^2 - 1) * centerUnitChannel alpha ^ M)| →
      alpha * centerProjectionConstant alpha / 2
        ≤ |centerError M alpha| / centerRho alpha ^ M := by
    intro M hM hD2 hdelta hS
    have hD : 0 < centerDenominatorWave M alpha := centerDenominatorWave_pos hM halpha0
    have hrpow : (0:Real) < centerRho alpha ^ M := pow_pos hrho0 M
    set S := Complex.re ((centerOmega^2 - 1) * centerUnitChannel alpha ^ M) with hSdef
    set d := centerEndpointTerm M alpha / centerRho alpha ^ M with hddef
    have hcu : centerChannel alpha = (centerRho alpha : Complex) * centerUnitChannel alpha := by
      unfold centerUnitChannel
      field_simp
    have hre : Complex.re ((centerOmega^2 - 1) * centerChannel alpha ^ M)
        = centerRho alpha ^ M * S := by
      rw [hcu, mul_pow, ← mul_assoc,
        mul_comm ((centerOmega^2 - 1)) (((centerRho alpha : Complex))^M), mul_assoc,
        ← Complex.ofReal_pow, Complex.re_ofReal_mul, hSdef]
    have hkey : centerError M alpha
        = alpha * (centerRho alpha ^ M * (2 * S + d)) / centerDenominatorWave M alpha := by
      rw [centerError_channel_formula hM halpha0, hre, hddef]
      field_simp
    have habs : |centerError M alpha| / centerRho alpha ^ M
        = alpha * |2 * S + d| / centerDenominatorWave M alpha := by
      rw [hkey, abs_div, abs_of_pos hD, abs_mul, abs_mul, abs_of_pos halpha0, abs_of_pos hrpow]
      field_simp
    rw [habs]
    have h1 : |2 * S| ≤ |2 * S + d| + |d| := by
      calc |2 * S| = |(2 * S + d) + (-d)| := by ring_nf
        _ ≤ |2 * S + d| + |(-d)| := abs_add_le _ _
        _ = |2 * S + d| + |d| := by rw [abs_neg]
    have h3 : |2 * S| = 2 * |S| := by rw [abs_mul]; norm_num
    have hbound : centerProjectionConstant alpha ≤ |2 * S + d| := by linarith
    rw [le_div_iff₀ hD]
    have hc : (0:Real) < alpha * centerProjectionConstant alpha / 2 := by positivity
    linarith [mul_le_mul_of_nonneg_left hbound halpha0.le, mul_lt_mul_of_pos_left hD2 hc]
  refine ⟨alpha * centerProjectionConstant alpha / 2, by positivity, ?_⟩
  have hev1 : ∀ᶠ M : Nat in atTop, centerDenominatorWave M alpha < 2 :=
    (tendsto_centerDenominatorWave halpha0).eventually (gt_mem_nhds (by norm_num))
  have habs0 : Tendsto (fun M : Nat => |centerEndpointTerm M alpha / centerRho alpha ^ M|)
      atTop (nhds 0) := by
    simpa using (tendsto_centerEndpointTerm_div_rho_pow halpha).abs
  have hev2 : ∀ᶠ M : Nat in atTop,
      |centerEndpointTerm M alpha / centerRho alpha ^ M| < centerProjectionConstant alpha / 2 :=
    habs0.eventually (gt_mem_nhds (by positivity))
  have hev3 : ∀ᶠ M : Nat in atTop, 1 ≤ M := eventually_atTop.mpr ⟨1, fun M hM => hM⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hev1.and (hev2.and hev3))
  refine eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hd1, he1, hm1⟩ := hN₀ N hN
  obtain ⟨hd2, he2, hm2⟩ := hN₀ (N + 1) (le_trans hN (Nat.le_succ N))
  rcases le_max_iff.mp (adjacent_center_projection_lower N halpha0) with h | h
  · exact le_max_of_le_left (hrow N hm1 hd1 he1 h)
  · exact le_max_of_le_right (hrow (N + 1) hm2 hd2 he2 h)

end SilverFiniteRow
