/-
Cubic-silver finite-row crossover, Phase B2C: local derivative spectral rate.
-/
import RequestProject.SilverFiniteRowAdjacentGuard

open scoped Real Topology BigOperators
open Filter

namespace SilverFiniteRow

noncomputable def centerHalfRate (alpha : Real) : Real :=
  Real.sqrt (centerRho alpha)

noncomputable def localDerivativeRate (alpha : Real) : Real :=
  (centerRho alpha + centerHalfRate alpha) / 2

theorem localDerivativeRate_separation
    {alpha : Real} (halpha : 0 < alpha) :
    centerRho alpha < localDerivativeRate alpha ∧
    localDerivativeRate alpha < centerHalfRate alpha ∧
    centerHalfRate alpha < 1 := by
  obtain ⟨h0, h1⟩ := centerRho_mem_unitInterval halpha
  have hsq : Real.sqrt (centerRho alpha) * Real.sqrt (centerRho alpha) = centerRho alpha :=
    Real.mul_self_sqrt h0.le
  have hspos : 0 < Real.sqrt (centerRho alpha) := Real.sqrt_pos.mpr h0
  have hs1 : Real.sqrt (centerRho alpha) < 1 := by
    nlinarith [hsq, hspos]
  have hlt : centerRho alpha < Real.sqrt (centerRho alpha) := by
    nlinarith [hsq, hspos, hs1]
  refine ⟨?_, ?_, ?_⟩
  · unfold localDerivativeRate centerHalfRate
    linarith
  · unfold localDerivativeRate centerHalfRate
    linarith
  · unfold centerHalfRate
    exact hs1

theorem centerHalfRate_pos
    {alpha : Real} (halpha : 0 < alpha) :
    0 < centerHalfRate alpha := by
  unfold centerHalfRate
  exact Real.sqrt_pos.mpr (centerRho_pos halpha)

theorem localDerivativeRate_pos
    {alpha : Real} (halpha : 0 < alpha) :
    0 < localDerivativeRate alpha := by
  have h1 : 0 < centerRho alpha := centerRho_pos halpha
  have h2 : 0 < centerHalfRate alpha := centerHalfRate_pos halpha
  unfold localDerivativeRate
  linarith

theorem localDerivativeRate_lt_one
    {alpha : Real} (halpha : 0 < alpha) :
    localDerivativeRate alpha < 1 := by
  obtain ⟨_, h2, h3⟩ := localDerivativeRate_separation halpha
  linarith

/-- On the positive axis the center error is the packet error function of the cube. -/
theorem centerError_eq_packetErrorFunction
    (N : Nat) {gamma : Real} (hgamma : 0 < gamma) :
    centerError N gamma = packetErrorFunction N (gamma ^ 3) := by
  have hval : (gamma ^ 3 : Real) ^ ((3 : Real)⁻¹) = gamma := by
    rw [show (gamma ^ 3 : Real) = gamma ^ ((3 : ℕ) : Real) by rw [Real.rpow_natCast]]
    rw [← Real.rpow_mul hgamma.le]
    norm_num
  rw [packetErrorFunction, centerError, hval]

theorem hasDerivAt_centerError_parameter
    (N : Nat) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt
      (fun gamma : Real => centerError N gamma)
      (3 * beta^2 * packetErrorDerivative N (beta^3)) beta := by
  have hcube : HasDerivAt (fun gamma : Real => gamma ^ 3) (3 * beta ^ 2) beta := by
    simpa using hasDerivAt_pow 3 beta
  have h3 : HasDerivAt (fun gamma : Real => packetErrorFunction N (gamma ^ 3))
      (packetErrorDerivative N (beta ^ 3) * (3 * beta ^ 2)) beta :=
    HasDerivAt.comp (h := fun gamma : Real => gamma ^ 3) beta
      (hasDerivAt_packetErrorFunction N (pow_pos hbeta 3)) hcube
  have h2 : HasDerivAt (fun gamma : Real => packetErrorFunction N (gamma ^ 3))
      (3 * beta ^ 2 * packetErrorDerivative N (beta ^ 3)) beta := by
    rw [mul_comm] at h3
    exact h3
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hbeta] with g hg
  exact centerError_eq_packetErrorFunction N hg

/-! ### The center channel as an explicit function of the parameter -/

noncomputable def centerChannelDeriv (beta : Real) : Complex :=
  (1 - centerOmega) / ((beta : Complex) + 1) ^ 2

noncomputable def centerEndpointRateDeriv (beta : Real) : Real :=
  -(((beta + 1) ^ 2)⁻¹)

theorem centerOfReal_add_one_ne_zero {beta : Real} (hbeta : 0 < beta) :
    ((beta : Complex) + 1) ≠ 0 := by
  have h : ((beta + 1 : Real) : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  push_cast at h
  exact h

theorem centerChannel_eq_div {beta : Real} (hbeta : 0 < beta) :
    centerChannel beta = ((beta : Complex) + centerOmega) / ((beta : Complex) + 1) := by
  have hb : (beta : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hbeta.ne'
  have hb1 : ((beta : Complex) + 1) ≠ 0 := centerOfReal_add_one_ne_zero hbeta
  unfold centerChannel centerT
  push_cast
  rw [div_eq_div_iff _ hb1]
  · field_simp
  · intro h
    apply hb1
    have : (beta : Complex) * (1 + (beta : Complex)⁻¹) = 0 := by rw [h]; ring
    rw [mul_add, mul_one, mul_inv_cancel₀ hb] at this
    linear_combination this

theorem centerEndpointRate_eq_inv {beta : Real} (hbeta : 0 < beta) :
    centerEndpointRate beta = (beta + 1)⁻¹ := by
  unfold centerEndpointRate centerT
  field_simp

theorem hasDerivAt_complexRe {f : Real → Complex} {f' : Complex} {x : Real}
    (h : HasDerivAt f f' x) :
    HasDerivAt (fun t : Real => (f t).re) f'.re x := by
  have hC : HasFDerivAt Complex.re Complex.reCLM (f x) := Complex.reCLM.hasFDerivAt
  exact hC.comp_hasDerivAt x h

theorem hasDerivAt_centerChannel {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt (fun b : Real => centerChannel b) (centerChannelDeriv beta) beta := by
  have hb1 : ((beta : Complex) + 1) ≠ 0 := centerOfReal_add_one_ne_zero hbeta
  have hofReal : HasDerivAt (fun b : Real => (b : Complex)) 1 beta :=
    (hasDerivAt_id beta).ofReal_comp
  have hnum : HasDerivAt (fun b : Real => (b : Complex) + centerOmega) 1 beta :=
    hofReal.add_const centerOmega
  have hden : HasDerivAt (fun b : Real => (b : Complex) + 1) 1 beta :=
    hofReal.add_const 1
  have hdiv := hnum.div hden hb1
  have hval : (1 * ((beta : Complex) + 1) - ((beta : Complex) + centerOmega) * 1)
      / ((beta : Complex) + 1) ^ 2 = centerChannelDeriv beta := by
    unfold centerChannelDeriv
    ring_nf
  rw [hval] at hdiv
  refine hdiv.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hbeta] with b hb
  exact centerChannel_eq_div hb

theorem hasDerivAt_centerEndpointRate {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt centerEndpointRate (centerEndpointRateDeriv beta) beta := by
  have hb1 : (beta + 1) ≠ 0 := by positivity
  have hden : HasDerivAt (fun b : Real => b + 1) 1 beta := (hasDerivAt_id beta).add_const 1
  have hinv := hden.inv hb1
  have hval : -1 / (beta + 1) ^ 2 = centerEndpointRateDeriv beta := by
    unfold centerEndpointRateDeriv
    field_simp
  rw [hval] at hinv
  refine hinv.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hbeta] with b hb
  exact centerEndpointRate_eq_inv hb

theorem hasDerivAt_centerChannel_pow (N : Nat) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt (fun b : Real => centerChannel b ^ N)
      ((N : Complex) * centerChannel beta ^ (N - 1) * centerChannelDeriv beta) beta :=
  (hasDerivAt_centerChannel hbeta).pow N

theorem hasDerivAt_centerEndpointRate_pow (N : Nat) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt (fun b : Real => centerEndpointRate b ^ N)
      ((N : Real) * centerEndpointRate beta ^ (N - 1) * centerEndpointRateDeriv beta) beta :=
  (hasDerivAt_centerEndpointRate hbeta).pow N

noncomputable def centerEndpointTermDeriv (N : Nat) (beta : Real) : Real :=
  3 * ResidueSlices.epsIdx 3 N *
    ((N : Real) * centerEndpointRate beta ^ (N - 1) * centerEndpointRateDeriv beta)

theorem hasDerivAt_centerEndpointTerm (N : Nat) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt (fun b : Real => centerEndpointTerm N b)
      (centerEndpointTermDeriv N beta) beta := by
  have h := (hasDerivAt_centerEndpointRate_pow N hbeta).const_mul
    (3 * ResidueSlices.epsIdx 3 N)
  simpa [centerEndpointTerm, centerEndpointTermDeriv] using h

noncomputable def centerNumeratorTerm (N : Nat) (beta : Real) : Real :=
  2 * Complex.re ((centerOmega ^ 2 - 1) * centerChannel beta ^ N) +
    centerEndpointTerm N beta

noncomputable def centerNumeratorTermDeriv (N : Nat) (beta : Real) : Real :=
  2 * Complex.re ((centerOmega ^ 2 - 1) *
      ((N : Complex) * centerChannel beta ^ (N - 1) * centerChannelDeriv beta)) +
    centerEndpointTermDeriv N beta

noncomputable def centerDenominatorWaveDeriv (N : Nat) (beta : Real) : Real :=
  2 * Complex.re ((N : Complex) * centerChannel beta ^ (N - 1) * centerChannelDeriv beta) -
    centerEndpointTermDeriv N beta

theorem hasDerivAt_centerNumeratorTerm (N : Nat) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt (fun b : Real => centerNumeratorTerm N b)
      (centerNumeratorTermDeriv N beta) beta := by
  have hpow := hasDerivAt_centerChannel_pow N hbeta
  have hmul := hpow.const_mul (centerOmega ^ 2 - 1)
  have hre := hasDerivAt_complexRe hmul
  have h2 := hre.const_mul (2 : Real)
  exact h2.add (hasDerivAt_centerEndpointTerm N hbeta)

theorem hasDerivAt_centerDenominatorWave (N : Nat) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt (fun b : Real => centerDenominatorWave N b)
      (centerDenominatorWaveDeriv N beta) beta := by
  have hpow := hasDerivAt_centerChannel_pow N hbeta
  have hre := hasDerivAt_complexRe hpow
  have h2 := hre.const_mul (2 : Real)
  have h3 := ((hasDerivAt_const beta (1 : Real)).add h2).sub
    (hasDerivAt_centerEndpointTerm N hbeta)
  have heq : centerDenominatorWaveDeriv N beta =
      0 + 2 * Complex.re ((N : Complex) * centerChannel beta ^ (N - 1) *
        centerChannelDeriv beta) - centerEndpointTermDeriv N beta := by
    unfold centerDenominatorWaveDeriv
    ring
  rw [heq]
  exact h3

theorem centerError_eq_quotient
    {N : Nat} (hN : 1 ≤ N) {beta : Real} (hbeta : 0 < beta) :
    centerError N beta =
      beta * centerNumeratorTerm N beta / centerDenominatorWave N beta := by
  rw [centerError_channel_formula hN hbeta]
  rfl

noncomputable def centerErrorParameterDeriv (N : Nat) (beta : Real) : Real :=
  ((centerNumeratorTerm N beta + beta * centerNumeratorTermDeriv N beta) *
      centerDenominatorWave N beta -
    beta * centerNumeratorTerm N beta * centerDenominatorWaveDeriv N beta) /
    centerDenominatorWave N beta ^ 2

theorem hasDerivAt_centerError_quotient
    {N : Nat} (hN : 1 ≤ N) {beta : Real} (hbeta : 0 < beta) :
    HasDerivAt (fun b : Real => centerError N b)
      (centerErrorParameterDeriv N beta) beta := by
  have hD : centerDenominatorWave N beta ≠ 0 := (centerDenominatorWave_pos hN hbeta).ne'
  have hu : HasDerivAt (fun b : Real => b * centerNumeratorTerm N b)
      (1 * centerNumeratorTerm N beta + beta * centerNumeratorTermDeriv N beta) beta :=
    (hasDerivAt_id beta).mul (hasDerivAt_centerNumeratorTerm N hbeta)
  have hdiv := hu.div (hasDerivAt_centerDenominatorWave N hbeta) hD
  have hval :
      ((1 * centerNumeratorTerm N beta + beta * centerNumeratorTermDeriv N beta) *
          centerDenominatorWave N beta -
        beta * centerNumeratorTerm N beta * centerDenominatorWaveDeriv N beta) /
        centerDenominatorWave N beta ^ 2 = centerErrorParameterDeriv N beta := by
    unfold centerErrorParameterDeriv
    rw [one_mul]
  rw [hval] at hdiv
  refine hdiv.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hbeta] with b hb
  exact centerError_eq_quotient hN hb

theorem packetErrorDerivative_eq_centerErrorParameterDeriv
    {N : Nat} (hN : 1 ≤ N) {beta : Real} (hbeta : 0 < beta) :
    packetErrorDerivative N (beta ^ 3) =
      centerErrorParameterDeriv N beta / (3 * beta ^ 2) := by
  have h1 := hasDerivAt_centerError_parameter N hbeta
  have h2 := hasDerivAt_centerError_quotient hN hbeta
  have h3 : 3 * beta ^ 2 * packetErrorDerivative N (beta ^ 3)
      = centerErrorParameterDeriv N beta := h1.unique h2
  have hne : (3 : Real) * beta ^ 2 ≠ 0 := by positivity
  rw [← h3]
  field_simp

/-! ### Elementary uniform bounds on the channel data -/

theorem norm_centerChannelDeriv_le {beta : Real} (hbeta : 1 < beta) :
    ‖centerChannelDeriv beta‖ ≤ ‖1 - centerOmega‖ := by
  have hb0 : (0 : Real) < beta := lt_trans one_pos hbeta
  have hb1 : ((beta : Complex) + 1) ≠ 0 := centerOfReal_add_one_ne_zero hb0
  have hnorm : ‖((beta : Complex) + 1) ^ 2‖ = (beta + 1) ^ 2 := by
    rw [norm_pow]
    congr 1
    rw [show ((beta : Complex) + 1) = ((beta + 1 : Real) : Complex) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hge : (1 : Real) ≤ (beta + 1) ^ 2 := by nlinarith
  unfold centerChannelDeriv
  rw [norm_div, hnorm]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (1 - centerOmega)]

theorem abs_centerEndpointRateDeriv_le {beta : Real} (hbeta : 1 < beta) :
    |centerEndpointRateDeriv beta| ≤ 1 := by
  have hge : (1 : Real) ≤ (beta + 1) ^ 2 := by nlinarith
  have hpos : (0 : Real) < (beta + 1) ^ 2 := by linarith
  unfold centerEndpointRateDeriv
  rw [abs_neg, abs_of_pos (by positivity)]
  rw [inv_le_one_iff₀]
  right
  exact hge

theorem epsIdx_bounds (N : Nat) :
    0 ≤ ResidueSlices.epsIdx 3 N ∧ ResidueSlices.epsIdx 3 N ≤ 1 := by
  unfold ResidueSlices.epsIdx
  split_ifs <;> norm_num

theorem abs_sub_le_abs_add_abs (x y : Real) : |x - y| ≤ |x| + |y| := by
  calc |x - y| = |x + -y| := by rw [sub_eq_add_neg]
    _ ≤ |x| + |-y| := abs_add_le _ _
    _ = |x| + |y| := by rw [abs_neg]

theorem abs_two_mul_re_le {z : Complex} {M : Real} (h : ‖z‖ ≤ M) :
    |2 * Complex.re z| ≤ 2 * M := by
  have h1 := Complex.abs_re_le_norm z
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
  linarith

theorem norm_centerChannel_pow_le {beta S : Real} {m : Nat}
    (h : centerRho beta ^ m ≤ S) : ‖centerChannel beta ^ m‖ ≤ S := by
  rw [norm_pow]
  exact h

theorem abs_centerEndpointTerm_le (N : Nat) {beta S : Real} (hbeta : 0 < beta)
    (h : centerEndpointRate beta ^ N ≤ S) :
    |centerEndpointTerm N beta| ≤ 3 * S := by
  obtain ⟨he0, he1⟩ := epsIdx_bounds N
  have hr0 : 0 ≤ centerEndpointRate beta := centerEndpointRate_nonneg hbeta
  have hpow0 : 0 ≤ centerEndpointRate beta ^ N := pow_nonneg hr0 N
  unfold centerEndpointTerm
  rw [abs_of_nonneg (by positivity)]
  nlinarith

theorem abs_centerEndpointTermDeriv_le (N : Nat) {beta S : Real} (hbeta : 1 < beta)
    (h : centerEndpointRate beta ^ (N - 1) ≤ S) :
    |centerEndpointTermDeriv N beta| ≤ 3 * ((N : Real) * S) := by
  have hb0 : 0 < beta := lt_trans one_pos hbeta
  obtain ⟨he0, he1⟩ := epsIdx_bounds N
  have hr0 : 0 ≤ centerEndpointRate beta := centerEndpointRate_nonneg hb0
  have hpow0 : 0 ≤ centerEndpointRate beta ^ (N - 1) := pow_nonneg hr0 (N - 1)
  have hS0 : 0 ≤ S := le_trans hpow0 h
  have hNn : (0 : Real) ≤ (N : Real) := Nat.cast_nonneg N
  have hrd : |centerEndpointRateDeriv beta| ≤ 1 := abs_centerEndpointRateDeriv_le hbeta
  have hout : |3 * ResidueSlices.epsIdx 3 N| ≤ 3 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hin : |(N : Real) * centerEndpointRate beta ^ (N - 1) *
      centerEndpointRateDeriv beta| ≤ (N : Real) * S := by
    calc |(N : Real) * centerEndpointRate beta ^ (N - 1) * centerEndpointRateDeriv beta|
        = ((N : Real) * centerEndpointRate beta ^ (N - 1)) *
            |centerEndpointRateDeriv beta| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ ((N : Real) * S) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h hNn) hrd (abs_nonneg _) (by positivity)
      _ = (N : Real) * S := mul_one _
  calc |centerEndpointTermDeriv N beta|
      = |3 * ResidueSlices.epsIdx 3 N| *
        |(N : Real) * centerEndpointRate beta ^ (N - 1) * centerEndpointRateDeriv beta| :=
        abs_mul _ _
    _ ≤ 3 * ((N : Real) * S) :=
        mul_le_mul hout hin (abs_nonneg _) (by norm_num)

theorem norm_centerChannelBlock_le (N : Nat) {beta S : Real} (hbeta : 1 < beta)
    (h : centerRho beta ^ (N - 1) ≤ S) :
    ‖(N : Complex) * centerChannel beta ^ (N - 1) * centerChannelDeriv beta‖
      ≤ (N : Real) * S * ‖1 - centerOmega‖ := by
  have hq := norm_centerChannel_pow_le h
  have hqd := norm_centerChannelDeriv_le hbeta
  have hNn : (0 : Real) ≤ (N : Real) := Nat.cast_nonneg N
  have hS0 : 0 ≤ S := le_trans (norm_nonneg _) hq
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hq hNn) hqd (norm_nonneg _) (by positivity)

theorem abs_centerNumeratorTerm_le (N : Nat) {beta S : Real} (hbeta : 0 < beta)
    (hq : centerRho beta ^ N ≤ S) (hr : centerEndpointRate beta ^ N ≤ S) :
    |centerNumeratorTerm N beta| ≤ (2 * ‖centerOmega ^ 2 - 1‖ + 3) * S := by
  have h1 : ‖(centerOmega ^ 2 - 1) * centerChannel beta ^ N‖
      ≤ ‖centerOmega ^ 2 - 1‖ * S := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_centerChannel_pow_le hq) (norm_nonneg _)
  have h2 := abs_two_mul_re_le h1
  have h3 := abs_centerEndpointTerm_le N hbeta hr
  calc |centerNumeratorTerm N beta|
      ≤ |2 * Complex.re ((centerOmega ^ 2 - 1) * centerChannel beta ^ N)| +
        |centerEndpointTerm N beta| := abs_add_le _ _
    _ ≤ 2 * (‖centerOmega ^ 2 - 1‖ * S) + 3 * S := by linarith
    _ = (2 * ‖centerOmega ^ 2 - 1‖ + 3) * S := by ring

theorem abs_centerNumeratorTermDeriv_le (N : Nat) {beta S : Real} (hbeta : 1 < beta)
    (hq : centerRho beta ^ (N - 1) ≤ S) (hr : centerEndpointRate beta ^ (N - 1) ≤ S) :
    |centerNumeratorTermDeriv N beta| ≤
      (2 * ‖centerOmega ^ 2 - 1‖ * ‖1 - centerOmega‖ + 3) * ((N : Real) * S) := by
  have hblock := norm_centerChannelBlock_le N hbeta hq
  have h1 : ‖(centerOmega ^ 2 - 1) *
      ((N : Complex) * centerChannel beta ^ (N - 1) * centerChannelDeriv beta)‖
      ≤ ‖centerOmega ^ 2 - 1‖ * ((N : Real) * S * ‖1 - centerOmega‖) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hblock (norm_nonneg _)
  have h2 := abs_two_mul_re_le h1
  have h3 := abs_centerEndpointTermDeriv_le N hbeta hr
  calc |centerNumeratorTermDeriv N beta|
      ≤ |2 * Complex.re ((centerOmega ^ 2 - 1) *
          ((N : Complex) * centerChannel beta ^ (N - 1) * centerChannelDeriv beta))| +
        |centerEndpointTermDeriv N beta| := abs_add_le _ _
    _ ≤ 2 * (‖centerOmega ^ 2 - 1‖ * ((N : Real) * S * ‖1 - centerOmega‖)) +
        3 * ((N : Real) * S) := by linarith
    _ = (2 * ‖centerOmega ^ 2 - 1‖ * ‖1 - centerOmega‖ + 3) * ((N : Real) * S) := by ring

theorem abs_centerDenominatorWaveDeriv_le (N : Nat) {beta S : Real} (hbeta : 1 < beta)
    (hq : centerRho beta ^ (N - 1) ≤ S) (hr : centerEndpointRate beta ^ (N - 1) ≤ S) :
    |centerDenominatorWaveDeriv N beta| ≤ (2 * ‖1 - centerOmega‖ + 3) * ((N : Real) * S) := by
  have h2 := abs_two_mul_re_le (norm_centerChannelBlock_le N hbeta hq)
  have h3 := abs_centerEndpointTermDeriv_le N hbeta hr
  calc |centerDenominatorWaveDeriv N beta|
      ≤ |2 * Complex.re ((N : Complex) * centerChannel beta ^ (N - 1) *
          centerChannelDeriv beta)| + |centerEndpointTermDeriv N beta| :=
        abs_sub_le_abs_add_abs _ _
    _ ≤ 2 * ((N : Real) * S * ‖1 - centerOmega‖) + 3 * ((N : Real) * S) := by linarith
    _ = (2 * ‖1 - centerOmega‖ + 3) * ((N : Real) * S) := by ring

theorem abs_centerDenominatorWave_sub_one_le (N : Nat) {beta S : Real} (hbeta : 0 < beta)
    (hq : centerRho beta ^ N ≤ S) (hr : centerEndpointRate beta ^ N ≤ S) :
    |centerDenominatorWave N beta - 1| ≤ 5 * S := by
  have h1 := abs_two_mul_re_le (norm_centerChannel_pow_le hq)
  have h2 := abs_centerEndpointTerm_le N hbeta hr
  have hsplit : centerDenominatorWave N beta - 1
      = 2 * Complex.re (centerChannel beta ^ N) - centerEndpointTerm N beta := by
    unfold centerDenominatorWave
    ring
  rw [hsplit]
  calc |2 * Complex.re (centerChannel beta ^ N) - centerEndpointTerm N beta|
      ≤ |2 * Complex.re (centerChannel beta ^ N)| + |centerEndpointTerm N beta| :=
        abs_sub_le_abs_add_abs _ _
    _ ≤ 2 * S + 3 * S := by linarith
    _ = 5 * S := by ring

/-- Pure algebraic quotient estimate behind the uniform derivative bound. -/
theorem abs_quotient_estimate {beta B T a1 a2 a3 u v w D : Real}
    (hbeta : 0 < beta) (hbB : beta ≤ B) (hB0 : 0 ≤ B)
    (hu : |u| ≤ a1 * T) (hv : |v| ≤ a2 * T)
    (hprod : |u| * |w| ≤ a1 * a3 * T)
    (hDlow : 1 / 2 ≤ D) (hDhigh : D ≤ 3 / 2) :
    |((u + beta * v) * D - beta * u * w) / D ^ 2|
      ≤ 4 * (3 / 2 * (a1 + B * a2) + B * (a1 * a3)) * T := by
  have hDpos : 0 < D := by linarith
  have hX : |u + beta * v| ≤ (a1 + B * a2) * T := by
    have e1 : |beta * v| = beta * |v| := by rw [abs_mul, abs_of_pos hbeta]
    have e2 : beta * |v| ≤ B * (a2 * T) := mul_le_mul hbB hv (abs_nonneg _) hB0
    calc |u + beta * v| ≤ |u| + |beta * v| := abs_add_le _ _
      _ = |u| + beta * |v| := by rw [e1]
      _ ≤ a1 * T + B * (a2 * T) := by linarith
      _ = (a1 + B * a2) * T := by ring
  have hX0 : 0 ≤ (a1 + B * a2) * T := le_trans (abs_nonneg _) hX
  have h1 : |(u + beta * v) * D| ≤ (a1 + B * a2) * T * (3 / 2) := by
    rw [abs_mul, abs_of_pos hDpos]
    exact mul_le_mul hX hDhigh hDpos.le hX0
  have h2 : |beta * u * w| ≤ B * (a1 * a3 * T) := by
    have he : |beta * u * w| = beta * (|u| * |w|) := by
      rw [abs_mul, abs_mul, abs_of_pos hbeta]
      ring
    rw [he]
    exact mul_le_mul hbB hprod (by positivity) hB0
  have hnumer : |(u + beta * v) * D - beta * u * w|
      ≤ (3 / 2 * (a1 + B * a2) + B * (a1 * a3)) * T := by
    calc |(u + beta * v) * D - beta * u * w|
        ≤ |(u + beta * v) * D| + |beta * u * w| := abs_sub_le_abs_add_abs _ _
      _ ≤ (a1 + B * a2) * T * (3 / 2) + B * (a1 * a3 * T) := by linarith
      _ = (3 / 2 * (a1 + B * a2) + B * (a1 * a3)) * T := by ring
  have hK0 : 0 ≤ (3 / 2 * (a1 + B * a2) + B * (a1 * a3)) * T :=
    le_trans (abs_nonneg _) hnumer
  have hDsq : 1 / 4 ≤ D ^ 2 := by nlinarith
  rw [abs_div, abs_of_pos (pow_pos hDpos 2), div_le_iff₀ (pow_pos hDpos 2)]
  nlinarith [mul_nonneg hK0 (by linarith : (0 : Real) ≤ D ^ 2 - 1 / 4)]

/-! ### Fixed-center geometric upper bound -/

theorem centerError_geometric_upper
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ C : Real, 0 < C ∧ ∃ N0 : Nat, ∀ N ≥ N0,
      |centerError N alpha| ≤ C * centerRho alpha ^ N := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  have hrnn : (0 : Real) ≤ centerEndpointRate alpha := centerEndpointRate_nonneg halpha0
  have hrlt : centerEndpointRate alpha < centerRho alpha := centerEndpointRate_lt_centerRho halpha
  set Kw : Real := ‖centerOmega ^ 2 - 1‖ with hKw
  have hKw0 : 0 ≤ Kw := norm_nonneg _
  refine ⟨2 * alpha * (2 * Kw + 3), by positivity, ?_⟩
  have hev : ∀ᶠ N : Nat in atTop, (1 : Real) / 2 < centerDenominatorWave N alpha :=
    (tendsto_centerDenominatorWave halpha0).eventually
      (lt_mem_nhds (by norm_num : (1 : Real) / 2 < 1))
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  refine ⟨max N1 1, ?_⟩
  intro N hN
  have hN1' : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hNge : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hDlow : (1 : Real) / 2 < centerDenominatorWave N alpha := hN1 N hN1'
  have hDpos : 0 < centerDenominatorWave N alpha := by linarith
  have hrhoN : 0 < centerRho alpha ^ N := pow_pos hrho0 N
  -- numerator bound
  have hchan : ‖centerChannel alpha ^ N‖ = centerRho alpha ^ N := by
    rw [norm_pow]; rfl
  have h1 : |2 * Complex.re ((centerOmega ^ 2 - 1) * centerChannel alpha ^ N)|
      ≤ 2 * Kw * centerRho alpha ^ N := by
    have hre := Complex.abs_re_le_norm ((centerOmega ^ 2 - 1) * centerChannel alpha ^ N)
    rw [norm_mul, hchan] at hre
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:Real) ≤ 2)]
    nlinarith
  have h2 : |centerEndpointTerm N alpha| ≤ 3 * centerRho alpha ^ N := by
    obtain ⟨he0, he1⟩ := epsIdx_bounds N
    have hrN : centerEndpointRate alpha ^ N ≤ centerRho alpha ^ N :=
      pow_le_pow_left₀ hrnn hrlt.le N
    have hrN0 : 0 ≤ centerEndpointRate alpha ^ N := pow_nonneg hrnn N
    unfold centerEndpointTerm
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hnum : |2 * Complex.re ((centerOmega ^ 2 - 1) * centerChannel alpha ^ N) +
      centerEndpointTerm N alpha| ≤ (2 * Kw + 3) * centerRho alpha ^ N := by
    calc |2 * Complex.re ((centerOmega ^ 2 - 1) * centerChannel alpha ^ N) +
            centerEndpointTerm N alpha|
        ≤ |2 * Complex.re ((centerOmega ^ 2 - 1) * centerChannel alpha ^ N)| +
            |centerEndpointTerm N alpha| := abs_add_le _ _
      _ ≤ 2 * Kw * centerRho alpha ^ N + 3 * centerRho alpha ^ N := by linarith
      _ = (2 * Kw + 3) * centerRho alpha ^ N := by ring
  rw [centerError_channel_formula hNge halpha0]
  rw [abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
  have habs : |alpha * (2 * Complex.re ((centerOmega ^ 2 - 1) * centerChannel alpha ^ N) +
      centerEndpointTerm N alpha)| ≤ alpha * ((2 * Kw + 3) * centerRho alpha ^ N) := by
    rw [abs_mul, abs_of_pos halpha0]
    exact mul_le_mul_of_nonneg_left hnum halpha0.le
  have hfac : 0 ≤ alpha * ((2 * Kw + 3) * centerRho alpha ^ N) := by positivity
  have hkey : 0 ≤ alpha * ((2 * Kw + 3) * centerRho alpha ^ N) *
      (2 * centerDenominatorWave N alpha - 1) :=
    mul_nonneg hfac (by linarith)
  nlinarith [habs, hkey]

/-! ### Exponential domination of the polynomial factor -/

theorem tendsto_natSucc_mul_pow {x : Real} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun N : Nat => ((N + 1 : Nat) : Real) * x ^ N) atTop (nhds 0) := by
  have h1 : Tendsto (fun N : Nat => (N : Real) * x ^ N) atTop (nhds 0) := by
    have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
    exact tendsto_self_mul_const_pow_of_abs_lt_one habs
  have h2 : Tendsto (fun N : Nat => x ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr ?_
  intro N
  push_cast
  ring

theorem tendsto_localDerivativeRate_div_centerHalfRate
    {alpha : Real} (halpha : 0 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        ((N + 1 : Nat) : Real) * localDerivativeRate alpha ^ N /
          centerHalfRate alpha ^ N)
      Filter.atTop (nhds 0) := by
  obtain ⟨hsep1, hsep2, _⟩ := localDerivativeRate_separation halpha
  have hR : 0 < localDerivativeRate alpha := localDerivativeRate_pos halpha
  have hH : 0 < centerHalfRate alpha := centerHalfRate_pos halpha
  set x : Real := localDerivativeRate alpha / centerHalfRate alpha with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by
    rw [hx, div_lt_one hH]
    exact hsep2
  have h := tendsto_natSucc_mul_pow hx0 hx1
  refine h.congr ?_
  intro N
  rw [hx, div_pow, mul_div_assoc]

/-! ### The flagship uniform local derivative spectral bound -/

theorem packetErrorDerivative_local_geometric_bound
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ delta C : Real, ∃ N0 : Nat,
      0 < delta ∧ delta < alpha - 1 ∧ 0 < C ∧
      ∀ N ≥ N0, ∀ beta ∈ Set.Icc (alpha - delta) (alpha + delta),
        |packetErrorDerivative N (beta^3)| ≤
          C * ((N + 1 : Nat) : Real) *
            localDerivativeRate alpha ^ N := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hsep1, -, -⟩ := localDerivativeRate_separation halpha0
  have hR0 : 0 < localDerivativeRate alpha := localDerivativeRate_pos halpha0
  have hR1 : localDerivativeRate alpha < 1 := localDerivativeRate_lt_one halpha0
  have hRne : localDerivativeRate alpha ≠ 0 := ne_of_gt hR0
  -- Continuity of the channel data in the parameter fixes a uniform neighbourhood.
  have hcontRho : ContinuousAt centerRho alpha := by
    have h := (hasDerivAt_centerChannel halpha0).continuousAt.norm
    exact h
  have hcontRate : ContinuousAt centerEndpointRate alpha :=
    (hasDerivAt_centerEndpointRate halpha0).continuousAt
  have hrateLt : centerEndpointRate alpha < localDerivativeRate alpha :=
    lt_trans (centerEndpointRate_lt_centerRho halpha) hsep1
  have hev : ∀ᶠ b in nhds alpha,
      centerRho b < localDerivativeRate alpha ∧
      centerEndpointRate b < localDerivativeRate alpha :=
    (hcontRho.eventually (gt_mem_nhds hsep1)).and
      (hcontRate.eventually (gt_mem_nhds hrateLt))
  obtain ⟨eps, heps0, heps⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨delta, hdelta⟩ : ∃ x : Real, x = min (eps / 2) ((alpha - 1) / 2) := ⟨_, rfl⟩
  have hdelta0 : 0 < delta := by
    rw [hdelta]; exact lt_min (by linarith) (by linarith)
  have hdeltaeps : delta ≤ eps / 2 := by rw [hdelta]; exact min_le_left _ _
  have hdeltahalf : delta ≤ (alpha - 1) / 2 := by rw [hdelta]; exact min_le_right _ _
  have hdeltalt : delta < alpha - 1 := by linarith
  -- Fixed constants.
  obtain ⟨a1, ha1⟩ : ∃ x : Real, x = 2 * ‖centerOmega ^ 2 - 1‖ + 3 := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ x : Real,
      x = 2 * ‖centerOmega ^ 2 - 1‖ * ‖1 - centerOmega‖ + 3 := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ x : Real, x = 2 * ‖1 - centerOmega‖ + 3 := ⟨_, rfl⟩
  have ha10 : 0 < a1 := by rw [ha1]; positivity
  have ha20 : 0 < a2 := by rw [ha2]; positivity
  have ha30 : 0 < a3 := by rw [ha3]; positivity
  obtain ⟨B, hB⟩ : ∃ x : Real, x = alpha + delta := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; linarith
  obtain ⟨C1, hC1⟩ : ∃ x : Real, x = 3 / 2 * (a1 + B * a2) + B * (a1 * a3) := ⟨_, rfl⟩
  have hC10 : 0 < C1 := by
    rw [hC1]
    have h1 : 0 < B * a2 := mul_pos hB0 ha20
    have h2 : 0 < B * (a1 * a3) := mul_pos hB0 (mul_pos ha10 ha30)
    linarith
  obtain ⟨C, hC⟩ : ∃ x : Real, x = 4 * C1 / (3 * localDerivativeRate alpha) := ⟨_, rfl⟩
  have hC0 : 0 < C := by
    rw [hC]; exact div_pos (by linarith) (by linarith)
  -- The threshold row index.
  have htend : Tendsto (fun n : Nat => localDerivativeRate alpha ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hR0.le hR1
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp
    (htend.eventually (gt_mem_nhds (by norm_num : (0 : Real) < 1 / 10)))
  refine ⟨delta, C, n0 + 1, hdelta0, hdeltalt, hC0, ?_⟩
  intro N hN beta hbeta_mem
  obtain ⟨hbl, hbr⟩ := hbeta_mem
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 n0) hN
  have hb1 : 1 < beta := by linarith
  have hb0 : 0 < beta := lt_trans one_pos hb1
  have hbB : beta ≤ B := by rw [hB]; linarith
  have hdist : dist beta alpha < eps := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  obtain ⟨hrhoLt, hrateLt'⟩ := heps hdist
  have hrho0 : 0 ≤ centerRho beta := norm_nonneg _
  have hr0 : 0 ≤ centerEndpointRate beta := centerEndpointRate_nonneg hb0
  -- Geometric data at row `N`.
  obtain ⟨S, hS⟩ : ∃ x : Real, x = localDerivativeRate alpha ^ (N - 1) := ⟨_, rfl⟩
  have hS0 : 0 < S := by rw [hS]; exact pow_pos hR0 _
  have hS1 : S ≤ 1 := by rw [hS]; exact pow_le_one₀ hR0.le hR1.le
  have hSsmall : S ≤ 1 / 10 := by
    rw [hS]; exact (hn0 (N - 1) (by omega)).le
  have hqN : centerRho beta ^ N ≤ S := by
    rw [hS]
    exact le_trans (pow_le_pow_left₀ hrho0 hrhoLt.le N)
      (pow_le_pow_of_le_one hR0.le hR1.le (by omega))
  have hqN1 : centerRho beta ^ (N - 1) ≤ S := by
    rw [hS]; exact pow_le_pow_left₀ hrho0 hrhoLt.le (N - 1)
  have hrN : centerEndpointRate beta ^ N ≤ S := by
    rw [hS]
    exact le_trans (pow_le_pow_left₀ hr0 hrateLt'.le N)
      (pow_le_pow_of_le_one hR0.le hR1.le (by omega))
  have hrN1 : centerEndpointRate beta ^ (N - 1) ≤ S := by
    rw [hS]; exact pow_le_pow_left₀ hr0 hrateLt'.le (N - 1)
  obtain ⟨T, hT⟩ : ∃ x : Real, x = ((N : Real) + 1) * S := ⟨_, rfl⟩
  have hNn : (0 : Real) ≤ (N : Real) := Nat.cast_nonneg N
  have hT0 : 0 < T := by rw [hT]; positivity
  have hST : S ≤ T := by
    rw [hT]; exact le_mul_of_one_le_left hS0.le (by linarith)
  have hNST : (N : Real) * S ≤ T := by
    rw [hT]; exact mul_le_mul_of_nonneg_right (by linarith) hS0.le
  -- Spectral bounds on the channel blocks.
  have hNum := abs_centerNumeratorTerm_le N hb0 hqN hrN
  have hNd := abs_centerNumeratorTermDeriv_le N hb1 hqN1 hrN1
  have hDd := abs_centerDenominatorWaveDeriv_le N hb1 hqN1 hrN1
  have hDclose := abs_centerDenominatorWave_sub_one_le N hb0 hqN hrN
  rw [← ha1] at hNum
  rw [← ha2] at hNd
  rw [← ha3] at hDd
  have hNumT : |centerNumeratorTerm N beta| ≤ a1 * T :=
    le_trans hNum (mul_le_mul_of_nonneg_left hST ha10.le)
  have hNdT : |centerNumeratorTermDeriv N beta| ≤ a2 * T :=
    le_trans hNd (mul_le_mul_of_nonneg_left hNST ha20.le)
  have hprod : |centerNumeratorTerm N beta| * |centerDenominatorWaveDeriv N beta|
      ≤ a1 * a3 * T := by
    have h1 : |centerNumeratorTerm N beta| * |centerDenominatorWaveDeriv N beta|
        ≤ (a1 * S) * (a3 * ((N : Real) * S)) :=
      mul_le_mul hNum hDd (abs_nonneg _) (by positivity)
    have hs : S * ((N : Real) * S) ≤ (N : Real) * S :=
      mul_le_of_le_one_left (by positivity) hS1
    have h3 : S * ((N : Real) * S) ≤ T := le_trans hs hNST
    have h2 : (a1 * S) * (a3 * ((N : Real) * S)) ≤ a1 * a3 * T := by
      calc (a1 * S) * (a3 * ((N : Real) * S)) = (a1 * a3) * (S * ((N : Real) * S)) := by ring
        _ ≤ (a1 * a3) * T := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = a1 * a3 * T := by ring
    linarith
  have hDbounds := abs_le.mp hDclose
  have hDlow : 1 / 2 ≤ centerDenominatorWave N beta := by linarith [hDbounds.1]
  have hDhigh : centerDenominatorWave N beta ≤ 3 / 2 := by linarith [hDbounds.2]
  have hquot := abs_quotient_estimate (beta := beta) (B := B) (T := T)
    (a1 := a1) (a2 := a2) (a3 := a3)
    (u := centerNumeratorTerm N beta) (v := centerNumeratorTermDeriv N beta)
    (w := centerDenominatorWaveDeriv N beta) (D := centerDenominatorWave N beta)
    hb0 hbB hB0.le hNumT hNdT hprod hDlow hDhigh
  have hderiv : |centerErrorParameterDeriv N beta| ≤ 4 * C1 * T := by
    rw [hC1]; exact hquot
  -- Divide by the chain-rule factor `3 * beta ^ 2 ≥ 3`.
  rw [packetErrorDerivative_eq_centerErrorParameterDeriv hN1 hb0, abs_div,
    abs_of_pos (by positivity : (0 : Real) < 3 * beta ^ 2)]
  have hb3 : (3 : Real) ≤ 3 * beta ^ 2 := by nlinarith
  have hCT0 : (0 : Real) ≤ 4 * C1 * T := by positivity
  have hstep : |centerErrorParameterDeriv N beta| / (3 * beta ^ 2) ≤ 4 * C1 * T / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : Real) < 3)]
    have h1 : 4 * C1 * T * 3 ≤ 4 * C1 * T * (3 * beta ^ 2) :=
      mul_le_mul_of_nonneg_left hb3 hCT0
    linarith
  have hRN : localDerivativeRate alpha ^ N
      = localDerivativeRate alpha * localDerivativeRate alpha ^ (N - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hfinal : 4 * C1 * T / 3 = C * ((N + 1 : Nat) : Real) * localDerivativeRate alpha ^ N := by
    rw [hC, hT, hS, hRN]
    push_cast
    field_simp
  linarith

theorem exists_centerError_and_localDerivative_bounds
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ CE delta CD : Real, ∃ NE ND : Nat,
      0 < CE ∧ 0 < delta ∧ delta < alpha - 1 ∧ 0 < CD ∧
      (∀ N ≥ NE,
        |centerError N alpha| ≤ CE * centerRho alpha ^ N) ∧
      (∀ N ≥ ND, ∀ beta ∈ Set.Icc (alpha - delta) (alpha + delta),
        |packetErrorDerivative N (beta^3)| ≤
          CD * ((N + 1 : Nat) : Real) *
            localDerivativeRate alpha ^ N) := by
  obtain ⟨CE, hCE, NE, hNE⟩ := centerError_geometric_upper halpha
  obtain ⟨delta, CD, ND, hdelta, hdelta', hCD, hbound⟩ :=
    packetErrorDerivative_local_geometric_bound halpha
  exact ⟨CE, delta, CD, NE, ND, hCE, hdelta, hdelta', hCD, hNE, hbound⟩

end SilverFiniteRow
