/-
Cubic-silver finite-row crossover, Phase B3: selected relative deviation and
center-remainder convergence.
All five targets are proved; signatures are verbatim from the harness.
-/
import RequestProject.SilverFiniteRowAdaptiveRow
import RequestProject.SilverFiniteRowRelative

open scoped Real Topology BigOperators
open Filter

namespace SilverFiniteRow

theorem tendsto_relativeCenterRemainder_of_reindexed_relativeDeviationVariation
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda y : Real} (halpha : 0 < alpha)
    (herror : ∀ᶠ N in Filter.atTop, centerError (u N) alpha ≠ 0)
    (hvariation : Filter.Tendsto
      (fun N : Nat => relativeDeviationVariation (u N) alpha lambda y)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun N : Nat => relativeCenterRemainder (u N) alpha lambda y)
      Filter.atTop (nhds 0) := by
  have hQ : Filter.Tendsto
      (fun N : Nat =>
        fixedPointFactor alpha (1 + movingMuShift (u N) alpha lambda)
          (movingDelta (u N) alpha y))
      Filter.atTop (nhds (3 * alpha ^ 2)) := by
    have h := (tendsto_moving_fixedPointFactor
      (alpha := alpha) (lambda := lambda) (y := y) halpha).comp hu
    simpa [Function.comp_def] using h
  have hs : Filter.Tendsto
      (fun N : Nat => movingCrossoverScale (u N) alpha)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_movingCrossoverScale (alpha := alpha) halpha).comp hu
    simpa [Function.comp_def] using h
  have hQabs : Filter.Tendsto
      (fun N : Nat =>
        |fixedPointFactor alpha (1 + movingMuShift (u N) alpha lambda)
          (movingDelta (u N) alpha y)|)
      Filter.atTop (nhds (3 * alpha ^ 2)) := by
    have h := hQ.abs
    rwa [abs_of_nonneg (show (0 : Real) ≤ 3 * alpha ^ 2 by positivity)] at h
  have h1 : Filter.Tendsto
      (fun N : Nat =>
        relativeDeviationVariation (u N) alpha lambda y *
          |fixedPointFactor alpha (1 + movingMuShift (u N) alpha lambda)
            (movingDelta (u N) alpha y)| / (3 * alpha ^ 2))
      Filter.atTop (nhds 0) := by
    simpa using (hvariation.mul hQabs).div_const (3 * alpha ^ 2)
  have h2 : Filter.Tendsto
      (fun N : Nat =>
        |fixedPointFactor alpha (1 + movingMuShift (u N) alpha lambda)
          (movingDelta (u N) alpha y) - 3 * alpha ^ 2| / (3 * alpha ^ 2))
      Filter.atTop (nhds 0) := by
    have h := (hQ.sub_const (3 * alpha ^ 2)).abs
    rw [sub_self, abs_zero] at h
    simpa using h.div_const (3 * alpha ^ 2)
  have h3 : Filter.Tendsto
      (fun N : Nat => movingCrossoverScale (u N) alpha * |y| ^ 3 / (3 * alpha))
      Filter.atTop (nhds 0) := by
    simpa using (hs.mul_const (|y| ^ 3)).div_const (3 * alpha)
  have hbound : Filter.Tendsto
      (fun N : Nat =>
        relativeDeviationVariation (u N) alpha lambda y *
            |fixedPointFactor alpha (1 + movingMuShift (u N) alpha lambda)
              (movingDelta (u N) alpha y)| / (3 * alpha ^ 2) +
          |fixedPointFactor alpha (1 + movingMuShift (u N) alpha lambda)
              (movingDelta (u N) alpha y) - 3 * alpha ^ 2| / (3 * alpha ^ 2) +
          movingCrossoverScale (u N) alpha * |y| ^ 3 / (3 * alpha))
      Filter.atTop (nhds 0) := by
    simpa using (h1.add h2).add h3
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards with N
    simp only [relativeCenterRemainder]
    exact div_nonneg (abs_nonneg _) (mul_nonneg halpha.le (abs_nonneg _))
  · filter_upwards [herror] with N hN
    exact relativeCenterRemainder_le halpha hN

private lemma cube_rpow_third {t : Real} (ht : 0 ≤ t) :
    (t ^ 3) ^ ((3 : Real)⁻¹) = t := by
  rw [← Real.rpow_natCast t 3, ← Real.rpow_mul ht]
  norm_num

private lemma rpow_third_cube {x : Real} (hx : 0 ≤ x) :
    (x ^ ((3 : Real)⁻¹)) ^ 3 = x := by
  rw [← Real.rpow_natCast (x ^ ((3 : Real)⁻¹)) 3, ← Real.rpow_mul hx]
  norm_num

private lemma le_of_sq_le_sq_nonneg {a b : Real} (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

/-- The final ratio estimate feeding the selected relative deviation bound. -/
private lemma ratio_le_of_scale_bounds
    {alpha Y C T s Eabs A qq Hp : Real}
    (halpha : 0 < alpha) (hY : 0 ≤ Y) (hC : 0 < C) (hT : 0 ≤ T)
    (hs : 0 < s) (hq : 0 < qq) (hH : 0 < Hp)
    (hEabs : Eabs = s ^ 2 / alpha)
    (hA : A ≤ C * T * (6 * alpha ^ 2 * Y * s))
    (hlow : qq * Hp ≤ s) :
    A / Eabs ≤ 6 * C * alpha ^ 3 * (Y + 1) / qq * (T / Hp) := by
  have hcoef : 0 ≤ 6 * C * alpha ^ 2 * (Y + 1) * T := by positivity
  have h1 : A ≤ 6 * C * alpha ^ 2 * (Y + 1) * T * s := by nlinarith
  have hkey : 6 * C * alpha ^ 3 * (Y + 1) / qq * (T / Hp) * (s ^ 2 / alpha) =
      6 * C * alpha ^ 2 * (Y + 1) * T * (s ^ 2 / (qq * Hp)) := by
    field_simp
  have hstep : s ≤ s ^ 2 / (qq * Hp) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [hEabs, div_le_iff₀ (by positivity), hkey]
  nlinarith [mul_le_mul_of_nonneg_left hstep hcoef]

theorem eventually_adaptiveRow_relativeDeviationVariation_bound
    {alpha : Real} (halpha : 1 < alpha)
    {L Y : Real} (hL : 0 ≤ L) (hY : 0 ≤ Y) :
    ∃ K : Real, 0 < K ∧
      ∀ᶠ N in Filter.atTop,
        ∀ lambda ∈ Set.Icc (-L) L, ∀ y ∈ Set.Icc (-Y) Y,
          relativeDeviationVariation (adaptiveRow N alpha) alpha lambda y ≤
            K *
              (((adaptiveRow N alpha + 1 : Nat) : Real) *
                  localDerivativeRate alpha ^ (adaptiveRow N alpha) /
                centerHalfRate alpha ^ (adaptiveRow N alpha)) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  have hrhopos : 0 < centerRho alpha := centerRho_pos halpha0
  have hHpos : 0 < centerHalfRate alpha := centerHalfRate_pos halpha0
  have hRpos : 0 < localDerivativeRate alpha := localDerivativeRate_pos halpha0
  have hHsq : centerHalfRate alpha ^ 2 = centerRho alpha := by
    rw [centerHalfRate]
    exact Real.sq_sqrt hrhopos.le
  obtain ⟨d0, C, hd0, hd0', hC, hderiv⟩ :=
    eventually_adaptiveRow_packetErrorDerivative_bound halpha
  obtain ⟨c, hc, hlower⟩ := eventually_adaptiveRow_centerError_lower halpha
  have hne := eventually_adaptiveRow_centerError_ne_zero halpha
  set d1 : Real := min d0 (alpha / 2) with hd1def
  have hd1pos : 0 < d1 := lt_min hd0 (by linarith)
  have hd1le : d1 ≤ d0 := min_le_left _ _
  have hd1half : d1 ≤ alpha / 2 := min_le_right _ _
  have hlowpos : 0 < alpha - d1 := by linarith
  set eps0 : Real := alpha ^ 3 - (alpha - d1) ^ 3 with heps0def
  have heps0pos : 0 < eps0 := by
    have h : (alpha - d1) ^ 3 < alpha ^ 3 :=
      pow_lt_pow_left₀ (by linarith) (by linarith) three_ne_zero
    rw [heps0def]
    linarith
  have heps0up : alpha ^ 3 + eps0 ≤ (alpha + d1) ^ 3 := by
    rw [heps0def]
    nlinarith [mul_nonneg halpha0.le (sq_nonneg d1)]
  set q : Real := Real.sqrt (alpha * c) with hqdef
  have hqpos : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hq2 : q ^ 2 = alpha * c := Real.sq_sqrt (by positivity)
  refine ⟨6 * C * alpha ^ 3 * (Y + 1) / q, by positivity, ?_⟩
  set S0 : Real := min (alpha / (L + 1)) (eps0 / (6 * alpha ^ 2 * (Y + 1)))
    with hS0def
  have hS0pos : 0 < S0 := lt_min (by positivity) (by positivity)
  have hscale : ∀ᶠ N in Filter.atTop,
      movingCrossoverScale (adaptiveRow N alpha) alpha < S0 := by
    have h := (tendsto_movingCrossoverScale (alpha := alpha) halpha0).comp
      (tendsto_adaptiveRow alpha)
    have h2 : Filter.Tendsto
        (fun N : Nat => movingCrossoverScale (adaptiveRow N alpha) alpha)
        Filter.atTop (nhds 0) := by simpa [Function.comp_def] using h
    exact h2.eventually (eventually_lt_nhds hS0pos)
  filter_upwards [hderiv, hlower, hne, hscale] with N hderivN hlowerN hneN hscaleN
  intro lambda hlambda y hy
  simp only [relativeDeviationVariation]
  set J : Nat := adaptiveRow N alpha with hJ
  set s : Real := movingCrossoverScale J alpha with hsdef
  set E : Real := centerError J alpha with hEdef
  set mu : Real := 1 + movingMuShift J alpha lambda with hmudef
  set dl : Real := movingDelta J alpha y with hdldef
  have hsnn : 0 ≤ s := by
    rw [hsdef, movingCrossoverScale, SilverCrossover.crossoverScale]
    exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = alpha * |E| := by
    rw [hsdef, hEdef, movingCrossoverScale]
    exact SilverCrossover.crossoverScale_sq halpha0.le
  have hEpos : 0 < |E| := abs_pos.mpr hneN
  have hspos : 0 < s := by
    have h : 0 < s ^ 2 := by rw [hs2]; positivity
    nlinarith
  have hEabs : |E| = s ^ 2 / alpha := by
    rw [hs2]
    field_simp
  obtain ⟨hlam1, hlam2⟩ := hlambda
  obtain ⟨hy1, hy2⟩ := hy
  have hlamabs : |lambda| ≤ L := abs_le.mpr ⟨hlam1, hlam2⟩
  have hyabs : |y| ≤ Y := abs_le.mpr ⟨hy1, hy2⟩
  have hsS0 : s ≤ S0 := hscaleN.le
  have hsL : s ≤ alpha / (L + 1) := le_trans hsS0 (min_le_left _ _)
  have hseps : s ≤ eps0 / (6 * alpha ^ 2 * (Y + 1)) :=
    le_trans hsS0 (min_le_right _ _)
  have hdlabs : |dl| = s * |y| := by
    rw [hdldef, movingDelta, ← hsdef, abs_mul, abs_of_nonneg hsnn]
  have hdlle : |dl| ≤ s * Y := by
    rw [hdlabs]
    exact mul_le_mul_of_nonneg_left hyabs hsnn
  have hmuabs : |mu| ≤ 2 := by
    have hshift : |movingMuShift J alpha lambda| ≤ 1 := by
      rw [movingMuShift, ← hsdef, abs_div, abs_mul, abs_of_nonneg hsnn,
        abs_of_pos halpha0, div_le_one halpha0]
      have h1 : |lambda| * s ≤ L * (alpha / (L + 1)) :=
        mul_le_mul hlamabs hsL hsnn hL
      have h2 : L * (alpha / (L + 1)) ≤ alpha := by
        rw [mul_div_assoc'] at h1 ⊢
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    have h3 : |mu| ≤ |(1 : Real)| + |movingMuShift J alpha lambda| := by
      rw [hmudef]
      exact abs_add_le _ _
    rw [abs_one] at h3
    linarith
  have hdisp : affineInput alpha mu (alpha + dl) - alpha ^ 3 =
      3 * mu * alpha ^ 2 * dl := by
    simp only [affineInput, SilverCrossover.affineIntercept,
      SilverCrossover.affineSlope]
    ring
  have hdispbound : |3 * mu * alpha ^ 2 * dl| ≤ 6 * alpha ^ 2 * Y * s := by
    have e : |3 * mu * alpha ^ 2 * dl| = 3 * alpha ^ 2 * (|mu| * |dl|) := by
      rw [show (3 : Real) * mu * alpha ^ 2 * dl = 3 * alpha ^ 2 * (mu * dl) by
        ring, abs_mul (3 * alpha ^ 2) (mu * dl), abs_mul mu dl,
        abs_of_nonneg (by positivity : (0 : Real) ≤ 3 * alpha ^ 2)]
    rw [e]
    have hmul : |mu| * |dl| ≤ 2 * (s * Y) :=
      mul_le_mul hmuabs hdlle (abs_nonneg _) (by norm_num)
    have := mul_le_mul_of_nonneg_left hmul
      (by positivity : (0 : Real) ≤ 3 * alpha ^ 2)
    linarith
  have hdispabs : |affineInput alpha mu (alpha + dl) - alpha ^ 3| ≤ eps0 := by
    rw [hdisp]
    rw [le_div_iff₀ (by positivity : (0 : Real) < 6 * alpha ^ 2 * (Y + 1))] at hseps
    have h7 : 0 ≤ alpha ^ 2 * s := mul_nonneg (sq_nonneg alpha) hsnn
    linarith
  have hsegb : ∀ x ∈ Set.uIcc (alpha ^ 3) (affineInput alpha mu (alpha + dl)),
      (alpha - d1) ^ 3 ≤ x ∧ x ≤ (alpha + d1) ^ 3 := by
    intro x hx
    obtain ⟨hda, hdb⟩ := abs_le.mp hdispabs
    have heps : eps0 = alpha ^ 3 - (alpha - d1) ^ 3 := heps0def
    rcases Set.mem_uIcc.mp hx with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hsegpos : ∀ x ∈ Set.uIcc (alpha ^ 3) (affineInput alpha mu (alpha + dl)),
      0 < x := by
    intro x hx
    have h := (hsegb x hx).1
    have h2 : 0 < (alpha - d1) ^ 3 := pow_pos hlowpos 3
    linarith
  obtain ⟨xi, hxi, heq⟩ :=
    deviationVariation_eq_deriv_mul (alpha := alpha) (mu := mu) (delta := dl)
      J halpha0 hsegpos
  have hxipos : 0 < xi := hsegpos xi hxi
  obtain ⟨hxi1, hxi2⟩ := hsegb xi hxi
  have hbeta3 : (xi ^ ((3 : Real)⁻¹)) ^ 3 = xi := rpow_third_cube hxipos.le
  have hb1 : alpha - d1 ≤ xi ^ ((3 : Real)⁻¹) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : Real) ≤ (alpha - d1) ^ 3)
      hxi1 (by norm_num : (0 : Real) ≤ (3 : Real)⁻¹)
    rwa [cube_rpow_third hlowpos.le] at h
  have hb2 : xi ^ ((3 : Real)⁻¹) ≤ alpha + d1 := by
    have h := Real.rpow_le_rpow hxipos.le hxi2
      (by norm_num : (0 : Real) ≤ (3 : Real)⁻¹)
    rwa [cube_rpow_third (by positivity : (0 : Real) ≤ alpha + d1)] at h
  have hbetamem : xi ^ ((3 : Real)⁻¹) ∈ Set.Icc (alpha - d0) (alpha + d0) :=
    ⟨by linarith, by linarith⟩
  have hderivbound : |packetErrorDerivative J xi| ≤
      C * ((J + 1 : Nat) : Real) * localDerivativeRate alpha ^ J := by
    have h := hderivN _ hbetamem
    rwa [hbeta3] at h
  have hAbound : |deviationVariation J alpha mu dl| ≤
      C * (((J + 1 : Nat) : Real) * localDerivativeRate alpha ^ J) *
        (6 * alpha ^ 2 * Y * s) := by
    rw [heq, abs_mul, hdisp]
    have h := mul_le_mul hderivbound hdispbound (abs_nonneg _)
      (by positivity : (0 : Real) ≤
        C * ((J + 1 : Nat) : Real) * localDerivativeRate alpha ^ J)
    calc |packetErrorDerivative J xi| * |3 * mu * alpha ^ 2 * dl|
        ≤ C * ((J + 1 : Nat) : Real) * localDerivativeRate alpha ^ J *
            (6 * alpha ^ 2 * Y * s) := h
      _ = C * (((J + 1 : Nat) : Real) * localDerivativeRate alpha ^ J) *
            (6 * alpha ^ 2 * Y * s) := by ring
  have hpowH : (centerHalfRate alpha ^ J) ^ 2 = centerRho alpha ^ J := by
    rw [← pow_mul, mul_comm, pow_mul, hHsq]
  have hlowq : q * centerHalfRate alpha ^ J ≤ s := by
    refine le_of_sq_le_sq_nonneg hsnn ?_
    have hsq : (q * centerHalfRate alpha ^ J) ^ 2 =
        alpha * (c * centerRho alpha ^ J) := by
      rw [mul_pow, hq2, hpowH]; ring
    rw [hsq, hs2]
    exact mul_le_mul_of_nonneg_left hlowerN halpha0.le
  exact ratio_le_of_scale_bounds halpha0 hY hC (by positivity) hspos hqpos
    (by positivity) hEabs hAbound hlowq

theorem eventually_adaptiveRow_relativeDeviationVariation_lt
    {alpha : Real} (halpha : 1 < alpha)
    {L Y epsilon : Real} (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N in Filter.atTop,
      ∀ lambda ∈ Set.Icc (-L) L, ∀ y ∈ Set.Icc (-Y) Y,
        relativeDeviationVariation (adaptiveRow N alpha) alpha lambda y <
          epsilon := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨K, hK, hbound⟩ :=
    eventually_adaptiveRow_relativeDeviationVariation_bound halpha hL hY
  have hrow := tendsto_adaptiveRow_localDerivativeRate_div_centerHalfRate halpha0
  have hsmall : ∀ᶠ N in Filter.atTop,
      ((adaptiveRow N alpha + 1 : Nat) : Real) *
            localDerivativeRate alpha ^ (adaptiveRow N alpha) /
          centerHalfRate alpha ^ (adaptiveRow N alpha) < epsilon / K :=
    hrow.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [hbound, hsmall] with N hN hN2 lambda hlambda y hy
  have h1 := hN lambda hlambda y hy
  have h2 : K *
      (((adaptiveRow N alpha + 1 : Nat) : Real) *
          localDerivativeRate alpha ^ (adaptiveRow N alpha) /
        centerHalfRate alpha ^ (adaptiveRow N alpha)) < K * (epsilon / K) :=
    mul_lt_mul_of_pos_left hN2 hK
  have h3 : K * (epsilon / K) = epsilon := by
    field_simp
  linarith

theorem tendsto_adaptiveRow_relativeDeviationVariation
    {alpha lambda y : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        relativeDeviationVariation (adaptiveRow N alpha) alpha lambda y)
      Filter.atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro eps heps
  filter_upwards [eventually_adaptiveRow_relativeDeviationVariation_lt halpha
    (abs_nonneg lambda) (abs_nonneg y) heps] with N hN
  have h := hN lambda ⟨neg_abs_le lambda, le_abs_self lambda⟩ y
    ⟨neg_abs_le y, le_abs_self y⟩
  have hnn : 0 ≤ relativeDeviationVariation (adaptiveRow N alpha) alpha lambda y := by
    simp only [relativeDeviationVariation]
    exact div_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact h

theorem tendsto_adaptiveRow_relativeCenterRemainder
    {alpha lambda y : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        relativeCenterRemainder (adaptiveRow N alpha) alpha lambda y)
      Filter.atTop (nhds 0) :=
  tendsto_relativeCenterRemainder_of_reindexed_relativeDeviationVariation
    (tendsto_adaptiveRow alpha) (lt_trans one_pos halpha)
    (eventually_adaptiveRow_centerError_ne_zero halpha)
    (tendsto_adaptiveRow_relativeDeviationVariation halpha)

end SilverFiniteRow
