/-
Cubic-silver finite-row crossover, Phase B4B1: exact fixed-point converse and
normalized crossover-residual convergence.
All nine targets are proved; signatures are verbatim from the harness.
-/
import RequestProject.SilverFiniteRowSelectedRemainder

open scoped Real Topology
open Filter

namespace SilverFiniteRow

theorem fixedPointFactor_pos_of_affineInput_pos
    {alpha mu delta : Real}
    (hinput : 0 < affineInput alpha mu (alpha + delta)) :
    0 < fixedPointFactor alpha mu delta := by
  have hu : 0 < limitingMap alpha mu (alpha + delta) := by
    rw [limitingMap]
    exact Real.rpow_pos_of_pos hinput _
  simp only [fixedPointFactor]
  nlinarith [sq_nonneg (alpha + delta + limitingMap alpha mu (alpha + delta) / 2),
    sq_nonneg (limitingMap alpha mu (alpha + delta)), hu]

theorem finiteMap_eq_self_iff_quadraticCrossover_eq_centerRemainder
    {N : Nat} {alpha muShift delta : Real}
    (halpha : 0 < alpha)
    (hinput : 0 < affineInput alpha (1 + muShift) (alpha + delta)) :
    finiteMap N alpha (1 + muShift) (alpha + delta) = alpha + delta ↔
      SilverCrossover.quadraticCrossover alpha (centerError N alpha)
          muShift delta =
        centerRemainder N alpha muShift delta := by
  constructor
  · intro hfixed
    exact quadraticCrossover_eq_centerRemainder_of_fixed halpha hinput hfixed
  · intro heq
    have hF : 0 < fixedPointFactor alpha (1 + muShift) delta :=
      fixedPointFactor_pos_of_affineInput_pos hinput
    have hu3 : limitingMap alpha (1 + muShift) (alpha + delta) ^ 3 =
        affineInput alpha (1 + muShift) (alpha + delta) := by
      rw [limitingMap, ← Real.rpow_natCast _ 3, ← Real.rpow_mul hinput.le]
      norm_num
    have hcubic : ((alpha + delta) -
          limitingMap alpha (1 + muShift) (alpha + delta)) *
          fixedPointFactor alpha (1 + muShift) delta =
        delta ^ 3 + 3 * alpha * delta ^ 2 - 3 * alpha ^ 2 * muShift * delta := by
      have h2 : SilverCrossover.cubicResidual alpha (1 + muShift) (alpha + delta) =
          delta ^ 3 + 3 * alpha * delta ^ 2 - 3 * alpha ^ 2 * muShift * delta := by
        rw [SilverCrossover.cubicResidual_add_displacement]
        ring
      have h3 : SilverCrossover.cubicResidual alpha (1 + muShift) (alpha + delta) =
          (alpha + delta) ^ 3 -
            limitingMap alpha (1 + muShift) (alpha + delta) ^ 3 := by
        rw [hu3]
        simp only [SilverCrossover.cubicResidual, affineInput]
      have h4 : (alpha + delta) ^ 3 -
            limitingMap alpha (1 + muShift) (alpha + delta) ^ 3 =
          delta ^ 3 + 3 * alpha * delta ^ 2 - 3 * alpha ^ 2 * muShift * delta := by
        rw [← h3, h2]
      simp only [fixedPointFactor]
      linear_combination h4
    simp only [SilverCrossover.quadraticCrossover, centerRemainder] at heq
    rw [eq_div_iff (by positivity : (3 : Real) * alpha ≠ 0)] at heq
    have hkey : packetDeviation N alpha (1 + muShift) (alpha + delta) *
          fixedPointFactor alpha (1 + muShift) delta =
        ((alpha + delta) - limitingMap alpha (1 + muShift) (alpha + delta)) *
          fixedPointFactor alpha (1 + muShift) delta := by
      linear_combination -heq - hcubic
    have hP := mul_right_cancel₀ (ne_of_gt hF) hkey
    simp only [packetDeviation] at hP
    linarith

noncomputable def signedRelativeCenterRemainder
    (N : Nat) (alpha lambda y : Real) : Real :=
  centerRemainder N alpha
      (movingMuShift N alpha lambda)
      (movingDelta N alpha y) /
    (alpha * |centerError N alpha|)

theorem abs_signedRelativeCenterRemainder
    (N : Nat) {alpha lambda y : Real} (halpha : 0 ≤ alpha) :
    |signedRelativeCenterRemainder N alpha lambda y| =
      relativeCenterRemainder N alpha lambda y := by
  simp only [signedRelativeCenterRemainder, relativeCenterRemainder, abs_div,
    abs_mul, abs_abs, abs_of_nonneg halpha]

theorem tendsto_adaptiveRow_signedRelativeCenterRemainder
    {alpha lambda y : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        signedRelativeCenterRemainder (adaptiveRow N alpha) alpha lambda y)
      Filter.atTop (nhds 0) := by
  have halpha0 : (0 : Real) ≤ alpha := le_of_lt (lt_trans one_pos halpha)
  refine squeeze_zero_norm (fun N => ?_)
    (tendsto_adaptiveRow_relativeCenterRemainder (alpha := alpha)
      (lambda := lambda) (y := y) halpha)
  rw [Real.norm_eq_abs, abs_signedRelativeCenterRemainder _ halpha0]

noncomputable def normalizedCrossoverResidual
    (N : Nat) (alpha lambda y : Real) : Real :=
  (SilverCrossover.quadraticCrossover alpha (centerError N alpha)
        (movingMuShift N alpha lambda) (movingDelta N alpha y) -
      centerRemainder N alpha
        (movingMuShift N alpha lambda) (movingDelta N alpha y)) /
    (alpha * |centerError N alpha|)

theorem normalizedCrossoverResidual_eq_zero_iff_fixed
    {N : Nat} {alpha lambda y : Real}
    (halpha : 0 < alpha) (herror : centerError N alpha ≠ 0)
    (hinput :
      0 < affineInput alpha (1 + movingMuShift N alpha lambda)
        (alpha + movingDelta N alpha y)) :
    normalizedCrossoverResidual N alpha lambda y = 0 ↔
      finiteMap N alpha (1 + movingMuShift N alpha lambda)
          (alpha + movingDelta N alpha y) =
        alpha + movingDelta N alpha y := by
  have hne : alpha * |centerError N alpha| ≠ 0 :=
    ne_of_gt (mul_pos halpha (abs_pos.mpr herror))
  rw [normalizedCrossoverResidual, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact (finiteMap_eq_self_iff_quadraticCrossover_eq_centerRemainder
        (N := N) halpha hinput).mpr (sub_eq_zero.mp h)
    · exact absurd h hne
  · intro h
    exact Or.inl (sub_eq_zero.mpr
      ((finiteMap_eq_self_iff_quadraticCrossover_eq_centerRemainder
        (N := N) halpha hinput).mp h))

theorem normalizedCrossoverResidual_eq_positive
    {N : Nat} {alpha lambda y : Real}
    (halpha : 0 < alpha) (herror : 0 < centerError N alpha) :
    normalizedCrossoverResidual N alpha lambda y =
      (y ^ 2 - lambda * y - 1) -
        signedRelativeCenterRemainder N alpha lambda y := by
  have hE : |centerError N alpha| = centerError N alpha := abs_of_pos herror
  have hq := SilverCrossover.quadraticCrossover_rescale_pos
    (alpha := alpha) (packetError := centerError N alpha)
    (lambda := lambda) (y := y) halpha herror
  simp only [normalizedCrossoverResidual, signedRelativeCenterRemainder,
    movingMuShift, movingDelta, movingCrossoverScale]
  rw [hq, hE]
  field_simp

theorem normalizedCrossoverResidual_eq_negative
    {N : Nat} {alpha lambda y : Real}
    (halpha : 0 < alpha) (herror : centerError N alpha < 0) :
    normalizedCrossoverResidual N alpha lambda y =
      (y ^ 2 - lambda * y + 1) -
        signedRelativeCenterRemainder N alpha lambda y := by
  have hE : |centerError N alpha| = -centerError N alpha := abs_of_neg herror
  have hq := SilverCrossover.quadraticCrossover_rescale_neg
    (alpha := alpha) (packetError := centerError N alpha)
    (lambda := lambda) (y := y) halpha herror
  simp only [normalizedCrossoverResidual, signedRelativeCenterRemainder,
    movingMuShift, movingDelta, movingCrossoverScale]
  rw [hq, hE]
  have hEne : centerError N alpha ≠ 0 := ne_of_lt herror
  field_simp
  ring

theorem tendsto_reindexed_adaptiveRow_normalizedCrossoverResidual_positive
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda y : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      0 < centerError (adaptiveRow (u n) alpha) alpha) :
    Filter.Tendsto
      (fun n : Nat =>
        normalizedCrossoverResidual (adaptiveRow (u n) alpha)
          alpha lambda y)
      Filter.atTop (nhds (y ^ 2 - lambda * y - 1)) := by
  have halpha0 : (0 : Real) < alpha := lt_trans one_pos halpha
  have hs : Filter.Tendsto
      (fun n : Nat =>
        signedRelativeCenterRemainder (adaptiveRow (u n) alpha) alpha lambda y)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_adaptiveRow_signedRelativeCenterRemainder
      (alpha := alpha) (lambda := lambda) (y := y) halpha).comp hu
    simpa [Function.comp_def] using h
  have hlim : Filter.Tendsto
      (fun n : Nat =>
        (y ^ 2 - lambda * y - 1) -
          signedRelativeCenterRemainder (adaptiveRow (u n) alpha) alpha lambda y)
      Filter.atTop (nhds (y ^ 2 - lambda * y - 1)) := by
    simpa using (tendsto_const_nhds (x := y ^ 2 - lambda * y - 1)
      (f := Filter.atTop (α := Nat))).sub hs
  refine hlim.congr' ?_
  filter_upwards [hsign] with n hn
  exact (normalizedCrossoverResidual_eq_positive halpha0 hn).symm

theorem tendsto_reindexed_adaptiveRow_normalizedCrossoverResidual_negative
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda y : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      centerError (adaptiveRow (u n) alpha) alpha < 0) :
    Filter.Tendsto
      (fun n : Nat =>
        normalizedCrossoverResidual (adaptiveRow (u n) alpha)
          alpha lambda y)
      Filter.atTop (nhds (y ^ 2 - lambda * y + 1)) := by
  have halpha0 : (0 : Real) < alpha := lt_trans one_pos halpha
  have hs : Filter.Tendsto
      (fun n : Nat =>
        signedRelativeCenterRemainder (adaptiveRow (u n) alpha) alpha lambda y)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_adaptiveRow_signedRelativeCenterRemainder
      (alpha := alpha) (lambda := lambda) (y := y) halpha).comp hu
    simpa [Function.comp_def] using h
  have hlim : Filter.Tendsto
      (fun n : Nat =>
        (y ^ 2 - lambda * y + 1) -
          signedRelativeCenterRemainder (adaptiveRow (u n) alpha) alpha lambda y)
      Filter.atTop (nhds (y ^ 2 - lambda * y + 1)) := by
    simpa using (tendsto_const_nhds (x := y ^ 2 - lambda * y + 1)
      (f := Filter.atTop (α := Nat))).sub hs
  refine hlim.congr' ?_
  filter_upwards [hsign] with n hn
  exact (normalizedCrossoverResidual_eq_negative halpha0 hn).symm

end SilverFiniteRow
