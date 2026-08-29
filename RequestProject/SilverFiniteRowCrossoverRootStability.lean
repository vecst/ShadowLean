/-
Cubic-silver finite-row crossover, Phase B4B2: local finite-row crossover-root
stability near simple limiting roots.

All eight targets are proved; signatures are verbatim from the harness.

The phase is CONDITIONAL: everything below is stated relative to an explicitly
supplied cofinal reindexing `u` and an eventually-fixed sign of the selected
center error.  No claim is made that either sign occurs cofinally.  The last two
targets certify EVENTUAL EXISTENCE of some finite-row fixed point in every
prescribed neighbourhood of a simple limiting root; they do not single out a
canonical branch and do not assert convergence of a chosen root sequence.  The
negative-channel double-root cases `|lambda| = 2` are excluded by `hsimple`.
-/
import RequestProject.SilverFiniteRowCrossoverResidual

open scoped Real Topology
open Filter

namespace SilverFiniteRow

/-- An affine function that is positive at both endpoints of a bracket is
positive throughout it. -/
private theorem affine_pos_of_endpoints {E C a b y : Real}
    (hya : a ≤ y) (hyb : y ≤ b)
    (hA : 0 < E + C * a) (hB : 0 < E + C * b) :
    0 < E + C * y := by
  rcases le_total 0 C with h | h
  · nlinarith [mul_nonneg h (sub_nonneg.mpr hya)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr h) (sub_nonneg.mpr hyb)]

/-- The moving affine input is an affine function of the normalized coordinate
`y`, with intercept `alpha ^ 3`. -/
private theorem affineInput_moving_eq (N : Nat) (alpha lambda y : Real) :
    affineInput alpha (1 + movingMuShift N alpha lambda)
        (alpha + movingDelta N alpha y) =
      alpha ^ 3 +
        (3 * (1 + movingMuShift N alpha lambda) * alpha ^ 2 *
          movingCrossoverScale N alpha) * y := by
  simp only [affineInput, movingDelta, SilverCrossover.affineIntercept,
    SilverCrossover.affineSlope]
  ring

/-- The moving affine input is continuous in the normalized coordinate. -/
private theorem continuousOn_moving_affineInput
    (N : Nat) (alpha lambda a b : Real) :
    ContinuousOn
      (fun y : Real =>
        affineInput alpha (1 + movingMuShift N alpha lambda)
          (alpha + movingDelta N alpha y))
      (Set.Icc a b) := by
  simp only [affineInput_moving_eq]
  fun_prop

/-- The limiting cube-root map is continuous in the normalized coordinate. -/
private theorem continuousOn_moving_limitingMap
    (N : Nat) (alpha lambda a b : Real) :
    ContinuousOn
      (fun y : Real =>
        limitingMap alpha (1 + movingMuShift N alpha lambda)
          (alpha + movingDelta N alpha y))
      (Set.Icc a b) := by
  simp only [limitingMap]
  exact (continuousOn_moving_affineInput N alpha lambda a b).rpow_const
    (fun _ _ => Or.inr (by norm_num))

/-- The finite-row packet map is continuous in the normalized coordinate on a
bracket where the affine input stays strictly positive. -/
private theorem continuousOn_moving_finiteMap
    {N : Nat} {alpha lambda a b : Real}
    (hinput : ∀ y ∈ Set.Icc a b,
      0 < affineInput alpha (1 + movingMuShift N alpha lambda)
        (alpha + movingDelta N alpha y)) :
    ContinuousOn
      (fun y : Real =>
        finiteMap N alpha (1 + movingMuShift N alpha lambda)
          (alpha + movingDelta N alpha y))
      (Set.Icc a b) := by
  have hA := continuousOn_moving_affineInput N alpha lambda a b
  simp only [finiteMap, packetRatio]
  refine ContinuousOn.div ((continuous_revA 3 1 N).comp_continuousOn hA)
    ((continuous_revA 3 0 N).comp_continuousOn hA) ?_
  intro y hy
  exact ne_of_gt (packetRatio_den_pos N (hinput y hy))

/-- The packet deviation is continuous in the normalized coordinate. -/
private theorem continuousOn_moving_packetDeviation
    {N : Nat} {alpha lambda a b : Real}
    (hinput : ∀ y ∈ Set.Icc a b,
      0 < affineInput alpha (1 + movingMuShift N alpha lambda)
        (alpha + movingDelta N alpha y)) :
    ContinuousOn
      (fun y : Real =>
        packetDeviation N alpha (1 + movingMuShift N alpha lambda)
          (alpha + movingDelta N alpha y))
      (Set.Icc a b) := by
  simp only [packetDeviation]
  exact (continuousOn_moving_finiteMap hinput).sub
    (continuousOn_moving_limitingMap N alpha lambda a b)

/-- The fixed-point factor is continuous in the normalized coordinate. -/
private theorem continuousOn_moving_fixedPointFactor
    (N : Nat) (alpha lambda a b : Real) :
    ContinuousOn
      (fun y : Real =>
        fixedPointFactor alpha (1 + movingMuShift N alpha lambda)
          (movingDelta N alpha y))
      (Set.Icc a b) := by
  have hL := continuousOn_moving_limitingMap N alpha lambda a b
  have hz : ContinuousOn
      (fun y : Real => alpha + movingDelta N alpha y) (Set.Icc a b) := by
    simp only [movingDelta]
    fun_prop
  simp only [fixedPointFactor]
  exact ((hz.pow 2).add (hz.mul hL)).add (hL.pow 2)

/-- The center remainder is continuous in the normalized coordinate. -/
private theorem continuousOn_moving_centerRemainder
    {N : Nat} {alpha lambda a b : Real}
    (hinput : ∀ y ∈ Set.Icc a b,
      0 < affineInput alpha (1 + movingMuShift N alpha lambda)
        (alpha + movingDelta N alpha y)) :
    ContinuousOn
      (fun y : Real =>
        centerRemainder N alpha (movingMuShift N alpha lambda)
          (movingDelta N alpha y))
      (Set.Icc a b) := by
  have hd : ContinuousOn
      (fun y : Real => movingDelta N alpha y) (Set.Icc a b) := by
    simp only [movingDelta]
    fun_prop
  simp only [centerRemainder]
  exact ((((continuousOn_moving_packetDeviation hinput).mul
    (continuousOn_moving_fixedPointFactor N alpha lambda a b)).sub
      (hd.pow 3)).sub continuousOn_const).div_const _

theorem eventually_reindexed_adaptiveRow_affineInput_pos_on_Icc
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda a b : Real} (halpha : 1 < alpha) :
    ∀ᶠ n in Filter.atTop, ∀ y ∈ Set.Icc a b,
      0 < affineInput alpha
        (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
        (alpha + movingDelta (adaptiveRow (u n) alpha) alpha y) := by
  have halpha0 : (0 : Real) < alpha := lt_trans one_pos halpha
  have hJ : Filter.Tendsto (fun n : Nat => adaptiveRow (u n) alpha)
      Filter.atTop Filter.atTop := by
    simpa [Function.comp_def] using (tendsto_adaptiveRow alpha).comp hu
  have ha := hJ.eventually
    (eventually_moving_affineInput_pos (alpha := alpha) (lambda := lambda)
      (y := a) halpha0)
  have hb := hJ.eventually
    (eventually_moving_affineInput_pos (alpha := alpha) (lambda := lambda)
      (y := b) halpha0)
  filter_upwards [ha, hb] with n hna hnb y hy
  rw [affineInput_moving_eq] at hna hnb ⊢
  exact affine_pos_of_endpoints hy.1 hy.2 hna hnb

theorem continuousOn_normalizedCrossoverResidual
    {N : Nat} {alpha lambda a b : Real}
    (halpha : 0 < alpha) (herror : centerError N alpha ≠ 0)
    (hinput : ∀ y ∈ Set.Icc a b,
      0 < affineInput alpha (1 + movingMuShift N alpha lambda)
        (alpha + movingDelta N alpha y)) :
    ContinuousOn
      (fun y : Real => normalizedCrossoverResidual N alpha lambda y)
      (Set.Icc a b) := by
  have hd : ContinuousOn
      (fun y : Real => movingDelta N alpha y) (Set.Icc a b) := by
    simp only [movingDelta]
    fun_prop
  have hquad : ContinuousOn
      (fun y : Real =>
        SilverCrossover.quadraticCrossover alpha (centerError N alpha)
          (movingMuShift N alpha lambda) (movingDelta N alpha y))
      (Set.Icc a b) := by
    simp only [SilverCrossover.quadraticCrossover]
    exact ((hd.pow 2).sub ((continuousOn_const.mul hd))).sub continuousOn_const
  have hne : alpha * |centerError N alpha| ≠ 0 :=
    ne_of_gt (mul_pos halpha (abs_pos.mpr herror))
  simp only [normalizedCrossoverResidual]
  exact (hquad.sub (continuousOn_moving_centerRemainder hinput)).div
    continuousOn_const (fun _ _ => hne)

theorem eventually_reindexed_normalizedCrossoverResidual_bracket_positive
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda a b : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      0 < centerError (adaptiveRow (u n) alpha) alpha)
    (hbracket :
      ((a ^ 2 - lambda * a - 1 < 0) ∧
          (0 < b ^ 2 - lambda * b - 1)) ∨
        ((b ^ 2 - lambda * b - 1 < 0) ∧
          (0 < a ^ 2 - lambda * a - 1))) :
    ∀ᶠ n in Filter.atTop,
      ((normalizedCrossoverResidual (adaptiveRow (u n) alpha)
            alpha lambda a < 0) ∧
        (0 < normalizedCrossoverResidual (adaptiveRow (u n) alpha)
            alpha lambda b)) ∨
      ((normalizedCrossoverResidual (adaptiveRow (u n) alpha)
            alpha lambda b < 0) ∧
        (0 < normalizedCrossoverResidual (adaptiveRow (u n) alpha)
            alpha lambda a)) := by
  have hta := tendsto_reindexed_adaptiveRow_normalizedCrossoverResidual_positive
    hu (alpha := alpha) (lambda := lambda) (y := a) halpha hsign
  have htb := tendsto_reindexed_adaptiveRow_normalizedCrossoverResidual_positive
    hu (alpha := alpha) (lambda := lambda) (y := b) halpha hsign
  rcases hbracket with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · filter_upwards [hta.eventually (eventually_lt_nhds h1),
      htb.eventually (eventually_gt_nhds h2)] with n hA hB
    exact Or.inl ⟨hA, hB⟩
  · filter_upwards [htb.eventually (eventually_lt_nhds h1),
      hta.eventually (eventually_gt_nhds h2)] with n hB hA
    exact Or.inr ⟨hB, hA⟩

theorem eventually_reindexed_normalizedCrossoverResidual_bracket_negative
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda a b : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      centerError (adaptiveRow (u n) alpha) alpha < 0)
    (hbracket :
      ((a ^ 2 - lambda * a + 1 < 0) ∧
          (0 < b ^ 2 - lambda * b + 1)) ∨
        ((b ^ 2 - lambda * b + 1 < 0) ∧
          (0 < a ^ 2 - lambda * a + 1))) :
    ∀ᶠ n in Filter.atTop,
      ((normalizedCrossoverResidual (adaptiveRow (u n) alpha)
            alpha lambda a < 0) ∧
        (0 < normalizedCrossoverResidual (adaptiveRow (u n) alpha)
            alpha lambda b)) ∨
      ((normalizedCrossoverResidual (adaptiveRow (u n) alpha)
            alpha lambda b < 0) ∧
        (0 < normalizedCrossoverResidual (adaptiveRow (u n) alpha)
            alpha lambda a)) := by
  have hta := tendsto_reindexed_adaptiveRow_normalizedCrossoverResidual_negative
    hu (alpha := alpha) (lambda := lambda) (y := a) halpha hsign
  have htb := tendsto_reindexed_adaptiveRow_normalizedCrossoverResidual_negative
    hu (alpha := alpha) (lambda := lambda) (y := b) halpha hsign
  rcases hbracket with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · filter_upwards [hta.eventually (eventually_lt_nhds h1),
      htb.eventually (eventually_gt_nhds h2)] with n hA hB
    exact Or.inl ⟨hA, hB⟩
  · filter_upwards [htb.eventually (eventually_lt_nhds h1),
      hta.eventually (eventually_gt_nhds h2)] with n hB hA
    exact Or.inr ⟨hB, hA⟩

theorem eventually_exists_positive_crossover_fixedPoint_in_bracket
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda a b : Real} (halpha : 1 < alpha) (hab : a ≤ b)
    (hsign : ∀ᶠ n in Filter.atTop,
      0 < centerError (adaptiveRow (u n) alpha) alpha)
    (hbracket :
      ((a ^ 2 - lambda * a - 1 < 0) ∧
          (0 < b ^ 2 - lambda * b - 1)) ∨
        ((b ^ 2 - lambda * b - 1 < 0) ∧
          (0 < a ^ 2 - lambda * a - 1))) :
    ∀ᶠ n in Filter.atTop, ∃ y ∈ Set.Icc a b,
      finiteMap (adaptiveRow (u n) alpha) alpha
          (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
          (alpha + movingDelta (adaptiveRow (u n) alpha) alpha y) =
        alpha + movingDelta (adaptiveRow (u n) alpha) alpha y := by
  have halpha0 : (0 : Real) < alpha := lt_trans one_pos halpha
  have hin := eventually_reindexed_adaptiveRow_affineInput_pos_on_Icc
    hu (alpha := alpha) (lambda := lambda) (a := a) (b := b) halpha
  have hbr := eventually_reindexed_normalizedCrossoverResidual_bracket_positive
    hu halpha hsign hbracket
  filter_upwards [hin, hbr, hsign] with n hinp hbrk hs
  have herror : centerError (adaptiveRow (u n) alpha) alpha ≠ 0 := ne_of_gt hs
  have hcont := continuousOn_normalizedCrossoverResidual
    (N := adaptiveRow (u n) alpha) (lambda := lambda) halpha0 herror hinp
  rcases hbrk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hab hcont ⟨h1.le, h2.le⟩
    exact ⟨y, hy, (normalizedCrossoverResidual_eq_zero_iff_fixed halpha0 herror
      (hinp y hy)).mp hy0⟩
  · obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' hab hcont ⟨h1.le, h2.le⟩
    exact ⟨y, hy, (normalizedCrossoverResidual_eq_zero_iff_fixed halpha0 herror
      (hinp y hy)).mp hy0⟩

theorem eventually_exists_negative_crossover_fixedPoint_in_bracket
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda a b : Real} (halpha : 1 < alpha) (hab : a ≤ b)
    (hsign : ∀ᶠ n in Filter.atTop,
      centerError (adaptiveRow (u n) alpha) alpha < 0)
    (hbracket :
      ((a ^ 2 - lambda * a + 1 < 0) ∧
          (0 < b ^ 2 - lambda * b + 1)) ∨
        ((b ^ 2 - lambda * b + 1 < 0) ∧
          (0 < a ^ 2 - lambda * a + 1))) :
    ∀ᶠ n in Filter.atTop, ∃ y ∈ Set.Icc a b,
      finiteMap (adaptiveRow (u n) alpha) alpha
          (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
          (alpha + movingDelta (adaptiveRow (u n) alpha) alpha y) =
        alpha + movingDelta (adaptiveRow (u n) alpha) alpha y := by
  have halpha0 : (0 : Real) < alpha := lt_trans one_pos halpha
  have hin := eventually_reindexed_adaptiveRow_affineInput_pos_on_Icc
    hu (alpha := alpha) (lambda := lambda) (a := a) (b := b) halpha
  have hbr := eventually_reindexed_normalizedCrossoverResidual_bracket_negative
    hu halpha hsign hbracket
  filter_upwards [hin, hbr, hsign] with n hinp hbrk hs
  have herror : centerError (adaptiveRow (u n) alpha) alpha ≠ 0 := ne_of_lt hs
  have hcont := continuousOn_normalizedCrossoverResidual
    (N := adaptiveRow (u n) alpha) (lambda := lambda) halpha0 herror hinp
  rcases hbrk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hab hcont ⟨h1.le, h2.le⟩
    exact ⟨y, hy, (normalizedCrossoverResidual_eq_zero_iff_fixed halpha0 herror
      (hinp y hy)).mp hy0⟩
  · obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' hab hcont ⟨h1.le, h2.le⟩
    exact ⟨y, hy, (normalizedCrossoverResidual_eq_zero_iff_fixed halpha0 herror
      (hinp y hy)).mp hy0⟩

theorem eventually_exists_positive_crossover_fixedPoint_near_simple_root
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda y0 epsilon : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      0 < centerError (adaptiveRow (u n) alpha) alpha)
    (hroot : y0 ^ 2 - lambda * y0 - 1 = 0)
    (hsimple : 2 * y0 - lambda ≠ 0) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in Filter.atTop, ∃ y : Real,
      |y - y0| < epsilon ∧
      finiteMap (adaptiveRow (u n) alpha) alpha
          (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
          (alpha + movingDelta (adaptiveRow (u n) alpha) alpha y) =
        alpha + movingDelta (adaptiveRow (u n) alpha) alpha y := by
  have habs : 0 < |2 * y0 - lambda| := abs_pos.mpr hsimple
  set d : Real := min (epsilon / 2) (|2 * y0 - lambda| / 2) with hd_def
  have hd0 : 0 < d := lt_min (by linarith) (by linarith)
  have hde : d < epsilon := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdl : d < |2 * y0 - lambda| :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hab : y0 - d ≤ y0 + d := by linarith
  have hpa : (y0 - d) ^ 2 - lambda * (y0 - d) - 1 =
      (-d) * (2 * y0 - lambda - d) := by linear_combination hroot
  have hpb : (y0 + d) ^ 2 - lambda * (y0 + d) - 1 =
      d * (2 * y0 - lambda + d) := by linear_combination hroot
  have hbracket :
      (((y0 - d) ^ 2 - lambda * (y0 - d) - 1 < 0) ∧
          (0 < (y0 + d) ^ 2 - lambda * (y0 + d) - 1)) ∨
        (((y0 + d) ^ 2 - lambda * (y0 + d) - 1 < 0) ∧
          (0 < (y0 - d) ^ 2 - lambda * (y0 - d) - 1)) := by
    rcases lt_or_gt_of_ne hsimple with hneg | hpos
    · have hval : |2 * y0 - lambda| = -(2 * y0 - lambda) := abs_of_neg hneg
      rw [hval] at hdl
      refine Or.inr ⟨?_, ?_⟩
      · rw [hpb]; nlinarith
      · rw [hpa]; nlinarith
    · have hval : |2 * y0 - lambda| = 2 * y0 - lambda := abs_of_pos hpos
      rw [hval] at hdl
      refine Or.inl ⟨?_, ?_⟩
      · rw [hpa]; nlinarith
      · rw [hpb]; nlinarith
  have hmain := eventually_exists_positive_crossover_fixedPoint_in_bracket
    hu (alpha := alpha) (lambda := lambda) (a := y0 - d) (b := y0 + d)
    halpha hab hsign hbracket
  filter_upwards [hmain] with n hn
  obtain ⟨y, hy, hfix⟩ := hn
  exact ⟨y, abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩, hfix⟩

theorem eventually_exists_negative_crossover_fixedPoint_near_simple_root
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda y0 epsilon : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      centerError (adaptiveRow (u n) alpha) alpha < 0)
    (hroot : y0 ^ 2 - lambda * y0 + 1 = 0)
    (hsimple : 2 * y0 - lambda ≠ 0) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in Filter.atTop, ∃ y : Real,
      |y - y0| < epsilon ∧
      finiteMap (adaptiveRow (u n) alpha) alpha
          (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
          (alpha + movingDelta (adaptiveRow (u n) alpha) alpha y) =
        alpha + movingDelta (adaptiveRow (u n) alpha) alpha y := by
  have habs : 0 < |2 * y0 - lambda| := abs_pos.mpr hsimple
  set d : Real := min (epsilon / 2) (|2 * y0 - lambda| / 2) with hd_def
  have hd0 : 0 < d := lt_min (by linarith) (by linarith)
  have hde : d < epsilon := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdl : d < |2 * y0 - lambda| :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hab : y0 - d ≤ y0 + d := by linarith
  have hpa : (y0 - d) ^ 2 - lambda * (y0 - d) + 1 =
      (-d) * (2 * y0 - lambda - d) := by linear_combination hroot
  have hpb : (y0 + d) ^ 2 - lambda * (y0 + d) + 1 =
      d * (2 * y0 - lambda + d) := by linear_combination hroot
  have hbracket :
      (((y0 - d) ^ 2 - lambda * (y0 - d) + 1 < 0) ∧
          (0 < (y0 + d) ^ 2 - lambda * (y0 + d) + 1)) ∨
        (((y0 + d) ^ 2 - lambda * (y0 + d) + 1 < 0) ∧
          (0 < (y0 - d) ^ 2 - lambda * (y0 - d) + 1)) := by
    rcases lt_or_gt_of_ne hsimple with hneg | hpos
    · have hval : |2 * y0 - lambda| = -(2 * y0 - lambda) := abs_of_neg hneg
      rw [hval] at hdl
      refine Or.inr ⟨?_, ?_⟩
      · rw [hpb]; nlinarith
      · rw [hpa]; nlinarith
    · have hval : |2 * y0 - lambda| = 2 * y0 - lambda := abs_of_pos hpos
      rw [hval] at hdl
      refine Or.inl ⟨?_, ?_⟩
      · rw [hpa]; nlinarith
      · rw [hpb]; nlinarith
  have hmain := eventually_exists_negative_crossover_fixedPoint_in_bracket
    hu (alpha := alpha) (lambda := lambda) (a := y0 - d) (b := y0 + d)
    halpha hab hsign hbracket
  filter_upwards [hmain] with n hn
  obtain ⟨y, hy, hfix⟩ := hn
  exact ⟨y, abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩, hfix⟩

end SilverFiniteRow
