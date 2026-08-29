/-
Cubic-silver finite-row crossover, Phase B4B3: select one convergent finite-row
crossover branch from the B4B2 local-existence theorem.
Signatures verbatim from the Phase B4B3 targets; all four bodies are proved.

The selection is classical: it produces ONE convergent sequence of finite-row
crossover fixed points, and is neither claimed unique nor canonical. The result
stays conditional on the supplied cofinal reindexing u and on the eventually
fixed sign of the selected center error; no cofinal-sign claim is made.
Negative-channel double roots |lambda| = 2 remain excluded by hsimple. The
branch lives in normalized y-coordinates, and the second Tendsto clause records
that the unscaled fixed-point values alpha + movingDelta ... converge to alpha.
-/
import RequestProject.SilverFiniteRowCrossoverRootStability

open scoped Real Topology
open Filter

namespace SilverFiniteRow

theorem exists_tendsto_selection_of_eventually_exists_near
    {P : Nat → Real → Prop} {y0 : Real}
    (hlocal : ∀ epsilon : Real, 0 < epsilon →
      ∀ᶠ n in Filter.atTop, ∃ y : Real,
        |y - y0| < epsilon ∧ P n y) :
    ∃ y : Nat → Real,
      Filter.Tendsto y Filter.atTop (nhds y0) ∧
      ∀ᶠ n in Filter.atTop, P n (y n) := by
  classical
  have hex : ∀ k : Nat, ∃ N : Nat, ∀ n, N ≤ n → ∃ y : Real,
      |y - y0| < 1 / ((k : Real) + 1) ∧ P n y := by
    intro k
    have hpos : (0 : Real) < 1 / ((k : Real) + 1) := by positivity
    exact Filter.eventually_atTop.mp (hlocal _ hpos)
  choose N hN using hex
  set M : Nat → Nat := fun k => (Finset.range (k + 1)).sup N with hMdef
  have hNM : ∀ k, N k ≤ M k := by
    intro k
    exact Finset.le_sup (f := N) (by simp)
  set K : Nat → Nat := fun n => Nat.findGreatest (fun k => M k ≤ n) n with hKdef
  have hKspec : ∀ n, M 0 ≤ n → M (K n) ≤ n := by
    intro n hn
    exact Nat.findGreatest_spec (P := fun k => M k ≤ n) (Nat.zero_le n) hn
  have hKle : ∀ k n, k ≤ n → M k ≤ n → k ≤ K n := by
    intro k n hkn hMk
    exact Nat.le_findGreatest (P := fun k => M k ≤ n) hkn hMk
  have hsel : ∀ n, M 0 ≤ n → ∃ z : Real,
      |z - y0| < 1 / ((K n : Real) + 1) ∧ P n z := by
    intro n hn
    exact hN (K n) n (le_trans (hNM _) (hKspec n hn))
  refine ⟨fun n =>
    if h : ∃ z : Real, |z - y0| < 1 / ((K n : Real) + 1) ∧ P n z then
      Classical.choose h else y0, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro eps heps
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt heps
    refine ⟨max (max (M 0) (M k)) k, ?_⟩
    intro n hn
    have hn0 : M 0 ≤ n :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnk : M k ≤ n :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hkn : k ≤ n := le_trans (le_max_right _ _) hn
    have hle : k ≤ K n := hKle k n hkn hnk
    have hspec := Classical.choose_spec (hsel n hn0)
    simp only [dif_pos (hsel n hn0)]
    have h2 : 1 / ((K n : Real) + 1) ≤ 1 / ((k : Real) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hle 1
    rw [Real.dist_eq]
    calc |Classical.choose (hsel n hn0) - y0|
        < 1 / ((K n : Real) + 1) := hspec.1
      _ ≤ 1 / ((k : Real) + 1) := h2
      _ < eps := hk
  · rw [Filter.eventually_atTop]
    refine ⟨M 0, fun n hn => ?_⟩
    simp only [dif_pos (hsel n hn)]
    exact (Classical.choose_spec (hsel n hn)).2

theorem tendsto_reindexed_moving_fixedPoint_value
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha y0 : Real} (halpha : 0 < alpha)
    {y : Nat → Real} (hy : Filter.Tendsto y Filter.atTop (nhds y0)) :
    Filter.Tendsto
      (fun n : Nat =>
        alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n))
      Filter.atTop (nhds alpha) := by
  have hJ : Filter.Tendsto (fun n : Nat => adaptiveRow (u n) alpha)
      Filter.atTop Filter.atTop := by
    simpa [Function.comp_def] using (tendsto_adaptiveRow alpha).comp hu
  have hscale : Filter.Tendsto
      (fun n : Nat => movingCrossoverScale (adaptiveRow (u n) alpha) alpha)
      Filter.atTop (nhds 0) :=
    (tendsto_movingCrossoverScale halpha).comp hJ
  have hprod : Filter.Tendsto
      (fun n : Nat =>
        movingCrossoverScale (adaptiveRow (u n) alpha) alpha * y n)
      Filter.atTop (nhds 0) := by
    simpa using hscale.mul hy
  simpa [movingDelta] using hprod.const_add alpha

theorem exists_tendsto_positive_crossover_fixedPoint_branch
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda y0 : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      0 < centerError (adaptiveRow (u n) alpha) alpha)
    (hroot : y0 ^ 2 - lambda * y0 - 1 = 0)
    (hsimple : 2 * y0 - lambda ≠ 0) :
    ∃ y : Nat → Real,
      Filter.Tendsto y Filter.atTop (nhds y0) ∧
      Filter.Tendsto
        (fun n : Nat =>
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n))
        Filter.atTop (nhds alpha) ∧
      ∀ᶠ n in Filter.atTop,
        finiteMap (adaptiveRow (u n) alpha) alpha
            (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
            (alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n)) =
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n) := by
  have hlocal : ∀ epsilon : Real, 0 < epsilon →
      ∀ᶠ n in Filter.atTop, ∃ y : Real,
        |y - y0| < epsilon ∧
        finiteMap (adaptiveRow (u n) alpha) alpha
            (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
            (alpha + movingDelta (adaptiveRow (u n) alpha) alpha y) =
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha y :=
    fun epsilon hepsilon =>
      eventually_exists_positive_crossover_fixedPoint_near_simple_root hu halpha hsign
        hroot hsimple hepsilon
  obtain ⟨y, hytends, hP⟩ :=
    exists_tendsto_selection_of_eventually_exists_near hlocal
  exact ⟨y, hytends,
    tendsto_reindexed_moving_fixedPoint_value hu (lt_trans one_pos halpha) hytends,
    hP⟩

theorem exists_tendsto_negative_crossover_fixedPoint_branch
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda y0 : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      centerError (adaptiveRow (u n) alpha) alpha < 0)
    (hroot : y0 ^ 2 - lambda * y0 + 1 = 0)
    (hsimple : 2 * y0 - lambda ≠ 0) :
    ∃ y : Nat → Real,
      Filter.Tendsto y Filter.atTop (nhds y0) ∧
      Filter.Tendsto
        (fun n : Nat =>
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n))
        Filter.atTop (nhds alpha) ∧
      ∀ᶠ n in Filter.atTop,
        finiteMap (adaptiveRow (u n) alpha) alpha
            (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
            (alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n)) =
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n) := by
  have hlocal : ∀ epsilon : Real, 0 < epsilon →
      ∀ᶠ n in Filter.atTop, ∃ y : Real,
        |y - y0| < epsilon ∧
        finiteMap (adaptiveRow (u n) alpha) alpha
            (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
            (alpha + movingDelta (adaptiveRow (u n) alpha) alpha y) =
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha y :=
    fun epsilon hepsilon =>
      eventually_exists_negative_crossover_fixedPoint_near_simple_root hu halpha hsign
        hroot hsimple hepsilon
  obtain ⟨y, hytends, hP⟩ :=
    exists_tendsto_selection_of_eventually_exists_near hlocal
  exact ⟨y, hytends,
    tendsto_reindexed_moving_fixedPoint_value hu (lt_trans one_pos halpha) hytends,
    hP⟩

end SilverFiniteRow
