/-
Cubic-silver finite-row crossover, Phase B4B4: package the convergent crossover
branches at the explicit real quadratic roots.

Packages the B4B3 branch-selection theorem at the explicit real roots of Paper B.
The positive channel `y^2 - lambda*y - 1` has both roots
`(lambda +- sqrt (lambda^2 + 4)) / 2` real and simple for every real `lambda`.
The negative channel `y^2 - lambda*y + 1` has explicit real roots
`(lambda +- sqrt (lambda^2 - 4)) / 2` only under `2 < |lambda|` (the double-root
boundary `|lambda| = 2` is excluded; `|lambda| < 2` has no real branches). Every
branch theorem stays conditional on the supplied cofinal reindexing `u` and an
eventually-fixed selected-error sign; the selected sequences are existential, not
unique and not canonical.
-/
import RequestProject.SilverFiniteRowCrossoverBranchSelection

open scoped Real Topology
open Filter

namespace SilverFiniteRow

noncomputable def positiveCrossoverRootPlus (lambda : Real) : Real :=
  (lambda + Real.sqrt (lambda ^ 2 + 4)) / 2

noncomputable def positiveCrossoverRootMinus (lambda : Real) : Real :=
  (lambda - Real.sqrt (lambda ^ 2 + 4)) / 2

noncomputable def negativeCrossoverRootPlus (lambda : Real) : Real :=
  (lambda + Real.sqrt (lambda ^ 2 - 4)) / 2

noncomputable def negativeCrossoverRootMinus (lambda : Real) : Real :=
  (lambda - Real.sqrt (lambda ^ 2 - 4)) / 2

theorem positiveCrossoverRootPlus_spec (lambda : Real) :
    positiveCrossoverRootPlus lambda ^ 2 -
          lambda * positiveCrossoverRootPlus lambda - 1 = 0 ∧
      2 * positiveCrossoverRootPlus lambda - lambda ≠ 0 := by
  have hs2 : Real.sqrt (lambda ^ 2 + 4) ^ 2 = lambda ^ 2 + 4 :=
    Real.sq_sqrt (by positivity)
  have hs0 : 0 < Real.sqrt (lambda ^ 2 + 4) :=
    Real.sqrt_pos.mpr (SilverCrossover.positive_error_discriminant lambda)
  constructor
  · unfold positiveCrossoverRootPlus
    nlinarith [hs2]
  · unfold positiveCrossoverRootPlus
    have : 2 * ((lambda + Real.sqrt (lambda ^ 2 + 4)) / 2) - lambda =
        Real.sqrt (lambda ^ 2 + 4) := by ring
    rw [this]
    exact ne_of_gt hs0

theorem positiveCrossoverRootMinus_spec (lambda : Real) :
    positiveCrossoverRootMinus lambda ^ 2 -
          lambda * positiveCrossoverRootMinus lambda - 1 = 0 ∧
      2 * positiveCrossoverRootMinus lambda - lambda ≠ 0 := by
  have hs2 : Real.sqrt (lambda ^ 2 + 4) ^ 2 = lambda ^ 2 + 4 :=
    Real.sq_sqrt (by positivity)
  have hs0 : 0 < Real.sqrt (lambda ^ 2 + 4) :=
    Real.sqrt_pos.mpr (SilverCrossover.positive_error_discriminant lambda)
  constructor
  · unfold positiveCrossoverRootMinus
    nlinarith [hs2]
  · unfold positiveCrossoverRootMinus
    have : 2 * ((lambda - Real.sqrt (lambda ^ 2 + 4)) / 2) - lambda =
        -Real.sqrt (lambda ^ 2 + 4) := by ring
    rw [this]
    exact neg_ne_zero.mpr (ne_of_gt hs0)

theorem negativeCrossoverRootPlus_spec_of_two_lt_abs
    {lambda : Real} (hlambda : 2 < |lambda|) :
    negativeCrossoverRootPlus lambda ^ 2 -
          lambda * negativeCrossoverRootPlus lambda + 1 = 0 ∧
      2 * negativeCrossoverRootPlus lambda - lambda ≠ 0 := by
  have hd : 0 < lambda ^ 2 - 4 :=
    SilverCrossover.positive_discriminant_of_two_lt_abs hlambda
  have hs2 : Real.sqrt (lambda ^ 2 - 4) ^ 2 = lambda ^ 2 - 4 := Real.sq_sqrt hd.le
  have hs0 : 0 < Real.sqrt (lambda ^ 2 - 4) := Real.sqrt_pos.mpr hd
  constructor
  · unfold negativeCrossoverRootPlus
    nlinarith [hs2]
  · unfold negativeCrossoverRootPlus
    have : 2 * ((lambda + Real.sqrt (lambda ^ 2 - 4)) / 2) - lambda =
        Real.sqrt (lambda ^ 2 - 4) := by ring
    rw [this]
    exact ne_of_gt hs0

theorem negativeCrossoverRootMinus_spec_of_two_lt_abs
    {lambda : Real} (hlambda : 2 < |lambda|) :
    negativeCrossoverRootMinus lambda ^ 2 -
          lambda * negativeCrossoverRootMinus lambda + 1 = 0 ∧
      2 * negativeCrossoverRootMinus lambda - lambda ≠ 0 := by
  have hd : 0 < lambda ^ 2 - 4 :=
    SilverCrossover.positive_discriminant_of_two_lt_abs hlambda
  have hs2 : Real.sqrt (lambda ^ 2 - 4) ^ 2 = lambda ^ 2 - 4 := Real.sq_sqrt hd.le
  have hs0 : 0 < Real.sqrt (lambda ^ 2 - 4) := Real.sqrt_pos.mpr hd
  constructor
  · unfold negativeCrossoverRootMinus
    nlinarith [hs2]
  · unfold negativeCrossoverRootMinus
    have : 2 * ((lambda - Real.sqrt (lambda ^ 2 - 4)) / 2) - lambda =
        -Real.sqrt (lambda ^ 2 - 4) := by ring
    rw [this]
    exact neg_ne_zero.mpr (ne_of_gt hs0)

theorem exists_tendsto_positive_crossover_fixedPoint_branch_plus
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      0 < centerError (adaptiveRow (u n) alpha) alpha) :
    ∃ y : Nat → Real,
      Filter.Tendsto y Filter.atTop
        (nhds (positiveCrossoverRootPlus lambda)) ∧
      Filter.Tendsto
        (fun n : Nat =>
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n))
        Filter.atTop (nhds alpha) ∧
      ∀ᶠ n in Filter.atTop,
        finiteMap (adaptiveRow (u n) alpha) alpha
            (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
            (alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n)) =
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n) := by
  obtain ⟨hroot, hsimple⟩ := positiveCrossoverRootPlus_spec lambda
  exact exists_tendsto_positive_crossover_fixedPoint_branch hu halpha hsign hroot hsimple

theorem exists_tendsto_positive_crossover_fixedPoint_branch_minus
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      0 < centerError (adaptiveRow (u n) alpha) alpha) :
    ∃ y : Nat → Real,
      Filter.Tendsto y Filter.atTop
        (nhds (positiveCrossoverRootMinus lambda)) ∧
      Filter.Tendsto
        (fun n : Nat =>
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n))
        Filter.atTop (nhds alpha) ∧
      ∀ᶠ n in Filter.atTop,
        finiteMap (adaptiveRow (u n) alpha) alpha
            (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
            (alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n)) =
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n) := by
  obtain ⟨hroot, hsimple⟩ := positiveCrossoverRootMinus_spec lambda
  exact exists_tendsto_positive_crossover_fixedPoint_branch hu halpha hsign hroot hsimple

theorem exists_tendsto_negative_crossover_fixedPoint_branch_plus_of_two_lt_abs
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      centerError (adaptiveRow (u n) alpha) alpha < 0)
    (hlambda : 2 < |lambda|) :
    ∃ y : Nat → Real,
      Filter.Tendsto y Filter.atTop
        (nhds (negativeCrossoverRootPlus lambda)) ∧
      Filter.Tendsto
        (fun n : Nat =>
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n))
        Filter.atTop (nhds alpha) ∧
      ∀ᶠ n in Filter.atTop,
        finiteMap (adaptiveRow (u n) alpha) alpha
            (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
            (alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n)) =
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n) := by
  obtain ⟨hroot, hsimple⟩ := negativeCrossoverRootPlus_spec_of_two_lt_abs hlambda
  exact exists_tendsto_negative_crossover_fixedPoint_branch hu halpha hsign hroot hsimple

theorem exists_tendsto_negative_crossover_fixedPoint_branch_minus_of_two_lt_abs
    {u : Nat → Nat} (hu : Filter.Tendsto u Filter.atTop Filter.atTop)
    {alpha lambda : Real} (halpha : 1 < alpha)
    (hsign : ∀ᶠ n in Filter.atTop,
      centerError (adaptiveRow (u n) alpha) alpha < 0)
    (hlambda : 2 < |lambda|) :
    ∃ y : Nat → Real,
      Filter.Tendsto y Filter.atTop
        (nhds (negativeCrossoverRootMinus lambda)) ∧
      Filter.Tendsto
        (fun n : Nat =>
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n))
        Filter.atTop (nhds alpha) ∧
      ∀ᶠ n in Filter.atTop,
        finiteMap (adaptiveRow (u n) alpha) alpha
            (1 + movingMuShift (adaptiveRow (u n) alpha) alpha lambda)
            (alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n)) =
          alpha + movingDelta (adaptiveRow (u n) alpha) alpha (y n) := by
  obtain ⟨hroot, hsimple⟩ := negativeCrossoverRootMinus_spec_of_two_lt_abs hlambda
  exact exists_tendsto_negative_crossover_fixedPoint_branch hu halpha hsign hroot hsimple

end SilverFiniteRow
