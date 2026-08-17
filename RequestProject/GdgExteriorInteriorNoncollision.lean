/-
# Phase 8C — parity-specific exterior/interior noncollision

This module packages the completed exterior/interior comparison into strict
ordering and noncollision statements for *actual* retained interior stationary
values versus an *actual* positive exterior critical value.

Contents:
* `gdgRetainedLobeIndices_five_eq_empty`
* `even_retained_stationary_value_lt_exterior_critical`
* `odd_retained_stationary_value_lt_exterior_critical`
* `even_retained_stationary_value_ne_exterior_critical`
* `odd_retained_stationary_value_ne_exterior_critical`

Three branches:
* odd `g = 5`: the retained index set is literally empty, so any statement
  quantified over a retained index holds vacuously;
* even `g ≥ 5`: the signed interior value is strictly negative on every open
  retained even lobe while the exterior cover value is strictly positive;
* odd `g ≥ 7`: Phase 8B gives the quantitative magnitude bound, and denominator
  positivity plus odd parity identifies the signed value with the magnitude.

NOT proved here: the Phase 9 flagship finite critical-set injectivity theorem,
monodromy, or any Galois statement.
-/
import RequestProject.GdgExteriorInteriorOdd

namespace GdgSquarefree

/-- **Target 1.** At `g = 5` the retained natural-lobe index set is empty. -/
theorem gdgRetainedLobeIndices_five_eq_empty :
    gdgRetainedLobeIndices 5 = (∅ : Finset ℕ) := by
  have h : gdgRetainedLobeCount 5 = 0 := by
    unfold gdgRetainedLobeCount
    norm_num
  rw [gdgRetainedLobeIndices, h, Finset.range_zero]

-- The stationarity and criticality hypotheses are part of the certified
-- interface: they guarantee that the compared numbers are genuine stationary
-- and critical values, even though the sign facts hold more generally.
set_option linter.unusedVariables false in
/-- **Target 2 (even).** For even `g ≥ 5`, an actual retained interior
stationary value is strictly smaller than an actual positive exterior critical
value. -/
theorem even_retained_stationary_value_lt_exterior_critical
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi tstar : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0)
      (gdgLobeRight g j 0))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (htstar : 0 < tstar)
    (hcritical :
      gdgExteriorCriticalRatio g tstar = Real.cos (gdgTheta g)) :
    gdgSignedInterior g phi <
      gdgExteriorCoverValue g tstar := by
  have hneg : gdgSignedInterior g phi < 0 :=
    gdgSignedInterior_neg_on_even_retained_lobeInterior hg hEven hj hphi
  have hpos : 0 < gdgExteriorCoverValue g tstar :=
    gdgExteriorCoverValue_pos hg htstar
  linarith

/-- Left endpoints of natural lobes with a nonnegative offset are
nonnegative. -/
private theorem gdgLobeLeft_nonneg_offset {g j : ℕ} (hg : 1 ≤ g)
    {offset : ℝ} (hoff : 0 ≤ offset) :
    0 ≤ gdgLobeLeft g j offset := by
  have hth : 0 < gdgTheta g := gdgTheta_pos hg
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  simp only [gdgLobeLeft]
  nlinarith

set_option linter.unusedVariables false in
/-- **Target 3 (odd).** For odd `g ≥ 5`, an actual retained interior stationary
value is strictly smaller than an actual positive exterior critical value.  The
case `g = 5` is vacuous because the retained index set is then empty. -/
theorem odd_retained_stationary_value_lt_exterior_critical
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi tstar : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (htstar : 0 < tstar)
    (hcritical :
      gdgExteriorCriticalRatio g tstar = Real.cos (gdgTheta g)) :
    gdgSignedInterior g phi <
      gdgExteriorCoverValue g tstar := by
  have hcase : g = 5 ∨ 7 ≤ g := by
    obtain ⟨k, hk⟩ := hOdd
    omega
  rcases hcase with rfl | hg7
  · rw [gdgRetainedLobeIndices_five_eq_empty] at hj
    exact absurd hj (Finset.notMem_empty j)
  · have hphiIcc := Set.Ioo_subset_Icc_self hphi
    have hmag : gdgInteriorMagnitude g phi <
        gdgExteriorCoverValue g tstar :=
      gdgOdd_retained_lobe_magnitude_lt_exterior_critical hg7 hOdd hj hphiIcc
        htstar hcritical
    have hden : 0 < gdgInteriorDenominator g phi :=
      gdgInteriorDenominator_pos_on_Icc hg
        (gdgLobeLeft_nonneg_offset (g := g) (j := j) (by omega) (by norm_num))
        ((gdgOdd_mem_iff_lobeRight_lt_pole hg hOdd).mp hj) phi hphiIcc
    rw [gdgSignedInterior_eq_magnitude_of_odd hOdd hden]
    exact hmag

/-- **Target 4 (even).** Noncollision: for even `g ≥ 5` an actual retained
interior stationary value never equals an actual positive exterior critical
value. -/
theorem even_retained_stationary_value_ne_exterior_critical
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi tstar : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0)
      (gdgLobeRight g j 0))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (htstar : 0 < tstar)
    (hcritical :
      gdgExteriorCriticalRatio g tstar = Real.cos (gdgTheta g)) :
    gdgSignedInterior g phi ≠
      gdgExteriorCoverValue g tstar :=
  ne_of_lt (even_retained_stationary_value_lt_exterior_critical hg hEven hj
    hphi hphiStat htstar hcritical)

/-- **Target 5 (odd).** Noncollision: for odd `g ≥ 5` an actual retained
interior stationary value never equals an actual positive exterior critical
value (the empty `g = 5` boundary included). -/
theorem odd_retained_stationary_value_ne_exterior_critical
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi tstar : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (htstar : 0 < tstar)
    (hcritical :
      gdgExteriorCriticalRatio g tstar = Real.cos (gdgTheta g)) :
    gdgSignedInterior g phi ≠
      gdgExteriorCoverValue g tstar :=
  ne_of_lt (odd_retained_stationary_value_lt_exterior_critical hg hOdd hj
    hphi hphiStat htstar hcritical)

end GdgSquarefree
