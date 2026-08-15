/-
gd_g reduced block cover — Phase 7B: PAIRWISE retained-lobe critical-value
ordering and distinct-lobe value noncollision.

Phase 7A gives strict ordering of stationary magnitudes (and parity-correct
signed values) across CONSECUTIVE retained lobes. Here that is lifted to
arbitrary retained indices `j < k` by induction on the positive distance
`k - j`: at distance one the statement is exactly Phase 7A, and at larger
distance the unique stationary phase of the predecessor lobe `k - 1`
(Phase 6B, `existsUnique_even/odd_retained_lobe_stationary`) is extracted and
used as the intermediate witness, so that the induction hypothesis on
`j → k - 1` composes with the Phase 7A step `k - 1 → k` via `lt_trans`.
Retainedness of the intermediate index follows from downward closedness of
`gdgRetainedLobeIndices` (`gdg_mem_retainedLobeIndices_iff` plus `omega`).

Since a retained lobe lies strictly before the pole, the denominator is
positive there, so the signed pullback is `-` magnitude for even `g` and `+`
magnitude for odd `g`. Hence signed critical values strictly DECREASE with the
lobe index for even `g` and strictly INCREASE for odd `g`. Splitting two
distinct retained indices with `lt_trichotomy` then yields noncollision of the
stationary values of two distinct retained lobes, in either orientation.

Scope: this module proves pairwise strict ordering and distinct-lobe
noncollision only. It does NOT prove any uniform quantitative gap, any
exterior/interior separation, a classification of arbitrary nonstationary
phases, monodromy, or any Galois statement. For `g = 5, 6, 7` there are not two
distinct retained indices, so all targets are vacuous there; at `g = 8` (even)
and `g = 9` (odd) exactly two retained lobes exist and the induction reduces
immediately to the Phase 7A base case.
-/
import RequestProject.GdgCriticalValueOrdering

namespace GdgSquarefree

/-- Nonnegativity of a natural lobe's left endpoint for a nonnegative offset. -/
private theorem gdgPairwise_lobeLeft_nonneg {g : ℕ} (hg : 1 ≤ g)
    (j : ℕ) {offset : ℝ} (hoff : 0 ≤ offset) :
    0 ≤ gdgLobeLeft g j offset := by
  have hth : 0 < gdgTheta g := gdgTheta_pos hg
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  simp only [gdgLobeLeft]
  positivity

/-- Denominator positivity at a point of a retained EVEN lobe. -/
private theorem gdgPairwise_even_den_pos {g j : ℕ}
    (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0) (gdgLobeRight g j 0)) :
    0 < gdgInteriorDenominator g phi :=
  gdgInteriorDenominator_pos_on_Icc hg
    (gdgPairwise_lobeLeft_nonneg (by omega) j le_rfl)
    ((gdgEven_mem_iff_lobeRight_lt_pole hg hEven).mp hj)
    phi (Set.Ioo_subset_Icc_self hphi)

/-- Denominator positivity at a point of a retained ODD lobe. -/
private theorem gdgPairwise_odd_den_pos {g j : ℕ}
    (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2))) :
    0 < gdgInteriorDenominator g phi :=
  gdgInteriorDenominator_pos_on_Icc hg
    (gdgPairwise_lobeLeft_nonneg (by omega) j (by norm_num))
    ((gdgOdd_mem_iff_lobeRight_lt_pole hg hOdd).mp hj)
    phi (Set.Ioo_subset_Icc_self hphi)

/-! ### Induction on the distance between two retained indices -/

/-- Even parity: strict magnitude growth from lobe `j` to lobe `j + d + 1`, by
induction on `d`. The step passes through the unique stationary phase of the
intermediate lobe `j + d` supplied by Phase 6B. -/
private theorem gdgPairwise_even_aux {g : ℕ} (hg : 5 ≤ g) (hEven : Even g) :
    ∀ (d j : ℕ) (phi psi : ℝ),
      j ∈ gdgRetainedLobeIndices g →
      (j + d + 1) ∈ gdgRetainedLobeIndices g →
      phi ∈ Set.Ioo (gdgLobeLeft g j 0) (gdgLobeRight g j 0) →
      psi ∈ Set.Ioo
        (gdgLobeLeft g (j + d + 1) 0) (gdgLobeRight g (j + d + 1) 0) →
      HasDerivAt (gdgSignedInterior g) 0 phi →
      HasDerivAt (gdgSignedInterior g) 0 psi →
      gdgInteriorMagnitude g phi < gdgInteriorMagnitude g psi := by
  intro d
  induction d with
  | zero =>
      intro j phi psi hj hk hphi hpsi hphiStat hpsiStat
      exact even_consecutive_retained_stationary_magnitude_lt hg hEven hj hk
        hphi hpsi hphiStat hpsiStat
  | succ d ih =>
      intro j phi psi hj hk hphi hpsi hphiStat hpsiStat
      have hsplit : j + (d + 1) + 1 = (j + d + 1) + 1 := by omega
      rw [hsplit] at hk hpsi
      have hell : (j + d + 1) ∈ gdgRetainedLobeIndices g := by
        rw [gdg_mem_retainedLobeIndices_iff] at hk ⊢
        omega
      obtain ⟨chi, ⟨hchi, hchiStat⟩, -⟩ :=
        existsUnique_even_retained_lobe_stationary hg hEven hell
      exact lt_trans (ih j phi chi hj hell hphi hchi hphiStat hchiStat)
        (even_consecutive_retained_stationary_magnitude_lt hg hEven hell hk
          hchi hpsi hchiStat hpsiStat)

/-- Odd parity: strict magnitude growth from lobe `j` to lobe `j + d + 1`, by
induction on `d`. The step passes through the unique stationary phase of the
intermediate lobe `j + d` supplied by Phase 6B. -/
private theorem gdgPairwise_odd_aux {g : ℕ} (hg : 5 ≤ g) (hOdd : Odd g) :
    ∀ (d j : ℕ) (phi psi : ℝ),
      j ∈ gdgRetainedLobeIndices g →
      (j + d + 1) ∈ gdgRetainedLobeIndices g →
      phi ∈ Set.Ioo
        (gdgLobeLeft g j ((1 : ℝ) / 2))
        (gdgLobeRight g j ((1 : ℝ) / 2)) →
      psi ∈ Set.Ioo
        (gdgLobeLeft g (j + d + 1) ((1 : ℝ) / 2))
        (gdgLobeRight g (j + d + 1) ((1 : ℝ) / 2)) →
      HasDerivAt (gdgSignedInterior g) 0 phi →
      HasDerivAt (gdgSignedInterior g) 0 psi →
      gdgInteriorMagnitude g phi < gdgInteriorMagnitude g psi := by
  intro d
  induction d with
  | zero =>
      intro j phi psi hj hk hphi hpsi hphiStat hpsiStat
      exact odd_consecutive_retained_stationary_magnitude_lt hg hOdd hj hk
        hphi hpsi hphiStat hpsiStat
  | succ d ih =>
      intro j phi psi hj hk hphi hpsi hphiStat hpsiStat
      have hsplit : j + (d + 1) + 1 = (j + d + 1) + 1 := by omega
      rw [hsplit] at hk hpsi
      have hell : (j + d + 1) ∈ gdgRetainedLobeIndices g := by
        rw [gdg_mem_retainedLobeIndices_iff] at hk ⊢
        omega
      obtain ⟨chi, ⟨hchi, hchiStat⟩, -⟩ :=
        existsUnique_odd_retained_lobe_stationary hg hOdd hell
      exact lt_trans (ih j phi chi hj hell hphi hchi hphiStat hchiStat)
        (odd_consecutive_retained_stationary_magnitude_lt hg hOdd hell hk
          hchi hpsi hchiStat hpsiStat)

/-! ### Targets 1–2: pairwise magnitude ordering -/

/-- **Target 1.** Even parity: for retained indices `j < k`, the stationary
magnitude on lobe `j` is strictly smaller than that on lobe `k`. -/
theorem even_pairwise_retained_stationary_magnitude_lt
    {g j k : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hk : k ∈ gdgRetainedLobeIndices g) (hjk : j < k)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g k 0) (gdgLobeRight g k 0))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (hpsiStat : HasDerivAt (gdgSignedInterior g) 0 psi) :
    gdgInteriorMagnitude g phi < gdgInteriorMagnitude g psi := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = j + d + 1 := ⟨k - j - 1, by omega⟩
  exact gdgPairwise_even_aux hg hEven d j phi psi hj hk hphi hpsi
    hphiStat hpsiStat

/-- **Target 2.** Odd parity: for retained indices `j < k`, the stationary
magnitude on lobe `j` is strictly smaller than that on lobe `k`. -/
theorem odd_pairwise_retained_stationary_magnitude_lt
    {g j k : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hk : k ∈ gdgRetainedLobeIndices g) (hjk : j < k)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g k ((1 : ℝ) / 2))
      (gdgLobeRight g k ((1 : ℝ) / 2)))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (hpsiStat : HasDerivAt (gdgSignedInterior g) 0 psi) :
    gdgInteriorMagnitude g phi < gdgInteriorMagnitude g psi := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = j + d + 1 := ⟨k - j - 1, by omega⟩
  exact gdgPairwise_odd_aux hg hOdd d j phi psi hj hk hphi hpsi
    hphiStat hpsiStat

/-! ### Targets 3–4: pairwise parity-correct signed ordering -/

/-- **Target 3.** Even parity: for retained indices `j < k`, the signed
stationary value on the later lobe is strictly SMALLER. -/
theorem even_pairwise_retained_stationary_value_gt
    {g j k : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hk : k ∈ gdgRetainedLobeIndices g) (hjk : j < k)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g k 0) (gdgLobeRight g k 0))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (hpsiStat : HasDerivAt (gdgSignedInterior g) 0 psi) :
    gdgSignedInterior g psi < gdgSignedInterior g phi := by
  have hmag :=
    even_pairwise_retained_stationary_magnitude_lt hg hEven hj hk hjk
      hphi hpsi hphiStat hpsiStat
  have hdenPhi := gdgPairwise_even_den_pos hg hEven hj hphi
  have hdenPsi := gdgPairwise_even_den_pos hg hEven hk hpsi
  rw [gdgSignedInterior_eq_neg_magnitude_of_even hEven hdenPhi,
    gdgSignedInterior_eq_neg_magnitude_of_even hEven hdenPsi]
  linarith

/-- **Target 4.** Odd parity: for retained indices `j < k`, the signed
stationary value on the later lobe is strictly LARGER. -/
theorem odd_pairwise_retained_stationary_value_lt
    {g j k : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hk : k ∈ gdgRetainedLobeIndices g) (hjk : j < k)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g k ((1 : ℝ) / 2))
      (gdgLobeRight g k ((1 : ℝ) / 2)))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (hpsiStat : HasDerivAt (gdgSignedInterior g) 0 psi) :
    gdgSignedInterior g phi < gdgSignedInterior g psi := by
  have hmag :=
    odd_pairwise_retained_stationary_magnitude_lt hg hOdd hj hk hjk
      hphi hpsi hphiStat hpsiStat
  have hdenPhi := gdgPairwise_odd_den_pos hg hOdd hj hphi
  have hdenPsi := gdgPairwise_odd_den_pos hg hOdd hk hpsi
  rw [gdgSignedInterior_eq_magnitude_of_odd hOdd hdenPhi,
    gdgSignedInterior_eq_magnitude_of_odd hOdd hdenPsi]
  linarith

/-! ### Targets 5–6: distinct-lobe value noncollision -/

/-- **Target 5.** Even parity: stationary values of two DISTINCT retained lobes
never coincide. -/
theorem even_distinct_retained_stationary_values_ne
    {g j k : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hk : k ∈ gdgRetainedLobeIndices g) (hjk : j ≠ k)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g k 0) (gdgLobeRight g k 0))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (hpsiStat : HasDerivAt (gdgSignedInterior g) 0 psi) :
    gdgSignedInterior g phi ≠ gdgSignedInterior g psi := by
  rcases lt_trichotomy j k with hlt | heq | hgt
  · have := even_pairwise_retained_stationary_value_gt hg hEven hj hk hlt
      hphi hpsi hphiStat hpsiStat
    intro h
    linarith
  · exact absurd heq hjk
  · have := even_pairwise_retained_stationary_value_gt hg hEven hk hj hgt
      hpsi hphi hpsiStat hphiStat
    intro h
    linarith

/-- **Target 6.** Odd parity: stationary values of two DISTINCT retained lobes
never coincide. -/
theorem odd_distinct_retained_stationary_values_ne
    {g j k : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hk : k ∈ gdgRetainedLobeIndices g) (hjk : j ≠ k)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g k ((1 : ℝ) / 2))
      (gdgLobeRight g k ((1 : ℝ) / 2)))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (hpsiStat : HasDerivAt (gdgSignedInterior g) 0 psi) :
    gdgSignedInterior g phi ≠ gdgSignedInterior g psi := by
  rcases lt_trichotomy j k with hlt | heq | hgt
  · have := odd_pairwise_retained_stationary_value_lt hg hOdd hj hk hlt
      hphi hpsi hphiStat hpsiStat
    intro h
    linarith
  · exact absurd heq hjk
  · have := odd_pairwise_retained_stationary_value_lt hg hOdd hk hj hgt
      hpsi hphi hpsiStat hphiStat
    intro h
    linarith

end GdgSquarefree
