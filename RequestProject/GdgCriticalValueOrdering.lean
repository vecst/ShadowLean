/-
gd_g reduced block cover — Phase 7A: CONSECUTIVE retained-lobe critical-value
ordering.

Phase 6B identifies, inside a retained natural lobe, the stationary points of the
signed pullback `gdgSignedInterior g` with the maximizers of the magnitude
`gdgInteriorMagnitude g` over the CLOSED natural lobe. Phase 1 supplies, on the
same closed lobe, a strictly positive attained greatest value. Two greatest
values of one set agree, so the stationary magnitude is strictly positive
(Targets 1–2).

Consecutive natural lobes are exact `gdgTheta g` translates of each other, so
`gdgInteriorMagnitude_max_shift_lt_of_pos` upgrades the positive greatest value
on lobe `j` to a strictly larger greatest value on lobe `j+1` (Targets 3–4).

On a retained lobe the denominator is positive, so the signed value is `-`
magnitude for even `g` and `+` magnitude for odd `g`. Hence consecutive signed
critical values strictly DECREASE for even `g` and strictly INCREASE for odd `g`
(Targets 5–6).

Scope: this module proves strict ordering for CONSECUTIVE retained lobes only.
It does NOT prove pairwise `j < k` ordering (Phase 7B), any uniform quantitative
gap (the smallest adjacent relative gap is only Θ(1/g)), exterior/interior
separation, monodromy, or any Galois statement. For `g = 5, 6, 7` no consecutive
retained pair exists, so Targets 3–6 are vacuous there; the first concrete cases
are `g = 8` (even) and `g = 9` (odd), and nothing below relies on a third lobe.
-/
import RequestProject.GdgLobeUniqueness

namespace GdgSquarefree

/-- The natural lobe is nondegenerate: `left ≤ right`. -/
private theorem gdgLobeLeft_le_gdgLobeRight {g : ℕ} (hg : 1 ≤ g)
    (j : ℕ) (offset : ℝ) :
    gdgLobeLeft g j offset ≤ gdgLobeRight g j offset := by
  have hth : 0 < gdgTheta g := gdgTheta_pos hg
  simp only [gdgLobeRight]
  linarith

/-- Nonnegativity of a natural lobe's left endpoint for a nonnegative offset. -/
private theorem gdgLobeLeft_nonneg {g : ℕ} (hg : 1 ≤ g)
    (j : ℕ) {offset : ℝ} (hoff : 0 ≤ offset) :
    0 ≤ gdgLobeLeft g j offset := by
  have hth : 0 < gdgTheta g := gdgTheta_pos hg
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  simp only [gdgLobeLeft]
  positivity

/-- Right endpoints translate by exactly one period step. -/
private theorem gdgLobeRight_succ {g : ℕ} (j : ℕ) (offset : ℝ) :
    gdgLobeRight g (j + 1) offset =
      gdgLobeRight g j offset + gdgTheta g := by
  simp only [gdgLobeRight, gdgLobeLeft, Nat.cast_add, Nat.cast_one]
  ring

/-- Two greatest values of the same set coincide. -/
private theorem gdg_isGreatest_unique {s : Set ℝ} {a b : ℝ}
    (ha : IsGreatest s a) (hb : IsGreatest s b) : a = b :=
  le_antisymm (hb.2 ha.1) (ha.2 hb.1)

/-! ### Targets 1–2: the stationary magnitude is a positive greatest value -/

/-- **Target 1.** In a retained EVEN lobe, a stationary point of the signed
pullback realizes the greatest magnitude on the closed natural lobe, and that
value is strictly positive. -/
theorem even_retained_lobe_stationary_isGreatest_pos
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
    (hstat : HasDerivAt (gdgSignedInterior g) 0 phi) :
    IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
        (gdgInteriorMagnitude g phi) ∧
      0 < gdgInteriorMagnitude g phi := by
  have hgreat :
      IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
        (gdgInteriorMagnitude g phi) :=
    (even_retained_lobe_stationary_iff_isGreatest hg hEven hj hphi).mp hstat
  obtain ⟨M, hM, hMpos⟩ :=
    exists_pos_even_retained_lobe_max hg hEven
      (gdg_mem_retainedLobeIndices_iff.mp hj)
  have hEq : M = gdgInteriorMagnitude g phi := gdg_isGreatest_unique hM hgreat
  exact ⟨hgreat, hEq ▸ hMpos⟩

/-- **Target 2.** In a retained ODD lobe, a stationary point of the signed
pullback realizes the greatest magnitude on the closed natural lobe, and that
value is strictly positive. -/
theorem odd_retained_lobe_stationary_isGreatest_pos
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hstat : HasDerivAt (gdgSignedInterior g) 0 phi) :
    IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc
            (gdgLobeLeft g j ((1 : ℝ) / 2))
            (gdgLobeRight g j ((1 : ℝ) / 2)))
        (gdgInteriorMagnitude g phi) ∧
      0 < gdgInteriorMagnitude g phi := by
  have hgreat :
      IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc
            (gdgLobeLeft g j ((1 : ℝ) / 2))
            (gdgLobeRight g j ((1 : ℝ) / 2)))
        (gdgInteriorMagnitude g phi) :=
    (odd_retained_lobe_stationary_iff_isGreatest hg hOdd hj hphi).mp hstat
  obtain ⟨M, hM, hMpos⟩ :=
    exists_pos_odd_retained_lobe_max hg hOdd
      (gdg_mem_retainedLobeIndices_iff.mp hj)
  have hEq : M = gdgInteriorMagnitude g phi := gdg_isGreatest_unique hM hgreat
  exact ⟨hgreat, hEq ▸ hMpos⟩

/-! ### Targets 3–4: strict magnitude growth across consecutive retained lobes -/

/-- **Target 3.** Even parity: the stationary magnitude strictly increases from a
retained lobe to the next retained lobe. -/
theorem even_consecutive_retained_stationary_magnitude_lt
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hjnext : j + 1 ∈ gdgRetainedLobeIndices g)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g (j + 1) 0) (gdgLobeRight g (j + 1) 0))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (hpsiStat : HasDerivAt (gdgSignedInterior g) 0 psi) :
    gdgInteriorMagnitude g phi < gdgInteriorMagnitude g psi := by
  have hg1 : 1 ≤ g := by omega
  obtain ⟨hmax, hpos⟩ :=
    even_retained_lobe_stationary_isGreatest_pos hg hEven hj hphi hphiStat
  obtain ⟨hmaxNext, -⟩ :=
    even_retained_lobe_stationary_isGreatest_pos hg hEven hjnext hpsi hpsiStat
  rw [gdgLobeLeft_succ hg1, gdgLobeRight_succ] at hmaxNext
  exact gdgInteriorMagnitude_max_shift_lt_of_pos hg
    (gdgLobeLeft_le_gdgLobeRight hg1 j 0)
    (gdgLobeLeft_nonneg hg1 j le_rfl)
    (gdgEven_next_lobe_before_pole hg hEven hjnext)
    hpos hmax hmaxNext

/-- **Target 4.** Odd parity: the stationary magnitude strictly increases from a
retained lobe to the next retained lobe. -/
theorem odd_consecutive_retained_stationary_magnitude_lt
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hjnext : j + 1 ∈ gdgRetainedLobeIndices g)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g (j + 1) ((1 : ℝ) / 2))
      (gdgLobeRight g (j + 1) ((1 : ℝ) / 2)))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (hpsiStat : HasDerivAt (gdgSignedInterior g) 0 psi) :
    gdgInteriorMagnitude g phi < gdgInteriorMagnitude g psi := by
  have hg1 : 1 ≤ g := by omega
  obtain ⟨hmax, hpos⟩ :=
    odd_retained_lobe_stationary_isGreatest_pos hg hOdd hj hphi hphiStat
  obtain ⟨hmaxNext, -⟩ :=
    odd_retained_lobe_stationary_isGreatest_pos hg hOdd hjnext hpsi hpsiStat
  rw [gdgLobeLeft_succ hg1, gdgLobeRight_succ] at hmaxNext
  exact gdgInteriorMagnitude_max_shift_lt_of_pos hg
    (gdgLobeLeft_le_gdgLobeRight hg1 j ((1 : ℝ) / 2))
    (gdgLobeLeft_nonneg hg1 j (by norm_num))
    (gdgOdd_next_lobe_before_pole hg hOdd hjnext)
    hpos hmax hmaxNext

/-! ### Targets 5–6: parity-correct signed ordering -/

/-- Denominator positivity at a point of a retained EVEN lobe. -/
private theorem gdgEven_denominator_pos_of_mem_lobe {g j : ℕ}
    (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0) (gdgLobeRight g j 0)) :
    0 < gdgInteriorDenominator g phi :=
  gdgInteriorDenominator_pos_on_Icc hg
    (gdgLobeLeft_nonneg (by omega) j le_rfl)
    ((gdgEven_mem_iff_lobeRight_lt_pole hg hEven).mp hj)
    phi (Set.Ioo_subset_Icc_self hphi)

/-- Denominator positivity at a point of a retained ODD lobe. -/
private theorem gdgOdd_denominator_pos_of_mem_lobe {g j : ℕ}
    (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2))) :
    0 < gdgInteriorDenominator g phi :=
  gdgInteriorDenominator_pos_on_Icc hg
    (gdgLobeLeft_nonneg (by omega) j (by norm_num))
    ((gdgOdd_mem_iff_lobeRight_lt_pole hg hOdd).mp hj)
    phi (Set.Ioo_subset_Icc_self hphi)

/-- **Target 5.** Even parity: the signed critical value on the later retained
lobe is strictly SMALLER. -/
theorem even_consecutive_retained_stationary_value_gt
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hjnext : j + 1 ∈ gdgRetainedLobeIndices g)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g (j + 1) 0) (gdgLobeRight g (j + 1) 0))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (hpsiStat : HasDerivAt (gdgSignedInterior g) 0 psi) :
    gdgSignedInterior g psi < gdgSignedInterior g phi := by
  have hmag :=
    even_consecutive_retained_stationary_magnitude_lt hg hEven hj hjnext
      hphi hpsi hphiStat hpsiStat
  have hdenPhi := gdgEven_denominator_pos_of_mem_lobe hg hEven hj hphi
  have hdenPsi := gdgEven_denominator_pos_of_mem_lobe hg hEven hjnext hpsi
  rw [gdgSignedInterior_eq_neg_magnitude_of_even hEven hdenPhi,
    gdgSignedInterior_eq_neg_magnitude_of_even hEven hdenPsi]
  linarith

/-- **Target 6.** Odd parity: the signed critical value on the later retained
lobe is strictly LARGER. -/
theorem odd_consecutive_retained_stationary_value_lt
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g)
    (hjnext : j + 1 ∈ gdgRetainedLobeIndices g)
    {phi psi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hpsi : psi ∈ Set.Ioo
      (gdgLobeLeft g (j + 1) ((1 : ℝ) / 2))
      (gdgLobeRight g (j + 1) ((1 : ℝ) / 2)))
    (hphiStat : HasDerivAt (gdgSignedInterior g) 0 phi)
    (hpsiStat : HasDerivAt (gdgSignedInterior g) 0 psi) :
    gdgSignedInterior g phi < gdgSignedInterior g psi := by
  have hmag :=
    odd_consecutive_retained_stationary_magnitude_lt hg hOdd hj hjnext
      hphi hpsi hphiStat hpsiStat
  have hdenPhi := gdgOdd_denominator_pos_of_mem_lobe hg hOdd hj hphi
  have hdenPsi := gdgOdd_denominator_pos_of_mem_lobe hg hOdd hjnext hpsi
  rw [gdgSignedInterior_eq_magnitude_of_odd hOdd hdenPhi,
    gdgSignedInterior_eq_magnitude_of_odd hOdd hdenPsi]
  linarith

end GdgSquarefree
