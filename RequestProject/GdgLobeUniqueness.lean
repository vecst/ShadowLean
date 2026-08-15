/-
gd_g completion roadmap, Phase 6B — LOBE-WISE UNIQUENESS of the stationary
phase and its identification with the Phase 1 magnitude maximizer.

Phase 4F produced, for each retained natural lobe, one located phase whose
block coordinate `2 cos φ` is a root of the block polynomial
`B_g = gdgBlockCriticalPolynomial g`, and Phase 5 produced the single exterior
real root `b_e < -2`.  Phase 6A (`RequestProject.GdgDegreeExhaustion`) showed
that `B_g` has exactly `gdgBlockDegree g = gdgRetainedLobeCount g + 1` distinct
complex roots.  Hence those chosen lobe roots together with `b_e` already
exhaust the complete complex root set.

This module transfers that exhaustion back to the real phase coordinate.  An
arbitrary stationary phase of `gdgSignedInterior g` inside a retained lobe maps
to a root of `B_g` along the already formalized chain

  stationary signed pullback → critical tetranomial root at `exp (i φ)`
    → channel quotient root → parity-correct reciprocal residual root
    → block-polynomial root at `2 cos φ`,

and the complete root family then forces its block coordinate to be the chosen
root of its own lobe (the exterior root is excluded because interior block
coordinates exceed `-2`, and the other lobes are excluded by the cross-lobe
block separation theorem).  Strict antitonicity of `2 cos` on `[0, π]` upgrades
this to equality of phases.  Fermat's theorem, applied to the parity-correct
signed identity on an interior neighbourhood, shows that the positive Phase 1
maximizer is stationary, so the unique stationary phase IS the unique positive
magnitude maximizer.

SCOPE.  This module proves: exactly one stationary phase per retained natural
lobe, its identity with the unique positive magnitude maximizer of that lobe,
and the complete block-root classification (retained lobe roots plus the single
exterior slot).  It does NOT prove critical-value ordering, exterior/interior
value separation, monodromy, or any Galois statement, and it does NOT use the
(numerically false) claim that the interior logarithmic derivative is globally
decreasing on a lobe.
-/
import RequestProject.GdgDegreeExhaustion

namespace GdgSquarefree

open Polynomial

/-! ### Private geometric helpers -/

/-- Left endpoints of natural lobes with a nonnegative offset are nonnegative. -/
private theorem lobeLeft_nonneg_aux {g j : ℕ} (hg : 1 ≤ g)
    {offset : ℝ} (hoff : 0 ≤ offset) :
    0 ≤ gdgLobeLeft g j offset := by
  have hth : 0 < gdgTheta g := gdgTheta_pos hg
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  simp only [gdgLobeLeft]
  nlinarith

/-- Denominator positivity on a retained closed EVEN lobe. -/
private theorem even_retained_den_pos {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Icc (gdgLobeLeft g j 0) (gdgLobeRight g j 0)) :
    0 < gdgInteriorDenominator g phi :=
  gdgInteriorDenominator_pos_on_Icc hg
    (lobeLeft_nonneg_aux (j := j) (by omega) (le_refl (0 : ℝ)))
    ((gdgEven_mem_iff_lobeRight_lt_pole hg hEven).mp hj) phi hphi

/-- Denominator positivity on a retained closed ODD lobe. -/
private theorem odd_retained_den_pos {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Icc
      (gdgLobeLeft g j ((1 : ℝ) / 2)) (gdgLobeRight g j ((1 : ℝ) / 2))) :
    0 < gdgInteriorDenominator g phi :=
  gdgInteriorDenominator_pos_on_Icc hg
    (lobeLeft_nonneg_aux (j := j) (by omega) (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2))
    ((gdgOdd_mem_iff_lobeRight_lt_pole hg hOdd).mp hj) phi hphi

/-- A phase strictly inside a retained EVEN lobe lies in `(0, π)`. -/
private theorem even_retained_phase_mem_Ioo_zero_pi {g j : ℕ} (hg : 5 ≤ g)
    (hEven : Even g) (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo (gdgLobeLeft g j 0) (gdgLobeRight g j 0)) :
    0 < phi ∧ phi < Real.pi := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hleft := lobeLeft_nonneg_aux (g := g) (j := j) (by omega) (le_refl (0 : ℝ))
  have hpole := (gdgEven_mem_iff_lobeRight_lt_pole hg hEven).mp hj
  exact ⟨lt_of_le_of_lt hleft hphi.1, by linarith [hphi.2]⟩

/-- A phase strictly inside a retained ODD lobe lies in `(0, π)`. -/
private theorem odd_retained_phase_mem_Ioo_zero_pi {g j : ℕ} (hg : 5 ≤ g)
    (hOdd : Odd g) (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2)) (gdgLobeRight g j ((1 : ℝ) / 2))) :
    0 < phi ∧ phi < Real.pi := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hleft := lobeLeft_nonneg_aux (g := g) (j := j) (by omega)
    (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
  have hpole := (gdgOdd_mem_iff_lobeRight_lt_pole hg hOdd).mp hj
  exact ⟨lt_of_le_of_lt hleft hphi.1, by linarith [hphi.2]⟩

/-- Strict upper block bound on `(0, π)`. -/
private theorem blockCoord_lt_two_of_mem {phi : ℝ} (h0 : 0 < phi)
    (hpi : phi < Real.pi) :
    gdgBlockCoord phi < 2 := by
  have h := Real.strictAntiOn_cos
    (Set.mem_Icc.mpr ⟨le_rfl, Real.pi_pos.le⟩)
    (Set.mem_Icc.mpr ⟨h0.le, hpi.le⟩) h0
  rw [Real.cos_zero] at h
  simp only [gdgBlockCoord]
  linarith

/-- Strict lower block bound on `(0, π)`. -/
private theorem neg_two_lt_blockCoord_of_mem {phi : ℝ} (h0 : 0 < phi)
    (hpi : phi < Real.pi) :
    -2 < gdgBlockCoord phi := by
  have h := Real.strictAntiOn_cos
    (Set.mem_Icc.mpr ⟨h0.le, hpi.le⟩)
    (Set.mem_Icc.mpr ⟨Real.pi_pos.le, le_rfl⟩) hpi
  rw [Real.cos_pi] at h
  simp only [gdgBlockCoord]
  linarith

/-- The cosine coefficient is strictly below `2` for `g ≥ 5`. -/
private theorem cosCoeff_lt_two_aux {g : ℕ} (hg : 5 ≤ g) :
    gdgCosCoeff g < 2 := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hthlt : gdgTheta g < Real.pi / 2 := gdgTheta_lt_pi_div_two hg
  have hpi := Real.pi_pos
  have hcos : Real.cos (gdgTheta g) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ))
      (by linarith : gdgTheta g ≤ Real.pi) hth
    rwa [Real.cos_zero] at this
  have hval : gdgCosCoeff g = 2 * Real.cos (gdgTheta g) := by
    simp only [gdgCosCoeff, gdgTheta]
  rw [hval]
  linarith

/-! ### Targets 1–2: stationary phases are block roots -/

/-- **Target 1.** A stationary phase strictly inside a retained EVEN lobe has a
block coordinate that is a root of the block polynomial. -/
theorem even_retained_lobe_stationary_blockRoot
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
    (hstat : HasDerivAt (gdgSignedInterior g) 0 phi) :
    (gdgBlockCriticalPolynomial g).eval
      (gdgBlockCoord phi : ℂ) = 0 := by
  have hden := even_retained_den_pos hg hEven hj (Set.Ioo_subset_Icc_self hphi)
  have hval : gdgSignedInterior g phi ≠ 0 :=
    ne_of_lt (gdgSignedInterior_neg_on_even_retained_lobeInterior hg hEven hj hphi)
  obtain ⟨hG, -, hQ⟩ :=
    criticalTetranomial_gdgUnitCircle_eq_zero_of_stationary hg
      (ne_of_gt hden) hval hstat
  exact gdgBlockCriticalPolynomial_gdgUnitCircle_eq_zero hg
    (gdgReciprocalResidualPolynomial_gdgUnitCircle_eq_zero_of_even hg hEven
      (gdgChannelQuotientPolynomial_gdgUnitCircle_eq_zero hg hG hQ))

/-- **Target 2.** A stationary phase strictly inside a retained ODD lobe has a
block coordinate that is a root of the block polynomial. -/
theorem odd_retained_lobe_stationary_blockRoot
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hstat : HasDerivAt (gdgSignedInterior g) 0 phi) :
    (gdgBlockCriticalPolynomial g).eval
      (gdgBlockCoord phi : ℂ) = 0 := by
  have hden := odd_retained_den_pos hg hOdd hj (Set.Ioo_subset_Icc_self hphi)
  have hval : gdgSignedInterior g phi ≠ 0 :=
    ne_of_gt (gdgSignedInterior_pos_on_odd_retained_lobeInterior hg hOdd hj hphi)
  obtain ⟨h0, hpi⟩ := odd_retained_phase_mem_Ioo_zero_pi hg hOdd hj hphi
  obtain ⟨hG, -, hQ⟩ :=
    criticalTetranomial_gdgUnitCircle_eq_zero_of_stationary hg
      (ne_of_gt hden) hval hstat
  exact gdgBlockCriticalPolynomial_gdgUnitCircle_eq_zero hg
    (gdgReciprocalResidualPolynomial_gdgUnitCircle_eq_zero_of_odd hg hOdd
      (gdgChannelQuotientPolynomial_gdgUnitCircle_eq_zero hg hG hQ)
      (blockCoord_lt_two_of_mem h0 hpi))

/-! ### The generic slot-family classification (Phase 6A degree exhaustion) -/

/-- Any injective real slot family of roots of the block polynomial exhausts the
complex root set, by Phase 6A's exact root count. -/
private theorem blockRoot_slot_classification {g : ℕ} (hg : 5 ≤ g)
    {r : gdgBlockRootSlot g → ℝ}
    (hroot : ∀ s, (gdgBlockCriticalPolynomial g).eval (r s : ℂ) = 0)
    (hinj : Function.Injective r) (z : ℂ) :
    (gdgBlockCriticalPolynomial g).eval z = 0 ↔ ∃ s, z = (r s : ℂ) := by
  have hinj' : Function.Injective fun s : gdgBlockRootSlot g =>
      ((r s : ℝ) : ℂ) := fun a b h => hinj (Complex.ofReal_injective h)
  have hsub : (Set.range fun s => ((r s : ℝ) : ℂ)) ⊆
      {z : ℂ | (gdgBlockCriticalPolynomial g).eval z = 0} := by
    rintro w ⟨s, rfl⟩
    exact hroot s
  have hcard : (Set.range fun s => ((r s : ℝ) : ℂ)).ncard = gdgBlockDegree g := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj', Set.ncard_univ,
      Nat.card_eq_fintype_card, card_gdgBlockRootSlot hg]
  have hle : Set.ncard {z : ℂ | (gdgBlockCriticalPolynomial g).eval z = 0} ≤
      (Set.range fun s => ((r s : ℝ) : ℂ)).ncard := by
    rw [hcard]
    exact le_of_eq (gdgBlockCriticalPolynomial_root_set_ncard hg)
  have hset := Set.eq_of_subset_of_ncard_le hsub hle
    (gdgBlockCriticalPolynomial_root_set_finite hg)
  constructor
  · intro hz
    have hmem : z ∈ (Set.range fun s => ((r s : ℝ) : ℂ)) := by
      rw [hset]; exact hz
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact hroot s

/-! ### Targets 3–4: the complete located root family -/

/-- **Target 3.** For even `g` the retained lobes carry located block roots
which, together with the exterior root, exhaust the complex root set. -/
theorem exists_even_complete_retained_lobe_blockRoot_family
    {g : ℕ} (hg : 5 ≤ g) (hEven : Even g) :
    ∃ phi : {j // j ∈ gdgRetainedLobeIndices g} → ℝ,
      ∃ be : ℝ,
        (∀ j, phi j ∈ Set.Ioo
          (gdgLobeLeft g j.1 0)
          (gdgLobeRight g j.1 0)) ∧
        (∀ j, (gdgBlockCriticalPolynomial g).eval
          (gdgBlockCoord (phi j) : ℂ) = 0) ∧
        (∀ j, gdgBlockCoord (phi j) ∈
          Set.Ioo (-gdgCosCoeff g) 2) ∧
        Function.Injective (fun j => gdgBlockCoord (phi j)) ∧
        be < -2 ∧
        (gdgBlockCriticalPolynomial g).eval (be : ℂ) = 0 ∧
        (∀ z : ℂ,
          (gdgBlockCriticalPolynomial g).eval z = 0 ↔
            (∃ j, z = (gdgBlockCoord (phi j) : ℂ)) ∨ z = (be : ℂ)) := by
  choose phi hmem hroot hIoo using
    fun j : {j // j ∈ gdgRetainedLobeIndices g} =>
      exists_even_retained_lobe_blockCriticalPolynomial_root hg hEven j.2
  obtain ⟨be, ⟨hbe2, hberoot⟩, -⟩ := existsUnique_exterior_blockRoot hg
  have hcos := cosCoeff_lt_two_aux hg
  have hinj : Function.Injective (fun j => gdgBlockCoord (phi j)) := by
    intro a b hab
    simp only at hab
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · exact absurd hab
        (gdgBlockCoord_ne_of_even_retained_lobes hg hEven a.2 b.2 h
          (hmem a) (hmem b))
    · exact Subtype.ext h
    · exact absurd hab.symm
        (gdgBlockCoord_ne_of_even_retained_lobes hg hEven b.2 a.2 h
          (hmem b) (hmem a))
  refine ⟨phi, be, hmem, hroot, hIoo, hinj, hbe2, hberoot, ?_⟩
  intro z
  set r : gdgBlockRootSlot g → ℝ := Sum.elim
    (fun k : Fin (gdgRetainedLobeCount g) =>
      gdgBlockCoord (phi ⟨(k : ℕ), gdg_mem_retainedLobeIndices_iff.mpr k.isLt⟩))
    (fun _ => be) with hr
  have hrroot : ∀ s, (gdgBlockCriticalPolynomial g).eval (r s : ℂ) = 0 := by
    rintro (k | u)
    · exact hroot _
    · exact hberoot
  have hrinj : Function.Injective r := by
    rintro (k | u) (l | v) h
    · simp only [hr, Sum.elim_inl] at h
      exact congrArg Sum.inl (Fin.ext (congrArg Subtype.val (hinj h)))
    · exfalso
      simp only [hr, Sum.elim_inl, Sum.elim_inr] at h
      have h1 := (hIoo ⟨(k : ℕ), gdg_mem_retainedLobeIndices_iff.mpr k.isLt⟩).1
      rw [h] at h1
      linarith
    · exfalso
      simp only [hr, Sum.elim_inl, Sum.elim_inr] at h
      have h1 := (hIoo ⟨(l : ℕ), gdg_mem_retainedLobeIndices_iff.mpr l.isLt⟩).1
      rw [← h] at h1
      linarith
    · cases u; cases v; rfl
  rw [blockRoot_slot_classification hg hrroot hrinj z]
  constructor
  · rintro ⟨(k | u), hs⟩
    · exact Or.inl ⟨_, hs⟩
    · exact Or.inr hs
  · rintro (⟨a, rfl⟩ | rfl)
    · exact ⟨Sum.inl ⟨a.1, gdg_mem_retainedLobeIndices_iff.mp a.2⟩, rfl⟩
    · exact ⟨Sum.inr (), rfl⟩

/-- **Target 4.** For odd `g` the retained lobes carry located block roots
which, together with the exterior root, exhaust the complex root set. -/
theorem exists_odd_complete_retained_lobe_blockRoot_family
    {g : ℕ} (hg : 5 ≤ g) (hOdd : Odd g) :
    ∃ phi : {j // j ∈ gdgRetainedLobeIndices g} → ℝ,
      ∃ be : ℝ,
        (∀ j, phi j ∈ Set.Ioo
          (gdgLobeLeft g j.1 ((1 : ℝ) / 2))
          (gdgLobeRight g j.1 ((1 : ℝ) / 2))) ∧
        (∀ j, (gdgBlockCriticalPolynomial g).eval
          (gdgBlockCoord (phi j) : ℂ) = 0) ∧
        (∀ j, gdgBlockCoord (phi j) ∈
          Set.Ioo (-gdgCosCoeff g) 2) ∧
        Function.Injective (fun j => gdgBlockCoord (phi j)) ∧
        be < -2 ∧
        (gdgBlockCriticalPolynomial g).eval (be : ℂ) = 0 ∧
        (∀ z : ℂ,
          (gdgBlockCriticalPolynomial g).eval z = 0 ↔
            (∃ j, z = (gdgBlockCoord (phi j) : ℂ)) ∨ z = (be : ℂ)) := by
  choose phi hmem hroot hIoo using
    fun j : {j // j ∈ gdgRetainedLobeIndices g} =>
      exists_odd_retained_lobe_blockCriticalPolynomial_root hg hOdd j.2
  obtain ⟨be, ⟨hbe2, hberoot⟩, -⟩ := existsUnique_exterior_blockRoot hg
  have hcos := cosCoeff_lt_two_aux hg
  have hinj : Function.Injective (fun j => gdgBlockCoord (phi j)) := by
    intro a b hab
    simp only at hab
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · exact absurd hab
        (gdgBlockCoord_ne_of_odd_retained_lobes hg hOdd a.2 b.2 h
          (hmem a) (hmem b))
    · exact Subtype.ext h
    · exact absurd hab.symm
        (gdgBlockCoord_ne_of_odd_retained_lobes hg hOdd b.2 a.2 h
          (hmem b) (hmem a))
  refine ⟨phi, be, hmem, hroot, hIoo, hinj, hbe2, hberoot, ?_⟩
  intro z
  set r : gdgBlockRootSlot g → ℝ := Sum.elim
    (fun k : Fin (gdgRetainedLobeCount g) =>
      gdgBlockCoord (phi ⟨(k : ℕ), gdg_mem_retainedLobeIndices_iff.mpr k.isLt⟩))
    (fun _ => be) with hr
  have hrroot : ∀ s, (gdgBlockCriticalPolynomial g).eval (r s : ℂ) = 0 := by
    rintro (k | u)
    · exact hroot _
    · exact hberoot
  have hrinj : Function.Injective r := by
    rintro (k | u) (l | v) h
    · simp only [hr, Sum.elim_inl] at h
      exact congrArg Sum.inl (Fin.ext (congrArg Subtype.val (hinj h)))
    · exfalso
      simp only [hr, Sum.elim_inl, Sum.elim_inr] at h
      have h1 := (hIoo ⟨(k : ℕ), gdg_mem_retainedLobeIndices_iff.mpr k.isLt⟩).1
      rw [h] at h1
      linarith
    · exfalso
      simp only [hr, Sum.elim_inl, Sum.elim_inr] at h
      have h1 := (hIoo ⟨(l : ℕ), gdg_mem_retainedLobeIndices_iff.mpr l.isLt⟩).1
      rw [← h] at h1
      linarith
    · cases u; cases v; rfl
  rw [blockRoot_slot_classification hg hrroot hrinj z]
  constructor
  · rintro ⟨(k | u), hs⟩
    · exact Or.inl ⟨_, hs⟩
    · exact Or.inr hs
  · rintro (⟨a, rfl⟩ | rfl)
    · exact ⟨Sum.inl ⟨a.1, gdg_mem_retainedLobeIndices_iff.mp a.2⟩, rfl⟩
    · exact ⟨Sum.inr (), rfl⟩

/-! ### Stationary-phase uniqueness inside one retained lobe -/

/-- Two stationary phases inside the same retained EVEN lobe coincide. -/
private theorem even_retained_stationary_unique {g j : ℕ} (hg : 5 ≤ g)
    (hEven : Even g) (hj : j ∈ gdgRetainedLobeIndices g) {p q : ℝ}
    (hp : p ∈ Set.Ioo (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
    (hpstat : HasDerivAt (gdgSignedInterior g) 0 p)
    (hq : q ∈ Set.Ioo (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
    (hqstat : HasDerivAt (gdgSignedInterior g) 0 q) :
    p = q := by
  obtain ⟨phi, be, hmem, -, -, -, hbe2, -, hclass⟩ :=
    exists_even_complete_retained_lobe_blockRoot_family hg hEven
  have key : ∀ x : ℝ, x ∈ Set.Ioo (gdgLobeLeft g j 0) (gdgLobeRight g j 0) →
      HasDerivAt (gdgSignedInterior g) 0 x →
      gdgBlockCoord x = gdgBlockCoord (phi ⟨j, hj⟩) := by
    intro x hx hxstat
    obtain ⟨hx0, hxpi⟩ := even_retained_phase_mem_Ioo_zero_pi hg hEven hj hx
    have hroot := even_retained_lobe_stationary_blockRoot hg hEven hj hx hxstat
    rcases (hclass _).mp hroot with ⟨k, hk⟩ | hk
    · have hkr : gdgBlockCoord x = gdgBlockCoord (phi k) := by exact_mod_cast hk
      rcases lt_trichotomy k.1 j with hlt | heq | hgt
      · exact absurd hkr.symm
          (gdgBlockCoord_ne_of_even_retained_lobes hg hEven k.2 hj hlt
            (hmem k) hx)
      · have hkj : k = ⟨j, hj⟩ := Subtype.ext heq
        rw [hkr, hkj]
      · exact absurd hkr
          (gdgBlockCoord_ne_of_even_retained_lobes hg hEven hj k.2 hgt
            hx (hmem k))
    · exfalso
      have hxbe : gdgBlockCoord x = be := by exact_mod_cast hk
      have := neg_two_lt_blockCoord_of_mem hx0 hxpi
      rw [hxbe] at this
      linarith
  have h1 := key p hp hpstat
  have h2 := key q hq hqstat
  obtain ⟨hp0, hppi⟩ := even_retained_phase_mem_Ioo_zero_pi hg hEven hj hp
  obtain ⟨hq0, hqpi⟩ := even_retained_phase_mem_Ioo_zero_pi hg hEven hj hq
  exact gdgBlockCoord_strictAntiOn.injOn
    (Set.mem_Icc.mpr ⟨hp0.le, hppi.le⟩)
    (Set.mem_Icc.mpr ⟨hq0.le, hqpi.le⟩) (h1.trans h2.symm)

/-- Two stationary phases inside the same retained ODD lobe coincide. -/
private theorem odd_retained_stationary_unique {g j : ℕ} (hg : 5 ≤ g)
    (hOdd : Odd g) (hj : j ∈ gdgRetainedLobeIndices g) {p q : ℝ}
    (hp : p ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2)) (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hpstat : HasDerivAt (gdgSignedInterior g) 0 p)
    (hq : q ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2)) (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hqstat : HasDerivAt (gdgSignedInterior g) 0 q) :
    p = q := by
  obtain ⟨phi, be, hmem, -, -, -, hbe2, -, hclass⟩ :=
    exists_odd_complete_retained_lobe_blockRoot_family hg hOdd
  have key : ∀ x : ℝ, x ∈ Set.Ioo
        (gdgLobeLeft g j ((1 : ℝ) / 2)) (gdgLobeRight g j ((1 : ℝ) / 2)) →
      HasDerivAt (gdgSignedInterior g) 0 x →
      gdgBlockCoord x = gdgBlockCoord (phi ⟨j, hj⟩) := by
    intro x hx hxstat
    obtain ⟨hx0, hxpi⟩ := odd_retained_phase_mem_Ioo_zero_pi hg hOdd hj hx
    have hroot := odd_retained_lobe_stationary_blockRoot hg hOdd hj hx hxstat
    rcases (hclass _).mp hroot with ⟨k, hk⟩ | hk
    · have hkr : gdgBlockCoord x = gdgBlockCoord (phi k) := by exact_mod_cast hk
      rcases lt_trichotomy k.1 j with hlt | heq | hgt
      · exact absurd hkr.symm
          (gdgBlockCoord_ne_of_odd_retained_lobes hg hOdd k.2 hj hlt
            (hmem k) hx)
      · have hkj : k = ⟨j, hj⟩ := Subtype.ext heq
        rw [hkr, hkj]
      · exact absurd hkr
          (gdgBlockCoord_ne_of_odd_retained_lobes hg hOdd hj k.2 hgt
            hx (hmem k))
    · exfalso
      have hxbe : gdgBlockCoord x = be := by exact_mod_cast hk
      have := neg_two_lt_blockCoord_of_mem hx0 hxpi
      rw [hxbe] at this
      linarith
  have h1 := key p hp hpstat
  have h2 := key q hq hqstat
  obtain ⟨hp0, hppi⟩ := odd_retained_phase_mem_Ioo_zero_pi hg hOdd hj hp
  obtain ⟨hq0, hqpi⟩ := odd_retained_phase_mem_Ioo_zero_pi hg hOdd hj hq
  exact gdgBlockCoord_strictAntiOn.injOn
    (Set.mem_Icc.mpr ⟨hp0.le, hppi.le⟩)
    (Set.mem_Icc.mpr ⟨hq0.le, hqpi.le⟩) (h1.trans h2.symm)

/-! ### Targets 5–6: exactly one stationary phase per retained lobe -/

/-- **Target 5.** Exactly one stationary phase inside each retained EVEN lobe. -/
theorem existsUnique_even_retained_lobe_stationary
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃! phi : ℝ,
      phi ∈ Set.Ioo
        (gdgLobeLeft g j 0) (gdgLobeRight g j 0) ∧
      HasDerivAt (gdgSignedInterior g) 0 phi := by
  obtain ⟨c, hc, hcstat⟩ :=
    exists_even_retained_lobe_hasDerivAt_gdgSignedInterior_zero hg hEven hj
  refine ⟨c, ⟨hc, hcstat⟩, ?_⟩
  rintro y ⟨hy, hystat⟩
  exact even_retained_stationary_unique hg hEven hj hy hystat hc hcstat

/-- **Target 6.** Exactly one stationary phase inside each retained ODD lobe. -/
theorem existsUnique_odd_retained_lobe_stationary
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃! phi : ℝ,
      phi ∈ Set.Ioo
        (gdgLobeLeft g j ((1 : ℝ) / 2))
        (gdgLobeRight g j ((1 : ℝ) / 2)) ∧
      HasDerivAt (gdgSignedInterior g) 0 phi := by
  obtain ⟨c, hc, hcstat⟩ :=
    exists_odd_retained_lobe_hasDerivAt_gdgSignedInterior_zero hg hOdd hj
  refine ⟨c, ⟨hc, hcstat⟩, ?_⟩
  rintro y ⟨hy, hystat⟩
  exact odd_retained_stationary_unique hg hOdd hj hy hystat hc hcstat

/-! ### Fermat's theorem at an interior magnitude maximizer -/

/-- An interior magnitude maximizer of a retained EVEN lobe is a local MINIMUM
of the signed pullback (even parity: signed = −magnitude), hence stationary. -/
private theorem even_retained_stationary_of_max {g j : ℕ} (hg : 5 ≤ g)
    (hEven : Even g) (hj : j ∈ gdgRetainedLobeIndices g) {p : ℝ}
    (hp : p ∈ Set.Ioo (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
    (hmax : ∀ y ∈ Set.Icc (gdgLobeLeft g j 0) (gdgLobeRight g j 0),
      gdgInteriorMagnitude g y ≤ gdgInteriorMagnitude g p) :
    HasDerivAt (gdgSignedInterior g) 0 p := by
  have hden := even_retained_den_pos hg hEven hj (Set.Ioo_subset_Icc_self hp)
  have hlocal : IsLocalMin (gdgSignedInterior g) p := by
    filter_upwards [Icc_mem_nhds hp.1 hp.2] with y hy
    have hdeny := even_retained_den_pos hg hEven hj hy
    rw [gdgSignedInterior_eq_neg_magnitude_of_even hEven hden,
      gdgSignedInterior_eq_neg_magnitude_of_even hEven hdeny]
    exact neg_le_neg (hmax y hy)
  have hHas :=
    (differentiableAt_gdgSignedInterior_of_denominator_ne_zero
      (ne_of_gt hden)).hasDerivAt
  have hzero := hlocal.hasDerivAt_eq_zero hHas
  rwa [hzero] at hHas

/-- An interior magnitude maximizer of a retained ODD lobe is a local MAXIMUM of
the signed pullback (odd parity: signed = magnitude), hence stationary. -/
private theorem odd_retained_stationary_of_max {g j : ℕ} (hg : 5 ≤ g)
    (hOdd : Odd g) (hj : j ∈ gdgRetainedLobeIndices g) {p : ℝ}
    (hp : p ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2)) (gdgLobeRight g j ((1 : ℝ) / 2)))
    (hmax : ∀ y ∈ Set.Icc
        (gdgLobeLeft g j ((1 : ℝ) / 2)) (gdgLobeRight g j ((1 : ℝ) / 2)),
      gdgInteriorMagnitude g y ≤ gdgInteriorMagnitude g p) :
    HasDerivAt (gdgSignedInterior g) 0 p := by
  have hden := odd_retained_den_pos hg hOdd hj (Set.Ioo_subset_Icc_self hp)
  have hlocal : IsLocalMax (gdgSignedInterior g) p := by
    filter_upwards [Icc_mem_nhds hp.1 hp.2] with y hy
    have hdeny := odd_retained_den_pos hg hOdd hj hy
    rw [gdgSignedInterior_eq_magnitude_of_odd hOdd hden,
      gdgSignedInterior_eq_magnitude_of_odd hOdd hdeny]
    exact hmax y hy
  have hHas :=
    (differentiableAt_gdgSignedInterior_of_denominator_ne_zero
      (ne_of_gt hden)).hasDerivAt
  have hzero := hlocal.hasDerivAt_eq_zero hHas
  rwa [hzero] at hHas

/-- The Phase 1 positive maximum of a retained EVEN lobe is attained strictly
inside the lobe, and its maximizer is stationary. -/
private theorem even_retained_interior_maximizer {g j : ℕ} (hg : 5 ≤ g)
    (hEven : Even g) (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃ p : ℝ, p ∈ Set.Ioo (gdgLobeLeft g j 0) (gdgLobeRight g j 0) ∧
      IsGreatest (gdgInteriorMagnitude g ''
        Set.Icc (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
        (gdgInteriorMagnitude g p) ∧
      0 < gdgInteriorMagnitude g p ∧
      HasDerivAt (gdgSignedInterior g) 0 p := by
  obtain ⟨M, hM, hMpos⟩ := exists_pos_even_retained_lobe_max hg hEven
    (gdg_mem_retainedLobeIndices_iff.mp hj)
  obtain ⟨p, hpIcc, hpM⟩ := hM.1
  have hvals := gdgEvenLobe_numerator_values (g := g) (j := j) hg hEven
  have hzeroL : gdgInteriorMagnitude g (gdgLobeLeft g j 0) = 0 := by
    simp only [gdgInteriorMagnitude, hvals.1, zero_div]
  have hzeroR : gdgInteriorMagnitude g (gdgLobeRight g j 0) = 0 := by
    simp only [gdgInteriorMagnitude, hvals.2.1, zero_div]
  have hneL : gdgLobeLeft g j 0 ≠ p := by
    intro h
    rw [← h, hzeroL] at hpM
    linarith
  have hneR : p ≠ gdgLobeRight g j 0 := by
    intro h
    rw [h, hzeroR] at hpM
    linarith
  have hp : p ∈ Set.Ioo (gdgLobeLeft g j 0) (gdgLobeRight g j 0) :=
    ⟨lt_of_le_of_ne hpIcc.1 hneL, lt_of_le_of_ne hpIcc.2 hneR⟩
  refine ⟨p, hp, by rw [hpM]; exact hM, by rw [hpM]; exact hMpos, ?_⟩
  refine even_retained_stationary_of_max hg hEven hj hp ?_
  intro y hy
  rw [hpM]
  exact hM.2 ⟨y, hy, rfl⟩

/-- The Phase 1 positive maximum of a retained ODD lobe is attained strictly
inside the lobe, and its maximizer is stationary. -/
private theorem odd_retained_interior_maximizer {g j : ℕ} (hg : 5 ≤ g)
    (hOdd : Odd g) (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃ p : ℝ, p ∈ Set.Ioo
        (gdgLobeLeft g j ((1 : ℝ) / 2)) (gdgLobeRight g j ((1 : ℝ) / 2)) ∧
      IsGreatest (gdgInteriorMagnitude g ''
        Set.Icc (gdgLobeLeft g j ((1 : ℝ) / 2))
          (gdgLobeRight g j ((1 : ℝ) / 2)))
        (gdgInteriorMagnitude g p) ∧
      0 < gdgInteriorMagnitude g p ∧
      HasDerivAt (gdgSignedInterior g) 0 p := by
  obtain ⟨M, hM, hMpos⟩ := exists_pos_odd_retained_lobe_max hg hOdd
    (gdg_mem_retainedLobeIndices_iff.mp hj)
  obtain ⟨p, hpIcc, hpM⟩ := hM.1
  have hvals := gdgOddLobe_numerator_values (g := g) (j := j) hg hOdd
  have hzeroL : gdgInteriorMagnitude g
      (gdgLobeLeft g j ((1 : ℝ) / 2)) = 0 := by
    simp only [gdgInteriorMagnitude, hvals.1, zero_div]
  have hzeroR : gdgInteriorMagnitude g
      (gdgLobeRight g j ((1 : ℝ) / 2)) = 0 := by
    simp only [gdgInteriorMagnitude, hvals.2.1, zero_div]
  have hneL : gdgLobeLeft g j ((1 : ℝ) / 2) ≠ p := by
    intro h
    rw [← h, hzeroL] at hpM
    linarith
  have hneR : p ≠ gdgLobeRight g j ((1 : ℝ) / 2) := by
    intro h
    rw [h, hzeroR] at hpM
    linarith
  have hp : p ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2)) (gdgLobeRight g j ((1 : ℝ) / 2)) :=
    ⟨lt_of_le_of_ne hpIcc.1 hneL, lt_of_le_of_ne hpIcc.2 hneR⟩
  refine ⟨p, hp, by rw [hpM]; exact hM, by rw [hpM]; exact hMpos, ?_⟩
  refine odd_retained_stationary_of_max hg hOdd hj hp ?_
  intro y hy
  rw [hpM]
  exact hM.2 ⟨y, hy, rfl⟩

/-! ### Targets 7–8: stationary ⟺ magnitude maximizer -/

/-- **Target 7.** Inside a retained EVEN lobe, stationarity of the signed
pullback is equivalent to being a magnitude maximizer of the closed lobe. -/
theorem even_retained_lobe_stationary_iff_isGreatest
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0) (gdgLobeRight g j 0)) :
    HasDerivAt (gdgSignedInterior g) 0 phi ↔
      IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
        (gdgInteriorMagnitude g phi) := by
  constructor
  · intro hstat
    obtain ⟨p, hp, hpmax, -, hpstat⟩ :=
      even_retained_interior_maximizer hg hEven hj
    have hEq : phi = p :=
      even_retained_stationary_unique hg hEven hj hphi hstat hp hpstat
    rw [hEq]
    exact hpmax
  · intro hgreat
    refine even_retained_stationary_of_max hg hEven hj hphi ?_
    intro y hy
    exact hgreat.2 ⟨y, hy, rfl⟩

/-- **Target 8.** Inside a retained ODD lobe, stationarity of the signed
pullback is equivalent to being a magnitude maximizer of the closed lobe. -/
theorem odd_retained_lobe_stationary_iff_isGreatest
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2))) :
    HasDerivAt (gdgSignedInterior g) 0 phi ↔
      IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc
            (gdgLobeLeft g j ((1 : ℝ) / 2))
            (gdgLobeRight g j ((1 : ℝ) / 2)))
        (gdgInteriorMagnitude g phi) := by
  constructor
  · intro hstat
    obtain ⟨p, hp, hpmax, -, hpstat⟩ :=
      odd_retained_interior_maximizer hg hOdd hj
    have hEq : phi = p :=
      odd_retained_stationary_unique hg hOdd hj hphi hstat hp hpstat
    rw [hEq]
    exact hpmax
  · intro hgreat
    refine odd_retained_stationary_of_max hg hOdd hj hphi ?_
    intro y hy
    exact hgreat.2 ⟨y, hy, rfl⟩

/-! ### Targets 9–10: the unique positive magnitude maximizer -/

/-- **Target 9.** Each retained EVEN lobe has exactly one interior phase
realizing the (strictly positive) maximum magnitude of the closed lobe. -/
theorem existsUnique_even_retained_lobe_magnitude_maximizer
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃! phi : ℝ,
      phi ∈ Set.Ioo
        (gdgLobeLeft g j 0) (gdgLobeRight g j 0) ∧
      IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc (gdgLobeLeft g j 0) (gdgLobeRight g j 0))
        (gdgInteriorMagnitude g phi) ∧
      0 < gdgInteriorMagnitude g phi := by
  obtain ⟨p, hp, hpmax, hppos, hpstat⟩ :=
    even_retained_interior_maximizer hg hEven hj
  refine ⟨p, ⟨hp, hpmax, hppos⟩, ?_⟩
  rintro y ⟨hy, hymax, -⟩
  have hystat :=
    (even_retained_lobe_stationary_iff_isGreatest hg hEven hj hy).mpr hymax
  exact even_retained_stationary_unique hg hEven hj hy hystat hp hpstat

/-- **Target 10.** Each retained ODD lobe has exactly one interior phase
realizing the (strictly positive) maximum magnitude of the closed lobe. -/
theorem existsUnique_odd_retained_lobe_magnitude_maximizer
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃! phi : ℝ,
      phi ∈ Set.Ioo
        (gdgLobeLeft g j ((1 : ℝ) / 2))
        (gdgLobeRight g j ((1 : ℝ) / 2)) ∧
      IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc
            (gdgLobeLeft g j ((1 : ℝ) / 2))
            (gdgLobeRight g j ((1 : ℝ) / 2)))
        (gdgInteriorMagnitude g phi) ∧
      0 < gdgInteriorMagnitude g phi := by
  obtain ⟨p, hp, hpmax, hppos, hpstat⟩ :=
    odd_retained_interior_maximizer hg hOdd hj
  refine ⟨p, ⟨hp, hpmax, hppos⟩, ?_⟩
  rintro y ⟨hy, hymax, -⟩
  have hystat :=
    (odd_retained_lobe_stationary_iff_isGreatest hg hOdd hj hy).mpr hymax
  exact odd_retained_stationary_unique hg hOdd hj hy hystat hp hpstat

end GdgSquarefree
