/-
gd_g completion roadmap, Phase 6A — DEGREE EXHAUSTION of the block polynomial.

Phase 4F (`RequestProject.GdgBlockRootBridge`) produced `L_g =
gdgRetainedLobeCount g` pairwise distinct real roots of the block polynomial
`B_g = gdgBlockCriticalPolynomial g`, all lying in the open interval
`(-gdgCosCoeff g, 2)`.  Phase 5 (`RequestProject.GdgExteriorRoot`) produced
exactly one real root strictly below `-2`.  Since `gdgCosCoeff g < 2` for
`g ≥ 5`, the exterior root is distinct from every interior root, so `B_g` has
at least `d_g = L_g + 1 = gdgBlockDegree g` distinct complex roots.

Phase 4E (`RequestProject.GdgBlockDescent`) gives `natDegree B_g = d_g`, and a
nonzero polynomial over `ℂ` has at most `natDegree` distinct roots.  The
exhibited family therefore saturates the degree bound, so the complete complex
root set of `B_g` is exactly the image of the finite real slot family
`gdgBlockRootSlot g = Fin L_g ⊕ Unit`.  In particular every complex root of
`B_g` is real.

This module claims degree exhaustion and the all-roots-real classification
only.  It does NOT claim squarefreeness of `B_g`, uniqueness of a `phi`
critical witness inside a natural lobe, identification with the Phase 1
maximum, critical-value ordering, or any monodromy or Galois statement.
-/
import RequestProject.GdgExteriorRoot

namespace GdgSquarefree

open Polynomial

/-! ### Local helpers -/

/-- For `g ≥ 5` the cosine coefficient `a_g = 2 cos (2π/g)` is strictly below
`2`.  (The same fact is proved privately in an earlier module; it is reproved
here from the `gdgTheta` API since that proof is not exported.) -/
private theorem gdgCosCoeff_lt_two_local {g : ℕ} (hg : 5 ≤ g) :
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

/-- The block degree is positive for `g ≥ 5`. -/
private theorem gdgBlockDegree_pos_local {g : ℕ} (hg : 5 ≤ g) :
    1 ≤ gdgBlockDegree g := by
  unfold gdgBlockDegree
  omega

/-- The block polynomial is nonzero for `g ≥ 5`. -/
private theorem gdgBlockCriticalPolynomial_ne_zero_local {g : ℕ} (hg : 5 ≤ g) :
    gdgBlockCriticalPolynomial g ≠ 0 := by
  intro h
  have hdeg := gdgBlockCriticalPolynomial_natDegree hg
  rw [h, Polynomial.natDegree_zero] at hdeg
  have := gdgBlockDegree_pos_local hg
  omega

/-- For `g ≥ 5` the complex root set of the block polynomial is exactly the
coercion of the finite set of its distinct roots. -/
private theorem gdgBlockCriticalPolynomial_root_set_eq_toFinset
    {g : ℕ} (hg : 5 ≤ g) :
    {z : ℂ | (gdgBlockCriticalPolynomial g).eval z = 0} =
      ((gdgBlockCriticalPolynomial g).roots.toFinset : Set ℂ) := by
  ext z
  simp [gdgBlockCriticalPolynomial_ne_zero_local hg, Polynomial.IsRoot]

/-! ### The finite slot type -/

/-- The finite family of root slots of the block polynomial: one slot for each
retained natural lobe, plus a single exterior slot. -/
abbrev gdgBlockRootSlot (g : ℕ) :=
  Fin (gdgRetainedLobeCount g) ⊕ Unit

/-- **Target 1.** The slot type has exactly `d_g = gdgBlockDegree g`
elements. -/
theorem card_gdgBlockRootSlot
    {g : ℕ} (hg : 5 ≤ g) :
    Fintype.card (gdgBlockRootSlot g) = gdgBlockDegree g := by
  have h := gdgRetainedLobeCount_add_one hg
  simp only [gdgBlockRootSlot, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit, gdgBlockDegree]
  exact h

/-! ### The interior family -/

/-- **Target 2.** The retained natural lobes carry an injective family of real
block roots, each located strictly inside `(-a_g, 2)`. -/
theorem exists_retained_lobe_blockRoot_embedding
    {g : ℕ} (hg : 5 ≤ g) :
    ∃ r : {j // j ∈ gdgRetainedLobeIndices g} → ℝ,
      (∀ j, r j ∈ Set.Ioo (-gdgCosCoeff g) 2) ∧
      (∀ j, (gdgBlockCriticalPolynomial g).eval (r j : ℂ) = 0) ∧
      Function.Injective r := by
  rcases Nat.even_or_odd g with hEven | hOdd
  · choose phi hmem hroot hIoo using
      fun j : {j // j ∈ gdgRetainedLobeIndices g} =>
        exists_even_retained_lobe_blockCriticalPolynomial_root hg hEven j.2
    refine ⟨fun j => gdgBlockCoord (phi j), hIoo, hroot, ?_⟩
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
  · choose phi hmem hroot hIoo using
      fun j : {j // j ∈ gdgRetainedLobeIndices g} =>
        exists_odd_retained_lobe_blockCriticalPolynomial_root hg hOdd j.2
    refine ⟨fun j => gdgBlockCoord (phi j), hIoo, hroot, ?_⟩
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

/-! ### The combined slot family -/

/-- **Target 3.** The full slot type carries an injective family of real roots
of the block polynomial: the interior slots land in `(-a_g, 2)` and the
exterior slot lands strictly below `-2`. -/
theorem exists_gdgBlockRootSlot_embedding
    {g : ℕ} (hg : 5 ≤ g) :
    ∃ r : gdgBlockRootSlot g → ℝ,
      (∀ s, (gdgBlockCriticalPolynomial g).eval (r s : ℂ) = 0) ∧
      Function.Injective r ∧
      (∀ j : Fin (gdgRetainedLobeCount g),
        r (Sum.inl j) ∈ Set.Ioo (-gdgCosCoeff g) 2) ∧
      r (Sum.inr ()) < -2 := by
  obtain ⟨ri, hriIoo, hriroot, hriinj⟩ :=
    exists_retained_lobe_blockRoot_embedding hg
  obtain ⟨be, ⟨hbe2, hberoot⟩, -⟩ := existsUnique_exterior_blockRoot hg
  have hcos := gdgCosCoeff_lt_two_local hg
  refine ⟨fun s => Sum.elim
    (fun j : Fin (gdgRetainedLobeCount g) =>
      ri ⟨(j : ℕ), gdg_mem_retainedLobeIndices_iff.mpr j.isLt⟩)
    (fun _ => be) s, ?_, ?_, ?_, ?_⟩
  · rintro (j | u)
    · exact hriroot _
    · exact hberoot
  · rintro (j | u) (k | v) h
    · simp only [Sum.elim_inl] at h
      have := hriinj h
      exact congrArg Sum.inl (Fin.ext (congrArg Subtype.val this))
    · exfalso
      simp only [Sum.elim_inl, Sum.elim_inr] at h
      have h1 := (hriIoo ⟨(j : ℕ), gdg_mem_retainedLobeIndices_iff.mpr j.isLt⟩).1
      rw [h] at h1
      linarith
    · exfalso
      simp only [Sum.elim_inl, Sum.elim_inr] at h
      have h1 := (hriIoo ⟨(k : ℕ), gdg_mem_retainedLobeIndices_iff.mpr k.isLt⟩).1
      rw [← h] at h1
      linarith
    · cases u; cases v; rfl
  · intro j
    exact hriIoo _
  · exact hbe2

/-! ### Finiteness and exact cardinality of the complex root set -/

/-- **Target 4.** The complex root set of the block polynomial is finite. -/
theorem gdgBlockCriticalPolynomial_root_set_finite
    {g : ℕ} (hg : 5 ≤ g) :
    Set.Finite {z : ℂ |
      (gdgBlockCriticalPolynomial g).eval z = 0} := by
  rw [gdgBlockCriticalPolynomial_root_set_eq_toFinset hg]
  exact Set.finite_coe_iff.mp (Finset.finite_toSet _).to_subtype

/-- The complex-cast slot family lands inside the root set. -/
private theorem slot_image_subset_root_set
    {g : ℕ} {r : gdgBlockRootSlot g → ℝ}
    (hroot : ∀ s, (gdgBlockCriticalPolynomial g).eval (r s : ℂ) = 0) :
    (Set.range fun s => ((r s : ℝ) : ℂ)) ⊆
      {z : ℂ | (gdgBlockCriticalPolynomial g).eval z = 0} := by
  rintro z ⟨s, rfl⟩
  exact hroot s

/-- The complex-cast slot family has exactly `d_g` values. -/
private theorem slot_image_ncard
    {g : ℕ} (hg : 5 ≤ g) {r : gdgBlockRootSlot g → ℝ}
    (hinj : Function.Injective r) :
    (Set.range fun s => ((r s : ℝ) : ℂ)).ncard = gdgBlockDegree g := by
  have hinj' : Function.Injective fun s : gdgBlockRootSlot g =>
      ((r s : ℝ) : ℂ) := fun a b h =>
    hinj (Complex.ofReal_injective h)
  have hrange : (Set.range fun s => ((r s : ℝ) : ℂ)) =
      (fun s => ((r s : ℝ) : ℂ)) '' Set.univ := by
    rw [Set.image_univ]
  rw [hrange, Set.ncard_image_of_injective _ hinj', Set.ncard_univ,
    Nat.card_eq_fintype_card, card_gdgBlockRootSlot hg]

/-- **Target 5.** The block polynomial has exactly `d_g` distinct complex
roots. -/
theorem gdgBlockCriticalPolynomial_root_set_ncard
    {g : ℕ} (hg : 5 ≤ g) :
    Set.ncard {z : ℂ |
      (gdgBlockCriticalPolynomial g).eval z = 0} =
        gdgBlockDegree g := by
  obtain ⟨r, hroot, hinj, -, -⟩ := exists_gdgBlockRootSlot_embedding hg
  refine le_antisymm ?_ ?_
  · rw [gdgBlockCriticalPolynomial_root_set_eq_toFinset hg,
      Set.ncard_coe_finset]
    calc (gdgBlockCriticalPolynomial g).roots.toFinset.card
        ≤ Multiset.card (gdgBlockCriticalPolynomial g).roots :=
          (gdgBlockCriticalPolynomial g).roots.toFinset_card_le
      _ ≤ (gdgBlockCriticalPolynomial g).natDegree :=
          Polynomial.card_roots' _
      _ = gdgBlockDegree g := gdgBlockCriticalPolynomial_natDegree hg
  · rw [← slot_image_ncard hg hinj]
    exact Set.ncard_le_ncard (slot_image_subset_root_set hroot)
      (gdgBlockCriticalPolynomial_root_set_finite hg)

/-! ### The complete classification -/

/-- **Target 6.** The complete complex root classification of the block
polynomial: an injective real slot family whose complex image is exactly the
root set, with the interior slots in `(-a_g, 2)` and the exterior slot below
`-2`. -/
theorem exists_gdgBlockRootSlot_classification
    {g : ℕ} (hg : 5 ≤ g) :
    ∃ r : gdgBlockRootSlot g → ℝ,
      Function.Injective r ∧
      (∀ s, (gdgBlockCriticalPolynomial g).eval (r s : ℂ) = 0) ∧
      (∀ z : ℂ, (gdgBlockCriticalPolynomial g).eval z = 0 ↔
        ∃ s, z = (r s : ℂ)) ∧
      (∀ j : Fin (gdgRetainedLobeCount g),
        r (Sum.inl j) ∈ Set.Ioo (-gdgCosCoeff g) 2) ∧
      r (Sum.inr ()) < -2 := by
  obtain ⟨r, hroot, hinj, hIoo, hext⟩ := exists_gdgBlockRootSlot_embedding hg
  have hsub := slot_image_subset_root_set hroot
  have hcard : Set.ncard {z : ℂ |
      (gdgBlockCriticalPolynomial g).eval z = 0} ≤
        (Set.range fun s => ((r s : ℝ) : ℂ)).ncard := by
    rw [slot_image_ncard hg hinj,
      gdgBlockCriticalPolynomial_root_set_ncard hg]
  have hset := Set.eq_of_subset_of_ncard_le hsub hcard
    (gdgBlockCriticalPolynomial_root_set_finite hg)
  refine ⟨r, hinj, hroot, ?_, hIoo, hext⟩
  intro z
  constructor
  · intro hz
    have : z ∈ (Set.range fun s => ((r s : ℝ) : ℂ)) := by
      rw [hset]; exact hz
    obtain ⟨s, hs⟩ := this
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact hroot s

/-- **Target 7.** Every complex root of the block polynomial is real. -/
theorem gdgBlockCriticalPolynomial_all_roots_real
    {g : ℕ} (hg : 5 ≤ g) {z : ℂ}
    (hz : (gdgBlockCriticalPolynomial g).eval z = 0) :
    ∃ b : ℝ, z = (b : ℂ) := by
  obtain ⟨r, -, -, hiff, -, -⟩ := exists_gdgBlockRootSlot_classification hg
  obtain ⟨s, hs⟩ := (hiff z).mp hz
  exact ⟨r s, hs⟩

end GdgSquarefree
