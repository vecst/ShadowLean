/-
# Phase 9 — the publication-facing gd_g critical-family certificate

This module bundles the analytic objects certified in Phases 1–8 into a single
structure `GdgCriticalFamilyCertificate`, and proves that such a certificate
exists for every `g ≥ 5` (with natural-lobe offset `0` for even `g` and
`1/2` for odd `g`).

Contents:
* `gdgCriticalSlotBlockCoord`, `gdgCriticalSlotValue` — transparent slot
  evaluators (block coordinates and cover values) parameterized by a phase
  family and an exterior parameter;
* `GdgCriticalFamilyCertificate` — the certificate structure;
* `gdgBlockCriticalPolynomial_roots_nodup`,
  `gdgBlockCriticalPolynomial_squarefree`,
  `nonempty_even_gdgCriticalFamilyCertificate`,
  `nonempty_odd_gdgCriticalFamilyCertificate`,
  `nonempty_gdgCriticalFamilyCertificate`.

This closes the analytic gd_g completion gate: exactly one stationary phase per
retained natural lobe, exactly one positive exterior critical parameter,
exhaustion of all (simple) complex roots of the free block critical polynomial,
their location on the real line, exact realization of the slot values by the
pulled cover, and pairwise injectivity of the critical values.

NOT claimed here: monodromy, local branch cycles, a symmetric or
wreath-product Galois group, or any radical-solvability threshold.
-/
import RequestProject.GdgExteriorInteriorNoncollision

namespace GdgSquarefree

open Polynomial

/-! ### Local helpers -/

/-- The block degree is positive for `g ≥ 5`. -/
private theorem flagship_blockDegree_pos {g : ℕ} (hg : 5 ≤ g) :
    1 ≤ gdgBlockDegree g := by
  simp only [gdgBlockDegree]
  omega

/-- The block polynomial is nonzero for `g ≥ 5`. -/
private theorem flagship_blockCritical_ne_zero {g : ℕ} (hg : 5 ≤ g) :
    gdgBlockCriticalPolynomial g ≠ 0 := by
  intro h
  have hdeg := gdgBlockCriticalPolynomial_natDegree hg
  rw [h, Polynomial.natDegree_zero] at hdeg
  have h1 := flagship_blockDegree_pos hg
  omega

/-- For `g ≥ 5` the cosine coefficient `a_g = 2 cos (2π/g)` is strictly below
`2`. -/
private theorem flagship_cosCoeff_lt_two {g : ℕ} (hg : 5 ≤ g) :
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

/-- Left endpoints of natural lobes with a nonnegative offset are
nonnegative. -/
private theorem flagship_lobeLeft_nonneg {g j : ℕ} (hg : 1 ≤ g)
    {offset : ℝ} (hoff : 0 ≤ offset) :
    0 ≤ gdgLobeLeft g j offset := by
  have hth : 0 < gdgTheta g := gdgTheta_pos hg
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  simp only [gdgLobeLeft]
  nlinarith

/-- On the retained interior the block coordinate lies strictly between
`-gdgCosCoeff g` and `2`. -/
private theorem flagship_blockCoord_mem_Ioo {g : ℕ} (hg : 5 ≤ g) {phi : ℝ}
    (h0 : 0 < phi) (hlt : phi < Real.pi - gdgTheta g) :
    gdgBlockCoord phi ∈ Set.Ioo (-gdgCosCoeff g) 2 := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hthlt : gdgTheta g < Real.pi / 2 := gdgTheta_lt_pi_div_two hg
  have hpi := Real.pi_pos
  have hmem : phi ∈ Set.Icc 0 Real.pi := ⟨h0.le, by linarith⟩
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, hpi.le⟩
  have hmem2 : Real.pi - gdgTheta g ∈ Set.Icc 0 Real.pi :=
    ⟨by linarith, by linarith⟩
  have h1 : Real.cos phi < Real.cos 0 := Real.strictAntiOn_cos hmem0 hmem h0
  have h2 : Real.cos (Real.pi - gdgTheta g) < Real.cos phi :=
    Real.strictAntiOn_cos hmem hmem2 hlt
  rw [Real.cos_pi_sub] at h2
  rw [Real.cos_zero] at h1
  have hcos : gdgCosCoeff g = 2 * Real.cos (gdgTheta g) := by
    simp only [gdgCosCoeff, gdgTheta]
  simp only [Set.mem_Ioo, gdgBlockCoord, hcos]
  constructor <;> linarith

/-- Any injective real slot family of roots of the block polynomial exhausts
the complex root set, by the Phase 6A exact root count. -/
private theorem flagship_slot_classification {g : ℕ} (hg : 5 ≤ g)
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
  have hcard : (Set.range fun s => ((r s : ℝ) : ℂ)).ncard =
      gdgBlockDegree g := by
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

/-! ### The slot evaluators -/

/-- The real block coordinate attached to each free root slot: the interior
block coordinate of the stationary phase on an interior slot, and the exterior
block coordinate on the exterior slot. -/
noncomputable def gdgCriticalSlotBlockCoord
    (g : ℕ) (phi : Fin (gdgRetainedLobeCount g) → ℝ) (t : ℝ) :
    gdgBlockRootSlot g → ℝ
  | Sum.inl j => gdgBlockCoord (phi j)
  | Sum.inr _ => gdgExteriorBlockCoord t

/-- The real critical value attached to each free root slot: the signed
interior cover value on an interior slot, and the positive exterior cover value
on the exterior slot. -/
noncomputable def gdgCriticalSlotValue
    (g : ℕ) (phi : Fin (gdgRetainedLobeCount g) → ℝ) (t : ℝ) :
    gdgBlockRootSlot g → ℝ
  | Sum.inl j => gdgSignedInterior g (phi j)
  | Sum.inr _ => gdgExteriorCoverValue g t

/-! ### The certificate -/

/-- The gd_g critical-family certificate at genus parameter `g` and
natural-lobe offset `offset`. -/
structure GdgCriticalFamilyCertificate (g : ℕ) (offset : ℝ) where
  phase : Fin (gdgRetainedLobeCount g) → ℝ
  exteriorParam : ℝ
  phase_mem : ∀ j,
    phase j ∈ Set.Ioo
      (gdgLobeLeft g j.1 offset)
      (gdgLobeRight g j.1 offset)
  phase_stationary : ∀ j,
    HasDerivAt (gdgSignedInterior g) 0 (phase j)
  phase_unique : ∀ j (psi : ℝ),
    (psi ∈ Set.Ioo
        (gdgLobeLeft g j.1 offset)
        (gdgLobeRight g j.1 offset) ∧
      HasDerivAt (gdgSignedInterior g) 0 psi) ↔
      psi = phase j
  exterior_pos : 0 < exteriorParam
  exterior_critical :
    gdgExteriorCriticalRatio g exteriorParam =
      Real.cos (gdgTheta g)
  exterior_unique : ∀ t : ℝ,
    (0 < t ∧
      gdgExteriorCriticalRatio g t = Real.cos (gdgTheta g)) ↔
      t = exteriorParam
  block_squarefree : Squarefree (gdgBlockCriticalPolynomial g)
  root_count :
    Set.ncard {z : ℂ |
      (gdgBlockCriticalPolynomial g).eval z = 0} =
        gdgBlockDegree g
  slot_block_injective :
    Function.Injective
      (gdgCriticalSlotBlockCoord g phase exteriorParam)
  root_classification : ∀ z : ℂ,
    (gdgBlockCriticalPolynomial g).eval z = 0 ↔
      ∃ s : gdgBlockRootSlot g,
        z = (gdgCriticalSlotBlockCoord g phase exteriorParam s : ℂ)
  interior_block_location : ∀ j,
    gdgBlockCoord (phase j) ∈ Set.Ioo (-gdgCosCoeff g) 2
  exterior_block_location :
    gdgExteriorBlockCoord exteriorParam < -2
  exterior_block_unique : ∀ b : ℝ,
    (b < -2 ∧
      (gdgBlockCriticalPolynomial g).eval (b : ℂ) = 0) ↔
      b = gdgExteriorBlockCoord exteriorParam
  interior_value_realization : ∀ j,
    gdgPulledCover g (gdgUnitCircle (phase j)) =
      (gdgCriticalSlotValue g phase exteriorParam (Sum.inl j) : ℂ)
  exterior_value_realization :
    gdgPulledCover g (gdgExteriorUnit exteriorParam) =
      (gdgCriticalSlotValue g phase exteriorParam (Sum.inr ()) : ℂ)
  slot_value_injective :
    Function.Injective
      (gdgCriticalSlotValue g phase exteriorParam)

/-! ### Target 1: the roots of the block polynomial are simple -/

/-- **Target 1.** For `g ≥ 5` the complex roots of the free block critical
polynomial are pairwise distinct: its root multiset has no repetition. -/
theorem gdgBlockCriticalPolynomial_roots_nodup
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgBlockCriticalPolynomial g).roots.Nodup := by
  have hne : gdgBlockCriticalPolynomial g ≠ 0 :=
    flagship_blockCritical_ne_zero hg
  have hsplits : (gdgBlockCriticalPolynomial g).Splits :=
    IsAlgClosed.splits _
  have hmult : Multiset.card (gdgBlockCriticalPolynomial g).roots =
      gdgBlockDegree g := by
    rw [Polynomial.splits_iff_card_roots.mp hsplits,
      gdgBlockCriticalPolynomial_natDegree hg]
  have hset : {z : ℂ | (gdgBlockCriticalPolynomial g).eval z = 0} =
      ((gdgBlockCriticalPolynomial g).roots.toFinset : Set ℂ) := by
    ext z
    simp [hne, Polynomial.IsRoot]
  have hfin : (gdgBlockCriticalPolynomial g).roots.toFinset.card =
      gdgBlockDegree g := by
    have hc := gdgBlockCriticalPolynomial_root_set_ncard hg
    rwa [hset, Set.ncard_coe_finset] at hc
  exact Multiset.toFinset_card_eq_card_iff_nodup.mp (by rw [hfin, hmult])

/-! ### Target 2: squarefreeness of the block polynomial -/

/-- **Target 2.** For `g ≥ 5` the free block critical polynomial is
squarefree. -/
theorem gdgBlockCriticalPolynomial_squarefree
    {g : ℕ} (hg : 5 ≤ g) :
    Squarefree (gdgBlockCriticalPolynomial g) := by
  have hne : gdgBlockCriticalPolynomial g ≠ 0 :=
    flagship_blockCritical_ne_zero hg
  have hsep : (gdgBlockCriticalPolynomial g).Separable :=
    (Polynomial.nodup_roots_iff_of_splits hne (IsAlgClosed.splits _)).mp
      (gdgBlockCriticalPolynomial_roots_nodup hg)
  exact hsep.squarefree

/-! ### The parity-free certificate constructor -/

/-- Assembling a certificate from parity-specific analytic input. -/
private theorem nonempty_certificate_of_data {g : ℕ} (hg : 5 ≤ g)
    {offset : ℝ} (hoff : 0 ≤ offset)
    (hpole : ∀ j : ℕ, j ∈ gdgRetainedLobeIndices g →
      gdgLobeRight g j offset < Real.pi - gdgTheta g)
    (hstationary : ∀ j : Fin (gdgRetainedLobeCount g),
      ∃! phi : ℝ,
        phi ∈ Set.Ioo
          (gdgLobeLeft g j.1 offset) (gdgLobeRight g j.1 offset) ∧
        HasDerivAt (gdgSignedInterior g) 0 phi)
    (hblockRoot : ∀ (j : ℕ), j ∈ gdgRetainedLobeIndices g → ∀ phi : ℝ,
      phi ∈ Set.Ioo (gdgLobeLeft g j offset) (gdgLobeRight g j offset) →
      HasDerivAt (gdgSignedInterior g) 0 phi →
      (gdgBlockCriticalPolynomial g).eval (gdgBlockCoord phi : ℂ) = 0)
    (hcoordNe : ∀ (j k : ℕ), j ∈ gdgRetainedLobeIndices g →
      k ∈ gdgRetainedLobeIndices g → j < k → ∀ phi psi : ℝ,
      phi ∈ Set.Ioo (gdgLobeLeft g j offset) (gdgLobeRight g j offset) →
      psi ∈ Set.Ioo (gdgLobeLeft g k offset) (gdgLobeRight g k offset) →
      gdgBlockCoord phi ≠ gdgBlockCoord psi)
    (hvalueNe : ∀ (j k : ℕ), j ∈ gdgRetainedLobeIndices g →
      k ∈ gdgRetainedLobeIndices g → j ≠ k → ∀ phi psi : ℝ,
      phi ∈ Set.Ioo (gdgLobeLeft g j offset) (gdgLobeRight g j offset) →
      psi ∈ Set.Ioo (gdgLobeLeft g k offset) (gdgLobeRight g k offset) →
      HasDerivAt (gdgSignedInterior g) 0 phi →
      HasDerivAt (gdgSignedInterior g) 0 psi →
      gdgSignedInterior g phi ≠ gdgSignedInterior g psi)
    (hextNe : ∀ (j : ℕ), j ∈ gdgRetainedLobeIndices g → ∀ phi t : ℝ,
      phi ∈ Set.Ioo (gdgLobeLeft g j offset) (gdgLobeRight g j offset) →
      HasDerivAt (gdgSignedInterior g) 0 phi → 0 < t →
      gdgExteriorCriticalRatio g t = Real.cos (gdgTheta g) →
      gdgSignedInterior g phi ≠ gdgExteriorCoverValue g t) :
    Nonempty (GdgCriticalFamilyCertificate g offset) := by
  classical
  choose phase hphase hphaseUniq using hstationary
  obtain ⟨tstar, ⟨htpos, htcrit⟩, htuniq⟩ :=
    existsUnique_gdgExteriorCriticalRatio_eq_cos hg
  have hmemIdx : ∀ j : Fin (gdgRetainedLobeCount g),
      (j : ℕ) ∈ gdgRetainedLobeIndices g := fun j =>
    gdg_mem_retainedLobeIndices_iff.mpr j.isLt
  have hcos2 := flagship_cosCoeff_lt_two hg
  -- interior block locations
  have hIoo : ∀ j : Fin (gdgRetainedLobeCount g),
      gdgBlockCoord (phase j) ∈ Set.Ioo (-gdgCosCoeff g) 2 := by
    intro j
    have hleft : (0 : ℝ) ≤ gdgLobeLeft g j.1 offset :=
      flagship_lobeLeft_nonneg (g := g) (j := j.1) (by omega) hoff
    have hright := hpole j.1 (hmemIdx j)
    exact flagship_blockCoord_mem_Ioo hg
      (lt_of_le_of_lt hleft (hphase j).1.1)
      (lt_trans (hphase j).1.2 hright)
  -- exterior block location
  have hextloc : gdgExteriorBlockCoord tstar < -2 :=
    gdgExteriorBlockCoord_lt_neg_two htpos
  -- every slot is a root
  have hroot : ∀ s : gdgBlockRootSlot g,
      (gdgBlockCriticalPolynomial g).eval
        ((gdgCriticalSlotBlockCoord g phase tstar s : ℝ) : ℂ) = 0 := by
    rintro (j | u)
    · exact hblockRoot j.1 (hmemIdx j) (phase j) (hphase j).1 (hphase j).2
    · exact (gdgBlockCriticalPolynomial_exterior_eq_zero_iff hg tstar).mpr
        htcrit
  -- coordinate injectivity
  have hinj : Function.Injective
      (gdgCriticalSlotBlockCoord g phase tstar) := by
    rintro (j | u) (k | v) h
    · simp only [gdgCriticalSlotBlockCoord] at h
      rcases lt_trichotomy (j : ℕ) (k : ℕ) with hlt | heq | hgt
      · exact absurd h (hcoordNe j.1 k.1 (hmemIdx j) (hmemIdx k) hlt
          (phase j) (phase k) (hphase j).1 (hphase k).1)
      · exact congrArg Sum.inl (Fin.ext heq)
      · exact absurd h.symm (hcoordNe k.1 j.1 (hmemIdx k) (hmemIdx j) hgt
          (phase k) (phase j) (hphase k).1 (hphase j).1)
    · exfalso
      simp only [gdgCriticalSlotBlockCoord] at h
      have h1 := (hIoo j).1
      rw [h] at h1
      linarith
    · exfalso
      simp only [gdgCriticalSlotBlockCoord] at h
      have h1 := (hIoo k).1
      rw [← h] at h1
      linarith
    · cases u; cases v; rfl
  -- the unique exterior real root below -2
  obtain ⟨b0, ⟨hb0lt, hb0root⟩, hb0uniq⟩ := existsUnique_exterior_blockRoot hg
  have hb0eq : b0 = gdgExteriorBlockCoord tstar :=
    (hb0uniq (gdgExteriorBlockCoord tstar)
      ⟨hextloc,
        (gdgBlockCriticalPolynomial_exterior_eq_zero_iff hg tstar).mpr
          htcrit⟩).symm
  -- value injectivity
  have hvinj : Function.Injective (gdgCriticalSlotValue g phase tstar) := by
    rintro (j | u) (k | v) h
    · simp only [gdgCriticalSlotValue] at h
      by_cases hjk : (j : ℕ) = (k : ℕ)
      · exact congrArg Sum.inl (Fin.ext hjk)
      · exact absurd h (hvalueNe j.1 k.1 (hmemIdx j) (hmemIdx k) hjk
          (phase j) (phase k) (hphase j).1 (hphase k).1
          (hphase j).2 (hphase k).2)
    · exfalso
      simp only [gdgCriticalSlotValue] at h
      exact hextNe j.1 (hmemIdx j) (phase j) tstar (hphase j).1
        (hphase j).2 htpos htcrit h
    · exfalso
      simp only [gdgCriticalSlotValue] at h
      exact hextNe k.1 (hmemIdx k) (phase k) tstar (hphase k).1
        (hphase k).2 htpos htcrit h.symm
    · cases u; cases v; rfl
  refine ⟨{
    phase := phase
    exteriorParam := tstar
    phase_mem := fun j => (hphase j).1
    phase_stationary := fun j => (hphase j).2
    phase_unique := fun j psi => ⟨fun h => hphaseUniq j psi h,
      fun h => h ▸ hphase j⟩
    exterior_pos := htpos
    exterior_critical := htcrit
    exterior_unique := fun t => ⟨fun h => htuniq t h,
      fun h => h ▸ ⟨htpos, htcrit⟩⟩
    block_squarefree := gdgBlockCriticalPolynomial_squarefree hg
    root_count := gdgBlockCriticalPolynomial_root_set_ncard hg
    slot_block_injective := hinj
    root_classification := flagship_slot_classification hg hroot hinj
    interior_block_location := hIoo
    exterior_block_location := hextloc
    exterior_block_unique := ?_
    interior_value_realization := ?_
    exterior_value_realization := ?_
    slot_value_injective := hvinj }⟩
  · intro b
    constructor
    · intro hb
      rw [hb0uniq b hb, hb0eq]
    · rintro rfl
      exact ⟨hextloc,
        (gdgBlockCriticalPolynomial_exterior_eq_zero_iff hg tstar).mpr htcrit⟩
  · intro j
    simpa only [gdgCriticalSlotValue] using
      gdgPulledCover_gdgUnitCircle_eq_signed (g := g) (phase j)
  · simpa only [gdgCriticalSlotValue] using
      gdgPulledCover_gdgExteriorUnit hg tstar

/-! ### Targets 3–5: existence of the certificate -/

/-- **Target 3.** For even `g ≥ 5` a critical-family certificate exists at the
natural-lobe offset `0`. -/
theorem nonempty_even_gdgCriticalFamilyCertificate
    {g : ℕ} (hg : 5 ≤ g) (hEven : Even g) :
    Nonempty (GdgCriticalFamilyCertificate g 0) := by
  refine nonempty_certificate_of_data hg le_rfl
    (fun j hj => (gdgEven_mem_iff_lobeRight_lt_pole hg hEven).mp hj)
    (fun j => existsUnique_even_retained_lobe_stationary hg hEven
      (gdg_mem_retainedLobeIndices_iff.mpr j.isLt))
    (fun j hj phi hphi hstat =>
      even_retained_lobe_stationary_blockRoot hg hEven hj hphi hstat)
    (fun j k hj hk hjk phi psi hphi hpsi =>
      gdgBlockCoord_ne_of_even_retained_lobes hg hEven hj hk hjk hphi hpsi)
    (fun j k hj hk hjk phi psi hphi hpsi hphiStat hpsiStat =>
      even_distinct_retained_stationary_values_ne hg hEven hj hk hjk hphi hpsi
        hphiStat hpsiStat)
    (fun j hj phi t hphi hstat ht hcrit =>
      even_retained_stationary_value_ne_exterior_critical hg hEven hj hphi
        hstat ht hcrit)

/-- **Target 4.** For odd `g ≥ 5` a critical-family certificate exists at the
natural-lobe offset `1/2`.  At `g = 5` the interior slot family is empty and
only the exterior slot survives. -/
theorem nonempty_odd_gdgCriticalFamilyCertificate
    {g : ℕ} (hg : 5 ≤ g) (hOdd : Odd g) :
    Nonempty
      (GdgCriticalFamilyCertificate g ((1 : ℝ) / 2)) := by
  refine nonempty_certificate_of_data hg (by norm_num)
    (fun j hj => (gdgOdd_mem_iff_lobeRight_lt_pole hg hOdd).mp hj)
    (fun j => existsUnique_odd_retained_lobe_stationary hg hOdd
      (gdg_mem_retainedLobeIndices_iff.mpr j.isLt))
    (fun j hj phi hphi hstat =>
      odd_retained_lobe_stationary_blockRoot hg hOdd hj hphi hstat)
    (fun j k hj hk hjk phi psi hphi hpsi =>
      gdgBlockCoord_ne_of_odd_retained_lobes hg hOdd hj hk hjk hphi hpsi)
    (fun j k hj hk hjk phi psi hphi hpsi hphiStat hpsiStat =>
      odd_distinct_retained_stationary_values_ne hg hOdd hj hk hjk hphi hpsi
        hphiStat hpsiStat)
    (fun j hj phi t hphi hstat ht hcrit =>
      odd_retained_stationary_value_ne_exterior_critical hg hOdd hj hphi
        hstat ht hcrit)

/-- **Target 5.** The all-`g` flagship entry point: for every `g ≥ 5` a
critical-family certificate exists, at offset `0` for even `g` and `1/2` for
odd `g`. -/
theorem nonempty_gdgCriticalFamilyCertificate
    {g : ℕ} (hg : 5 ≤ g) :
    (Even g ∧ Nonempty (GdgCriticalFamilyCertificate g 0)) ∨
      (Odd g ∧ Nonempty
        (GdgCriticalFamilyCertificate g ((1 : ℝ) / 2))) := by
  rcases Nat.even_or_odd g with hEven | hOdd
  · exact Or.inl ⟨hEven, nonempty_even_gdgCriticalFamilyCertificate hg hEven⟩
  · exact Or.inr ⟨hOdd, nonempty_odd_gdgCriticalFamilyCertificate hg hOdd⟩

end GdgSquarefree
