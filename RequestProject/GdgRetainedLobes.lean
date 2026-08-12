/-
gd_g completion roadmap, Phase 2A — RETAINED natural-lobe index set, exact
counts, the one-step pole guard, and a positive maximum on every retained lobe.

For g ≥ 5 the formula-defined natural lobes whose right endpoint lies strictly
before the removed pole π − θ_g (θ_g = 2π/g) are indexed by a finite set of size
  L_g = (g − 4) / 2   (Nat division)
      = g/2 − 2  (even g)  = (g − 5)/2  (odd g).
Adding the single exterior critical slot gives (g − 2)/2 free slots. The
before-pole condition `gdgLobeRight … < π − θ_g` is STRICT; the interval ending
at equality is the removed-pole interval and is never retained.

SCOPE. This fixes the retained-lobe index set/count, the pole guard, and
positive maxima on every retained lobe. It does NOT classify every real zero of
the trigonometric numerator (that converse zero-classification is Phase 2B and
is not asserted here), and it does NOT prove critical-point existence,
uniqueness, free-factor degree, critical-value separation, monodromy, or a
Galois-group theorem.

Reuses GdgSquarefree.gdgTheta, gdgTheta_pos, gdgLobeLeft, gdgLobeRight,
gdgLobeMid, gdgLobeLeft_succ, gdgLobeRight_eq_next_left, exists_pos_even_lobe_max,
exists_pos_odd_lobe_max (from GdgNaturalLobes and below it).

Proof routes (statements verbatim; standard axioms only; no numerical π):

* T1 (gdg_mem_retainedLobeIndices_iff, gdg_card_retainedLobeIndices):
  `Finset.mem_range`, `Finset.card_range` after unfolding the defs.

* T2 (…_eq_even / …_eq_odd): `obtain ⟨k, rfl⟩ := hEven`/`hOdd`, unfold
  gdgRetainedLobeCount, `omega` (Nat floor-division and truncated subtraction).

* T3 (…_add_one): `unfold gdgRetainedLobeCount; omega` (g ≥ 5, so
  (g−4)/2 + 1 = (g−2)/2 exactly in ℕ).

* T4 (…_even_lt_pole_iff / …_odd_lt_pole_iff): unfold gdgLobeRight, gdgLobeLeft;
  a PURE linear rearrangement (add θ_g to both sides), treating `(j:ℝ)*θ_g` as an
  atom — `constructor <;> intro h <;> nlinarith` (or ring_nf + linarith). `hg` is
  unused here (interface only) → a narrow linter.unusedVariables guard.

* T5 (…_even_last_lt_pole / …_odd_last_lt_pole): rewrite via T4 to
  `((j:ℝ)+2)·θ_g < π` (even) / `((j:ℝ)+5/2)·θ_g < π` (odd); with θ_g = 2π/g,
  g > 0, π > 0 this is equivalent to the Nat/real fact `2*(j+2) < g` (even) /
  `2*j+5 < g` (odd), which follows from `hj : j < gdgRetainedLobeCount g` and T2
  by `omega`, cast to ℝ.

* T6 (exists_pos_even_retained_lobe_max / …_odd_…): feed T5's strict pole bound
  into exists_pos_even_lobe_max / exists_pos_odd_lobe_max.

Certification: no sorry/admit/new axiom/unsafe/implemented_by; no silent
weakening (preserve strict `<` and exact Nat / real forms); keep unclosable
targets out and report their exact name + remaining goal; run module, Main, audit
with --wfail (v4.33.0-rc2); report #print axioms per public theorem. This module
fixes the retained-lobe index set, exact count, pole guard, and positive maxima;
zero-classification completeness, critical-point existence/uniqueness, degree,
separation, and monodromy remain OPEN.
-/
import Mathlib
import RequestProject.GdgNaturalLobes

namespace GdgSquarefree

/-- Number of retained natural lobes for `g` (right endpoint strictly before the
pole): `L_g = (g − 4)/2` in ℕ. -/
def gdgRetainedLobeCount (g : ℕ) : ℕ :=
  (g - 4) / 2

/-- The retained natural-lobe index set `{0, …, L_g − 1}`. -/
def gdgRetainedLobeIndices (g : ℕ) : Finset ℕ :=
  Finset.range (gdgRetainedLobeCount g)

/-- **Target 1a.** Membership in the retained index set. -/
@[simp] theorem gdg_mem_retainedLobeIndices_iff {g j : ℕ} :
    j ∈ gdgRetainedLobeIndices g ↔
      j < gdgRetainedLobeCount g := by
  simp [gdgRetainedLobeIndices]

/-- **Target 1b.** Cardinality of the retained index set. -/
@[simp] theorem gdg_card_retainedLobeIndices (g : ℕ) :
    (gdgRetainedLobeIndices g).card =
      gdgRetainedLobeCount g := by
  simp [gdgRetainedLobeIndices]

/-- **Target 2 (even).** Even-parity count formula. -/
theorem gdgRetainedLobeCount_eq_even {g : ℕ}
    (hEven : Even g) :
    gdgRetainedLobeCount g = g / 2 - 2 := by
  obtain ⟨k, rfl⟩ := hEven
  unfold gdgRetainedLobeCount
  omega

/-- **Target 2 (odd).** Odd-parity count formula. -/
theorem gdgRetainedLobeCount_eq_odd {g : ℕ}
    (hOdd : Odd g) :
    gdgRetainedLobeCount g = (g - 5) / 2 := by
  obtain ⟨k, rfl⟩ := hOdd
  unfold gdgRetainedLobeCount
  omega

/-- **Target 3.** Total free-slot count: retained lobes plus the exterior slot. -/
theorem gdgRetainedLobeCount_add_one {g : ℕ} (hg : 5 ≤ g) :
    gdgRetainedLobeCount g + 1 = (g - 2) / 2 := by
  unfold gdgRetainedLobeCount
  omega

-- `hg` is part of the fixed interface but the rearrangement is unconditional.
set_option linter.unusedVariables false in
/-- **Target 4 (even).** Exact pole-angle rearrangement, even offset. -/
theorem gdgLobeRight_even_lt_pole_iff {g j : ℕ} (hg : 5 ≤ g) :
    gdgLobeRight g j 0 < Real.pi - gdgTheta g ↔
      ((j : ℝ) + 2) * gdgTheta g < Real.pi := by
  simp only [gdgLobeRight, gdgLobeLeft]
  constructor <;> intro h <;> nlinarith [h]

-- `hg` is part of the fixed interface but the rearrangement is unconditional.
set_option linter.unusedVariables false in
/-- **Target 4 (odd).** Exact pole-angle rearrangement, odd offset. -/
theorem gdgLobeRight_odd_lt_pole_iff {g j : ℕ} (hg : 5 ≤ g) :
    gdgLobeRight g j ((1 : ℝ) / 2) < Real.pi - gdgTheta g ↔
      ((j : ℝ) + (5 : ℝ) / 2) * gdgTheta g < Real.pi := by
  simp only [gdgLobeRight, gdgLobeLeft]
  constructor <;> intro h <;> nlinarith [h]

/-- **Target 5 (even).** Every retained even index is strictly before the pole. -/
theorem gdgLobeRight_even_last_lt_pole {g : ℕ}
    (hg : 5 ≤ g) (hEven : Even g)
    {j : ℕ} (hj : j < gdgRetainedLobeCount g) :
    gdgLobeRight g j 0 < Real.pi - gdgTheta g := by
  rw [gdgLobeRight_even_lt_pole_iff hg]
  have hgpos : (0 : ℝ) < (g : ℝ) := by
    have : (0 : ℕ) < g := by omega
    exact_mod_cast this
  have hpi := Real.pi_pos
  have hnat : 2 * (j + 2) < g := by
    rw [gdgRetainedLobeCount_eq_even hEven] at hj
    obtain ⟨k, rfl⟩ := hEven
    omega
  have hcast : 2 * ((j : ℝ) + 2) < (g : ℝ) := by exact_mod_cast hnat
  rw [gdgTheta, mul_div_assoc', div_lt_iff₀ hgpos]
  nlinarith

/-- **Target 5 (odd).** Every retained odd index is strictly before the pole. -/
theorem gdgLobeRight_odd_last_lt_pole {g : ℕ}
    (hg : 5 ≤ g) (hOdd : Odd g)
    {j : ℕ} (hj : j < gdgRetainedLobeCount g) :
    gdgLobeRight g j ((1 : ℝ) / 2) < Real.pi - gdgTheta g := by
  rw [gdgLobeRight_odd_lt_pole_iff hg]
  have hgpos : (0 : ℝ) < (g : ℝ) := by
    have : (0 : ℕ) < g := by omega
    exact_mod_cast this
  have hpi := Real.pi_pos
  have hnat : 2 * j + 5 < g := by
    rw [gdgRetainedLobeCount_eq_odd hOdd] at hj
    obtain ⟨k, rfl⟩ := hOdd
    omega
  have hcast : 2 * (j : ℝ) + 5 < (g : ℝ) := by exact_mod_cast hnat
  rw [gdgTheta, mul_div_assoc', div_lt_iff₀ hgpos]
  nlinarith

/-- **Target 6 (even).** Positive attained maximum on every retained even lobe. -/
theorem exists_pos_even_retained_lobe_max {g : ℕ}
    (hg : 5 ≤ g) (hEven : Even g)
    {j : ℕ} (hj : j < gdgRetainedLobeCount g) :
    ∃ M,
      IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc (gdgLobeLeft g j 0) (gdgLobeRight g j 0)) M ∧
      0 < M := by
  exact exists_pos_even_lobe_max hg hEven
    (gdgLobeRight_even_last_lt_pole hg hEven hj)

/-- **Target 6 (odd).** Positive attained maximum on every retained odd lobe. -/
theorem exists_pos_odd_retained_lobe_max {g : ℕ}
    (hg : 5 ≤ g) (hOdd : Odd g)
    {j : ℕ} (hj : j < gdgRetainedLobeCount g) :
    ∃ M,
      IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc
            (gdgLobeLeft g j ((1 : ℝ) / 2))
            (gdgLobeRight g j ((1 : ℝ) / 2))) M ∧
      0 < M := by
  exact exists_pos_odd_lobe_max hg hOdd
    (gdgLobeRight_odd_last_lt_pole hg hOdd hj)

/-- **Phase 2A T1.** Full even membership ⟺ before-pole equivalence. -/
theorem gdgEven_mem_iff_lobeRight_lt_pole {g j : ℕ}
    (hg : 5 ≤ g) (hEven : Even g) :
    j ∈ gdgRetainedLobeIndices g ↔
      gdgLobeRight g j 0 < Real.pi - gdgTheta g := by
  constructor
  · intro hmem
    exact gdgLobeRight_even_last_lt_pole hg hEven
      (gdg_mem_retainedLobeIndices_iff.mp hmem)
  · intro hlt
    rw [gdgLobeRight_even_lt_pole_iff hg, gdgTheta] at hlt
    have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (show 0 < g by omega)
    rw [show ((j : ℝ) + 2) * (2 * Real.pi / (g : ℝ))
          = ((j : ℝ) + 2) * (2 * Real.pi) / (g : ℝ) by ring, div_lt_iff₀ hg0] at hlt
    have hnum : 2 * ((j : ℝ) + 2) < (g : ℝ) := by nlinarith [hlt, Real.pi_pos]
    have hnat : 2 * (j + 2) < g := by exact_mod_cast hnum
    rw [gdg_mem_retainedLobeIndices_iff]
    obtain ⟨m, rfl⟩ := hEven
    unfold gdgRetainedLobeCount
    omega

/-- **Phase 2A T2.** Full odd membership ⟺ before-pole equivalence. -/
theorem gdgOdd_mem_iff_lobeRight_lt_pole {g j : ℕ}
    (hg : 5 ≤ g) (hOdd : Odd g) :
    j ∈ gdgRetainedLobeIndices g ↔
      gdgLobeRight g j ((1 : ℝ) / 2) <
        Real.pi - gdgTheta g := by
  constructor
  · intro hmem
    exact gdgLobeRight_odd_last_lt_pole hg hOdd
      (gdg_mem_retainedLobeIndices_iff.mp hmem)
  · intro hlt
    rw [gdgLobeRight_odd_lt_pole_iff hg, gdgTheta] at hlt
    have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (show 0 < g by omega)
    rw [show ((j : ℝ) + (5 : ℝ) / 2) * (2 * Real.pi / (g : ℝ))
          = ((j : ℝ) + (5 : ℝ) / 2) * (2 * Real.pi) / (g : ℝ) by ring, div_lt_iff₀ hg0] at hlt
    have hnum : 2 * (j : ℝ) + 5 < (g : ℝ) := by nlinarith [hlt, Real.pi_pos]
    have hnat : 2 * j + 5 < g := by exact_mod_cast hnum
    rw [gdg_mem_retainedLobeIndices_iff]
    obtain ⟨m, rfl⟩ := hOdd
    unfold gdgRetainedLobeCount
    omega

/-- **Phase 2A T3.** Shifted even one-step pole guard. -/
theorem gdgEven_next_lobe_before_pole {g j : ℕ}
    (hg : 5 ≤ g) (hEven : Even g)
    (hjnext : j + 1 ∈ gdgRetainedLobeIndices g) :
    gdgLobeRight g j 0 + gdgTheta g <
      Real.pi - gdgTheta g := by
  have hid : gdgLobeRight g j 0 + gdgTheta g = gdgLobeRight g (j + 1) 0 := by
    unfold gdgLobeRight gdgLobeLeft
    push_cast
    ring
  rw [hid]
  exact (gdgEven_mem_iff_lobeRight_lt_pole hg hEven).mp hjnext

/-- **Phase 2A T4.** Shifted odd one-step pole guard. -/
theorem gdgOdd_next_lobe_before_pole {g j : ℕ}
    (hg : 5 ≤ g) (hOdd : Odd g)
    (hjnext : j + 1 ∈ gdgRetainedLobeIndices g) :
    gdgLobeRight g j ((1 : ℝ) / 2) + gdgTheta g <
      Real.pi - gdgTheta g := by
  have hid : gdgLobeRight g j ((1 : ℝ) / 2) + gdgTheta g
      = gdgLobeRight g (j + 1) ((1 : ℝ) / 2) := by
    unfold gdgLobeRight gdgLobeLeft
    push_cast
    ring
  rw [hid]
  exact (gdgOdd_mem_iff_lobeRight_lt_pole hg hOdd).mp hjnext

/-- **Phase 2A T5.** Distinct lobes have pairwise-disjoint open interiors. -/
theorem gdgLobe_interiors_disjoint_of_lt {g j k : ℕ}
    (hg : 1 ≤ g) (hjk : j < k) (offset : ℝ) :
    Disjoint
      (Set.Ioo
        (gdgLobeLeft g j offset)
        (gdgLobeRight g j offset))
      (Set.Ioo
        (gdgLobeLeft g k offset)
        (gdgLobeRight g k offset)) := by
  have hθ : 0 < gdgTheta g := gdgTheta_pos hg
  have hjk1 : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show j + 1 ≤ k by omega)
  have hle : gdgLobeRight g j offset ≤ gdgLobeLeft g k offset := by
    unfold gdgLobeRight gdgLobeLeft
    nlinarith [hθ, hjk1]
  rw [Set.disjoint_left]
  rintro x ⟨_, hxj2⟩ ⟨hxk1, _⟩
  linarith [hxj2, hle, hxk1]

/-- **Phase 2A T6 (g=5).** No retained interior lobe. -/
@[simp] theorem gdgRetainedLobeCount_five :
    gdgRetainedLobeCount 5 = 0 := by
  unfold gdgRetainedLobeCount; rfl

/-- **Phase 2A T6 (g=6).** One retained even lobe. -/
@[simp] theorem gdgRetainedLobeCount_six :
    gdgRetainedLobeCount 6 = 1 := by
  unfold gdgRetainedLobeCount; rfl

/-- **Phase 2A T6 (g=7).** One retained odd lobe. -/
@[simp] theorem gdgRetainedLobeCount_seven :
    gdgRetainedLobeCount 7 = 1 := by
  unfold gdgRetainedLobeCount; rfl

end GdgSquarefree
