/-
gd_g completion roadmap, Phase 2B — EXHAUSTIVE natural-zero / lobe classification.

Phase 2A (GdgRetainedLobes) indexed exactly the formula-defined retained lobes
but did not prove the converse: that every real zero of the numerator
|2 cos(gφ) − 2(−1)^g| has one of the formula locations. This module closes that
gap in three layers:
  (1) classify every real numerator zero by an INTEGER index (Targets 3,4);
  (2) on the pre-pole domain, pin the zero to a UNIQUE finite endpoint index
      (Targets 5,6, using the retained endpoint set below);
  (3) prove strict numerator positivity in every consecutive formula lobe, so no
      hidden zero lies between its endpoints (Targets 7,8).

θ_g = gdgTheta g = 2π/g. Even zeros are at n·θ_g (cos(gφ)=1); odd zeros at
(n+1/2)·θ_g (cos(gφ)=−1), n ∈ ℤ (negative real zeros exist — the global index
type is Int; Nat appears only after domain bounds prove nonnegativity).

SCOPE. This is zero/lobe geometry only. It does NOT prove critical-point
existence, critical-point uniqueness, degree exhaustion, critical-value
separation, monodromy, or any Galois-group conclusion.

Reuses gdgTheta, gdgTheta_pos, gdgInteriorNumeratorAbs, gdgLobeLeft, gdgLobeRight,
gdgEvenLobe_numerator_values, gdgOddLobe_numerator_values, gdgRetainedLobeCount,
gdgRetainedLobeIndices, gdg_mem_retainedLobeIndices_iff, gdgRetainedLobeCount_eq_*,
gdgEven/Odd_mem_iff_lobeRight_lt_pole; and the Mathlib classifications
Real.cos_eq_one_iff (cos x = 1 ↔ ∃ n:ℤ, (n)·(2π) = x) and Real.cos_eq_neg_one_iff
(cos x = −1 ↔ ∃ k:ℤ, π + k·(2π) = x, x implicit).

Proof routes (statements verbatim; standard axioms only; NO numeric π; NO false
"interior log-derivative globally decreasing" claim):

* T1/T2 (endpoint set membership/card; retained lobe = adjacent endpoint pair):
  Finset.mem_range / card_range + omega. `gdgRetainedZeroIndices g` has ONE more
  element than the lobe count (Finset.range (count+1)); at g=5 the lobe count is 0
  but this endpoint set has one element (the first odd zero) — do not collapse it.

* T3 (even global): |z|=0 ↔ z=0; hEven.neg_one_pow turns (−1)^g into 1; the
  numerator equality reduces to cos(gφ)=1; Real.cos_eq_one_iff gives ∃ n:ℤ,
  n·(2π)=gφ; with (g:ℝ)·θ_g = 2π (g≠0), φ = n·θ_g. Both directions.

* T4 (odd global): hOdd.neg_one_pow turns (−1)^g into −1; reduce to cos(gφ)=−1;
  Real.cos_eq_neg_one_iff gives ∃ k:ℤ, π + k·(2π) = gφ; the identity
  π + n·(2π) = (n+1/2)·(2π) then gives φ = (n+1/2)·θ_g. Both directions.

* T5/T6 (unique finite endpoint on the pre-pole domain, ∃!): forward — from T3/T4
  get φ = idx·θ_g (resp. (idx+1/2)θ_g); the LEFT-CLOSED bound (0 even; θ_g/2 odd)
  forces the Int index ≥ 0 (cast to Nat j via θ_g>0), the RIGHT-OPEN bound
  (< π−θ_g) plus the exact count forces j ≤ gdgRetainedLobeCount g, so
  j ∈ gdgRetainedZeroIndices g and φ = gdgLobeLeft g j (0 / (1/2)); reverse —
  endpoint membership gives a classified zero (gdgEven/OddLobe_numerator_values or
  T3/T4). UNIQUENESS from θ_g > 0. Keep the domain right-open (pole excluded) and
  DO NOT weaken ∃! to ∃. (g=5 odd: exactly one endpoint θ_g/2, no retained lobe —
  nonvacuous.)

* T7/T8 (no hidden zero in a lobe interior, Set.Ioo, global in j): abs ≥ 0; if
  the numerator were 0 then by T3/T4 φ = n·θ_g (resp. (n+1/2)θ_g) for some n:ℤ,
  but φ ∈ (jθ_g, (j+1)θ_g) forces j < n < j+1 (θ_g>0), impossible for an integer.
  Uses Ioo (open) — endpoints ARE zeros, so never claim positivity on Icc.

Certification: no sorry/admit/new axiom/unsafe/implemented_by; no silent
weakening (preserve ∃!, strict/right-open bounds, Int global index); keep
unclosable targets out and report exact name + remaining goal; run module, Main,
audit with --wfail (v4.33.0-rc2); report #print axioms per public theorem. This
completes EXHAUSTIVE natural-zero/lobe classification (Phase 2B) — every real
zero is globally Int-indexed and, on the pre-pole domain, has a unique finite
endpoint, and no hidden zero occurs inside a formula lobe — but NOT critical-point
existence/uniqueness, degree exhaustion, critical-value separation, or monodromy.
-/
import Mathlib
import RequestProject.GdgRetainedLobes

namespace GdgSquarefree

/-- Finite retained ENDPOINT indices: one more than the retained lobe count. -/
def gdgRetainedZeroIndices (g : ℕ) : Finset ℕ :=
  Finset.range (gdgRetainedLobeCount g + 1)

/-- **Target 1a.** Endpoint-index membership. -/
@[simp] theorem gdg_mem_retainedZeroIndices_iff {g j : ℕ} :
    j ∈ gdgRetainedZeroIndices g ↔
      j ≤ gdgRetainedLobeCount g := by
  simp only [gdgRetainedZeroIndices, Finset.mem_range]
  omega

/-- **Target 1b.** Endpoint-index cardinality. -/
@[simp] theorem gdg_card_retainedZeroIndices (g : ℕ) :
    (gdgRetainedZeroIndices g).card =
      gdgRetainedLobeCount g + 1 := by
  simp [gdgRetainedZeroIndices]

/-- **Target 2.** A retained lobe index is exactly an adjacent endpoint pair. -/
theorem gdg_mem_retainedLobeIndices_iff_endpoint_pair {g j : ℕ} :
    j ∈ gdgRetainedLobeIndices g ↔
      j ∈ gdgRetainedZeroIndices g ∧
        j + 1 ∈ gdgRetainedZeroIndices g := by
  simp only [gdg_mem_retainedLobeIndices_iff, gdg_mem_retainedZeroIndices_iff]
  omega

/-- **Target 3.** Global even numerator-zero classification (Int index). -/
theorem gdgEven_numerator_zero_iff_int_index {g : ℕ}
    (hg : 1 ≤ g) (hEven : Even g) (phi : ℝ) :
    gdgInteriorNumeratorAbs g phi = 0 ↔
      ∃ n : ℤ,
        phi = (n : ℝ) * gdgTheta g := by
  have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hgth : (g : ℝ) * gdgTheta g = 2 * Real.pi := by
    rw [gdgTheta]; field_simp
  have hpar : ((-1 : ℝ) ^ g) = 1 := hEven.neg_one_pow
  rw [gdgInteriorNumeratorAbs, hpar, abs_eq_zero]
  constructor
  · intro h
    have hcos : Real.cos ((g : ℝ) * phi) = 1 := by linarith
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hcos
    refine ⟨n, mul_left_cancel₀ (ne_of_gt hg0) ?_⟩
    rw [show (g : ℝ) * ((n : ℝ) * gdgTheta g)
        = (n : ℝ) * ((g : ℝ) * gdgTheta g) by ring, hgth, hn]
  · rintro ⟨n, rfl⟩
    rw [show (g : ℝ) * ((n : ℝ) * gdgTheta g)
        = (n : ℝ) * ((g : ℝ) * gdgTheta g) by ring, hgth,
      (Real.cos_eq_one_iff _).mpr ⟨n, rfl⟩]
    ring

/-- **Target 4.** Global odd numerator-zero classification (Int index). -/
theorem gdgOdd_numerator_zero_iff_int_index {g : ℕ}
    (hg : 1 ≤ g) (hOdd : Odd g) (phi : ℝ) :
    gdgInteriorNumeratorAbs g phi = 0 ↔
      ∃ n : ℤ,
        phi = ((n : ℝ) + (1 : ℝ) / 2) * gdgTheta g := by
  have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hgth : (g : ℝ) * gdgTheta g = 2 * Real.pi := by
    rw [gdgTheta]; field_simp
  have hpar : ((-1 : ℝ) ^ g) = -1 := hOdd.neg_one_pow
  rw [gdgInteriorNumeratorAbs, hpar, abs_eq_zero]
  constructor
  · intro h
    have hcos : Real.cos ((g : ℝ) * phi) = -1 := by linarith
    obtain ⟨n, hn⟩ := Real.cos_eq_neg_one_iff.mp hcos
    refine ⟨n, mul_left_cancel₀ (ne_of_gt hg0) ?_⟩
    rw [show (g : ℝ) * (((n : ℝ) + (1 : ℝ) / 2) * gdgTheta g)
        = ((n : ℝ) + (1 : ℝ) / 2) * ((g : ℝ) * gdgTheta g) by ring, hgth, ← hn]
    ring
  · rintro ⟨n, rfl⟩
    rw [show (g : ℝ) * (((n : ℝ) + (1 : ℝ) / 2) * gdgTheta g)
        = ((n : ℝ) + (1 : ℝ) / 2) * ((g : ℝ) * gdgTheta g) by ring, hgth,
      show ((n : ℝ) + (1 : ℝ) / 2) * (2 * Real.pi)
        = Real.pi + (n : ℝ) * (2 * Real.pi) by ring,
      Real.cos_eq_neg_one_iff.mpr ⟨n, rfl⟩]
    ring

/-- **Target 5.** Unique finite even endpoint classification on the pre-pole
interval (left-closed at 0, right-open at the pole). -/
theorem gdgEven_numerator_zero_iff_existsUnique_retained_endpoint
    {g : ℕ} (hg : 5 ≤ g) (hEven : Even g) {phi : ℝ}
    (hphi : phi ∈ Set.Ico 0 (Real.pi - gdgTheta g)) :
    gdgInteriorNumeratorAbs g phi = 0 ↔
      ∃! j : ℕ,
        j ∈ gdgRetainedZeroIndices g ∧
          phi = gdgLobeLeft g j 0 := by
  have hg1 : 1 ≤ g := by omega
  have hth : 0 < gdgTheta g := gdgTheta_pos hg1
  have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg1
  obtain ⟨hlo, hhi⟩ := hphi
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (gdgEven_numerator_zero_iff_int_index hg1 hEven phi).mp h
    have hn0 : 0 ≤ n := by
      by_contra hcon
      push Not at hcon
      have hle : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      nlinarith
    have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast congrArg (fun m : ℤ => (m : ℝ)) (Int.toNat_of_nonneg hn0)
    refine ⟨n.toNat, ⟨?_, ?_⟩, ?_⟩
    · rw [gdg_mem_retainedZeroIndices_iff]
      have hlt : ((n : ℝ) + 1) * gdgTheta g < Real.pi := by
        rw [hn] at hhi; nlinarith
      have hlt' : ((n : ℝ) + 1) * (2 * Real.pi) < Real.pi * (g : ℝ) := by
        rw [gdgTheta] at hlt
        rw [show ((n : ℝ) + 1) * (2 * Real.pi / (g : ℝ))
          = ((n : ℝ) + 1) * (2 * Real.pi) / (g : ℝ) by ring,
          div_lt_iff₀ hg0] at hlt
        linarith
      have hnum : 2 * ((n : ℝ) + 1) < (g : ℝ) := by nlinarith [Real.pi_pos]
      have hnat : 2 * (n + 1) < (g : ℤ) := by exact_mod_cast hnum
      obtain ⟨m, rfl⟩ := hEven
      unfold gdgRetainedLobeCount
      omega
    · rw [gdgLobeLeft, hcast, add_zero, hn]
    · rintro k ⟨-, hk⟩
      rw [gdgLobeLeft, add_zero, hn] at hk
      have hkn : (k : ℝ) = (n : ℝ) := by
        have := mul_right_cancel₀ (ne_of_gt hth) hk.symm
        linarith
      have : (k : ℝ) = ((n.toNat : ℕ) : ℝ) := by rw [hcast]; exact hkn
      exact_mod_cast this
  · rintro ⟨j, ⟨-, rfl⟩, -⟩
    exact (gdgEvenLobe_numerator_values hg hEven).1

/-- **Target 6.** Unique finite odd endpoint classification on the pre-pole
interval (left-closed at θ_g/2, right-open at the pole). -/
theorem gdgOdd_numerator_zero_iff_existsUnique_retained_endpoint
    {g : ℕ} (hg : 5 ≤ g) (hOdd : Odd g) {phi : ℝ}
    (hphi : phi ∈ Set.Ico
      (gdgLobeLeft g 0 ((1 : ℝ) / 2))
      (Real.pi - gdgTheta g)) :
    gdgInteriorNumeratorAbs g phi = 0 ↔
      ∃! j : ℕ,
        j ∈ gdgRetainedZeroIndices g ∧
          phi = gdgLobeLeft g j ((1 : ℝ) / 2) := by
  have hg1 : 1 ≤ g := by omega
  have hth : 0 < gdgTheta g := gdgTheta_pos hg1
  have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg1
  obtain ⟨hlo, hhi⟩ := hphi
  simp only [gdgLobeLeft, Nat.cast_zero, zero_add] at hlo
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (gdgOdd_numerator_zero_iff_int_index hg1 hOdd phi).mp h
    have hn0 : 0 ≤ n := by
      by_contra hcon
      push Not at hcon
      have hle : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      rw [hn] at hlo
      nlinarith
    have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast congrArg (fun m : ℤ => (m : ℝ)) (Int.toNat_of_nonneg hn0)
    refine ⟨n.toNat, ⟨?_, ?_⟩, ?_⟩
    · rw [gdg_mem_retainedZeroIndices_iff]
      have hlt : ((n : ℝ) + 3 / 2) * gdgTheta g < Real.pi := by
        rw [hn] at hhi; nlinarith
      have hlt' : ((n : ℝ) + 3 / 2) * (2 * Real.pi) < Real.pi * (g : ℝ) := by
        rw [gdgTheta] at hlt
        rw [show ((n : ℝ) + 3 / 2) * (2 * Real.pi / (g : ℝ))
          = ((n : ℝ) + 3 / 2) * (2 * Real.pi) / (g : ℝ) by ring,
          div_lt_iff₀ hg0] at hlt
        linarith
      have hnum : 2 * (n : ℝ) + 3 < (g : ℝ) := by nlinarith [Real.pi_pos]
      have hnat : 2 * n + 3 < (g : ℤ) := by exact_mod_cast hnum
      obtain ⟨m, rfl⟩ := hOdd
      unfold gdgRetainedLobeCount
      omega
    · rw [gdgLobeLeft, hcast, hn]
    · rintro k ⟨-, hk⟩
      rw [gdgLobeLeft, hn] at hk
      have hkn : (k : ℝ) = (n : ℝ) := by
        have := mul_right_cancel₀ (ne_of_gt hth) hk.symm
        linarith
      have : (k : ℝ) = ((n.toNat : ℕ) : ℝ) := by rw [hcast]; exact hkn
      exact_mod_cast this
  · rintro ⟨j, ⟨-, rfl⟩, -⟩
    exact (gdgOddLobe_numerator_values hg hOdd).1

/-- **Target 7.** No hidden zero inside an even formula lobe (open interior). -/
theorem gdgEven_numerator_pos_on_lobeInterior {g j : ℕ}
    (hg : 1 ≤ g) (hEven : Even g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0)
      (gdgLobeRight g j 0)) :
    0 < gdgInteriorNumeratorAbs g phi := by
  obtain ⟨h1, h2⟩ := hphi
  simp only [gdgLobeRight, gdgLobeLeft, add_zero] at h1 h2
  have hne : gdgInteriorNumeratorAbs g phi ≠ 0 := by
    intro h
    obtain ⟨n, rfl⟩ := (gdgEven_numerator_zero_iff_int_index hg hEven phi).mp h
    have hth : 0 < gdgTheta g := gdgTheta_pos hg
    have hlt1 : (j : ℝ) < (n : ℝ) := by
      have := (mul_lt_mul_iff_of_pos_right hth).mp h1
      linarith
    have hlt2 : (n : ℝ) < (j : ℝ) + 1 := by
      have h2' : (n : ℝ) * gdgTheta g < ((j : ℝ) + 1) * gdgTheta g := by
        nlinarith [h2]
      have := (mul_lt_mul_iff_of_pos_right hth).mp h2'
      linarith
    have hi1 : (j : ℤ) < n := by exact_mod_cast hlt1
    have hi2 : n < (j : ℤ) + 1 := by exact_mod_cast hlt2
    omega
  have h0 : 0 ≤ gdgInteriorNumeratorAbs g phi := by
    rw [gdgInteriorNumeratorAbs]; exact abs_nonneg _
  exact lt_of_le_of_ne h0 (Ne.symm hne)

/-- **Target 8.** No hidden zero inside an odd formula lobe (open interior). -/
theorem gdgOdd_numerator_pos_on_lobeInterior {g j : ℕ}
    (hg : 1 ≤ g) (hOdd : Odd g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2))) :
    0 < gdgInteriorNumeratorAbs g phi := by
  obtain ⟨h1, h2⟩ := hphi
  simp only [gdgLobeRight, gdgLobeLeft] at h1 h2
  have hne : gdgInteriorNumeratorAbs g phi ≠ 0 := by
    intro h
    obtain ⟨n, rfl⟩ := (gdgOdd_numerator_zero_iff_int_index hg hOdd phi).mp h
    have hth : 0 < gdgTheta g := gdgTheta_pos hg
    have hlt1 : (j : ℝ) < (n : ℝ) := by
      have := (mul_lt_mul_iff_of_pos_right hth).mp h1
      linarith
    have hlt2 : (n : ℝ) < (j : ℝ) + 1 := by
      have h2' : (((n : ℝ) + (1 : ℝ) / 2)) * gdgTheta g
          < ((j : ℝ) + (1 : ℝ) / 2 + 1) * gdgTheta g := by
        nlinarith [h2]
      have := (mul_lt_mul_iff_of_pos_right hth).mp h2'
      linarith
    have hi1 : (j : ℤ) < n := by exact_mod_cast hlt1
    have hi2 : n < (j : ℤ) + 1 := by exact_mod_cast hlt2
    omega
  have h0 : 0 ≤ gdgInteriorNumeratorAbs g phi := by
    rw [gdgInteriorNumeratorAbs]; exact abs_nonneg _
  exact lt_of_le_of_ne h0 (Ne.symm hne)

end GdgSquarefree
