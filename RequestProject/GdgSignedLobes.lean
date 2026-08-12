/-
gd_g completion roadmap, Phase 3A — SIGNED real pullback, regularity, parity
signs, and a per-lobe φ-stationary-point (Rolle) witness.

The magnitude function gdgInteriorMagnitude orders maxima but cannot be
differentiated cleanly through its absolute value at the zero endpoints. This
module introduces the SIGNED real pullback gdgSignedInterior, relates it exactly
to the magnitude on the nonsingular (denominator ≠ 0) domain, proves its parity
signs and regularity, and applies Rolle to get a genuine HasDerivAt … 0 witness
inside every retained lobe. Division is totalized in Lean; the mathematical cover
is used ONLY where the denominator is nonzero — the removed pole is never treated
as an ordinary point.

This run STOPS at a HasDerivAt (gdgSignedInterior g) 0 c witness in the φ
coordinate. It does NOT call this a free critical point of the algebraic cover;
the chain-rule/coordinate bridge to coverNumerator/coverQuadratic/
criticalTetranomial is Phase 3B. It does NOT prove critical-point uniqueness,
degree exhaustion, full critical-value separation, or monodromy.

Proof routes (statements verbatim; standard axioms only; no numeric π; no false
"interior log-derivative globally decreasing" claim):

* T1 abs_…_eq_gdgInteriorMagnitude: with denom>0, denom^g>0, so
  |num/denom^g| = |num|/denom^g = gdgInteriorNumeratorAbs/denom^g = magnitude.
* T2 parity identities: even — hEven.neg_one_pow, Real.cos_le_one ⇒ numerator
  2cos(gφ)−2 ≤ 0 ⇒ signed = −magnitude; odd — hOdd.neg_one_pow,
  Real.neg_one_le_cos ⇒ numerator 2cos(gφ)+2 ≥ 0 ⇒ signed = magnitude. Equalities.
* T3 continuity on [left,right] before pole: gdgInteriorDenominator_pos_on_Icc
  gives denom≠0 pointwise; numerator continuous; ContinuousOn.div.
* T4 differentiableAt off denom-zero: cos ∘ affine, sub, Nat pow, div by nonzero
  denom^g (pow_ne_zero). This is the regularity feeding Rolle's HasDerivAt.
* T5 retained endpoint values: retained membership ⇒ right < π−θ_g (mem-iff) and
  left ≥ 0, so denom>0 on the closed lobe; numerator endpoint values 0
  (gdgEven/OddLobe_numerator_values) ⇒ signed = 0. Guarded by membership — never
  via 0/0 at a singular endpoint.
* T6 strict interior sign: denom>0 (membership+before-pole); T2 parity identity +
  the Phase 2B gdgEven/Odd_numerator_pos_on_lobeInterior (magnitude>0 in the open
  lobe) ⇒ signed <0 (even) / >0 (odd). No strict claim at endpoints.
* T7/T8 Rolle witness: gdgTheta_pos ⇒ left<right; T3 continuity on Icc; T5 equal
  endpoint values; Rolle (exists_hasDerivAt_eq_zero / exists_deriv_eq_zero) gives
  an interior c; retained before-pole ⇒ denom≠0 at c; T4 differentiability there
  ⇒ HasDerivAt (gdgSignedInterior g) 0 c. Existence only (no uniqueness); at g=5
  the retained odd index set is empty so T8 is correctly vacuous.

Certification: no sorry/admit/new axiom/unsafe/implemented_by; no silent
weakening (preserve strict signs, retained-membership guards, HasDerivAt over
deriv, no uniqueness); keep unclosable targets out and report exact name +
remaining goal; run module, Main, audit with --wfail (v4.33.0-rc2); report
#print axioms per public theorem. This closes signed-lobe regularity, parity
signs, and per-lobe φ-stationary-point existence (Phase 3A) — NOT the φ→block
critical bridge, critical-point uniqueness, degree exhaustion, full
critical-value separation, or monodromy.
-/
import Mathlib
import RequestProject.GdgZeroClassification

namespace GdgSquarefree

/-- Signed real pullback of the reduced gd_g block cover (totalized division;
used mathematically only where the denominator is nonzero). -/
noncomputable def gdgSignedInterior (g : ℕ) (phi : ℝ) : ℝ :=
  (2 * Real.cos ((g : ℝ) * phi) -
      2 * ((-1 : ℝ) ^ g)) /
    (gdgInteriorDenominator g phi) ^ g

/-- **Target 1.** The absolute value of the signed pullback is the magnitude. -/
theorem abs_gdgSignedInterior_eq_gdgInteriorMagnitude
    {g : ℕ} {phi : ℝ}
    (hden : 0 < gdgInteriorDenominator g phi) :
    |gdgSignedInterior g phi| =
      gdgInteriorMagnitude g phi := by
  have hp : 0 < (gdgInteriorDenominator g phi) ^ g := pow_pos hden g
  simp only [gdgSignedInterior, gdgInteriorMagnitude, gdgInteriorNumeratorAbs,
    abs_div, abs_of_pos hp]

/-- **Target 2 (even).** Even parity: signed = −magnitude. -/
theorem gdgSignedInterior_eq_neg_magnitude_of_even {g : ℕ}
    (hEven : Even g) {phi : ℝ}
    (hden : 0 < gdgInteriorDenominator g phi) :
    gdgSignedInterior g phi =
      -gdgInteriorMagnitude g phi := by
  have hp : 0 < (gdgInteriorDenominator g phi) ^ g := pow_pos hden g
  have hnum : 2 * Real.cos ((g : ℝ) * phi) - 2 * ((-1 : ℝ) ^ g) ≤ 0 := by
    rw [hEven.neg_one_pow]
    have := Real.cos_le_one ((g : ℝ) * phi)
    linarith
  have hsig : gdgSignedInterior g phi ≤ 0 := by
    simp only [gdgSignedInterior]
    exact div_nonpos_iff.mpr (Or.inr ⟨hnum, hp.le⟩)
  rw [← abs_gdgSignedInterior_eq_gdgInteriorMagnitude hden, abs_of_nonpos hsig,
    neg_neg]

/-- **Target 2 (odd).** Odd parity: signed = magnitude. -/
theorem gdgSignedInterior_eq_magnitude_of_odd {g : ℕ}
    (hOdd : Odd g) {phi : ℝ}
    (hden : 0 < gdgInteriorDenominator g phi) :
    gdgSignedInterior g phi =
      gdgInteriorMagnitude g phi := by
  have hp : 0 < (gdgInteriorDenominator g phi) ^ g := pow_pos hden g
  have hnum : 0 ≤ 2 * Real.cos ((g : ℝ) * phi) - 2 * ((-1 : ℝ) ^ g) := by
    rw [hOdd.neg_one_pow]
    have := Real.neg_one_le_cos ((g : ℝ) * phi)
    linarith
  have hsig : 0 ≤ gdgSignedInterior g phi := by
    simp only [gdgSignedInterior]
    exact div_nonneg hnum hp.le
  rw [← abs_gdgSignedInterior_eq_gdgInteriorMagnitude hden, abs_of_nonneg hsig]

/-- **Target 3.** Continuity on a closed pre-pole interval. -/
theorem continuousOn_gdgSignedInterior_of_before_pole
    {g : ℕ} (hg : 5 ≤ g) {left right : ℝ}
    (hleft0 : 0 ≤ left)
    (hright : right < Real.pi - gdgTheta g) :
    ContinuousOn (gdgSignedInterior g) (Set.Icc left right) := by
  have hden := gdgInteriorDenominator_pos_on_Icc hg hleft0 hright
  have hnum : ContinuousOn
      (fun phi : ℝ => 2 * Real.cos ((g : ℝ) * phi) - 2 * ((-1 : ℝ) ^ g))
      (Set.Icc left right) := by
    fun_prop
  have hdenc : ContinuousOn
      (fun phi : ℝ => (gdgInteriorDenominator g phi) ^ g)
      (Set.Icc left right) := by
    simp only [gdgInteriorDenominator]
    fun_prop
  exact hnum.div hdenc (fun x hx => pow_ne_zero _ (ne_of_gt (hden x hx)))

/-- **Target 4.** Differentiability off the denominator zero set. -/
theorem differentiableAt_gdgSignedInterior_of_denominator_ne_zero
    {g : ℕ} {phi : ℝ}
    (hden : gdgInteriorDenominator g phi ≠ 0) :
    DifferentiableAt ℝ (gdgSignedInterior g) phi := by
  have hnum : DifferentiableAt ℝ
      (fun x : ℝ => 2 * Real.cos ((g : ℝ) * x) - 2 * ((-1 : ℝ) ^ g)) phi := by
    fun_prop
  have hdenc : DifferentiableAt ℝ
      (fun x : ℝ => (gdgInteriorDenominator g x) ^ g) phi := by
    simp only [gdgInteriorDenominator]
    fun_prop
  exact hnum.div hdenc (pow_ne_zero _ hden)

/-- Left endpoints of natural lobes with a nonnegative offset are nonnegative. -/
private theorem gdgLobeLeft_nonneg {g j : ℕ} (hg : 1 ≤ g)
    {offset : ℝ} (hoff : 0 ≤ offset) :
    0 ≤ gdgLobeLeft g j offset := by
  have hth : 0 < gdgTheta g := gdgTheta_pos hg
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  simp only [gdgLobeLeft]
  nlinarith

/-- On a retained EVEN lobe the denominator is positive (the removed pole lies
strictly to the right of the closed lobe). -/
private theorem gdgEven_retained_denominator_pos {g j : ℕ}
    (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Icc (gdgLobeLeft g j 0) (gdgLobeRight g j 0)) :
    0 < gdgInteriorDenominator g phi :=
  gdgInteriorDenominator_pos_on_Icc hg
    (gdgLobeLeft_nonneg (j := j) (by omega) le_rfl)
    ((gdgEven_mem_iff_lobeRight_lt_pole hg hEven).mp hj) phi hphi

/-- On a retained ODD lobe the denominator is positive (the removed pole lies
strictly to the right of the closed lobe). -/
private theorem gdgOdd_retained_denominator_pos {g j : ℕ}
    (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Icc
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2))) :
    0 < gdgInteriorDenominator g phi :=
  gdgInteriorDenominator_pos_on_Icc hg
    (gdgLobeLeft_nonneg (j := j) (by omega) (by norm_num))
    ((gdgOdd_mem_iff_lobeRight_lt_pole hg hOdd).mp hj) phi hphi

/-- Both endpoints of a natural lobe lie in its closed interval. -/
private theorem gdgLobe_endpoints_mem_Icc {g j : ℕ} (hg : 1 ≤ g) (offset : ℝ) :
    gdgLobeLeft g j offset ∈
        Set.Icc (gdgLobeLeft g j offset) (gdgLobeRight g j offset) ∧
      gdgLobeRight g j offset ∈
        Set.Icc (gdgLobeLeft g j offset) (gdgLobeRight g j offset) := by
  have hth : 0 < gdgTheta g := gdgTheta_pos hg
  simp only [Set.mem_Icc, gdgLobeRight]
  exact ⟨⟨le_rfl, by linarith⟩, ⟨by linarith, le_rfl⟩⟩

/-- **Target 5 (even).** Signed pullback vanishes at both retained even
endpoints. -/
theorem gdgSignedInterior_even_endpoint_values {g j : ℕ}
    (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    gdgSignedInterior g (gdgLobeLeft g j 0) = 0 ∧
      gdgSignedInterior g (gdgLobeRight g j 0) = 0 := by
  obtain ⟨hmemL, hmemR⟩ := gdgLobe_endpoints_mem_Icc (g := g) (j := j) (by omega) 0
  have hvals := gdgEvenLobe_numerator_values (j := j) hg hEven
  constructor
  · rw [gdgSignedInterior_eq_neg_magnitude_of_even hEven
      (gdgEven_retained_denominator_pos hg hEven hj hmemL)]
    simp only [gdgInteriorMagnitude, hvals.1, zero_div, neg_zero]
  · rw [gdgSignedInterior_eq_neg_magnitude_of_even hEven
      (gdgEven_retained_denominator_pos hg hEven hj hmemR)]
    simp only [gdgInteriorMagnitude, hvals.2.1, zero_div, neg_zero]

/-- **Target 5 (odd).** Signed pullback vanishes at both retained odd
endpoints. -/
theorem gdgSignedInterior_odd_endpoint_values {g j : ℕ}
    (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    gdgSignedInterior g
        (gdgLobeLeft g j ((1 : ℝ) / 2)) = 0 ∧
      gdgSignedInterior g
        (gdgLobeRight g j ((1 : ℝ) / 2)) = 0 := by
  obtain ⟨hmemL, hmemR⟩ :=
    gdgLobe_endpoints_mem_Icc (g := g) (j := j) (by omega) ((1 : ℝ) / 2)
  have hvals := gdgOddLobe_numerator_values (j := j) hg hOdd
  constructor
  · rw [gdgSignedInterior_eq_magnitude_of_odd hOdd
      (gdgOdd_retained_denominator_pos hg hOdd hj hmemL)]
    simp only [gdgInteriorMagnitude, hvals.1, zero_div]
  · rw [gdgSignedInterior_eq_magnitude_of_odd hOdd
      (gdgOdd_retained_denominator_pos hg hOdd hj hmemR)]
    simp only [gdgInteriorMagnitude, hvals.2.1, zero_div]

/-- **Target 6 (even).** Strictly negative inside every retained even lobe. -/
theorem gdgSignedInterior_neg_on_even_retained_lobeInterior
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j 0)
      (gdgLobeRight g j 0)) :
    gdgSignedInterior g phi < 0 := by
  have hden := gdgEven_retained_denominator_pos hg hEven hj
    (Set.Ioo_subset_Icc_self hphi)
  have hnum := gdgEven_numerator_pos_on_lobeInterior (g := g) (j := j)
    (by omega) hEven hphi
  have hmag : 0 < gdgInteriorMagnitude g phi := by
    simp only [gdgInteriorMagnitude]
    exact div_pos hnum (pow_pos hden g)
  rw [gdgSignedInterior_eq_neg_magnitude_of_even hEven hden]
  linarith

/-- **Target 6 (odd).** Strictly positive inside every retained odd lobe. -/
theorem gdgSignedInterior_pos_on_odd_retained_lobeInterior
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Ioo
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2))) :
    0 < gdgSignedInterior g phi := by
  have hden := gdgOdd_retained_denominator_pos hg hOdd hj
    (Set.Ioo_subset_Icc_self hphi)
  have hnum := gdgOdd_numerator_pos_on_lobeInterior (g := g) (j := j)
    (by omega) hOdd hphi
  have hmag : 0 < gdgInteriorMagnitude g phi := by
    simp only [gdgInteriorMagnitude]
    exact div_pos hnum (pow_pos hden g)
  rw [gdgSignedInterior_eq_magnitude_of_odd hOdd hden]
  exact hmag

/-- **Target 7.** Rolle witness in every retained even lobe. -/
theorem exists_even_retained_lobe_hasDerivAt_gdgSignedInterior_zero
    {g j : ℕ} (hg : 5 ≤ g) (hEven : Even g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃ c ∈ Set.Ioo
        (gdgLobeLeft g j 0)
        (gdgLobeRight g j 0),
      HasDerivAt (gdgSignedInterior g) 0 c := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hab : gdgLobeLeft g j 0 < gdgLobeRight g j 0 := by
    simp only [gdgLobeRight]
    linarith
  have hcont := continuousOn_gdgSignedInterior_of_before_pole hg
    (gdgLobeLeft_nonneg (g := g) (j := j) (by omega) (le_rfl : (0 : ℝ) ≤ 0))
    ((gdgEven_mem_iff_lobeRight_lt_pole hg hEven).mp hj)
  have hend := gdgSignedInterior_even_endpoint_values hg hEven hj
  obtain ⟨c, hc, hderiv⟩ :=
    exists_deriv_eq_zero hab hcont (by rw [hend.1, hend.2])
  refine ⟨c, hc, ?_⟩
  have hden := gdgEven_retained_denominator_pos hg hEven hj
    (Set.Ioo_subset_Icc_self hc)
  have hdiff := differentiableAt_gdgSignedInterior_of_denominator_ne_zero
    (ne_of_gt hden)
  have hHas := hdiff.hasDerivAt
  rwa [hderiv] at hHas

/-- **Target 8.** Rolle witness in every retained odd lobe. -/
theorem exists_odd_retained_lobe_hasDerivAt_gdgSignedInterior_zero
    {g j : ℕ} (hg : 5 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    ∃ c ∈ Set.Ioo
        (gdgLobeLeft g j ((1 : ℝ) / 2))
        (gdgLobeRight g j ((1 : ℝ) / 2)),
      HasDerivAt (gdgSignedInterior g) 0 c := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hab : gdgLobeLeft g j ((1 : ℝ) / 2) < gdgLobeRight g j ((1 : ℝ) / 2) := by
    simp only [gdgLobeRight]
    linarith
  have hcont := continuousOn_gdgSignedInterior_of_before_pole hg
    (gdgLobeLeft_nonneg (g := g) (j := j) (by omega)
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2))
    ((gdgOdd_mem_iff_lobeRight_lt_pole hg hOdd).mp hj)
  have hend := gdgSignedInterior_odd_endpoint_values hg hOdd hj
  obtain ⟨c, hc, hderiv⟩ :=
    exists_deriv_eq_zero hab hcont (by rw [hend.1, hend.2])
  refine ⟨c, hc, ?_⟩
  have hden := gdgOdd_retained_denominator_pos hg hOdd hj
    (Set.Ioo_subset_Icc_self hc)
  have hdiff := differentiableAt_gdgSignedInterior_of_denominator_ne_zero
    (ne_of_gt hden)
  have hHas := hdiff.hasDerivAt
  rwa [hderiv] at hHas

end GdgSquarefree
