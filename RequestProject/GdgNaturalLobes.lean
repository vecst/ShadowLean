/-
gd_g reduced block cover — NATURAL LOBE geometry and positive-maximum existence.

θ_g = gdgTheta g = 2π/g. The numerator |2 cos(gφ) − 2(−1)^g| vanishes at
the natural zero locations: φ_j = j·θ_g (even g, since (−1)^g = 1 and cos(gφ)=1) and
φ_j = (j+1/2)·θ_g (odd g, since (−1)^g = −1 and cos(gφ)=−1). A natural lobe is the
closed interval between one zero and the next; its midpoint has numerator exactly
4. The zero at π−θ_g is the REMOVED POLE (the unreduced quotient is singular
there even though Lean totalizes division), so a retained compact lobe must sit
strictly before it (right < π − θ_g, strict).

This module proves lobe geometry, denominator positivity, continuity, and
existence of a strictly positive attained maximum on each retained natural lobe.
It does NOT prove the global lobe count, per-lobe critical-point existence or
uniqueness, the free-factor degree, full critical-value separation, or any
monodromy/Galois statement.

Reuses GdgSquarefree.gdgTheta, gdgTheta_pos, gdgInteriorNumeratorAbs,
gdgInteriorDenominator, gdgInteriorMagnitude (from GdgLobeTranslation).

Proof routes (statements verbatim; standard axioms only; NO floating-point):

* gdgLobeLeft_succ / gdgLobeRight_eq_next_left (T1): push_cast `((j+1:ℕ):ℝ)
  = (j:ℝ)+1`, unfold the defs, `ring`; the second uses the first. `hg` is retained
  for the interface but unused — a narrow `set_option linter.unusedVariables false
  in` guard.

* gdgEvenLobe_numerator_values / gdgOddLobe_numerator_values (T2): first prove
  `hgθ : (g:ℝ) * gdgTheta g = 2*π` (g ≥ 1, so (g:ℝ) ≠ 0). Then g·gdgLobeLeft
  = j·(g θ_g) = 2π·j ⇒ cos = 1 (Real.cos_nat_mul_two_pi / cos_int_mul_two_pi);
  g·gdgLobeMid = 2π·j + π ⇒ cos = −1; parity via `Even.neg_one_pow` /
  `Odd.neg_one_pow`. Even: |2·1 − 2·1| = 0 (endpoints), |2·(−1) − 2·1| = 4 (mid).
  Odd: endpoints cos = −1 giving 0, mid cos = 1 giving |2·1 − 2·(−1)| = 4. Get the
  right endpoint from gdgInteriorNumeratorAbs_shift + T1 or directly. Use
  `Real.cos_add_int_mul_two_pi`/`Real.cos_add_two_pi`/`Real.cos_pi`; exact, no
  numerics.

* gdgInteriorDenominator_pos_on_Icc (T3): for φ ∈ [left,right] ⊆ [0, π−θ_g),
  φ < π−θ_g < π, so `Real.strictAntiOn_cos` gives cos φ > cos(π−θ_g) = −cos θ_g
  (`Real.cos_pi_sub`); hence cos φ + cos θ_g > 0, times 2. Keep `right < π−θ_g`
  strict.

* continuousOn_gdgInteriorMagnitude_of_before_pole (T4): numerator
  |2cos(gφ)−2(−1)^g| is continuous; denominator^g is continuous and NONZERO on the
  interval (T3 ⇒ denom > 0 ⇒ denom^g ≠ 0), so `ContinuousOn.div` applies.

* exists_gdgInteriorMagnitude_isGreatest_pos (T5): `isCompact_Icc`, nonempty from
  `hwitness`; T4 continuity ⇒ attained greatest value (`IsCompact.exists_isMaxOn`
  / image-greatest); T3 gives denom(witness) > 0 ⇒ denom^g > 0, with hnum ⇒
  0 < magnitude(witness) ≤ M. No maximizer uniqueness.

* exists_pos_even_lobe_max / exists_pos_odd_lobe_max (T6/T7): apply T5 with the
  MIDPOINT as witness. Midpoint ∈ [left,right] from `gdgTheta_pos` (θ_g/2 ∈
  [0,θ_g]); hleft0 from left = (j+offset)·θ_g ≥ 0; hnum = the exact value 4 from T2.

BOUNDARY GUARDRAILS (do not violate): endpoints have numerator 0, so NEVER assume
0 < numerator on the whole Icc; nonnegativity is insufficient for a positive
maximum — use the midpoint value 4; keep every before-pole inequality STRICT;
g=5 has no retained odd lobe (its strict hbefore is uninhabited) — do not invent
one or weaken the boundary; do not include the zero at π−θ_g in a compact lobe;
do NOT use the false "interior log-derivative globally decreasing" claim; do not
claim maximizer/critical-point uniqueness.

Certification: no sorry/admit/new axiom/unsafe/implemented_by; no silent
weakening; keep unclosable targets out and report their exact name + remaining
goal; run module, Main, audit with --wfail (v4.33.0-rc2); report #print axioms
per public theorem. This module proves positive-maximum EXISTENCE on each
retained natural lobe only — not the global lobe count, critical-point
uniqueness, full separation, or monodromy.
-/
import Mathlib
import RequestProject.GdgLobeTranslation

namespace GdgSquarefree

/-- Left endpoint of the `j`-th natural lobe (offset 0 even, 1/2 odd). -/
noncomputable def gdgLobeLeft (g j : ℕ) (offset : ℝ) : ℝ :=
  ((j : ℝ) + offset) * gdgTheta g

/-- Right endpoint of the `j`-th natural lobe. -/
noncomputable def gdgLobeRight (g j : ℕ) (offset : ℝ) : ℝ :=
  gdgLobeLeft g j offset + gdgTheta g

/-- Midpoint of the `j`-th natural lobe (numerator magnitude exactly 4). -/
noncomputable def gdgLobeMid (g j : ℕ) (offset : ℝ) : ℝ :=
  gdgLobeLeft g j offset + gdgTheta g / 2

set_option linter.unusedVariables false in
/-- **Target 1a.** Left endpoints translate by exactly one period step. -/
theorem gdgLobeLeft_succ {g : ℕ} (hg : 1 ≤ g)
    (j : ℕ) (offset : ℝ) :
    gdgLobeLeft g (j + 1) offset =
      gdgLobeLeft g j offset + gdgTheta g := by
  simp only [gdgLobeLeft, Nat.cast_add, Nat.cast_one]
  ring

set_option linter.unusedVariables false in
/-- **Target 1b.** The right endpoint is the next left endpoint. -/
theorem gdgLobeRight_eq_next_left {g : ℕ} (hg : 1 ≤ g)
    (j : ℕ) (offset : ℝ) :
    gdgLobeRight g j offset = gdgLobeLeft g (j + 1) offset := by
  rw [gdgLobeRight, gdgLobeLeft_succ hg j offset]

/-- The period step satisfies `(g:ℝ) * θ_g = 2π` exactly, for `g ≥ 1`. -/
private theorem gdg_mul_theta {g : ℕ} (hg : 1 ≤ g) :
    (g : ℝ) * gdgTheta g = 2 * Real.pi := by
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  rw [gdgTheta]
  field_simp

/-- Exact numerator magnitude at a point `((j:ℝ) + c) · θ_g`. -/
private theorem gdg_num_at {g : ℕ} (hg : 1 ≤ g) (j : ℕ) (c : ℝ) :
    gdgInteriorNumeratorAbs g (((j : ℝ) + c) * gdgTheta g) =
      |2 * Real.cos (c * (2 * Real.pi)) - 2 * ((-1 : ℝ) ^ g)| := by
  have harg : (g : ℝ) * (((j : ℝ) + c) * gdgTheta g) =
      c * (2 * Real.pi) + ((j : ℤ) : ℝ) * (2 * Real.pi) := by
    calc (g : ℝ) * (((j : ℝ) + c) * gdgTheta g)
        = ((j : ℝ) + c) * ((g : ℝ) * gdgTheta g) := by ring
      _ = ((j : ℝ) + c) * (2 * Real.pi) := by rw [gdg_mul_theta hg]
      _ = c * (2 * Real.pi) + ((j : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
  simp only [gdgInteriorNumeratorAbs, harg, Real.cos_add_int_mul_two_pi]

/-- **Target 2 (even).** Exact numerator values at the even-lobe endpoints (0)
and midpoint (4). -/
theorem gdgEvenLobe_numerator_values {g j : ℕ}
    (hg : 5 ≤ g) (hEven : Even g) :
    gdgInteriorNumeratorAbs g (gdgLobeLeft g j 0) = 0 ∧
    gdgInteriorNumeratorAbs g (gdgLobeRight g j 0) = 0 ∧
    gdgInteriorNumeratorAbs g (gdgLobeMid g j 0) = 4 := by
  have hg1 : 1 ≤ g := by omega
  have hpar : ((-1 : ℝ) ^ g) = 1 := hEven.neg_one_pow
  have hL : gdgLobeLeft g j 0 = (((j : ℝ)) + 0) * gdgTheta g := by
    simp only [gdgLobeLeft]
  have hR : gdgLobeRight g j 0 = (((j : ℝ)) + 1) * gdgTheta g := by
    simp only [gdgLobeRight, gdgLobeLeft]; ring
  have hM : gdgLobeMid g j 0 = (((j : ℝ)) + 1 / 2) * gdgTheta g := by
    simp only [gdgLobeMid, gdgLobeLeft]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hL, gdg_num_at hg1, hpar]
    norm_num
  · rw [hR, gdg_num_at hg1, hpar]
    rw [show (1 : ℝ) * (2 * Real.pi) = 2 * Real.pi by ring, Real.cos_two_pi]
    norm_num
  · rw [hM, gdg_num_at hg1, hpar]
    rw [show (1 / 2 : ℝ) * (2 * Real.pi) = Real.pi by ring, Real.cos_pi]
    norm_num

/-- **Target 2 (odd).** Exact numerator values at the odd-lobe endpoints (0)
and midpoint (4). -/
theorem gdgOddLobe_numerator_values {g j : ℕ}
    (hg : 5 ≤ g) (hOdd : Odd g) :
    gdgInteriorNumeratorAbs g
        (gdgLobeLeft g j ((1 : ℝ) / 2)) = 0 ∧
    gdgInteriorNumeratorAbs g
        (gdgLobeRight g j ((1 : ℝ) / 2)) = 0 ∧
    gdgInteriorNumeratorAbs g
        (gdgLobeMid g j ((1 : ℝ) / 2)) = 4 := by
  have hg1 : 1 ≤ g := by omega
  have hpar : ((-1 : ℝ) ^ g) = -1 := hOdd.neg_one_pow
  have hL : gdgLobeLeft g j ((1 : ℝ) / 2) = (((j : ℝ)) + 1 / 2) * gdgTheta g := by
    simp only [gdgLobeLeft]
  have hR : gdgLobeRight g j ((1 : ℝ) / 2) = (((j : ℝ)) + 3 / 2) * gdgTheta g := by
    simp only [gdgLobeRight, gdgLobeLeft]; ring
  have hM : gdgLobeMid g j ((1 : ℝ) / 2) = (((j : ℝ)) + 1) * gdgTheta g := by
    simp only [gdgLobeMid, gdgLobeLeft]; ring
  have hcos3 : Real.cos ((3 / 2 : ℝ) * (2 * Real.pi)) = -1 := by
    rw [show (3 / 2 : ℝ) * (2 * Real.pi) = Real.pi + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_pi]
  refine ⟨?_, ?_, ?_⟩
  · rw [hL, gdg_num_at hg1, hpar]
    rw [show (1 / 2 : ℝ) * (2 * Real.pi) = Real.pi by ring, Real.cos_pi]
    norm_num
  · rw [hR, gdg_num_at hg1, hpar, hcos3]
    norm_num
  · rw [hM, gdg_num_at hg1, hpar]
    rw [show (1 : ℝ) * (2 * Real.pi) = 2 * Real.pi by ring, Real.cos_two_pi]
    norm_num

/-- **Target 3.** The denominator is positive on any closed interval that ends
strictly before the removed pole. -/
theorem gdgInteriorDenominator_pos_on_Icc {g : ℕ} (hg : 5 ≤ g)
    {left right : ℝ} (hleft0 : 0 ≤ left)
    (hright : right < Real.pi - gdgTheta g) :
    ∀ phi ∈ Set.Icc left right,
      0 < gdgInteriorDenominator g phi := by
  intro phi hphi
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hthlt : gdgTheta g < Real.pi / 2 := gdgTheta_lt_pi_div_two hg
  have hpi := Real.pi_pos
  have h1 : 0 ≤ phi := le_trans hleft0 hphi.1
  have h2 : phi < Real.pi - gdgTheta g := lt_of_le_of_lt hphi.2 hright
  have hmem : phi ∈ Set.Icc 0 Real.pi := ⟨h1, by linarith⟩
  have hmem2 : Real.pi - gdgTheta g ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have hlt : Real.cos (Real.pi - gdgTheta g) < Real.cos phi :=
    Real.strictAntiOn_cos hmem hmem2 h2
  rw [Real.cos_pi_sub] at hlt
  simp only [gdgInteriorDenominator]
  linarith

/-- **Target 4.** The interior magnitude is continuous on a retained closed
interval (denominator nonvanishing there). -/
theorem continuousOn_gdgInteriorMagnitude_of_before_pole
    {g : ℕ} (hg : 5 ≤ g) {left right : ℝ}
    (hleft0 : 0 ≤ left)
    (hright : right < Real.pi - gdgTheta g) :
    ContinuousOn (gdgInteriorMagnitude g) (Set.Icc left right) := by
  have hden := gdgInteriorDenominator_pos_on_Icc hg hleft0 hright
  have hnum : ContinuousOn (fun phi : ℝ => gdgInteriorNumeratorAbs g phi)
      (Set.Icc left right) := by
    simp only [gdgInteriorNumeratorAbs]
    fun_prop
  have hdenc : ContinuousOn
      (fun phi : ℝ => (gdgInteriorDenominator g phi) ^ g) (Set.Icc left right) := by
    simp only [gdgInteriorDenominator]
    fun_prop
  have : ContinuousOn
      (fun phi : ℝ =>
        gdgInteriorNumeratorAbs g phi / (gdgInteriorDenominator g phi) ^ g)
      (Set.Icc left right) :=
    hnum.div hdenc (fun x hx => pow_ne_zero _ (ne_of_gt (hden x hx)))
  exact this

/-- **Target 5.** A retained closed interval carrying a point of positive
numerator has an attained, strictly positive maximum magnitude. -/
theorem exists_gdgInteriorMagnitude_isGreatest_pos
    {g : ℕ} (hg : 5 ≤ g) {left right witness : ℝ}
    (hleft0 : 0 ≤ left)
    (hright : right < Real.pi - gdgTheta g)
    (hwitness : witness ∈ Set.Icc left right)
    (hnum : 0 < gdgInteriorNumeratorAbs g witness) :
    ∃ M,
      IsGreatest
        (gdgInteriorMagnitude g '' Set.Icc left right) M ∧
      0 < M := by
  have hcont := continuousOn_gdgInteriorMagnitude_of_before_pole hg hleft0 hright
  have hne : (Set.Icc left right).Nonempty := ⟨witness, hwitness⟩
  obtain ⟨x, hx, hmax⟩ := (isCompact_Icc (a := left) (b := right)).exists_isMaxOn hne hcont
  refine ⟨gdgInteriorMagnitude g x, ⟨⟨x, hx, rfl⟩, ?_⟩, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hmax hz
  · have hden := gdgInteriorDenominator_pos_on_Icc hg hleft0 hright witness hwitness
    have hpos : 0 < gdgInteriorMagnitude g witness := by
      simp only [gdgInteriorMagnitude]
      exact div_pos hnum (pow_pos hden g)
    exact lt_of_lt_of_le hpos (hmax hwitness)

/-- **Target 6.** Every retained natural EVEN lobe has a strictly positive
attained maximum (midpoint witness, value 4). -/
theorem exists_pos_even_lobe_max {g j : ℕ}
    (hg : 5 ≤ g) (hEven : Even g)
    (hbefore : gdgLobeRight g j 0 <
      Real.pi - gdgTheta g) :
    ∃ M,
      IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc (gdgLobeLeft g j 0) (gdgLobeRight g j 0)) M ∧
      0 < M := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hleft0 : 0 ≤ gdgLobeLeft g j 0 := by
    simp only [gdgLobeLeft]
    nlinarith
  have hmem : gdgLobeMid g j 0 ∈
      Set.Icc (gdgLobeLeft g j 0) (gdgLobeRight g j 0) := by
    simp only [gdgLobeMid, gdgLobeRight]
    constructor <;> linarith
  have hnum : 0 < gdgInteriorNumeratorAbs g (gdgLobeMid g j 0) := by
    rw [(gdgEvenLobe_numerator_values (j := j) hg hEven).2.2]
    norm_num
  exact exists_gdgInteriorMagnitude_isGreatest_pos hg hleft0 hbefore hmem hnum

/-- **Target 7.** Every retained natural ODD lobe has a strictly positive
attained maximum (midpoint witness, value 4). -/
theorem exists_pos_odd_lobe_max {g j : ℕ}
    (hg : 5 ≤ g) (hOdd : Odd g)
    (hbefore : gdgLobeRight g j ((1 : ℝ) / 2) <
      Real.pi - gdgTheta g) :
    ∃ M,
      IsGreatest
        (gdgInteriorMagnitude g ''
          Set.Icc
            (gdgLobeLeft g j ((1 : ℝ) / 2))
            (gdgLobeRight g j ((1 : ℝ) / 2))) M ∧
      0 < M := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hleft0 : 0 ≤ gdgLobeLeft g j ((1 : ℝ) / 2) := by
    simp only [gdgLobeLeft]
    nlinarith
  have hmem : gdgLobeMid g j ((1 : ℝ) / 2) ∈
      Set.Icc (gdgLobeLeft g j ((1 : ℝ) / 2)) (gdgLobeRight g j ((1 : ℝ) / 2)) := by
    simp only [gdgLobeMid, gdgLobeRight]
    constructor <;> linarith
  have hnum : 0 < gdgInteriorNumeratorAbs g (gdgLobeMid g j ((1 : ℝ) / 2)) := by
    rw [(gdgOddLobe_numerator_values (j := j) hg hOdd).2.2]
    norm_num
  exact exists_gdgInteriorMagnitude_isGreatest_pos hg hleft0 hbefore hmem hnum

end GdgSquarefree
