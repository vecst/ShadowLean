/-
gd_g reduced block cover — LOBE TRANSLATION layer.

This module proves TRANSLATION DOMINANCE for the interior magnitude of the
reduced gd_g block cover: shifting a retained lobe by one period step
θ_g = 2π/g strictly increases the magnitude (numerator is exactly periodic, the
positive denominator strictly shrinks), and this transfers to consecutive lobe
maxima. It is analytic/structural only — it introduces NO monodromy, NO Galois
theory, NO polynomial root-counting, and it is NOT yet the full pairwise
critical-value separation theorem.

On the unit circle b = 2 cos φ the reduced cover value is
gdgInteriorMagnitude g φ = |2 cos(gφ) − 2(−1)^g| / (2(cos φ + cos θ_g))^g
(numerator = 𝒟_g(b) − 2(−1)^g with 𝒟_g(2cos φ) = 2 cos(gφ); denominator
= (b + c)^g with c = 2 cos θ_g, θ_g = 2π/g).

Reuses GdgSquarefree.gdgCosCoeff_pos (angle estimate) and the separation lemmas
where relevant. Do not reprove results of GdgCriticalTetranomial,
GdgCriticalCandidateLocation, GdgCriticalValueSeparation.

Proof routes (keep every displayed signature verbatim; standard axioms only):

* gdgTheta_pos / gdgTheta_lt_pi_div_two (T1): 0 < 2π/g (g ≥ 1); and 2π/g < π/2
  for g ≥ 5 (2π/g ≤ 2π/5 = 0.4π < 0.5π) — the same estimate used inside
  gdgCosCoeff_pos; reuse or reprove, keep strict.

* gdgInteriorNumeratorAbs_shift (T2): EXACT. (g:ℝ)·θ_g = (g:ℝ)·(2π/g) = 2π
  (g ≥ 1 so (g:ℝ) ≠ 0), so cos(g(φ+θ_g)) = cos(gφ + 2π) = cos(gφ)
  (Real.cos_add_two_pi / periodicity). The two |·| arguments are literally equal.

* gdgInteriorDenominator_shift_pos_lt (T3): with θ_g > 0 and φ ≥ 0, both φ and
  φ+θ_g lie in [0,π] and φ < φ+θ_g < π−θ_g < π (from hbefore). Strict decrease of
  cos on [0,π] (Real.strictAntiOn_cos) gives cos(φ+θ_g) < cos φ (denominator
  strictly smaller) and cos(φ+θ_g) > cos(π−θ_g) = −cos θ_g (denominator positive,
  using cos(π−θ)=−cos θ, Real.cos_pi_sub). Multiply by 2; keep both strict.

* gdgInteriorMagnitude_shift_lt (T4): numerator equal and positive (T2 + hnum),
  denominators positive with the shifted one strictly smaller (T3), and the
  g-th power (g ≥ 5 ≥ 1) is strictly monotone on positives
  (pow_lt_pow_left), so N/D_big^g < N/D_small^g. Establish positivity BEFORE any
  division/cross-multiplication (div_lt_div_of_pos_left or one_lt_div chain).

* gdgInteriorMagnitude_max_shift_lt (T5): from IsGreatest take a maximizer
  φ* ∈ Icc left right with M = magnitude φ*; then φ*+θ_g ∈ Icc (left+θ_g)
  (right+θ_g); apply T4 (0 ≤ φ* from hleft0 ≤ left ≤ φ*; φ*+θ_g < π−θ_g from
  φ* ≤ right and hright; numerator positive from hnum at φ*); and
  magnitude (φ*+θ_g) ≤ Mnext (IsGreatest upper bound on the shifted image). Chain
  M = magnitude φ* < magnitude (φ*+θ_g) ≤ Mnext. Uniqueness of maximizers is NOT
  used.

* gdgExteriorCriticalRatio_strictAntiOn / _eq_cos_unique (T6, OPTIONAL, only after
  T1–T5): cosh((g−2)t/2)/cosh(gt/2) is strictly decreasing on Ioi 0 for g ≥ 5;
  logarithmic derivative ((g−2)/2)tanh((g−2)t/2) − (g/2)tanh(gt/2) < 0 because
  x ↦ x·tanh(x t) is strictly increasing for x>0, t>0. Corollary: the equation
  gdgExteriorCriticalRatio g t = cos θ_g has at most one t>0 (uniqueness).

IMPORTANT FALSE ROUTE — DO NOT USE. Do NOT claim the interior logarithmic
derivative is globally strictly decreasing on every retained lobe; that is
numerically FALSE. For even g it is L(φ)=cot(gφ/2)+sin φ/(cos φ+cos θ); at g=36,
φ=2.7163265766647773 one gets L≈5.382457928772, L'≈+0.121136166264 (guardrail
only, not proof input). Interior uniqueness must later come from lobe existence
plus a global degree count or a valid refined phase argument — NOT from this
module.

Certification: no sorry/admit/new axiom/unsafe/implemented_by; no silent
weakening of any strict inequality; keep unclosable targets out and report their
exact name + remaining goal; run module, Main, audit with --wfail (v4.33.0-rc2);
report #print axioms per public theorem. This module proves TRANSLATION
DOMINANCE only, not full pairwise critical-value separation and not any
monodromy statement.
-/
import Mathlib
import RequestProject.GdgCriticalCandidateLocation
import RequestProject.GdgCriticalValueSeparation

namespace GdgSquarefree

noncomputable def gdgTheta (g : ℕ) : ℝ :=
  2 * Real.pi / (g : ℝ)

noncomputable def gdgInteriorNumeratorAbs (g : ℕ) (phi : ℝ) : ℝ :=
  abs (2 * Real.cos ((g : ℝ) * phi) - 2 * ((-1 : ℝ) ^ g))

noncomputable def gdgInteriorDenominator (g : ℕ) (phi : ℝ) : ℝ :=
  2 * (Real.cos phi + Real.cos (gdgTheta g))

noncomputable def gdgInteriorMagnitude (g : ℕ) (phi : ℝ) : ℝ :=
  gdgInteriorNumeratorAbs g phi /
    (gdgInteriorDenominator g phi) ^ g

/-- **Target 1a.** The period step is positive. -/
theorem gdgTheta_pos {g : ℕ} (hg : 1 ≤ g) :
    0 < gdgTheta g := by
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  exact div_pos (by positivity) hgpos

/-- **Target 1b.** The period step is below `π/2` for `g ≥ 5`. -/
theorem gdgTheta_lt_pi_div_two {g : ℕ} (hg : 5 ≤ g) :
    gdgTheta g < Real.pi / 2 := by
  have hg5 : (5 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hpi := Real.pi_pos
  rw [gdgTheta, div_lt_div_iff₀ hgpos (by norm_num : (0:ℝ) < 2)]
  nlinarith

/-- **Target 2.** Exact one-period periodicity of the numerator magnitude. -/
theorem gdgInteriorNumeratorAbs_shift {g : ℕ} (hg : 1 ≤ g) (phi : ℝ) :
    gdgInteriorNumeratorAbs g (phi + gdgTheta g) =
      gdgInteriorNumeratorAbs g phi := by
  have hgne : ((g : ℝ)) ≠ 0 := by
    have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
    exact ne_of_gt hgpos
  have harg : (g : ℝ) * (phi + gdgTheta g) = (g : ℝ) * phi + 2 * Real.pi := by
    rw [gdgTheta]; field_simp
  simp only [gdgInteriorNumeratorAbs, harg, Real.cos_add_two_pi]

/-- **Target 3.** The denominator is positive at the shifted point and strictly
smaller than at the original point (shifted point strictly before the pole). -/
theorem gdgInteriorDenominator_shift_pos_lt {g : ℕ} (hg : 5 ≤ g)
    {phi : ℝ} (hphi0 : 0 ≤ phi)
    (hbefore : phi + gdgTheta g < Real.pi - gdgTheta g) :
    0 < gdgInteriorDenominator g (phi + gdgTheta g) ∧
      gdgInteriorDenominator g (phi + gdgTheta g) <
        gdgInteriorDenominator g phi := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hthlt : gdgTheta g < Real.pi / 2 := gdgTheta_lt_pi_div_two hg
  have hpi := Real.pi_pos
  have hmem1 : phi ∈ Set.Icc 0 Real.pi := ⟨hphi0, by linarith⟩
  have hmem2 : phi + gdgTheta g ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have hmem3 : Real.pi - gdgTheta g ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have hlt : Real.cos (phi + gdgTheta g) < Real.cos phi :=
    Real.strictAntiOn_cos hmem1 hmem2 (by linarith)
  have hgt : Real.cos (Real.pi - gdgTheta g) < Real.cos (phi + gdgTheta g) :=
    Real.strictAntiOn_cos hmem2 hmem3 hbefore
  rw [Real.cos_pi_sub] at hgt
  refine ⟨?_, ?_⟩ <;> simp only [gdgInteriorDenominator] <;> linarith

/-- **Target 4.** Strict pointwise lobe dominance: one period step strictly
increases the interior magnitude. -/
theorem gdgInteriorMagnitude_shift_lt {g : ℕ} (hg : 5 ≤ g)
    {phi : ℝ} (hphi0 : 0 ≤ phi)
    (hbefore : phi + gdgTheta g < Real.pi - gdgTheta g)
    (hnum : 0 < gdgInteriorNumeratorAbs g phi) :
    gdgInteriorMagnitude g phi <
      gdgInteriorMagnitude g (phi + gdgTheta g) := by
  obtain ⟨hpos, hlt⟩ := gdgInteriorDenominator_shift_pos_lt hg hphi0 hbefore
  have hnum' : gdgInteriorNumeratorAbs g (phi + gdgTheta g) =
      gdgInteriorNumeratorAbs g phi := gdgInteriorNumeratorAbs_shift (by omega) phi
  have hpowlt : (gdgInteriorDenominator g (phi + gdgTheta g)) ^ g <
      (gdgInteriorDenominator g phi) ^ g :=
    pow_lt_pow_left₀ hlt (le_of_lt hpos) (by omega)
  have hpowpos : 0 < (gdgInteriorDenominator g (phi + gdgTheta g)) ^ g := pow_pos hpos g
  simp only [gdgInteriorMagnitude, hnum']
  exact div_lt_div_of_pos_left hnum hpowpos hpowlt

set_option linter.unusedVariables false in
/-- **Target 5.** Translation dominance transfers to consecutive lobe maxima.

The hypothesis `hle : left ≤ right` is part of the prescribed signature; the
proof does not need it (a maximizer is extracted from the image, which is
already witnessed nonempty by `hmax`), so it is kept only for the interface. -/
theorem gdgInteriorMagnitude_max_shift_lt {g : ℕ} (hg : 5 ≤ g)
    {left right M Mnext : ℝ}
    (hle : left ≤ right) (hleft0 : 0 ≤ left)
    (hright : right + gdgTheta g < Real.pi - gdgTheta g)
    (hnum : ∀ phi, phi ∈ Set.Icc left right →
      0 < gdgInteriorNumeratorAbs g phi)
    (hmax : IsGreatest
      (gdgInteriorMagnitude g '' Set.Icc left right) M)
    (hmaxNext : IsGreatest
      (gdgInteriorMagnitude g ''
        Set.Icc (left + gdgTheta g) (right + gdgTheta g)) Mnext) :
    M < Mnext := by
  obtain ⟨⟨p, hp, hpM⟩, -⟩ := hmax
  have hp0 : 0 ≤ p := le_trans hleft0 hp.1
  have hbefore : p + gdgTheta g < Real.pi - gdgTheta g := by
    have hpr := hp.2; linarith
  have hstep : gdgInteriorMagnitude g p < gdgInteriorMagnitude g (p + gdgTheta g) :=
    gdgInteriorMagnitude_shift_lt hg hp0 hbefore (hnum p hp)
  have hmem : p + gdgTheta g ∈ Set.Icc (left + gdgTheta g) (right + gdgTheta g) :=
    ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hle2 : gdgInteriorMagnitude g (p + gdgTheta g) ≤ Mnext :=
    hmaxNext.2 ⟨p + gdgTheta g, hmem, rfl⟩
  calc M = gdgInteriorMagnitude g p := hpM.symm
    _ < gdgInteriorMagnitude g (p + gdgTheta g) := hstep
    _ ≤ Mnext := hle2

/-- Exterior critical-value ratio (normal form for the g≥5 exterior root). -/
noncomputable def gdgExteriorCriticalRatio (g : ℕ) (t : ℝ) : ℝ :=
  Real.cosh (((g : ℝ) - 2) * t / 2) /
    Real.cosh ((g : ℝ) * t / 2)

/-- Auxiliary cross-multiplication inequality: for `0 ≤ a < b` and `0 < s < t`,
`cosh (a t) · cosh (b s) < cosh (a s) · cosh (b t)`. -/
private theorem cosh_mul_cosh_cross {a b s t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hs : 0 < s) (hst : s < t) :
    Real.cosh (a * t) * Real.cosh (b * s) < Real.cosh (a * s) * Real.cosh (b * t) := by
  have key : ∀ X Y : ℝ,
      2 * (Real.cosh X * Real.cosh Y) = Real.cosh (X + Y) + Real.cosh (X - Y) := by
    intro X Y; rw [Real.cosh_add, Real.cosh_sub]; ring
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have ht : 0 < t := hs.trans hst
  have h1 : Real.cosh (a * t + b * s) < Real.cosh (a * s + b * t) := by
    rw [Real.cosh_lt_cosh, abs_of_nonneg (by positivity : (0:ℝ) ≤ a * t + b * s),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ a * s + b * t)]
    nlinarith
  have hneg : a * s - b * t < 0 := by nlinarith
  have h2 : Real.cosh (a * t - b * s) < Real.cosh (a * s - b * t) := by
    rw [Real.cosh_lt_cosh, abs_of_neg hneg, abs_lt]
    constructor <;> nlinarith
  nlinarith [key (a * t) (b * s), key (a * s) (b * t)]

/-- **Target 6a (optional).** The exterior ratio is strictly decreasing on
`(0, ∞)` for `g ≥ 5`. -/
theorem gdgExteriorCriticalRatio_strictAntiOn {g : ℕ} (hg : 5 ≤ g) :
    StrictAntiOn (gdgExteriorCriticalRatio g) (Set.Ioi 0) := by
  intro s hs t ht hst
  have hs0 : 0 < s := hs
  have hg5 : (5 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  set a : ℝ := ((g : ℝ) - 2) / 2 with ha_def
  set b : ℝ := (g : ℝ) / 2 with hb_def
  have ha : 0 ≤ a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def, hb_def]; linarith
  have hcross := cosh_mul_cosh_cross ha hab hs0 hst
  have e1 : ((g : ℝ) - 2) * t / 2 = a * t := by rw [ha_def]; ring
  have e2 : ((g : ℝ) - 2) * s / 2 = a * s := by rw [ha_def]; ring
  have e3 : (g : ℝ) * t / 2 = b * t := by rw [hb_def]; ring
  have e4 : (g : ℝ) * s / 2 = b * s := by rw [hb_def]; ring
  simp only [gdgExteriorCriticalRatio, e1, e2, e3, e4]
  rw [div_lt_div_iff₀ (Real.cosh_pos _) (Real.cosh_pos _)]
  exact hcross

/-- **Target 6b (optional).** Exterior uniqueness: at most one positive solution
of `gdgExteriorCriticalRatio g t = cos θ_g`. -/
theorem gdgExteriorCriticalRatio_eq_cos_unique {g : ℕ} (hg : 5 ≤ g)
    {t1 t2 : ℝ} (ht1 : 0 < t1) (ht2 : 0 < t2)
    (h1 : gdgExteriorCriticalRatio g t1 = Real.cos (gdgTheta g))
    (h2 : gdgExteriorCriticalRatio g t2 = Real.cos (gdgTheta g)) :
    t1 = t2 :=
  (gdgExteriorCriticalRatio_strictAntiOn hg).injOn ht1 ht2 (h1.trans h2.symm)

end GdgSquarefree
