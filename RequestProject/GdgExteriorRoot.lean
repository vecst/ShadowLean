/-
gd_g completion roadmap, Phase 5 — the EXTERIOR ROOT.

Phase 4F (`RequestProject.GdgBlockRootBridge`) transported every retained
interior lobe witness to a root of the descended block polynomial `B_g` lying
in `(-a_g, 2)`.  This module produces the remaining root, which lies strictly
below `-2`, from the exterior analytic equation

  cosh ((g - 2) t / 2) / cosh (g t / 2) = cos (2 π / g),   t > 0.

In the reciprocal coordinate the exterior parameter is `u = -exp t`, whose
block coordinate is `b = u + u⁻¹ = -2 cosh t < -2`.  The three exact identities
that drive the module are, writing `θ = gdgTheta g` and `r = exp t`,

  criticalTetranomial g (2 cos θ) ((-1)^g) (-r)
      = 2 (cos θ (1 + r^g) - (r + r^(g-1))),
  coverQuadratic (2 cos θ) (-r) = 2 r (cosh t - cos θ) > 0,
  gdgPulledCover g (-r)
      = 2 (cosh (g t) - 1) / (2 (cosh t - cos θ))^g.

It proves existence and uniqueness of the exterior critical parameter, its
identification with the unique block root strictly below `-2`, and strict
positivity of the exact pulled-cover value there.  It does NOT claim degree
exhaustion, uniqueness of interior roots, that all roots are real,
squarefreeness of the descended block polynomial, critical-value separation,
monodromy, or any Galois-theoretic statement.
-/
import RequestProject.GdgBlockRootBridge

namespace GdgSquarefree

open Polynomial

/-! ### Elementary facts about `θ_g = 2π/g` -/

/-- The cosine coefficient is `2 cos θ_g` by definition. -/
private theorem gdgCosCoeff_eq_two_mul_cos (g : ℕ) :
    gdgCosCoeff g = 2 * Real.cos (gdgTheta g) := rfl

/-- For `g ≥ 5` the cosine of the period step is strictly positive. -/
private theorem cos_gdgTheta_pos {g : ℕ} (hg : 5 ≤ g) :
    0 < Real.cos (gdgTheta g) := by
  have h := gdgCosCoeff_pos hg
  rw [gdgCosCoeff_eq_two_mul_cos] at h
  linarith

/-- For `g ≥ 5` the cosine of the period step is strictly below `1`. -/
private theorem cos_gdgTheta_lt_one {g : ℕ} (hg : 5 ≤ g) :
    Real.cos (gdgTheta g) < 1 := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hthlt : gdgTheta g < Real.pi / 2 := gdgTheta_lt_pi_div_two hg
  have hpi := Real.pi_pos
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ))
    (by linarith : gdgTheta g ≤ Real.pi) hth
  rwa [Real.cos_zero] at this

/-! ### Exponential normal forms of the exterior ratio -/

private theorem exp_half_pow (t : ℝ) (n : ℕ) :
    Real.exp ((n : ℝ) * t / 2) = Real.exp (t / 2) ^ n := by
  rw [show (n : ℝ) * t / 2 = (n : ℝ) * (t / 2) by ring, Real.exp_nat_mul]

/-- Exact algebraic normal form of the exterior ratio in `r = exp t`. -/
private theorem gdgExteriorCriticalRatio_pow_form {g : ℕ} (hg : 5 ≤ g) (t : ℝ) :
    gdgExteriorCriticalRatio g t =
      (Real.exp t + Real.exp t ^ (g - 1)) / (1 + Real.exp t ^ g) := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 5 := ⟨g - 5, by omega⟩
  set s := Real.exp (t / 2) with hs
  have hspos : 0 < s := Real.exp_pos _
  have hne : s ≠ 0 := ne_of_gt hspos
  have hs2 : Real.exp t = s ^ 2 := by
    rw [hs, sq, ← Real.exp_add]; congr 1; ring
  have e1 : Real.exp ((((k + 5 : ℕ) : ℝ) - 2) * t / 2) = s ^ (k + 3) := by
    rw [← exp_half_pow t (k + 3)]; congr 1; push_cast; ring
  have e2 : Real.exp (((k + 5 : ℕ) : ℝ) * t / 2) = s ^ (k + 5) :=
    exp_half_pow t (k + 5)
  have h1 : Real.cosh ((((k + 5 : ℕ) : ℝ) - 2) * t / 2)
      = (s ^ (k + 3) + (s ^ (k + 3))⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, e1]
  have h2 : Real.cosh (((k + 5 : ℕ) : ℝ) * t / 2)
      = (s ^ (k + 5) + (s ^ (k + 5))⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, e2]
  have hd1 : (s ^ (k + 5) + (s ^ (k + 5))⁻¹) / 2 ≠ 0 := by positivity
  have hd2 : (1 : ℝ) + (s ^ 2) ^ (k + 5) ≠ 0 := by positivity
  simp only [gdgExteriorCriticalRatio, h1, h2, hs2, show k + 5 - 1 = k + 4 from rfl]
  rw [div_eq_div_iff hd1 hd2]
  field_simp
  ring

/-- Exact algebraic normal form of the exterior ratio in `q = exp (-t)`. -/
private theorem gdgExteriorCriticalRatio_expneg_form {g : ℕ} (hg : 5 ≤ g) (t : ℝ) :
    gdgExteriorCriticalRatio g t =
      (Real.exp (-t) ^ (g - 1) + Real.exp (-t)) / (1 + Real.exp (-t) ^ g) := by
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos _
  have hg1 : Real.exp t ^ g = Real.exp t * Real.exp t ^ (g - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [gdgExteriorCriticalRatio_pow_form hg t, Real.exp_neg, inv_pow, inv_pow, hg1,
    div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

/-! ### Target 1: continuity -/

/-- **Target 1.** The exterior ratio is continuous on all of `ℝ`; the
denominator `cosh (g t / 2)` never vanishes. -/
theorem gdgExteriorCriticalRatio_continuous (g : ℕ) :
    Continuous (gdgExteriorCriticalRatio g) := by
  unfold gdgExteriorCriticalRatio
  exact Continuous.div (by fun_prop) (by fun_prop) fun t => (Real.cosh_pos _).ne'

/-! ### Target 2: value at the origin -/

/-- **Target 2.** The exterior ratio equals `1` at `t = 0`, for every natural
`g` (including the natural-subtraction boundaries). -/
theorem gdgExteriorCriticalRatio_zero (g : ℕ) :
    gdgExteriorCriticalRatio g 0 = 1 := by
  simp [gdgExteriorCriticalRatio]

/-! ### Target 3: decay at infinity -/

/-- **Target 3.** For `g ≥ 5` the exterior ratio tends to `0` at `+∞`. -/
theorem tendsto_gdgExteriorCriticalRatio_atTop
    {g : ℕ} (hg : 5 ≤ g) :
    Filter.Tendsto (gdgExteriorCriticalRatio g)
      Filter.atTop (nhds 0) := by
  have hq : Filter.Tendsto (fun t : ℝ => Real.exp (-t)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hcont : ContinuousAt (fun q : ℝ => (q ^ (g - 1) + q) / (1 + q ^ g)) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    rw [zero_pow (by omega : g ≠ 0)]
    norm_num
  have hval : ((0 : ℝ) ^ (g - 1) + 0) / (1 + (0 : ℝ) ^ g) = 0 := by
    rw [zero_pow (by omega : g - 1 ≠ 0), zero_pow (by omega : g ≠ 0)]
    norm_num
  have hcomp := hcont.tendsto.comp hq
  rw [hval] at hcomp
  refine hcomp.congr fun t => ?_
  simp only [Function.comp_apply]
  exact (gdgExteriorCriticalRatio_expneg_form hg t).symm

/-! ### Targets 4–5: existence and uniqueness of the exterior parameter -/

/-- **Target 4.** For `g ≥ 5` there is a strictly positive solution of the
exterior ratio equation. -/
theorem exists_gdgExteriorCriticalRatio_eq_cos
    {g : ℕ} (hg : 5 ≤ g) :
    ∃ t : ℝ, 0 < t ∧
      gdgExteriorCriticalRatio g t = Real.cos (gdgTheta g) := by
  have hc0 : 0 < Real.cos (gdgTheta g) := cos_gdgTheta_pos hg
  have hc1 : Real.cos (gdgTheta g) < 1 := cos_gdgTheta_lt_one hg
  have htend := tendsto_gdgExteriorCriticalRatio_atTop hg
  have hev : ∀ᶠ t : ℝ in Filter.atTop,
      gdgExteriorCriticalRatio g t < Real.cos (gdgTheta g) :=
    htend.eventually (gt_mem_nhds hc0)
  obtain ⟨T, hT0, hTlt⟩ := ((Filter.eventually_gt_atTop (0 : ℝ)).and hev).exists
  have hcont := (gdgExteriorCriticalRatio_continuous g).continuousOn
    (s := Set.Icc 0 T)
  have hsub := intermediate_value_Icc' (le_of_lt hT0) hcont
  have hmem : Real.cos (gdgTheta g) ∈
      Set.Icc (gdgExteriorCriticalRatio g T) (gdgExteriorCriticalRatio g 0) := by
    rw [gdgExteriorCriticalRatio_zero]
    exact ⟨le_of_lt hTlt, le_of_lt hc1⟩
  obtain ⟨t, ht, hteq⟩ := hsub hmem
  refine ⟨t, ?_, hteq⟩
  rcases lt_or_eq_of_le ht.1 with h | h
  · exact h
  · exfalso
    rw [← h, gdgExteriorCriticalRatio_zero] at hteq
    linarith

/-- **Target 5.** For `g ≥ 5` the positive solution of the exterior ratio
equation is unique. -/
theorem existsUnique_gdgExteriorCriticalRatio_eq_cos
    {g : ℕ} (hg : 5 ≤ g) :
    ∃! t : ℝ, 0 < t ∧
      gdgExteriorCriticalRatio g t = Real.cos (gdgTheta g) := by
  obtain ⟨t, ht0, hteq⟩ := exists_gdgExteriorCriticalRatio_eq_cos hg
  refine ⟨t, ⟨ht0, hteq⟩, ?_⟩
  rintro s ⟨hs0, hseq⟩
  exact gdgExteriorCriticalRatio_eq_cos_unique hg hs0 ht0 hseq hteq

/-! ### The exterior algebraic coordinates -/

/-- The exterior reciprocal coordinate `u = -exp t`. -/
noncomputable def gdgExteriorUnit (t : ℝ) : ℂ :=
  -(Real.exp t : ℂ)

/-- The exterior block coordinate `b = u + u⁻¹ = -2 cosh t`. -/
noncomputable def gdgExteriorBlockCoord (t : ℝ) : ℝ :=
  -2 * Real.cosh t

/-- The exact real value of the pulled cover at the exterior parameter. -/
noncomputable def gdgExteriorCoverValue (g : ℕ) (t : ℝ) : ℝ :=
  2 * (Real.cosh ((g : ℝ) * t) - 1) /
    (2 * (Real.cosh t - Real.cos (gdgTheta g))) ^ g

/-! ### Targets 6–9: elementary properties of the exterior coordinates -/

/-- **Target 6.** The exterior reciprocal coordinate is nonzero. -/
theorem gdgExteriorUnit_ne_zero (t : ℝ) :
    gdgExteriorUnit t ≠ 0 := by
  simp only [gdgExteriorUnit, ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]
  exact (Real.exp_pos t).ne'

/-- **Target 7.** The exterior reciprocal coordinate is never the reciprocal
fixed point `u = 1`. -/
theorem gdgExteriorUnit_ne_one (t : ℝ) :
    gdgExteriorUnit t ≠ 1 := by
  intro h
  have hre : -(Real.exp t) = (1 : ℝ) := by
    have h2 := congrArg Complex.re h
    simp only [gdgExteriorUnit, Complex.neg_re, Complex.ofReal_re, Complex.one_re] at h2
    exact h2
  have := Real.exp_pos t
  linarith

/-- **Target 8.** The reciprocal sum of the exterior unit is the exterior block
coordinate `-2 cosh t`. -/
theorem gdgExteriorUnit_add_inv (t : ℝ) :
    gdgExteriorUnit t + (gdgExteriorUnit t)⁻¹ =
      (gdgExteriorBlockCoord t : ℂ) := by
  have hinv : (-(Real.exp t : ℂ))⁻¹ = -((Real.exp (-t) : ℝ) : ℂ) := by
    rw [inv_neg, Real.exp_neg, Complex.ofReal_inv]
  simp only [gdgExteriorUnit, gdgExteriorBlockCoord, hinv, Real.cosh_eq,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  ring

/-- **Target 9.** For `t > 0` the exterior block coordinate is strictly below
`-2`. -/
theorem gdgExteriorBlockCoord_lt_neg_two
    {t : ℝ} (ht : 0 < t) :
    gdgExteriorBlockCoord t < -2 := by
  have h : 1 < Real.cosh t := Real.one_lt_cosh.mpr (ne_of_gt ht)
  simp only [gdgExteriorBlockCoord]
  linarith

/-! ### The three exact exterior identities -/

private theorem neg_one_pow_sq (g : ℕ) : ((-1 : ℂ) ^ g) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

private theorem neg_one_pow_mul_pred {g : ℕ} (hg : 1 ≤ g) :
    ((-1 : ℂ) ^ g) * ((-1 : ℂ) ^ (g - 1)) = -1 := by
  rw [← pow_add, Odd.neg_one_pow ⟨g - 1, by omega⟩]

/-- Exact evaluation of the specialized critical tetranomial at `u = -exp t`. -/
private theorem criticalTetranomial_gdgExteriorUnit_eq
    {g : ℕ} (hg : 5 ≤ g) (t : ℝ) :
    criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g) (gdgExteriorUnit t)
      = ((2 * (Real.cos (gdgTheta g) * (1 + Real.exp t ^ g)
          - (Real.exp t + Real.exp t ^ (g - 1))) : ℝ) : ℂ) := by
  have hA := neg_one_pow_sq g
  have hB := neg_one_pow_mul_pred (g := g) (by omega)
  simp only [criticalTetranomial, gdgExteriorUnit, gdgCosCoeff_eq_two_mul_cos,
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_pow,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  linear_combination (2 * (Real.exp t : ℂ) ^ (g - 1)) * hB
    + (2 * (Real.cos (gdgTheta g) : ℂ) * (Real.exp t : ℂ) ^ g) * hA

/-- Exact evaluation of the channel quadratic at `u = -exp t`. -/
private theorem coverQuadratic_gdgExteriorUnit_eq (g : ℕ) (t : ℝ) :
    coverQuadratic (gdgCosCoeff g : ℂ) (gdgExteriorUnit t)
      = ((2 * Real.exp t * (Real.cosh t - Real.cos (gdgTheta g)) : ℝ) : ℂ) := by
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]; simp
  have hexpC : (Real.exp t : ℂ) * (Real.exp (-t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hexp, Complex.ofReal_one]
  simp only [coverQuadratic, gdgExteriorUnit, gdgCosCoeff_eq_two_mul_cos, Real.cosh_eq,
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  linear_combination -hexpC

/-- Exact evaluation of the cover numerator at `u = -exp t`. -/
private theorem coverNumerator_gdgExteriorUnit_eq (g : ℕ) (t : ℝ) :
    coverNumerator g ((-1 : ℂ) ^ g) (gdgExteriorUnit t)
      = ((1 - Real.exp t ^ g : ℝ) : ℂ) := by
  have hA := neg_one_pow_sq g
  simp only [coverNumerator, gdgExteriorUnit, Complex.ofReal_sub, Complex.ofReal_pow,
    Complex.ofReal_one]
  linear_combination (-(Real.exp t : ℂ) ^ g) * hA

/-- Strict positivity of the real channel quadratic value at `u = -exp t`. -/
private theorem coverQuadratic_gdgExteriorUnit_real_pos
    {g : ℕ} (hg : 5 ≤ g) (t : ℝ) :
    0 < 2 * Real.exp t * (Real.cosh t - Real.cos (gdgTheta g)) := by
  have h1 : (1 : ℝ) ≤ Real.cosh t := Real.one_le_cosh t
  have h2 : Real.cos (gdgTheta g) < 1 := cos_gdgTheta_lt_one hg
  have h3 : 0 < Real.exp t := Real.exp_pos t
  have h4 : 0 < Real.cosh t - Real.cos (gdgTheta g) := by linarith
  positivity

/-! ### Target 10: the tetranomial equation is the ratio equation -/

/-- **Target 10.** At the exterior parameter the specialized critical
tetranomial vanishes exactly when the exterior ratio equation holds. -/
theorem criticalTetranomial_gdgExteriorUnit_eq_zero_iff
    {g : ℕ} (hg : 5 ≤ g) (t : ℝ) :
    criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g)
        (gdgExteriorUnit t) = 0 ↔
      gdgExteriorCriticalRatio g t = Real.cos (gdgTheta g) := by
  have hden : (0 : ℝ) < 1 + Real.exp t ^ g := by positivity
  rw [criticalTetranomial_gdgExteriorUnit_eq hg t, Complex.ofReal_eq_zero,
    gdgExteriorCriticalRatio_pow_form hg t, div_eq_iff (ne_of_gt hden)]
  constructor <;> intro h <;> linarith

/-! ### Target 11: the channel quadratic never vanishes on the exterior ray -/

/-- **Target 11.** The channel quadratic is nonzero at every exterior
parameter, including `t = 0`. -/
theorem coverQuadratic_gdgExteriorUnit_ne_zero
    {g : ℕ} (hg : 5 ≤ g) (t : ℝ) :
    coverQuadratic (gdgCosCoeff g : ℂ) (gdgExteriorUnit t) ≠ 0 := by
  rw [coverQuadratic_gdgExteriorUnit_eq g t, ne_eq, Complex.ofReal_eq_zero]
  exact (coverQuadratic_gdgExteriorUnit_real_pos hg t).ne'

/-! ### Target 12: the parity-correct residual at the exterior parameter -/

/-- **Target 12.** At the exterior parameter the parity-correct reciprocal
residual vanishes exactly when the specialized critical tetranomial does. For
odd `g` the fixed factor `X - 1` is cancelled legitimately, because
`u = -exp t ≠ 1`. -/
theorem gdgReciprocalResidualPolynomial_exterior_eq_zero_iff
    {g : ℕ} (hg : 5 ≤ g) (t : ℝ) :
    (gdgReciprocalResidualPolynomial g).eval (gdgExteriorUnit t) = 0 ↔
      criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g)
        (gdgExteriorUnit t) = 0 := by
  have hQ : (gdgQuadraticPolynomial g).eval (gdgExteriorUnit t) ≠ 0 := by
    rw [gdgQuadraticPolynomial_eval]
    exact coverQuadratic_gdgExteriorUnit_ne_zero hg t
  have hchan : (gdgChannelQuotientPolynomial g).eval (gdgExteriorUnit t) = 0 ↔
      criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g)
        (gdgExteriorUnit t) = 0 := by
    rw [gdgChannelQuotient_eval_eq_zero_iff hg hQ, gdgCriticalPolynomial_eval]
  rcases Nat.even_or_odd g with hEven | hOdd
  · rw [gdgReciprocalResidualPolynomial, if_neg (Nat.not_odd_iff_even.mpr hEven)]
    exact hchan
  · rw [gdgReciprocalResidualPolynomial, if_pos hOdd, ← hchan]
    have hfac := congrArg (fun p : Polynomial ℂ => p.eval (gdgExteriorUnit t))
      (gdgXSubOne_mul_oddResidual hg hOdd)
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hfac
    rw [← hfac]
    constructor
    · intro h
      rw [h, mul_zero]
    · intro h
      exact (mul_eq_zero.mp h).resolve_left
        (sub_ne_zero.mpr (gdgExteriorUnit_ne_one t))

/-! ### Target 13: the block polynomial at the exterior block coordinate -/

/-- **Target 13.** The descended block polynomial vanishes at the exterior
block coordinate exactly when the exterior ratio equation holds. -/
theorem gdgBlockCriticalPolynomial_exterior_eq_zero_iff
    {g : ℕ} (hg : 5 ≤ g) (t : ℝ) :
    (gdgBlockCriticalPolynomial g).eval
        (gdgExteriorBlockCoord t : ℂ) = 0 ↔
      gdgExteriorCriticalRatio g t = Real.cos (gdgTheta g) := by
  rw [← gdgExteriorUnit_add_inv t,
    gdgBlockCriticalPolynomial_eval_eq_zero_iff hg (gdgExteriorUnit_ne_zero t),
    gdgReciprocalResidualPolynomial_exterior_eq_zero_iff hg t,
    criticalTetranomial_gdgExteriorUnit_eq_zero_iff hg t]

/-! ### Targets 14–15: the unique exterior block root -/

/-- **Target 14.** There is exactly one positive exterior parameter whose block
coordinate is a root of the block polynomial. -/
theorem existsUnique_exterior_parametrized_blockRoot
    {g : ℕ} (hg : 5 ≤ g) :
    ∃! t : ℝ, 0 < t ∧
      (gdgBlockCriticalPolynomial g).eval
        (gdgExteriorBlockCoord t : ℂ) = 0 := by
  simp only [gdgBlockCriticalPolynomial_exterior_eq_zero_iff hg]
  exact existsUnique_gdgExteriorCriticalRatio_eq_cos hg

/-- **Target 15.** The block polynomial has exactly one real root strictly
below `-2`. No root count, degree exhaustion or squarefreeness is used. -/
theorem existsUnique_exterior_blockRoot
    {g : ℕ} (hg : 5 ≤ g) :
    ∃! b : ℝ, b < -2 ∧
      (gdgBlockCriticalPolynomial g).eval (b : ℂ) = 0 := by
  obtain ⟨t₀, ⟨ht₀pos, ht₀eval⟩, ht₀uniq⟩ :=
    existsUnique_exterior_parametrized_blockRoot hg
  refine ⟨gdgExteriorBlockCoord t₀,
    ⟨gdgExteriorBlockCoord_lt_neg_two ht₀pos, ht₀eval⟩, ?_⟩
  rintro b ⟨hb2, hbeval⟩
  have hb1 : (1 : ℝ) < -b / 2 := by linarith
  set t : ℝ := Real.arcosh (-b / 2) with ht_def
  have hcosh : Real.cosh t = -b / 2 := Real.cosh_arcosh (le_of_lt hb1)
  have htpos : 0 < t := Real.arcosh_pos hb1
  have hcoord : gdgExteriorBlockCoord t = b := by
    simp only [gdgExteriorBlockCoord, hcosh]
    ring
  have heval : (gdgBlockCriticalPolynomial g).eval
      (gdgExteriorBlockCoord t : ℂ) = 0 := by
    rw [hcoord]; exact hbeval
  have : t = t₀ := ht₀uniq t ⟨htpos, heval⟩
  rw [← hcoord, this]

/-! ### Targets 16–17: the exact pulled-cover value -/

set_option linter.unusedVariables false in
/-- **Target 16.** The pulled cover at the exterior unit is the exact real
value `gdgExteriorCoverValue`. The hypothesis `hg : 5 ≤ g` is part of the
prescribed interface; the identity itself holds for every natural `g`, so the
proof does not use it. -/
theorem gdgPulledCover_gdgExteriorUnit
    {g : ℕ} (hg : 5 ≤ g) (t : ℝ) :
    gdgPulledCover g (gdgExteriorUnit t) =
      (gdgExteriorCoverValue g t : ℂ) := by
  have hrpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hrg : (0 : ℝ) < Real.exp t ^ g := by positivity
  have hexpg : Real.exp ((g : ℝ) * t) = Real.exp t ^ g := Real.exp_nat_mul t g
  have hcoshg : Real.cosh ((g : ℝ) * t)
      = (Real.exp t ^ g + (Real.exp t ^ g)⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, hexpg]
  have hnum : (1 - Real.exp t ^ g) ^ 2
      = Real.exp t ^ g * (2 * (Real.cosh ((g : ℝ) * t) - 1)) := by
    rw [hcoshg]
    field_simp
    ring
  have hquad : (2 * Real.exp t * (Real.cosh t - Real.cos (gdgTheta g))) ^ g
      = Real.exp t ^ g * (2 * (Real.cosh t - Real.cos (gdgTheta g))) ^ g := by
    rw [← mul_pow]
    ring_nf
  have hreal : (1 - Real.exp t ^ g) ^ 2
      / (2 * Real.exp t * (Real.cosh t - Real.cos (gdgTheta g))) ^ g
      = gdgExteriorCoverValue g t := by
    rw [hnum, hquad, gdgExteriorCoverValue,
      mul_div_mul_left _ _ (ne_of_gt hrg)]
  rw [gdgPulledCover, coverNumerator_gdgExteriorUnit_eq g t,
    coverQuadratic_gdgExteriorUnit_eq g t, ← Complex.ofReal_pow,
    ← Complex.ofReal_pow, ← Complex.ofReal_div, hreal]

/-- **Target 17.** The exact pulled-cover value at a positive exterior
parameter is strictly positive. -/
theorem gdgExteriorCoverValue_pos
    {g : ℕ} (hg : 5 ≤ g) {t : ℝ} (ht : 0 < t) :
    0 < gdgExteriorCoverValue g t := by
  have hg0 : (0 : ℝ) < (g : ℝ) := by
    have : (5 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    linarith
  have hgt : (g : ℝ) * t ≠ 0 := by positivity
  have hcosh : 1 < Real.cosh ((g : ℝ) * t) := Real.one_lt_cosh.mpr hgt
  have h1 : (1 : ℝ) ≤ Real.cosh t := Real.one_le_cosh t
  have h2 : Real.cos (gdgTheta g) < 1 := cos_gdgTheta_lt_one hg
  have hD : 0 < 2 * (Real.cosh t - Real.cos (gdgTheta g)) := by linarith
  have hDg : 0 < (2 * (Real.cosh t - Real.cos (gdgTheta g))) ^ g := pow_pos hD g
  have hN : 0 < 2 * (Real.cosh ((g : ℝ) * t) - 1) := by linarith
  exact div_pos hN hDg

end GdgSquarefree
