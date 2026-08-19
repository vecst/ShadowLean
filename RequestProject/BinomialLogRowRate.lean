/-
Executable diagonal logarithm, Phase 2B: the explicit finite-row rate.

Phase 2A bounded the surrogate bias `|logSurrogate g x - log x|`. This file
supplies the OTHER half: an explicit finite-row bound for
`|binomialLog g N x - logSurrogate g x|`, inherited from the existing
slice-ratio explicit-rate theorem `slice_ratio_explicit_rate_rpow` (applied at
`k = g-1` and `k = 1`, same beta, same threshold), plus a compact-interval
theorem CONDITIONAL on a supplied uniform spectral-gap envelope `ρ`.

Scope: this phase does NOT construct `ρ` from interval endpoints and does NOT
choose `N` by a closed formula (those are Phase 2C). It does not claim a
complete joint diagonal schedule.
-/
import RequestProject.BinomialLogDiagonalBias

namespace ResidueSlices

noncomputable def canonicalLogRoot (g : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / g)

noncomputable def logRowGap (g : ℕ) (x : ℝ) : ℝ :=
  spectralGap g (x ^ ((g : ℝ)⁻¹)) (canonicalLogRoot g)

noncomputable def logRowBeta (g N : ℕ) (x : ℝ) : ℝ :=
  ((g : ℝ) - 1) * logRowGap g x ^ N

/-- The canonical `g`-th root of unity used by the diagonal logarithm rows is
primitive. -/
private theorem canonicalLogRoot_isPrimitiveRoot {g : ℕ} (hg : 0 < g) :
    IsPrimitiveRoot (canonicalLogRoot g) g :=
  Complex.isPrimitiveRoot_exp g hg.ne'

theorem logRowGap_mem_unitInterval {g : ℕ} (hg : 2 ≤ g) {x : ℝ} (hx : 0 < x) :
    0 ≤ logRowGap g x ∧ logRowGap g x < 1 := by
  have hg0 : 0 < g := by omega
  have ht : 0 < x ^ ((g : ℝ)⁻¹) := Real.rpow_pos_of_pos hx _
  exact spectralGap_mem_unitInterval hg0 ht (canonicalLogRoot_isPrimitiveRoot hg0)

/-- `logRowBeta` is nonnegative for `g ≥ 1` and `x > 0`. -/
private theorem logRowBeta_nonneg {g : ℕ} (hg : 2 ≤ g) {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ logRowBeta g N x := by
  have h := (logRowGap_mem_unitInterval hg hx).1
  have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast Nat.one_le_of_lt hg
  exact mul_nonneg (by linarith) (pow_nonneg h N)

/-- The purely algebraic transfer step: a bound on two slice ratios yields a
bound on the corresponding Möbius-type expressions, since both denominators are
at least `2`. -/
private theorem row_transfer_bound {G x r1 r2 L1 L2 e1 e2 : ℝ}
    (hx : 0 ≤ x) (hG : 0 ≤ G)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2)
    (h1 : |r1 - L1| ≤ e1) (h2 : |r2 - L2| ≤ e2) :
    |2 * G * (x * r1 - r2) / (x * r1 + 2 + r2) -
        2 * G * (x * L1 - L2) / (x * L1 + 2 + L2)| ≤
      G * (x * e1 + e2 + x * (L1 * e2 + L2 * e1)) := by
  have hd1 := abs_le.mp h1
  have hd2 := abs_le.mp h2
  have hB : (2 : ℝ) ≤ x * r1 + 2 + r2 := by nlinarith
  have hB' : (2 : ℝ) ≤ x * L1 + 2 + L2 := by nlinarith
  have hBpos : (0 : ℝ) < x * r1 + 2 + r2 := by linarith
  have hB'pos : (0 : ℝ) < x * L1 + 2 + L2 := by linarith
  have key : 2 * G * (x * r1 - r2) / (x * r1 + 2 + r2) -
      2 * G * (x * L1 - L2) / (x * L1 + 2 + L2) =
      (4 * G * (x * (r1 - L1) - (r2 - L2) + x * ((r1 - L1) * L2 - (r2 - L2) * L1))) /
        ((x * r1 + 2 + r2) * (x * L1 + 2 + L2)) := by
    field_simp
    ring
  have hE : |x * (r1 - L1) - (r2 - L2) + x * ((r1 - L1) * L2 - (r2 - L2) * L1)| ≤
      x * e1 + e2 + x * (L1 * e2 + L2 * e1) := by
    have ha := mul_nonneg hx (sub_nonneg.mpr hd1.2)
    have hb := mul_nonneg (mul_nonneg hx hL2) (sub_nonneg.mpr hd1.2)
    have hc := mul_nonneg (mul_nonneg hx hL1) (by linarith : (0 : ℝ) ≤ e2 + (r2 - L2))
    have ha' := mul_nonneg hx (by linarith : (0 : ℝ) ≤ (r1 - L1) + e1)
    have hb' := mul_nonneg (mul_nonneg hx hL2) (by linarith : (0 : ℝ) ≤ (r1 - L1) + e1)
    have hc' := mul_nonneg (mul_nonneg hx hL1) (sub_nonneg.mpr hd2.2)
    rw [abs_le]
    constructor <;> nlinarith [hd1.1, hd1.2, hd2.1, hd2.2]
  have hcoef : (0 : ℝ) ≤ x * e1 + e2 + x * (L1 * e2 + L2 * e1) :=
    le_trans (abs_nonneg _) hE
  rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (x * r1 + 2 + r2) * (x * L1 + 2 + L2)),
    div_le_iff₀ (by positivity)]
  have habs : |4 * G * (x * (r1 - L1) - (r2 - L2) + x * ((r1 - L1) * L2 - (r2 - L2) * L1))| ≤
      4 * G * (x * e1 + e2 + x * (L1 * e2 + L2 * e1)) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 4 * G)]
    exact mul_le_mul_of_nonneg_left hE (by linarith)
  have hprod : (4 : ℝ) ≤ (x * r1 + 2 + r2) * (x * L1 + 2 + L2) := by nlinarith
  nlinarith [mul_nonneg hG hcoef]

theorem binomialLog_row_explicit_rate {g : ℕ} (hg : 2 ≤ g)
    {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : logRowBeta g N x ≤ 1 / 2) :
    |binomialLog g N x - logSurrogate g x| ≤
      4 * (g : ℝ) * logRowBeta g N x *
        (x ^ ((g : ℝ)⁻¹) + x ^ (-(g : ℝ)⁻¹) + 2) := by
  have hg0 : 0 < g := by omega
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hω := canonicalLogRoot_isPrimitiveRoot hg0
  have hbeta := logRowBeta_nonneg hg hx N
  -- the two slice-ratio bounds, at `k = g-1` and `k = 1`
  have hN' : ((g : ℝ) - 1) * spectralGap g (x ^ ((g : ℝ))⁻¹) (canonicalLogRoot g) ^ N ≤ 1 / 2 :=
    hN
  have h1 := slice_ratio_explicit_rate_rpow hg0 (show g - 1 < g by omega) hx hω hN'
  have h2 := slice_ratio_explicit_rate_rpow hg0 (show 1 < g by omega) hx hω hN'
  set β := logRowBeta g N x with hβ
  have hβeq : ((g : ℝ) - 1) * spectralGap g (x ^ ((g : ℝ))⁻¹) (canonicalLogRoot g) ^ N = β := rfl
  rw [hβeq] at h1 h2
  have hL2' : x ^ (-((1 : ℕ) : ℝ) / (g : ℝ)) = x ^ (-(g : ℝ)⁻¹) := by
    congr 1
    push_cast
    ring
  rw [hL2'] at h2
  set L1 : ℝ := x ^ (-((g - 1 : ℕ) : ℝ) / (g : ℝ)) with hL1def
  set r1 : ℝ := slice g (g - 1) N x / slice g 0 N x with hr1def
  set r2 : ℝ := slice g 1 N x / slice g 0 N x with hr2def
  -- positivity facts
  have hs0 : 0 < slice g 0 N x := slice_zero_pos g N hx.le
  have hr1nn : 0 ≤ r1 := div_nonneg (slice_nonneg _ _ _ hx.le) hs0.le
  have hr2nn : 0 ≤ r2 := div_nonneg (slice_nonneg _ _ _ hx.le) hs0.le
  have hL1pos : 0 < L1 := Real.rpow_pos_of_pos hx _
  have hL2pos : 0 < x ^ (-(g : ℝ)⁻¹) := Real.rpow_pos_of_pos hx _
  -- limiting identities
  have hxL1 : x * L1 = x ^ ((g : ℝ)⁻¹) := by
    have hexp : (1 : ℝ) + (-((g - 1 : ℕ) : ℝ) / (g : ℝ)) = (g : ℝ)⁻¹ := by
      rw [Nat.cast_sub (by omega : 1 ≤ g)]
      have hgne : (g : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    calc x * L1 = x ^ (1 : ℝ) * x ^ (-((g - 1 : ℕ) : ℝ) / (g : ℝ)) := by
          rw [Real.rpow_one, hL1def]
      _ = x ^ ((1 : ℝ) + (-((g - 1 : ℕ) : ℝ) / (g : ℝ))) := by rw [← Real.rpow_add hx]
      _ = x ^ ((g : ℝ)⁻¹) := by rw [hexp]
  have hYM : x ^ ((g : ℝ)⁻¹) * x ^ (-(g : ℝ)⁻¹) = 1 := by
    rw [← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero]
  -- the two expressions as Möbius forms
  have hbl : binomialLog g N x = 2 * (g : ℝ) * (x * r1 - r2) / (x * r1 + 2 + r2) := by
    unfold binomialLog logNumerator logDenominator
    rw [hr1def, hr2def]
    field_simp
  have hls : logSurrogate g x =
      2 * (g : ℝ) * (x * L1 - x ^ (-(g : ℝ)⁻¹)) / (x * L1 + 2 + x ^ (-(g : ℝ)⁻¹)) := by
    unfold logSurrogate
    rw [hxL1]
    set y := x ^ ((g : ℝ)⁻¹) with hy
    have hypos : 0 < y := Real.rpow_pos_of_pos hx _
    have hyinv : x ^ (-(g : ℝ)⁻¹) = y⁻¹ := by rw [hy, ← Real.rpow_neg hx.le]
    rw [hyinv]
    have h1' : y + 1 ≠ 0 := by positivity
    have h2' : y + 2 + y⁻¹ ≠ 0 := by
      have : 0 < y⁻¹ := inv_pos.mpr hypos
      positivity
    field_simp
    ring
  rw [hbl, hls]
  have hmain := row_transfer_bound (G := (g : ℝ)) (x := x) (r1 := r1) (r2 := r2)
    (L1 := L1) (L2 := x ^ (-(g : ℝ)⁻¹)) (e1 := 4 * β * L1) (e2 := 4 * β * x ^ (-(g : ℝ)⁻¹))
    hx.le (by linarith) hr1nn hr2nn hL1pos.le hL2pos.le h1 h2
  refine hmain.trans_eq ?_
  linear_combination (4 * (g : ℝ) * β * (1 + 2 * x ^ (-(g : ℝ)⁻¹))) * hxL1 +
    (8 * (g : ℝ) * β) * hYM

noncomputable def logRowIntervalFactor (g : ℕ) (a b : ℝ) : ℝ :=
  b ^ ((g : ℝ)⁻¹) + (a ^ ((g : ℝ)⁻¹))⁻¹ + 2

noncomputable def logRowBetaEnvelope (g N : ℕ) (ρ : ℝ) : ℝ :=
  ((g : ℝ) - 1) * ρ ^ N

theorem binomialLog_row_interval_rate_of_gap_bound {g : ℕ} (hg : 2 ≤ g)
    {a b ρ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hgap : ∀ x ∈ Set.Icc a b, logRowGap g x ≤ ρ)
    {N : ℕ} (hN : logRowBetaEnvelope g N ρ ≤ 1 / 2) :
    ∀ x ∈ Set.Icc a b,
      |binomialLog g N x - logSurrogate g x| ≤
        4 * (g : ℝ) * logRowBetaEnvelope g N ρ *
          logRowIntervalFactor g a b := by
  intro x hxmem
  obtain ⟨hax, hxb⟩ := hxmem
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgapx : logRowGap g x ≤ ρ := hgap x ⟨hax, hxb⟩
  -- `hab` and `hρ1` belong to the requested interface: the bound below needs only
  -- membership `x ∈ [a, b]` and `0 ≤ ρ`, while `ρ < 1` is what makes the later
  -- (Phase 2C) row selection possible.
  have _interface : 0 < b ∧ ρ < 1 := ⟨lt_of_lt_of_le ha hab, hρ1⟩
  have hgap0 : 0 ≤ logRowGap g x := (logRowGap_mem_unitInterval hg hx).1
  -- beta comparison
  have hbetale : logRowBeta g N x ≤ logRowBetaEnvelope g N ρ := by
    unfold logRowBeta logRowBetaEnvelope
    have hpow : logRowGap g x ^ N ≤ ρ ^ N := pow_le_pow_left₀ hgap0 hgapx N
    exact mul_le_mul_of_nonneg_left hpow (by linarith)
  have hbeta0 : 0 ≤ logRowBeta g N x := by
    unfold logRowBeta
    exact mul_nonneg (by linarith) (pow_nonneg hgap0 N)
  have hNx : logRowBeta g N x ≤ 1 / 2 := le_trans hbetale hN
  have hpt := binomialLog_row_explicit_rate hg hx hNx
  refine hpt.trans ?_
  -- interval comparison of the factors
  have hginv : (0 : ℝ) ≤ (g : ℝ)⁻¹ := by positivity
  have hxb' : x ^ ((g : ℝ)⁻¹) ≤ b ^ ((g : ℝ)⁻¹) := Real.rpow_le_rpow hx.le hxb hginv
  have hax' : a ^ ((g : ℝ)⁻¹) ≤ x ^ ((g : ℝ)⁻¹) := Real.rpow_le_rpow ha.le hax hginv
  have hapos : 0 < a ^ ((g : ℝ)⁻¹) := Real.rpow_pos_of_pos ha _
  have hxpos : 0 < x ^ ((g : ℝ)⁻¹) := Real.rpow_pos_of_pos hx _
  have hinv : x ^ (-(g : ℝ)⁻¹) ≤ (a ^ ((g : ℝ)⁻¹))⁻¹ := by
    rw [Real.rpow_neg hx.le]
    exact inv_anti₀ hapos hax'
  have hfac : x ^ ((g : ℝ)⁻¹) + x ^ (-(g : ℝ)⁻¹) + 2 ≤ logRowIntervalFactor g a b := by
    unfold logRowIntervalFactor
    linarith
  have hfac0 : 0 ≤ x ^ ((g : ℝ)⁻¹) + x ^ (-(g : ℝ)⁻¹) + 2 := by positivity
  have henv0 : 0 ≤ logRowBetaEnvelope g N ρ :=
    mul_nonneg (by linarith) (pow_nonneg hρ0 N)
  have hstep1 : 4 * (g : ℝ) * logRowBeta g N x * (x ^ ((g : ℝ)⁻¹) + x ^ (-(g : ℝ)⁻¹) + 2) ≤
      4 * (g : ℝ) * logRowBetaEnvelope g N ρ * (x ^ ((g : ℝ)⁻¹) + x ^ (-(g : ℝ)⁻¹) + 2) := by
    have : 4 * (g : ℝ) * logRowBeta g N x ≤ 4 * (g : ℝ) * logRowBetaEnvelope g N ρ := by
      nlinarith
    exact mul_le_mul_of_nonneg_right this hfac0
  have hstep2 : 4 * (g : ℝ) * logRowBetaEnvelope g N ρ *
      (x ^ ((g : ℝ)⁻¹) + x ^ (-(g : ℝ)⁻¹) + 2) ≤
      4 * (g : ℝ) * logRowBetaEnvelope g N ρ * logRowIntervalFactor g a b :=
    mul_le_mul_of_nonneg_left hfac (by nlinarith)
  linarith

noncomputable def logRowQualified
    (g N : ℕ) (a b ρ ε : ℝ) : Prop :=
  logRowBetaEnvelope g N ρ ≤ 1 / 2 ∧
    4 * (g : ℝ) * logRowBetaEnvelope g N ρ *
      logRowIntervalFactor g a b < ε

theorem binomialLog_row_error_lt_of_qualified {g : ℕ} (hg : 2 ≤ g)
    {a b ρ ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hgap : ∀ x ∈ Set.Icc a b, logRowGap g x ≤ ρ)
    {N : ℕ} (hN : logRowQualified g N a b ρ ε) :
    ∀ x ∈ Set.Icc a b,
      |binomialLog g N x - logSurrogate g x| < ε := by
  intro x hxmem
  exact lt_of_le_of_lt
    (binomialLog_row_interval_rate_of_gap_bound hg ha hab hρ0 hρ1 hgap hN.1 x hxmem) hN.2

end ResidueSlices
