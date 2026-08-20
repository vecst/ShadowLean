/-
Diagonal logarithm, Phase 2C2: the explicit row selector and final certified
evaluator.

Phases 2A/2B/2C1 provide: an explicit surrogate-bias modulus (choose g); an
explicit finite-row error bound conditional on a row threshold; and an explicit
interval spectral-gap envelope rho with 0 < rho < 1. This file solves the row
threshold by an explicit logarithm/ceiling formula and combines a half-budget
row error with a half-budget surrogate bias into a certified compact-interval
evaluator: from a,b,epsilon it defines concrete g and N and proves uniform
absolute error < epsilon on [a,b].

These definitions are noncomputable (real logs, real powers, Nat.ceil) — they
are explicit mathematical selectors, not extracted machine code.
-/
import RequestProject.BinomialLogGapEnvelope

namespace ResidueSlices

noncomputable def logRowPowerTarget (g : ℕ) (a b ε : ℝ) : ℝ :=
  min (1 / (2 * ((g : ℝ) - 1)))
    (ε / (8 * (g : ℝ) * ((g : ℝ) - 1) * logRowIntervalFactor g a b))

theorem logRowPowerTarget_pos {g : ℕ} (hg : 2 ≤ g)
    {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) :
    0 < logRowPowerTarget g a b ε := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : 0 < (g : ℝ) - 1 := by linarith
  have hF : 0 < logRowIntervalFactor g a b := by
    have h1 : 0 < b ^ ((g : ℝ)⁻¹) := Real.rpow_pos_of_pos hb _
    have h2 : 0 < a ^ ((g : ℝ)⁻¹) := Real.rpow_pos_of_pos ha _
    have h3 : 0 < (a ^ ((g : ℝ)⁻¹))⁻¹ := inv_pos.mpr h2
    unfold logRowIntervalFactor
    linarith
  refine lt_min (div_pos one_pos (by linarith)) (div_pos hε ?_)
  have h8 : 0 < 8 * (g : ℝ) := by linarith
  exact mul_pos (mul_pos h8 hg1) hF

theorem logRowPowerTarget_lt_one {g : ℕ} (hg : 2 ≤ g)
    {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) :
    logRowPowerTarget g a b ε < 1 := by
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hpos : (0 : ℝ) < 2 := by norm_num
  have hle : (2 : ℝ) ≤ 2 * ((g : ℝ) - 1) := by linarith
  have hhalf : 1 / (2 * ((g : ℝ) - 1)) ≤ 1 / 2 := one_div_le_one_div_of_le hpos hle
  have hmin : logRowPowerTarget g a b ε ≤ 1 / (2 * ((g : ℝ) - 1)) := min_le_left _ _
  -- `ha`, `hab`, `hε` are part of the requested interface; the bound needs only `g ≥ 2`.
  have _interface : 0 < a ∧ a ≤ b ∧ 0 < ε := ⟨ha, hab, hε⟩
  linarith

noncomputable def logRowModulus (g : ℕ) (a b ε : ℝ) : ℕ :=
  max 1 (Nat.ceil
    (Real.log (logRowPowerTarget g a b ε) /
      Real.log (logRowGapEnvelope g a b)))

theorem one_le_logRowModulus (g : ℕ) (a b ε : ℝ) :
    1 ≤ logRowModulus g a b ε :=
  le_max_left _ _

theorem logRowGapEnvelope_pow_logRowModulus_le_target
    {g : ℕ} (hg : 2 ≤ g) {a b ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) :
    logRowGapEnvelope g a b ^ logRowModulus g a b ε ≤
      logRowPowerTarget g a b ε := by
  set q : ℝ := logRowPowerTarget g a b ε with hq
  set r : ℝ := logRowGapEnvelope g a b with hr
  have hq0 : 0 < q := logRowPowerTarget_pos hg ha hab hε
  have hq1 : q < 1 := logRowPowerTarget_lt_one hg ha hab hε
  have hr0 : 0 < r := logRowGapEnvelope_pos g a b
  have hr1 : r < 1 := logRowGapEnvelope_lt_one hg ha hab
  have hlq : Real.log q < 0 := Real.log_neg hq0 hq1
  have hlr : Real.log r < 0 := Real.log_neg hr0 hr1
  set N : ℕ := logRowModulus g a b ε with hN
  have hNdef : N = max 1 (Nat.ceil (Real.log q / Real.log r)) := rfl
  have hratio : Real.log q / Real.log r ≤ (N : ℝ) := by
    have h1 : Real.log q / Real.log r ≤ (Nat.ceil (Real.log q / Real.log r) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil (Real.log q / Real.log r) : ℝ) ≤ (N : ℝ) := by
      have : Nat.ceil (Real.log q / Real.log r) ≤ N := hNdef ▸ le_max_right _ _
      exact_mod_cast this
    linarith
  have hmul : (N : ℝ) * Real.log r ≤ Real.log q := (div_le_iff_of_neg hlr).mp hratio
  have hpow : r ^ N = Real.exp ((N : ℝ) * Real.log r) := by
    rw [← Real.rpow_natCast r N, Real.rpow_def_of_pos hr0, mul_comm]
  calc r ^ N = Real.exp ((N : ℝ) * Real.log r) := hpow
    _ ≤ Real.exp (Real.log q) := Real.exp_le_exp.mpr hmul
    _ = q := Real.exp_log hq0

theorem logRowQualified_logRowModulus
    {g : ℕ} (hg : 2 ≤ g) {a b ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) :
    logRowQualified g (logRowModulus g a b ε) a b
      (logRowGapEnvelope g a b) ε := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg1 : 0 < (g : ℝ) - 1 := by linarith
  have hF : 0 < logRowIntervalFactor g a b := by
    have h1 : 0 < b ^ ((g : ℝ)⁻¹) := Real.rpow_pos_of_pos hb _
    have h2 : 0 < (a ^ ((g : ℝ)⁻¹))⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos ha _)
    unfold logRowIntervalFactor
    linarith
  set F : ℝ := logRowIntervalFactor g a b with hFdef
  set P : ℝ := logRowGapEnvelope g a b ^ logRowModulus g a b ε with hP
  have hP0 : 0 ≤ P := pow_nonneg (logRowGapEnvelope_pos g a b).le _
  have hPq : P ≤ logRowPowerTarget g a b ε :=
    logRowGapEnvelope_pow_logRowModulus_le_target hg ha hab hε
  have h1 : P ≤ 1 / (2 * ((g : ℝ) - 1)) := le_trans hPq (min_le_left _ _)
  have h2 : P ≤ ε / (8 * (g : ℝ) * ((g : ℝ) - 1) * F) := le_trans hPq (min_le_right _ _)
  have hden : 0 < 8 * (g : ℝ) * ((g : ℝ) - 1) * F :=
    mul_pos (mul_pos (by linarith) hg1) hF
  have h1' : P * (2 * ((g : ℝ) - 1)) ≤ 1 := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * ((g : ℝ) - 1))] at h1
    exact h1
  have h2' : P * (8 * (g : ℝ) * ((g : ℝ) - 1) * F) ≤ ε := by
    rw [le_div_iff₀ hden] at h2
    exact h2
  refine ⟨?_, ?_⟩
  · unfold logRowBetaEnvelope
    nlinarith
  · unfold logRowBetaEnvelope
    nlinarith

noncomputable def diagonalLogG (a b ε : ℝ) : ℕ :=
  max 2 (logSurrogateBiasModulus a b (ε / 2))

noncomputable def diagonalLogN (a b ε : ℝ) : ℕ :=
  logRowModulus (diagonalLogG a b ε) a b (ε / 2)

noncomputable def diagonalBinomialLog (a b ε x : ℝ) : ℝ :=
  binomialLog (diagonalLogG a b ε) (diagonalLogN a b ε) x

theorem two_le_diagonalLogG (a b ε : ℝ) :
    2 ≤ diagonalLogG a b ε :=
  le_max_left _ _

theorem biasModulus_le_diagonalLogG (a b ε : ℝ) :
    logSurrogateBiasModulus a b (ε / 2) ≤ diagonalLogG a b ε :=
  le_max_right _ _

theorem diagonalBinomialLog_error_lt {a b ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) :
    ∀ x ∈ Set.Icc a b,
      |diagonalBinomialLog a b ε x - Real.log x| < ε := by
  intro x hx
  have hε2 : 0 < ε / 2 := by linarith
  have hg2 : 2 ≤ diagonalLogG a b ε := two_le_diagonalLogG a b ε
  have hrow :
      |binomialLog (diagonalLogG a b ε) (diagonalLogN a b ε) x -
          logSurrogate (diagonalLogG a b ε) x| < ε / 2 :=
    binomialLog_row_error_lt_of_envelope_qualified hg2 ha hab
      (logRowQualified_logRowModulus hg2 ha hab hε2) x hx
  have hbias : |logSurrogate (diagonalLogG a b ε) x - Real.log x| < ε / 2 :=
    logSurrogate_error_lt_of_biasModulus ha hab hε2 (biasModulus_le_diagonalLogG a b ε) x hx
  have hsplit :
      |binomialLog (diagonalLogG a b ε) (diagonalLogN a b ε) x - Real.log x| ≤
        |binomialLog (diagonalLogG a b ε) (diagonalLogN a b ε) x -
            logSurrogate (diagonalLogG a b ε) x| +
          |logSurrogate (diagonalLogG a b ε) x - Real.log x| :=
    abs_sub_le _ _ _
  unfold diagonalBinomialLog
  linarith

end ResidueSlices
