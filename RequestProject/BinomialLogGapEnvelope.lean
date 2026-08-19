/-
Executable diagonal logarithm, Phase 2C1: the explicit interval spectral-gap
envelope.

Phase 2B proves an interval finite-row error bound CONDITIONAL on a supplied
`ρ` with `logRowGap g x ≤ ρ < 1`. This file removes that external envelope by
CONSTRUCTING an explicit `ρ = logRowGapEnvelope g a b` from `g` and the positive
interval `[a, b]`.

Derivation. With `t = x^(1/g)`, `A = a^(1/g)`, `B = b^(1/g)`,
`c_g = 1 - cos(2π/g)`: for `x ∈ [a,b]`, `A ≤ t ≤ B`, so
`t/(1+t)^2 ≥ A/(1+B)^2`. For every nonzero channel `j < g`, `re_pow_le_cos`
gives `Re(ω^j) ≤ cos(2π/g)`, whence
`channelRatio(t,ω,j)^2 ≤ 1 - 2 c_g t/(1+t)^2`, and with `1+z ≤ exp z`,
`channelRatio(t,ω,j) ≤ exp(-c_g t/(1+t)^2) ≤ exp(-c_g A/(1+B)^2)
= logRowGapEnvelope g a b`.

Scope: this phase does NOT choose `N`. Phase 2C2 will select `N` (logs and
ceilings) and combine the row error with the Phase 2A surrogate bias. No row
modulus, no `Nat.find`, no existence-of-qualifying-`N` claim here.
-/
import RequestProject.BinomialLogRowRate
import RequestProject.DiagonalZeta

namespace ResidueSlices

noncomputable def logRowGapEnvelope (g : ℕ) (a b : ℝ) : ℝ :=
  Real.exp (-(1 - Real.cos (2 * Real.pi / g)) *
    a ^ ((g : ℝ)⁻¹) / (1 + b ^ ((g : ℝ)⁻¹)) ^ 2)

/-- The canonical `g`-th root of unity of the logarithm rows is primitive.
`BinomialLogRowRate` keeps its own copy of this fact private, so it is
re-established here from `Complex.isPrimitiveRoot_exp`. -/
private theorem canonicalLogRoot_primitive {g : ℕ} (hg : 0 < g) :
    IsPrimitiveRoot (canonicalLogRoot g) g :=
  Complex.isPrimitiveRoot_exp g hg.ne'

/-- The spectral-gap constant `c_g = 1 - cos(2π/g)` is positive for `g ≥ 2`
(for `g = 2` it equals `2`). -/
private theorem one_sub_cos_pos {g : ℕ} (hg : 2 ≤ g) :
    0 < 1 - Real.cos (2 * Real.pi / g) := by
  have h := diagGap_pos hg
  unfold diagGap at h
  linarith

theorem logRowGapEnvelope_pos (g : ℕ) (a b : ℝ) :
    0 < logRowGapEnvelope g a b :=
  Real.exp_pos _

theorem logRowGapEnvelope_lt_one {g : ℕ} (hg : 2 ≤ g)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    logRowGapEnvelope g a b < 1 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < 1 - Real.cos (2 * Real.pi / g) := one_sub_cos_pos hg
  have hA : 0 < a ^ ((g : ℝ)⁻¹) := Real.rpow_pos_of_pos ha _
  have hB : 0 < b ^ ((g : ℝ)⁻¹) := Real.rpow_pos_of_pos hb _
  have hden : 0 < (1 + b ^ ((g : ℝ)⁻¹)) ^ 2 := by positivity
  unfold logRowGapEnvelope
  rw [Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (by nlinarith) hden

theorem channelRatio_le_logRowGapEnvelope {g : ℕ} (hg : 2 ≤ g)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : x ∈ Set.Icc a b)
    {j : ℕ} (hj : j < g) (hj0 : j ≠ 0) :
    channelRatio (x ^ ((g : ℝ)⁻¹)) (canonicalLogRoot g) j ≤
      logRowGapEnvelope g a b := by
  obtain ⟨hax, hxb⟩ := hx
  have hx0 : 0 < x := lt_of_lt_of_le ha hax
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hω : IsPrimitiveRoot (canonicalLogRoot g) g := canonicalLogRoot_primitive (by omega)
  have hc : 0 < 1 - Real.cos (2 * Real.pi / g) := one_sub_cos_pos hg
  have hginv : (0 : ℝ) ≤ (g : ℝ)⁻¹ := by positivity
  set t : ℝ := x ^ ((g : ℝ)⁻¹) with ht
  set A : ℝ := a ^ ((g : ℝ)⁻¹) with hAdef
  set B : ℝ := b ^ ((g : ℝ)⁻¹) with hBdef
  have hA : 0 < A := Real.rpow_pos_of_pos ha _
  have hAt : A ≤ t := Real.rpow_le_rpow ha.le hax hginv
  have htB : t ≤ B := Real.rpow_le_rpow hx0.le hxb hginv
  have ht0 : 0 < t := lt_of_lt_of_le hA hAt
  -- the squared norm identity, bounded through `re_pow_le_cos`
  have h_sq : channelRatio t (canonicalLogRoot g) j ^ 2 ≤
      1 - 2 * (1 - Real.cos (2 * Real.pi / g)) * t / (1 + t) ^ 2 := by
    have h_norm_sq : ‖1 + (t : ℂ) * canonicalLogRoot g ^ j‖ ^ 2 =
        1 + 2 * t * (canonicalLogRoot g ^ j).re + t ^ 2 := by
      have h_abs : Complex.normSq (canonicalLogRoot g ^ j) = 1 := by
        simp [Complex.normSq_eq_norm_sq, hω.norm'_eq_one (by omega)]
      simp only [Complex.sq_norm, Complex.normSq_apply] at *
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
      nlinarith [h_abs]
    have h_norm_sq_bound : ‖1 + (t : ℂ) * canonicalLogRoot g ^ j‖ ^ 2 ≤
        1 + 2 * t * Real.cos (2 * Real.pi / g) + t ^ 2 := by
      have := re_pow_le_cos hg hω hj hj0
      nlinarith
    unfold channelRatio
    rw [div_pow, div_le_iff₀ (by positivity)]
    rw [sub_mul, div_mul_cancel₀ _ (by positivity : ((1 : ℝ) + t) ^ 2 ≠ 0)]
    nlinarith
  -- pass to the exponential bound
  have h_exp : channelRatio t (canonicalLogRoot g) j ≤
      Real.exp (-(1 - Real.cos (2 * Real.pi / g)) * t / (1 + t) ^ 2) := by
    have h2 : channelRatio t (canonicalLogRoot g) j ^ 2 ≤
        Real.exp (-2 * (1 - Real.cos (2 * Real.pi / g)) * t / (1 + t) ^ 2) := by
      calc channelRatio t (canonicalLogRoot g) j ^ 2
          ≤ 1 - 2 * (1 - Real.cos (2 * Real.pi / g)) * t / (1 + t) ^ 2 := h_sq
        _ = -2 * (1 - Real.cos (2 * Real.pi / g)) * t / (1 + t) ^ 2 + 1 := by ring
        _ ≤ Real.exp (-2 * (1 - Real.cos (2 * Real.pi / g)) * t / (1 + t) ^ 2) :=
            Real.add_one_le_exp _
    convert Real.le_sqrt_of_sq_le h2 using 1
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  refine h_exp.trans ?_
  unfold logRowGapEnvelope
  refine Real.exp_le_exp.mpr ?_
  have hmono : A / (1 + B) ^ 2 ≤ t / (1 + t) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (1 + t) ^ 2 ≤ (1 + B) ^ 2 := by nlinarith
    calc A * (1 + t) ^ 2 ≤ t * (1 + t) ^ 2 :=
          mul_le_mul_of_nonneg_right hAt (by positivity)
      _ ≤ t * (1 + B) ^ 2 := mul_le_mul_of_nonneg_left hsq ht0.le
  have hcneg : -(1 - Real.cos (2 * Real.pi / g)) ≤ 0 := by linarith
  calc -(1 - Real.cos (2 * Real.pi / g)) * t / (1 + t) ^ 2
      = -(1 - Real.cos (2 * Real.pi / g)) * (t / (1 + t) ^ 2) := by ring
    _ ≤ -(1 - Real.cos (2 * Real.pi / g)) * (A / (1 + B) ^ 2) :=
        mul_le_mul_of_nonpos_left hmono hcneg
    _ = -(1 - Real.cos (2 * Real.pi / g)) * A / (1 + B) ^ 2 := by ring

theorem logRowGap_le_logRowGapEnvelope {g : ℕ} (hg : 2 ≤ g)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∀ x ∈ Set.Icc a b,
      logRowGap g x ≤ logRowGapEnvelope g a b := by
  intro x hx
  unfold logRowGap spectralGap
  refine Finset.max'_le _ _ _ ?_
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact (logRowGapEnvelope_pos g a b).le
  · obtain ⟨j, hjmem, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hjrange, hjne⟩ := Finset.mem_sdiff.mp hjmem
    exact channelRatio_le_logRowGapEnvelope hg ha hab hx (Finset.mem_range.mp hjrange)
      (by simpa using hjne)

theorem logRowGapEnvelope_mem_unitInterval {g : ℕ} (hg : 2 ≤ g)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ logRowGapEnvelope g a b ∧ logRowGapEnvelope g a b < 1 :=
  ⟨(logRowGapEnvelope_pos g a b).le, logRowGapEnvelope_lt_one hg ha hab⟩

theorem binomialLog_row_interval_rate {g : ℕ} (hg : 2 ≤ g)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {N : ℕ}
    (hN : logRowBetaEnvelope g N (logRowGapEnvelope g a b) ≤ 1 / 2) :
    ∀ x ∈ Set.Icc a b,
      |binomialLog g N x - logSurrogate g x| ≤
        4 * (g : ℝ) *
          logRowBetaEnvelope g N (logRowGapEnvelope g a b) *
          logRowIntervalFactor g a b :=
  binomialLog_row_interval_rate_of_gap_bound hg ha hab
    (logRowGapEnvelope_pos g a b).le (logRowGapEnvelope_lt_one hg ha hab)
    (logRowGap_le_logRowGapEnvelope hg ha hab) hN

theorem binomialLog_row_error_lt_of_envelope_qualified {g : ℕ} (hg : 2 ≤ g)
    {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) {N : ℕ}
    (hN : logRowQualified g N a b (logRowGapEnvelope g a b) ε) :
    ∀ x ∈ Set.Icc a b,
      |binomialLog g N x - logSurrogate g x| < ε :=
  binomialLog_row_error_lt_of_qualified hg ha hab
    (logRowGapEnvelope_pos g a b).le (logRowGapEnvelope_lt_one hg ha hab)
    (logRowGap_le_logRowGapEnvelope hg ha hab) hN

end ResidueSlices
