/-
Executable diagonal logarithm, Phase 2A: the explicit surrogate-bias bound.

`BinomialLogConvergence` supplies the exact closed form
`logSurrogate g x = 2 * g * Real.tanh (Real.log x / (2 * g))` for `1 ≤ g`, `0 < x`.
This file turns that identity into a *quantitative* error bound

  |logSurrogate g x - Real.log x| ≤ |Real.log x| ^ 3 / (12 * g ^ 2),

together with a compact-interval version and an explicit modulus
`logSurrogateBiasModulus` for choosing `g` so that the surrogate bias is `< ε`
uniformly on `[a, b] ⊆ (0, ∞)`.

This closes only the *surrogate-bias* half of the diagonal logarithm problem.
Nothing here asserts a finite-row `N` bound, convergence of `binomialLog`, or a
joint-schedule limit.

The analytic input is a global cubic bound `|u - tanh u| ≤ |u| ^ 3 / 3`, valid
for every real `u`.  Mathlib (at this revision) has neither a derivative lemma
for `Real.tanh` nor `|tanh u| ≤ |u|`, so both are developed here from
`Real.tanh_eq_sinh_div_cosh` and the derivatives of `sinh`/`cosh`.
-/
import RequestProject.BinomialLogConvergence

namespace ResidueSlices

/-! ### Auxiliary facts about `Real.tanh` -/

/-- `sinh / cosh`, as a function, is `Real.tanh`. -/
private theorem sinh_div_cosh_eq_tanh : (Real.sinh / Real.cosh : ℝ → ℝ) = Real.tanh :=
  funext fun x => by
    simp only [Pi.div_apply]
    exact (Real.tanh_eq_sinh_div_cosh x).symm

/-- The derivative of `Real.tanh` is `1 - tanh ^ 2` (quotient rule plus
`cosh ^ 2 - sinh ^ 2 = 1`). -/
private theorem hasDerivAt_tanh (u : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh u ^ 2) u := by
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  have h := (Real.hasDerivAt_sinh u).div (Real.hasDerivAt_cosh u) hc
  have heq : (Real.cosh u * Real.cosh u - Real.sinh u * Real.sinh u) / Real.cosh u ^ 2
      = 1 - Real.tanh u ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_pow]
    field_simp
  rw [heq, sinh_div_cosh_eq_tanh] at h
  exact h

private theorem tanh_differentiable : Differentiable ℝ Real.tanh :=
  fun u => (hasDerivAt_tanh u).differentiableAt

/-- `u ↦ u - tanh u` has derivative `tanh ^ 2 ≥ 0`, hence is monotone. -/
private theorem sub_tanh_monotone : Monotone (fun u : ℝ => u - Real.tanh u) := by
  apply monotone_of_deriv_nonneg (f := fun u : ℝ => u - Real.tanh u)
    (differentiable_id.sub tanh_differentiable)
  intro x
  have hd : HasDerivAt (fun u : ℝ => u - Real.tanh u) (1 - (1 - Real.tanh x ^ 2)) x :=
    (hasDerivAt_id x).sub (hasDerivAt_tanh x)
  rw [hd.deriv]
  nlinarith [sq_nonneg (Real.tanh x)]

/-- `|tanh u| ≤ |u|` for every real `u`. -/
private theorem abs_tanh_le_abs (u : ℝ) : |Real.tanh u| ≤ |u| := by
  rcases le_total 0 u with hu | hu
  · have h1 : (0:ℝ) - Real.tanh 0 ≤ u - Real.tanh u := sub_tanh_monotone hu
    rw [Real.tanh_zero] at h1
    have h2 : 0 ≤ Real.tanh u := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hu) (Real.cosh_pos u).le
    rw [abs_of_nonneg h2, abs_of_nonneg hu]
    linarith
  · have h1 : u - Real.tanh u ≤ (0:ℝ) - Real.tanh 0 := sub_tanh_monotone hu
    rw [Real.tanh_zero] at h1
    have h2 : Real.tanh u ≤ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr hu) (Real.cosh_pos u).le
    rw [abs_of_nonpos h2, abs_of_nonpos hu]
    linarith

private theorem sq_tanh_le_sq (u : ℝ) : Real.tanh u ^ 2 ≤ u ^ 2 := by
  have h := abs_tanh_le_abs u
  nlinarith [abs_nonneg (Real.tanh u), abs_nonneg u, sq_abs (Real.tanh u), sq_abs u]

/-- `u ↦ u ^ 3 / 3 - (u - tanh u)` has derivative `u ^ 2 - tanh ^ 2 u ≥ 0`,
hence is monotone. -/
private theorem cube_sub_monotone : Monotone (fun u : ℝ => u ^ 3 / 3 - (u - Real.tanh u)) := by
  apply monotone_of_deriv_nonneg (f := fun u : ℝ => u ^ 3 / 3 - (u - Real.tanh u))
    (((differentiable_pow 3).div_const 3).sub (differentiable_id.sub tanh_differentiable))
  intro x
  have h1 : HasDerivAt (fun u : ℝ => u ^ 3 / 3) ((3 : ℕ) * x ^ (3 - 1) / 3) x :=
    (hasDerivAt_pow 3 x).div_const 3
  have hd : HasDerivAt (fun u : ℝ => u ^ 3 / 3 - (u - Real.tanh u))
      ((3 : ℕ) * x ^ (3 - 1) / 3 - (1 - (1 - Real.tanh x ^ 2))) x :=
    h1.sub ((hasDerivAt_id x).sub (hasDerivAt_tanh x))
  rw [hd.deriv]
  have h2 := sq_tanh_le_sq x
  push_cast
  nlinarith

/-! ### The global cubic bound -/

/-- **Global cubic bound.** For every real `u` (positive, negative or zero),
`|u - tanh u| ≤ |u| ^ 3 / 3`. -/
theorem abs_sub_tanh_le_cube (u : ℝ) :
    |u - Real.tanh u| ≤ |u| ^ 3 / 3 := by
  rcases le_total 0 u with hu | hu
  · have h1 : (0:ℝ) ^ 3 / 3 - (0 - Real.tanh 0) ≤ u ^ 3 / 3 - (u - Real.tanh u) :=
      cube_sub_monotone hu
    rw [Real.tanh_zero] at h1
    norm_num at h1
    have h2 : Real.tanh u ≤ u := by
      have h := abs_tanh_le_abs u
      rw [abs_of_nonneg hu] at h
      exact le_trans (le_abs_self _) h
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u - Real.tanh u), abs_of_nonneg hu]
    linarith
  · have h1 : u ^ 3 / 3 - (u - Real.tanh u) ≤ (0:ℝ) ^ 3 / 3 - (0 - Real.tanh 0) :=
      cube_sub_monotone hu
    rw [Real.tanh_zero] at h1
    norm_num at h1
    have h2 : u ≤ Real.tanh u := by
      have h := abs_tanh_le_abs u
      rw [abs_of_nonpos hu] at h
      have h3 := neg_abs_le (Real.tanh u)
      linarith
    rw [abs_of_nonpos (by linarith : u - Real.tanh u ≤ 0), abs_of_nonpos hu]
    have h4 : (-u) ^ 3 = -(u ^ 3) := by ring
    rw [h4]
    linarith

/-! ### The explicit surrogate-bias bound -/

/-- **Surrogate-bias bound with the exact constant `1/12`.**
For `1 ≤ g` and `0 < x`,
`|logSurrogate g x - Real.log x| ≤ |Real.log x| ^ 3 / (12 * g ^ 2)`. -/
theorem logSurrogate_error_bound {g : ℕ} (hg : 1 ≤ g) {x : ℝ} (hx : 0 < x) :
    |logSurrogate g x - Real.log x| ≤
      |Real.log x| ^ 3 / (12 * (g : ℝ) ^ 2) := by
  have hgR : (1:ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg0 : (0:ℝ) < (g : ℝ) := lt_of_lt_of_le zero_lt_one hgR
  have h2g : (0:ℝ) < 2 * (g : ℝ) := by linarith
  rw [logSurrogate_eq_tanh hg hx]
  set L : ℝ := Real.log x with hLdef
  set u : ℝ := L / (2 * (g : ℝ)) with hudef
  have hLu : L = 2 * (g : ℝ) * u := by
    rw [hudef]; field_simp
  have hrw : 2 * (g : ℝ) * Real.tanh u - L = -(2 * (g : ℝ) * (u - Real.tanh u)) := by
    rw [hLu]; ring
  rw [hrw, abs_neg, abs_mul, abs_of_nonneg h2g.le]
  have habs : |u| = |L| / (2 * (g : ℝ)) := by
    rw [hudef, abs_div, abs_of_pos h2g]
  have hstep : 2 * (g : ℝ) * |u - Real.tanh u| ≤ 2 * (g : ℝ) * (|u| ^ 3 / 3) :=
    mul_le_mul_of_nonneg_left (abs_sub_tanh_le_cube u) h2g.le
  refine hstep.trans (le_of_eq ?_)
  rw [habs]
  field_simp
  ring

/-! ### Compact-interval form -/

/-- The uniform bound on `|Real.log x|` for `x` in a compact interval
`[a, b] ⊆ (0, ∞)`. -/
noncomputable def logIntervalBound (a b : ℝ) : ℝ :=
  max |Real.log a| |Real.log b|

theorem logIntervalBound_nonneg (a b : ℝ) :
    0 ≤ logIntervalBound a b :=
  le_max_of_le_left (abs_nonneg _)

theorem abs_log_le_logIntervalBound {a b x : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    |Real.log x| ≤ logIntervalBound a b := by
  obtain ⟨hax, hxb⟩ := hx
  have hx0 : 0 < x := lt_of_lt_of_le ha hax
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hla : Real.log a ≤ Real.log x := Real.log_le_log ha hax
  have hlb : Real.log x ≤ Real.log b := Real.log_le_log hx0 hxb
  have h1 : |Real.log a| ≤ logIntervalBound a b := le_max_left _ _
  have h2 : |Real.log b| ≤ logIntervalBound a b := le_max_right _ _
  have h3 : -|Real.log a| ≤ Real.log a := neg_abs_le _
  have h4 : Real.log b ≤ |Real.log b| := le_abs_self _
  rw [abs_le]
  constructor
  · linarith
  · linarith

theorem logSurrogate_error_bound_Icc {g : ℕ} (hg : 1 ≤ g)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    |logSurrogate g x - Real.log x| ≤
      logIntervalBound a b ^ 3 / (12 * (g : ℝ) ^ 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  refine (logSurrogate_error_bound hg hx0).trans ?_
  gcongr
  exact abs_log_le_logIntervalBound ha hab hx

/-! ### The bias modulus -/

/-- An explicit `g` beyond which the surrogate bias is `< ε` on `[a, b]`. -/
noncomputable def logSurrogateBiasModulus (a b ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.sqrt (logIntervalBound a b ^ 3 / (12 * ε))) + 1)

theorem one_le_logSurrogateBiasModulus (a b ε : ℝ) :
    1 ≤ logSurrogateBiasModulus a b ε :=
  le_max_left _ _

theorem logSurrogate_error_lt_of_biasModulus {a b ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) {g : ℕ}
    (hg : logSurrogateBiasModulus a b ε ≤ g) :
    ∀ x ∈ Set.Icc a b,
      |logSurrogate g x - Real.log x| < ε := by
  intro x hx
  set B : ℝ := logIntervalBound a b with hB
  have hB0 : 0 ≤ B := logIntervalBound_nonneg a b
  have harg : 0 ≤ B ^ 3 / (12 * ε) := by positivity
  set s : ℝ := Real.sqrt (B ^ 3 / (12 * ε)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hg1 : 1 ≤ g := le_trans (one_le_logSurrogateBiasModulus a b ε) hg
  have hgceil : Nat.ceil s + 1 ≤ g := le_trans (le_max_right _ _) hg
  have hgR : s < (g : ℝ) := by
    have h1 : s ≤ (Nat.ceil s : ℝ) := Nat.le_ceil s
    have h2 : ((Nat.ceil s + 1 : ℕ) : ℝ) ≤ (g : ℝ) := by exact_mod_cast hgceil
    push_cast at h2
    linarith
  have hg0 : (0:ℝ) < (g : ℝ) := lt_of_le_of_lt hs0 hgR
  have hsq : B ^ 3 / (12 * ε) < (g : ℝ) ^ 2 := by
    have := Real.sq_sqrt harg
    nlinarith [hs0, hgR]
  have hden : (0:ℝ) < 12 * (g : ℝ) ^ 2 := by positivity
  have hfinal : B ^ 3 / (12 * (g : ℝ) ^ 2) < ε := by
    rw [div_lt_iff₀ hden]
    have h12 : (0:ℝ) < 12 * ε := by linarith
    rw [div_lt_iff₀ h12] at hsq
    nlinarith
  exact lt_of_le_of_lt (logSurrogate_error_bound_Icc hg1 ha hab hx) hfinal

end ResidueSlices
