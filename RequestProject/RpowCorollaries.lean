import RequestProject.ExplicitSpectralRate

open scoped BigOperators

namespace ResidueSlices

/-- The zeroth slice is strictly positive on the nonnegative real axis. -/
theorem slice_zero_pos (g N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < slice g 0 N x :=
  zero_lt_one.trans_le (one_le_slice_zero g N hx)

/-- Explicit denominator-nonzero statement: every slice ratio in the
development has a nonvanishing denominator on the nonnegative real axis. -/
theorem slice_zero_ne_zero (g N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    slice g 0 N x ≠ 0 :=
  (slice_zero_pos g N hx).ne'

/-- The real `g`-th root: `(x ^ (1/g)) ^ g = x` for `x > 0`. -/
private lemma rpow_inv_pow {g : ℕ} (hg : 0 < g) {x : ℝ} (hx : 0 < x) :
    (x ^ ((g : ℝ))⁻¹) ^ g = x := by
  rw [← Real.rpow_natCast (x ^ ((g : ℝ))⁻¹) g, ← Real.rpow_mul hx.le,
    inv_mul_cancel₀ (by exact_mod_cast hg.ne' : (g : ℝ) ≠ 0), Real.rpow_one]

/-- Rewriting the limit point: `((x^(1/g))^k)⁻¹ = x ^ (−k/g)`. -/
private lemma rpow_inv_pow_k {g k : ℕ} {x : ℝ} (hx : 0 < x) :
    ((x ^ ((g : ℝ))⁻¹) ^ k)⁻¹ = x ^ (-(k : ℝ) / (g : ℝ)) := by
  rw [← Real.rpow_natCast (x ^ ((g : ℝ))⁻¹) k, ← Real.rpow_mul hx.le,
    ← Real.rpow_neg hx.le]
  ring_nf

/-- **Positive-`x` convergence in literal `rpow` form**: for every `x > 0`,
the residue-slice ratio converges to `x ^ (−k/g)` as a real power — no
substitution `x = t^g` required in the statement. -/
theorem tendsto_slice_ratio_rpow
    {g k : ℕ} (hg : 0 < g) (hk : k < g) {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (fun N : ℕ => slice g k N x / slice g 0 N x)
      Filter.atTop (nhds (x ^ (-(k : ℝ) / (g : ℝ)))) := by
  have ht : 0 < x ^ ((g : ℝ))⁻¹ := Real.rpow_pos_of_pos hx _
  have h := tendsto_general_slice_ratio hg hk ht
  rw [rpow_inv_pow hg hx, rpow_inv_pow_k hx] at h
  exact h

/-- **Explicit rate in literal `rpow` form**: past the checkable threshold
`(g−1)ρ^N ≤ 1/2`, the error against `x ^ (−k/g)` is at most
`4(g−1)·ρ^N·x^(−k/g)` — the bound exactly as stated in the paper
(`residue_packetization.tex`, explicit ratio inequality). -/
theorem slice_ratio_explicit_rate_rpow
    {g k : ℕ} (hg : 0 < g) (hk : k < g) {x : ℝ} (hx : 0 < x)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) {N : ℕ}
    (hN : ((g : ℝ) - 1) * spectralGap g (x ^ ((g : ℝ))⁻¹) ω ^ N ≤ 1 / 2) :
    |slice g k N x / slice g 0 N x - x ^ (-(k : ℝ) / (g : ℝ))| ≤
      4 * (((g : ℝ) - 1) * spectralGap g (x ^ ((g : ℝ))⁻¹) ω ^ N) *
        x ^ (-(k : ℝ) / (g : ℝ)) := by
  have ht : 0 < x ^ ((g : ℝ))⁻¹ := Real.rpow_pos_of_pos hx _
  have h := general_slice_ratio_explicit_rate hg hk ht hω hN
  rw [rpow_inv_pow hg hx, rpow_inv_pow_k hx] at h
  refine h.trans_eq ?_
  rw [div_eq_mul_inv, rpow_inv_pow_k hx]

end ResidueSlices
