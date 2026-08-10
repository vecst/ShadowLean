/-
gd_g block cover — real-variable foundation for separating the FREE critical
values (reusable by the later lobe argument). This module is analytic only: no
monodromy, no Galois theory.

Write `c = cos θ`, `h = cosh θ`. The core is the strict gap `h + cos 2θ < 2c`
on `0 < θ ≤ 2π/7`; everything else is an algebraic/positivity consequence.

Proof routes (keep every displayed signature verbatim; standard axioms only;
NO floating-point `norm_num` — use exact analytic bounds and certified rational
π enclosures such as `Real.pi_lt_3141593`, `Real.pi_gt_3141592`):

* gdg_scalar_gap_pos (Target 1) — the inequality is TIGHT near θ = 2π/7
  (gap ≈ 0.039), so use sharp Taylor bounds. With `cos 2θ = 2 cos²θ - 1` it is
  equivalent to `2 cos θ (1 - cos θ) > cosh θ - 1`, i.e. (half-angle)
  `2 cos θ · sin²(θ/2) > sinh²(θ/2)`. Suggested route: bound
  `cosh θ = (Real.exp θ + Real.exp (-θ))/2` from above via `Real.exp_bound`
  (Taylor-with-remainder), `cos θ` from below and `cos 2θ` from above via the
  `Real.cos`/`Real.sin` Taylor bounds, reducing to a rational-coefficient
  polynomial inequality in θ that `nlinarith` closes using `0 < θ` and the
  certified bound `θ ≤ 2π/7 < 0.898` (from `π < 3.141593`). Degree-6/8 truncation
  is enough. Preserve the strict `<`.

* gdg_cosh_sub_cos_pos (Target 2a) — `cosh θ ≥ 1` (`Real.one_le_cosh`) and
  `cos θ ≤ 1` (`Real.cos_le_one`) with strictness from `θ > 0`
  (`Real.one_lt_cosh` needs `θ ≠ 0`, or `Real.cos_lt_one`): `cosh θ - cos θ > 0`.

* gdg_one_lt_ratio (Target 2b) — with the positive denominator `cosh θ - cos θ`
  from 2a, `1 < (cos θ - cos 2θ)/(cosh θ - cos θ)` is `one_lt_div`-equivalent to
  `cos θ - cos 2θ > cosh θ - cos θ`, i.e. `2 cos θ > cosh θ + cos 2θ` = Target 1.

* gdg_one_lt_exterior (Target 3) — `cosh (2π) > 3` suffices. E.g.
  `cosh (2π) ≥ Real.exp (2π) / 2` and `Real.exp (2π) > Real.exp 4 > 3·... `
  (`Real.add_one_le_exp` / `Real.exp_lt_exp` with `2π > 4` from `π > 3.14`, and a
  crude `Real.exp 4 > 6`), giving `(cosh (2π) - 1)/2 > 1`. Keep the final
  statement `1 < (cosh (2π) - 1)/2` verbatim.

* gdg_one_lt_powered (Target 4, optional) — from 2b the base `R > 1`, so
  `R ^ g ≥ R > 1` for `g ≥ 1` (`one_lt_pow` / `one_le_pow_iff`), and the exterior
  factor `> 1` from Target 3; `one_lt_mul_of_lt_of_le` (both factors `> 1`).

Certification: no sorry/admit/new axiom/unsafe/implemented_by; do not weaken any
strict `<`; keep unclosable targets out and report their exact name + remaining
goal; run module, Main, and audit with `--wfail`; report `#print axioms` for
each proved public theorem.
-/
import Mathlib

namespace GdgSquarefree

/-! ### Auxiliary explicit Taylor bounds (no floating point; all rational). -/

/-- Degree-4 Taylor upper bound for `Real.exp` with an explicit remainder,
valid on `|x| ≤ 1`. -/
private lemma exp_upper_aux {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + |x| ^ 5 / 100 := by
  have h := Real.exp_bound hx (n := 5) (by norm_num)
  have hs : ∑ m ∈ Finset.range 5, x ^ m / (Nat.factorial m : ℝ)
      = 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at h
  have h2 := (abs_le.mp h).2
  norm_num at h2 ⊢
  linarith

/-- Explicit upper bound for `Real.cosh` on `[0, 1]`. -/
private lemma cosh_upper_aux {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.cosh x ≤ 1 + x ^ 2 / 2 + x ^ 4 / 24 + x ^ 5 / 100 := by
  have hax : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hax' : |(-x)| ≤ 1 := by rwa [abs_neg]
  have h1 := exp_upper_aux hax
  have h2 := exp_upper_aux hax'
  rw [abs_of_nonneg hx0] at h1
  rw [abs_neg, abs_of_nonneg hx0] at h2
  rw [Real.cosh_eq]
  nlinarith [h1, h2]

/-- The rational polynomial inequality underlying Target 1: the `cosh` upper bound
stays below `2·U·(1 - U)`, where `U = 1 - x²/2 + 5x⁴/96` is the quartic upper
bound for `cos x`. -/
private lemma poly_key {x : ℝ} (hx0 : 0 < x) (hxa : x ≤ 0.8976) :
    x ^ 2 / 2 + x ^ 4 / 24 + x ^ 5 / 100
      < x ^ 2 - (29 / 48) * x ^ 4 + (5 / 48) * x ^ 6 - (25 / 4608) * x ^ 8 := by
  nlinarith [sq_nonneg x, pow_pos hx0 2, pow_pos hx0 4, pow_pos hx0 6,
    mul_pos hx0 hx0, sq_nonneg (x - 0.8976), sq_nonneg (x ^ 2 - 0.8),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hxa) hx0.le) hx0.le,
    mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hxa) hx0.le) hx0.le) hx0.le]

/-- **Target 1.** The scalar denominator gap: on `0 < θ ≤ 2π/7`,
`cosh θ + cos 2θ < 2 cos θ` (strict; tight near the endpoint). -/
theorem gdg_scalar_gap_pos {theta : ℝ}
    (htheta0 : 0 < theta) (htheta7 : theta ≤ 2 * Real.pi / 7) :
    Real.cosh theta + Real.cos (2 * theta) < 2 * Real.cos theta := by
  have hxa : theta ≤ 0.8976 := by
    have := Real.pi_lt_d6
    linarith
  have hx1 : theta ≤ 1 := by linarith
  have habs : |theta| ≤ 1 := by rw [abs_of_nonneg htheta0.le]; exact hx1
  have hcb := Real.cos_bound habs
  rw [abs_of_nonneg htheta0.le] at hcb
  have hcb2 := abs_le.mp hcb
  set c := Real.cos theta with hc
  set U : ℝ := 1 - theta ^ 2 / 2 + 5 * theta ^ 4 / 96 with hU
  have hcU : c ≤ U := by simp only [hU]; nlinarith [hcb2.2]
  have hcL : 1 - theta ^ 2 / 2 - 5 * theta ^ 4 / 96 ≤ c := by nlinarith [hcb2.1]
  have hpow4 : theta ^ 4 ≤ 0.8976 ^ 4 := pow_le_pow_left₀ htheta0.le hxa 4
  have hpow2 : theta ^ 2 ≤ 0.8976 ^ 2 := pow_le_pow_left₀ htheta0.le hxa 2
  have hsum : 1 ≤ c + U := by
    simp only [hU] at *
    nlinarith
  have hmono : 2 * U - 2 * U ^ 2 ≤ 2 * c - 2 * c ^ 2 := by nlinarith [hcU, hsum]
  have hUexp : 2 * U - 2 * U ^ 2
      = theta ^ 2 - (29 / 48) * theta ^ 4 + (5 / 48) * theta ^ 6
          - (25 / 4608) * theta ^ 8 := by
    simp only [hU]; ring
  have hcosh := cosh_upper_aux htheta0.le hx1
  have hp := poly_key htheta0 hxa
  rw [Real.cos_two_mul]
  rw [hUexp] at hmono
  linarith

/-- **Target 2a.** Positivity of the denominator `cosh θ - cos θ`.

The hypothesis `htheta7 : theta ≤ 2 * π / 7` is kept because it is part of the
requested interface, but it turns out to be unnecessary: `0 < theta` alone gives
`cos theta ≤ 1 < cosh theta`. -/
theorem gdg_cosh_sub_cos_pos {theta : ℝ}
    (htheta0 : 0 < theta) (htheta7 : theta ≤ 2 * Real.pi / 7) :
    0 < Real.cosh theta - Real.cos theta := by
  have _htheta7 := htheta7
  have h1 : 1 < Real.cosh theta := Real.one_lt_cosh.mpr (ne_of_gt htheta0)
  have h2 : Real.cos theta ≤ 1 := Real.cos_le_one theta
  linarith

/-- **Target 2b.** The denominator ratio exceeds one. -/
theorem gdg_one_lt_ratio {theta : ℝ}
    (htheta0 : 0 < theta) (htheta7 : theta ≤ 2 * Real.pi / 7) :
    1 < (Real.cos theta - Real.cos (2 * theta)) /
          (Real.cosh theta - Real.cos theta) := by
  have hden : 0 < Real.cosh theta - Real.cos theta :=
    gdg_cosh_sub_cos_pos htheta0 htheta7
  rw [one_lt_div hden]
  have := gdg_scalar_gap_pos htheta0 htheta7
  linarith

/-- **Target 3.** The exterior constant exceeds one. -/
theorem gdg_one_lt_exterior :
    1 < (Real.cosh (2 * Real.pi) - 1) / 2 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h1 : 2 * Real.pi + 1 ≤ Real.exp (2 * Real.pi) := Real.add_one_le_exp _
  have h2 : 0 < Real.exp (-(2 * Real.pi)) := Real.exp_pos _
  rw [Real.cosh_eq]
  linarith

/-- **Target 4 (optional).** Powered comparison combining Targets 2b and 3. -/
theorem gdg_one_lt_powered {theta : ℝ}
    (htheta0 : 0 < theta) (htheta7 : theta ≤ 2 * Real.pi / 7)
    {g : ℕ} (hg : 1 ≤ g) :
    1 <
      ((Real.cos theta - Real.cos (2 * theta)) /
          (Real.cosh theta - Real.cos theta)) ^ g *
        ((Real.cosh (2 * Real.pi) - 1) / 2) := by
  have hR : 1 < (Real.cos theta - Real.cos (2 * theta)) /
      (Real.cosh theta - Real.cos theta) := gdg_one_lt_ratio htheta0 htheta7
  have hRg : 1 < ((Real.cos theta - Real.cos (2 * theta)) /
      (Real.cosh theta - Real.cos theta)) ^ g :=
    one_lt_pow₀ hR (Nat.one_le_iff_ne_zero.mp hg)
  have hE : 1 < (Real.cosh (2 * Real.pi) - 1) / 2 := gdg_one_lt_exterior
  nlinarith [hRg, hE]

end GdgSquarefree
