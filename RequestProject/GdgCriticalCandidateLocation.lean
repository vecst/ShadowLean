/-
gd_g squarefreeness — analytic candidate-location layer.

Builds on `RequestProject.GdgCriticalTetranomial` (namespace `GdgSquarefree`),
which already proves the exact critical tetranomial derivative, its occurrence
in the pulled-cover derivative numerator, the reciprocal quadratic satisfied by
every repeated root, and the explicit value `u + u⁻¹ = (8 - g(a²+4))/(2a(g-1))`
for every nonzero repeated root (`criticalTetranomial_common_root_reciprocal`).
DO NOT reprove those.

This module specializes the abstract coefficient `a` to `a_g = 2 cos(2π/g)` and
locates the only two possible repeated roots (the reciprocal roots of
`X² - gdgCandidateB g · X + 1`).

Write `c = Real.cos (2π/g)`, so `gdgCosCoeff g = 2c`.

Proof routes (keep every statement verbatim; standard axioms only):

* gdgCosCoeff_pos (T1): for g ≥ 5, `0 < 2π/g < π/2` (since `2π/g ≤ 2π/5 < π/2`
  and `2π/g > 0`), so `Real.cos (2π/g) > 0` (cos positive on `(-π/2, π/2)`,
  `Real.cos_pos_of_mem_Ioo`); hence `2c > 0`. No numerical approximation.

* gdgCandidateB_add_two (T2): unfold `gdgCandidateB`, `gdgCosCoeff` (`= 2c`);
  `c ≠ 0` (from T1) and `(g:ℝ) - 1 ≠ 0` (g ≥ 5); `field_simp; ring`. The claimed
  identity is exact:  `(2 - g(c²+1))/(c(g-1)) + 2 = (1-c)(2 - g(1-c))/(c(g-1))`.

* gdgCandidateB_eq_common_root_reciprocal (T3): apply
  `criticalTetranomial_common_root_reciprocal` (hg : 2 ≤ g from 5 ≤ g;
  `a := (gdgCosCoeff g : ℂ)` nonzero from T1 via `Complex.ofReal_ne_zero`;
  `hu, hG, hG'`), then rewrite the RHS to `(gdgCandidateB g : ℂ)` with
  `push_cast` / `Complex.ofReal_*` and `Nat.cast_sub` for `((g-1:ℕ):ℂ) = (g:ℂ)-1`.
  Reuse the existing ring algebra; do not duplicate it.

* gdgCandidateB_lt_neg_two (T4a, 5 ≤ g ≤ 9): via T2, `c(g-1) > 0`, `1-c > 0`
  (cos < 1 since `2π/g ∈ (0, 2π)`), so `sign(gdgCandidateB g + 2) = sign(2 - g(1-c))`;
  need `2 - g(1-c) < 0`. `interval_cases g` (five cases); for each use an exact
  trigonometric upper bound on `cos (2π/g)` (equivalently a lower bound on
  `1 - cos`, e.g. `1 - cos x ≥ x²/2 - x⁴/24`) plus a certified rational bound for
  π. If a finite case lacks a usable Mathlib trig lemma, omit T4a and report it.

* gdgCandidateB_mem_Ioo_neg_two_zero (T4b, g ≥ 10): `-2 < gdgCandidateB g` from
  `2 - g(1-c) > 0` using `1 - cos x < x²/2` (so `g(1-c) < 2π²/g ≤ π²/5 < 2`,
  needs a certified `π² < 10`); `gdgCandidateB g < 0` since the numerator
  `2 - g(c²+1) < 0` (`g(c²+1) ≥ g ≥ 10 > 2`) and `c(g-1) > 0`. Symbolic only,
  no norm_num on floats.

* gdgCandidateB_not_tetranomial_root (T5, optional, only if T1–T4 close): the
  remaining squarefreeness exclusion — neither reciprocal root of
  `X² - gdgCandidateB g · X + 1` is a root of the specialized tetranomial for
  g ≥ 5. Do NOT claim it from the location inequalities alone. If it cannot be
  closed, omit it and report its exact name and remaining goal.

Certification: no sorry/admit/new axiom/unsafe/implemented_by; do not weaken any
target; keep unclosable targets out of the module and report them; run the
module, Main, and audit with `--wfail`; report `#print axioms` for each proved
public theorem.
-/
import Mathlib
import RequestProject.GdgCriticalTetranomial

namespace GdgSquarefree

/-- The specialized cosine coefficient `a_g = 2 cos(2π/g)`. -/
noncomputable def gdgCosCoeff (g : ℕ) : ℝ :=
  2 * Real.cos (2 * Real.pi / (g : ℝ))

/-- **Target 1.** The cosine coefficient is positive for `g ≥ 5`. -/
theorem gdgCosCoeff_pos {g : ℕ} (hg : 5 ≤ g) : 0 < gdgCosCoeff g := by
  have hgR : (5 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hpi := Real.pi_pos
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have h1 : 0 < 2 * Real.pi / (g : ℝ) := by positivity
  have h2 : 2 * Real.pi / (g : ℝ) < Real.pi / 2 := by
    rw [div_lt_iff₀ hgpos]
    nlinarith
  have := Real.cos_pos_of_mem_Ioo ⟨by linarith, h2⟩
  unfold gdgCosCoeff
  linarith

/-- Half-angle identity used to control `1 - cos`. -/
private theorem one_sub_cos_eq_two_mul_sin_sq (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have h := Real.cos_two_mul' (x / 2)
  have h2 : 2 * (x / 2) = x := by ring
  rw [h2] at h
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

/-- `1 - cos (2π/g) = 2 sin (π/g)²`. -/
private theorem one_sub_cos_two_pi_div (g : ℕ) (hg : 0 < g) :
    1 - Real.cos (2 * Real.pi / (g : ℝ)) = 2 * Real.sin (Real.pi / (g : ℝ)) ^ 2 := by
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hhalf : 2 * Real.pi / (g : ℝ) / 2 = Real.pi / (g : ℝ) := by
    field_simp
  rw [one_sub_cos_eq_two_mul_sin_sq, hhalf]

/-- `sin (π/g) > 0` for `g ≥ 2`. -/
private theorem sin_pi_div_pos {g : ℕ} (hg : 2 ≤ g) : 0 < Real.sin (Real.pi / (g : ℝ)) := by
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hpi := Real.pi_pos
  refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- `cos (2π/g) < 1` for `g ≥ 2`. -/
private theorem cos_two_pi_div_lt_one {g : ℕ} (hg : 2 ≤ g) :
    Real.cos (2 * Real.pi / (g : ℝ)) < 1 := by
  have h := one_sub_cos_two_pi_div g (by omega)
  have hs := sin_pi_div_pos hg
  nlinarith

set_option linter.unusedVariables false in
/-- Generic numeric lower bound for `n · sin x ²` from rational enclosures of `x`. -/
private theorem one_lt_mul_sin_sq_of_bounds {n x l u : ℝ}
    (h1 : l ≤ x) (h2 : x ≤ u) (hu : u ≤ 1) (hl : 0 < l)
    (hpos : 0 < l - u ^ 3 / 4) (hn : 1 < n * (l - u ^ 3 / 4) ^ 2) :
    1 < n * Real.sin x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le hl h1
  have hx1 : x ≤ 1 := le_trans h2 hu
  have hcube : x ^ 3 ≤ u ^ 3 := by gcongr
  have hs : l - u ^ 3 / 4 < Real.sin x := by
    have := Real.sin_gt_sub_cube hx0
    nlinarith [this, hcube, pow_pos hx0 3]
  have hsq : (l - u ^ 3 / 4) ^ 2 < Real.sin x ^ 2 :=
    pow_lt_pow_left₀ hs (le_of_lt hpos) two_ne_zero
  have hnpos : 0 < n := by nlinarith [sq_nonneg (l - u ^ 3 / 4)]
  nlinarith

/-- For `5 ≤ g ≤ 9` one has `g · sin (π/g)² > 1`, i.e. `g (1 - cos (2π/g)) > 2`. -/
private theorem one_lt_g_mul_sin_sq {g : ℕ} (hg : 5 ≤ g) (hg' : g ≤ 9) :
    1 < (g : ℝ) * Real.sin (Real.pi / (g : ℝ)) ^ 2 := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  interval_cases g
  · push_cast
    exact one_lt_mul_sin_sq_of_bounds (l := 3141592 / 5000000) (u := 3141593 / 5000000)
      (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · push_cast
    exact one_lt_mul_sin_sq_of_bounds (l := 3141592 / 6000000) (u := 3141593 / 6000000)
      (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · push_cast
    exact one_lt_mul_sin_sq_of_bounds (l := 3141592 / 7000000) (u := 3141593 / 7000000)
      (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · push_cast
    exact one_lt_mul_sin_sq_of_bounds (l := 3141592 / 8000000) (u := 3141593 / 8000000)
      (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · push_cast
    exact one_lt_mul_sin_sq_of_bounds (l := 3141592 / 9000000) (u := 3141593 / 9000000)
      (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The candidate reciprocal sum `u + u⁻¹` for a repeated root, obtained by
specializing `a = gdgCosCoeff g` in the abstract reciprocal value. -/
noncomputable def gdgCandidateB (g : ℕ) : ℝ :=
  (8 - (g : ℝ) * (gdgCosCoeff g ^ 2 + 4)) / (2 * gdgCosCoeff g * ((g : ℝ) - 1))

/-- **Target 2.** Exact factored form of `gdgCandidateB g + 2` (with
`c = cos (2π/g)`). -/
theorem gdgCandidateB_add_two {g : ℕ} (hg : 5 ≤ g) :
    gdgCandidateB g + 2 =
      ((1 - Real.cos (2 * Real.pi / (g : ℝ))) *
          (2 - (g : ℝ) * (1 - Real.cos (2 * Real.pi / (g : ℝ))))) /
        (Real.cos (2 * Real.pi / (g : ℝ)) * ((g : ℝ) - 1)) := by
  have hgR : (5 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hc : 0 < Real.cos (2 * Real.pi / (g : ℝ)) := by
    have := gdgCosCoeff_pos hg
    unfold gdgCosCoeff at this
    linarith
  have hc0 : Real.cos (2 * Real.pi / (g : ℝ)) ≠ 0 := ne_of_gt hc
  have hg0 : (g : ℝ) - 1 ≠ 0 := by linarith
  unfold gdgCandidateB gdgCosCoeff
  field_simp
  ring

/-- **Target 3.** Every nonzero common root of the specialized critical
tetranomial and its derivative has reciprocal sum `gdgCandidateB g`. -/
theorem gdgCandidateB_eq_common_root_reciprocal {g : ℕ} (hg : 5 ≤ g) {u : ℂ}
    (hu : u ≠ 0)
    (hG : criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g) u = 0)
    (hG' : criticalTetranomialDeriv g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g) u = 0) :
    u + u⁻¹ = (gdgCandidateB g : ℂ) := by
  have ha : ((gdgCosCoeff g : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (gdgCosCoeff_pos hg))
  have h := criticalTetranomial_common_root_reciprocal (by omega : 2 ≤ g) ha hu hG hG'
  have hgc : ((g - 1 : ℕ) : ℂ) = (g : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ g)]
    norm_num
  rw [h, hgc]
  unfold gdgCandidateB
  push_cast
  ring

/-- **Target 4a.** For `5 ≤ g ≤ 9` the candidate lies below `-2`. -/
theorem gdgCandidateB_lt_neg_two {g : ℕ} (hg : 5 ≤ g) (hg' : g ≤ 9) :
    gdgCandidateB g < -2 := by
  have hgR : (5 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hc : 0 < Real.cos (2 * Real.pi / (g : ℝ)) := by
    have := gdgCosCoeff_pos hg
    unfold gdgCosCoeff at this
    linarith
  have hclt : Real.cos (2 * Real.pi / (g : ℝ)) < 1 := cos_two_pi_div_lt_one (by omega)
  have hsin := one_lt_g_mul_sin_sq hg hg'
  have hcos := one_sub_cos_two_pi_div g (by omega)
  have hnum : 2 - (g : ℝ) * (1 - Real.cos (2 * Real.pi / (g : ℝ))) < 0 := by
    rw [hcos]
    nlinarith
  have hden : 0 < Real.cos (2 * Real.pi / (g : ℝ)) * ((g : ℝ) - 1) := by
    apply mul_pos hc
    linarith
  have hkey := gdgCandidateB_add_two hg
  have : gdgCandidateB g + 2 < 0 := by
    rw [hkey]
    apply div_neg_of_neg_of_pos _ hden
    apply mul_neg_of_pos_of_neg _ hnum
    linarith
  linarith

/-- **Target 4b.** For `g ≥ 10` the candidate lies strictly in `(-2, 0)`. -/
theorem gdgCandidateB_mem_Ioo_neg_two_zero {g : ℕ} (hg : 10 ≤ g) :
    -2 < gdgCandidateB g ∧ gdgCandidateB g < 0 := by
  have hgR : (10 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hc : 0 < Real.cos (2 * Real.pi / (g : ℝ)) := by
    have := gdgCosCoeff_pos (by omega : 5 ≤ g)
    unfold gdgCosCoeff at this
    linarith
  have hclt : Real.cos (2 * Real.pi / (g : ℝ)) < 1 := cos_two_pi_div_lt_one (by omega)
  have hden : 0 < Real.cos (2 * Real.pi / (g : ℝ)) * ((g : ℝ) - 1) :=
    mul_pos hc (by linarith)
  -- Upper bound for `g (1 - cos (2π/g))`.
  have hcos := one_sub_cos_two_pi_div g (by omega)
  have hspos := sin_pi_div_pos (by omega : 2 ≤ g)
  have hslt : Real.sin (Real.pi / (g : ℝ)) < Real.pi / (g : ℝ) :=
    Real.sin_lt (by positivity)
  have hsq : Real.sin (Real.pi / (g : ℝ)) ^ 2 < (Real.pi / (g : ℝ)) ^ 2 :=
    pow_lt_pow_left₀ hslt (le_of_lt hspos) two_ne_zero
  have hpi2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hnum : 0 < 2 - (g : ℝ) * (1 - Real.cos (2 * Real.pi / (g : ℝ))) := by
    rw [hcos]
    have h1 : (g : ℝ) * (2 * Real.sin (Real.pi / (g : ℝ)) ^ 2)
        < (g : ℝ) * (2 * (Real.pi / (g : ℝ)) ^ 2) := by
      have : (0:ℝ) < 2 * (g:ℝ) := by linarith
      nlinarith
    have h2 : (g : ℝ) * (2 * (Real.pi / (g : ℝ)) ^ 2) = 2 * Real.pi ^ 2 / (g : ℝ) := by
      field_simp
    have h3 : 2 * Real.pi ^ 2 / (g : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hgpos]
      nlinarith
    linarith
  constructor
  · have hkey := gdgCandidateB_add_two (by omega : 5 ≤ g)
    have : 0 < gdgCandidateB g + 2 := by
      rw [hkey]
      apply div_pos _ hden
      apply mul_pos _ hnum
      linarith
    linarith
  · unfold gdgCandidateB
    apply div_neg_of_neg_of_pos
    · nlinarith [sq_nonneg (gdgCosCoeff g)]
    · have := gdgCosCoeff_pos (by omega : 5 ≤ g)
      have h2 : (0:ℝ) < (g:ℝ) - 1 := by linarith
      positivity

/-! ### Target 5: the candidate roots are not roots of the tetranomial -/

/-- Euler's formula in the form `2 cos y = e^{iy} + e^{-iy}`. -/
private theorem two_cos_eq (y : ℝ) :
    (2 : ℂ) * (Real.cos y : ℂ) = Complex.exp (y * Complex.I) + (Complex.exp (y * Complex.I))⁻¹ := by
  have h := Complex.two_cos (y : ℂ)
  rw [← Complex.exp_neg, Complex.ofReal_cos, ← neg_mul]
  exact h

/-- Value of the critical tetranomial at a negative real point `-v`. -/
private theorem tetranomial_neg_ofReal {g : ℕ} (hg : 1 ≤ g) (a v : ℝ) :
    criticalTetranomial g (a : ℂ) ((-1 : ℂ) ^ g) (-(v : ℂ))
      = ((a * (1 + v ^ g) - 2 * (v + v ^ (g - 1)) : ℝ) : ℂ) := by
  unfold criticalTetranomial
  have h1 : (-(v:ℂ)) ^ g = (-1:ℂ)^g * (v:ℂ)^g := by rw [neg_pow]
  have h2 : (-(v:ℂ)) ^ (g-1) = (-1:ℂ)^(g-1) * (v:ℂ)^(g-1) := by rw [neg_pow]
  have h3 : (-1:ℂ)^g * (-1:ℂ)^g = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨g, by ring⟩
  have h4 : (-1:ℂ)^g * (-1:ℂ)^(g-1) = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨g-1, by omega⟩
  push_cast
  rw [h1, h2]
  linear_combination ((v:ℂ)^g * (a:ℂ)) * h3 + 2*(v:ℂ)^(g-1) * h4

/-- Value of the critical tetranomial at a point `-e^{ix}` of the unit circle:
it is `e^{i g x/2}` times an explicit real factor. -/
private theorem tetranomial_exp_form (k : ℕ) (a x : ℝ) :
    criticalTetranomial (k+2) (a:ℂ) ((-1:ℂ)^(k+2)) (-(Complex.exp ((x:ℝ)*Complex.I)))
      = Complex.exp ((((k:ℝ)+2)*x/2 : ℝ)*Complex.I) *
        (2*(a:ℂ)*(Real.cos (((k:ℝ)+2)*x/2) : ℂ) - 4*(Real.cos ((k:ℝ)*x/2) : ℂ)) := by
  have hpow : ∀ n : ℕ, ∀ y : ℝ, (n : ℝ)*x/2 = y →
      (Complex.exp (((x/2 : ℝ):ℂ)*Complex.I))^n = Complex.exp ((y:ℝ)*Complex.I) := by
    intro n y hy
    rw [← Complex.exp_nat_mul]
    congr 1
    rw [← hy]
    push_cast
    ring
  set t := Complex.exp (((x/2 : ℝ):ℂ)*Complex.I) with ht
  have htne : t ≠ 0 := Complex.exp_ne_zero _
  have hkne : (t:ℂ)^k ≠ 0 := pow_ne_zero _ htne
  have hx : Complex.exp ((x:ℝ)*Complex.I) = t^2 := (hpow 2 x (by push_cast; ring)).symm
  have he : t^(k+2) = Complex.exp ((((k:ℝ)+2)*x/2 : ℝ)*Complex.I) :=
    hpow (k+2) _ (by push_cast; ring)
  have hek : t^k = Complex.exp (((k:ℝ)*x/2 : ℝ)*Complex.I) := hpow k _ rfl
  have hc1 : (2:ℂ) * ((Real.cos (((k:ℝ)+2)*x/2) : ℝ):ℂ) = t^(k+2) + (t^(k+2))⁻¹ := by
    rw [he]; exact two_cos_eq _
  have hc2 : (2:ℂ) * ((Real.cos ((k:ℝ)*x/2) : ℝ):ℂ) = t^k + (t^k)⁻¹ := by
    rw [hek]; exact two_cos_eq _
  have hsq2 : ((-1:ℂ))^(k*2) = 1 := Even.neg_one_pow ⟨k, by ring⟩
  have hneg1 : (-(t^2))^(k+2) = (-1:ℂ)^k * (t^2)^(k+2) := by
    rw [neg_pow]; ring
  have hneg2 : (-(t^2))^(k+1) = -((-1:ℂ)^k) * (t^2)^(k+1) := by
    rw [neg_pow]; ring
  have e1 : ((Real.cos (((k:ℝ)+2)*x/2) : ℝ):ℂ) = (t^(k+2) + (t^(k+2))⁻¹)/2 := by
    field_simp at hc1 ⊢
    linear_combination hc1
  have e2 : ((Real.cos ((k:ℝ)*x/2) : ℝ):ℂ) = (t^k + (t^k)⁻¹)/2 := by
    field_simp at hc2 ⊢
    linear_combination hc2
  unfold criticalTetranomial
  rw [hx, ← he, show k+2-1 = k+1 from rfl, hneg1, hneg2, e1, e2,
    show ((-1:ℂ)^(k+2)) = (-1:ℂ)^k by ring]
  field_simp
  ring_nf
  linear_combination (2*(a:ℂ)*t^4*t^(k*3) - 4*t^2*t^(k*3)) * hsq2

/-- The exact identity `c² + 1 + B c = (1 - c²)/(g-1)`. -/
private theorem candidateB_cos_identity {g : ℕ} (hg : 5 ≤ g) :
    Real.cos (2 * Real.pi / (g:ℝ)) ^ 2 + 1
        + gdgCandidateB g * Real.cos (2 * Real.pi / (g:ℝ))
      = (1 - Real.cos (2 * Real.pi / (g:ℝ)) ^ 2) / ((g:ℝ) - 1) := by
  have hgR : (5:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg
  have hc : 0 < Real.cos (2 * Real.pi / (g : ℝ)) := by
    have := gdgCosCoeff_pos hg
    unfold gdgCosCoeff at this
    linarith
  have hc0 : Real.cos (2 * Real.pi / (g : ℝ)) ≠ 0 := ne_of_gt hc
  have hg0 : (g:ℝ) - 1 ≠ 0 := by linarith
  unfold gdgCandidateB gdgCosCoeff
  field_simp
  ring

/-- If `v > 0` is a root of `v² + B v + 1` and `c² + 1 + B c > 0`, then `c v < 1` and `c < v`. -/
private theorem real_root_bounds {c v B : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hv : 0 < v)
    (hq : v ^ 2 + B * v + 1 = 0) (hid : 0 < c ^ 2 + 1 + B * c) :
    c * v < 1 ∧ c < v := by
  have key : (1 - c*v) * (v - c) = v * (c^2 + 1 + B*c) - c * (v^2 + B*v + 1) := by ring
  rw [hq] at key
  have hpos : 0 < (1 - c*v) * (v - c) := by
    rw [key]
    have := mul_pos hv hid
    linarith
  rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by linarith, by linarith⟩
  · exfalso
    nlinarith

/-- The real factor at a negative real candidate root is strictly negative. -/
private theorem real_factor_neg {g : ℕ} (hg : 5 ≤ g) {c v : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hv : 0 < v) (hcv : c * v < 1) (hvc : c < v) :
    2 * c * (1 + v ^ g) - 2 * (v + v ^ (g - 1)) < 0 := by
  have hP : v ^ g = v ^ (g-1) * v := by
    rw [← pow_succ]
    congr 1
    omega
  have hQ : v ^ (g-1) = v ^ (g-2) * v := by
    rw [← pow_succ]
    congr 1
    omega
  have hPpos : 0 < v ^ (g-1) := pow_pos hv _
  have hQpos : 0 < v ^ (g-2) := pow_pos hv _
  rcases le_total 1 v with h | h
  · rw [hP]
    nlinarith
  · rw [hP, hQ]
    nlinarith

/-- Target 5, real-root case: for `B < -2` neither (necessarily real, negative) root of
`X² - B X + 1` is a root of the tetranomial. -/
private theorem tetranomial_ne_zero_of_real_root {g : ℕ} (hg : 5 ≤ g) {r : ℝ} (hr : r < 0)
    (hq : r ^ 2 - gdgCandidateB g * r + 1 = 0) :
    criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g) (r : ℂ) ≠ 0 := by
  have hgR : (5:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg
  have hc0 : 0 < Real.cos (2 * Real.pi / (g : ℝ)) := by
    have := gdgCosCoeff_pos hg
    unfold gdgCosCoeff at this
    linarith
  have hc1 : Real.cos (2 * Real.pi / (g : ℝ)) < 1 := cos_two_pi_div_lt_one (by omega)
  set c := Real.cos (2 * Real.pi / (g : ℝ)) with hcdef
  have hid : 0 < c ^ 2 + 1 + gdgCandidateB g * c := by
    rw [candidateB_cos_identity hg]
    have : 0 < 1 - c ^ 2 := by nlinarith
    have hg1 : (0:ℝ) < (g:ℝ) - 1 := by linarith
    positivity
  set v := -r with hvdef
  have hv : 0 < v := by rw [hvdef]; linarith
  have hqv : v ^ 2 + gdgCandidateB g * v + 1 = 0 := by
    rw [hvdef]
    linear_combination hq
  obtain ⟨hcv, hvc⟩ := real_root_bounds hc0 hc1 hv hqv hid
  have hru : (r : ℂ) = -((v : ℝ) : ℂ) := by
    rw [hvdef]
    push_cast
    ring
  rw [hru, tetranomial_neg_ofReal (by omega) _ _]
  have hcoeff : gdgCosCoeff g = 2 * c := rfl
  rw [Complex.ofReal_ne_zero, hcoeff]
  exact ne_of_lt (real_factor_neg hg hc0 hc1 hv hcv hvc)

/-- For `g ≥ 10` the candidate angle `arccos (-B/2)` is at most `π/g`. -/
private theorem arccos_candidate_le {g : ℕ} (hg : 10 ≤ g) :
    Real.arccos (-(gdgCandidateB g) / 2) ≤ Real.pi / (g:ℝ) := by
  have hgR : (10:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg
  have hgpos : (0:ℝ) < (g:ℝ) := by linarith
  have hpi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hc0 : 0 < Real.cos (2 * Real.pi / (g : ℝ)) := by
    have := gdgCosCoeff_pos (by omega : 5 ≤ g)
    unfold gdgCosCoeff at this
    linarith
  set c := Real.cos (2 * Real.pi / (g : ℝ)) with hcdef
  set s := Real.sin (Real.pi / (g:ℝ)) with hsdef
  set t := Real.sin (Real.pi / (2*(g:ℝ))) with htdef
  have hs2 : 1 - c = 2 * s ^ 2 := one_sub_cos_two_pi_div g (by omega)
  have hspos : 0 < s := sin_pi_div_pos (by omega)
  have hslt : s < Real.pi / (g:ℝ) := Real.sin_lt (by positivity)
  have htpos : 0 < t := by
    rw [htdef]
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hst : s ≤ 2 * t := by
    have harg : Real.pi / (g:ℝ) = 2 * (Real.pi / (2*(g:ℝ))) := by
      field_simp
    have hsplit : s = 2 * t * Real.cos (Real.pi / (2*(g:ℝ))) := by
      rw [hsdef, harg, Real.sin_two_mul, htdef]
    nlinarith [Real.cos_le_one (Real.pi / (2*(g:ℝ))), htpos]
  -- lower bound on `c`
  have hcbig : (4:ℝ) ≤ c * ((g:ℝ) - 1) := by
    have h1 : s ^ 2 ≤ (Real.pi / (g:ℝ)) ^ 2 := by nlinarith
    have hg2 : (100:ℝ) ≤ (g:ℝ)^2 := by nlinarith
    have h2 : (Real.pi / (g:ℝ)) ^ 2 ≤ Real.pi ^ 2 / 100 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hc8 : (0.8:ℝ) ≤ c := by
      norm_num
      linarith
    nlinarith
  -- the half-angle bound
  have hkey : Real.cos (Real.pi / (g:ℝ)) ≤ -(gdgCandidateB g) / 2 := by
    have hhalf : 1 - Real.cos (Real.pi / (g:ℝ)) = 2 * t ^ 2 := by
      have hx := one_sub_cos_eq_two_mul_sin_sq (Real.pi / (g:ℝ))
      rw [show Real.pi / (g:ℝ) / 2 = Real.pi / (2*(g:ℝ)) by ring] at hx
      rw [hx, htdef]
    have hB := gdgCandidateB_add_two (by omega : 5 ≤ g)
    rw [← hcdef, hs2] at hB
    have hden : 0 < c * ((g:ℝ) - 1) := by nlinarith
    have ht2pos : 0 < t ^ 2 := by positivity
    have hs4 : s ^ 2 ≤ 4 * t ^ 2 := by nlinarith
    have hRHS : 16 * t ^ 2 ≤ 4 * t ^ 2 * (c * ((g:ℝ) - 1)) := by nlinarith
    have hnum : 2 * s ^ 2 * (2 - (g:ℝ) * (2 * s ^ 2)) ≤ 4 * t ^ 2 * (c * ((g:ℝ) - 1)) := by
      rcases le_total (2 - (g:ℝ) * (2 * s ^ 2)) 0 with h | h
      · nlinarith [sq_nonneg s]
      · nlinarith [sq_nonneg s, mul_nonneg (sq_nonneg s) (Nat.cast_nonneg g : (0:ℝ) ≤ (g:ℝ))]
    have hBle : gdgCandidateB g + 2 ≤ 4 * t ^ 2 := by
      rw [hB]
      rw [div_le_iff₀ hden]
      nlinarith
    linarith
  calc Real.arccos (-(gdgCandidateB g) / 2)
      ≤ Real.arccos (Real.cos (Real.pi / (g:ℝ))) := Real.arccos_le_arccos hkey
    _ = Real.pi / (g:ℝ) := by
        apply Real.arccos_cos (by positivity)
        rw [div_le_iff₀ hgpos]
        nlinarith

/-- The real factor at a unit-circle candidate root is strictly negative. -/
private theorem circle_factor_neg {k : ℕ} {c x : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hx0 : 0 < x) (hx : ((k:ℝ)+2) * x / 2 ≤ Real.pi / 2) :
    2 * (2*c) * Real.cos (((k:ℝ)+2) * x / 2) - 4 * Real.cos ((k:ℝ) * x / 2) < 0 := by
  have hpi := Real.pi_pos
  have hknn : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hchi : 0 ≤ (k:ℝ) * x / 2 := by positivity
  have hlt : (k:ℝ) * x / 2 < ((k:ℝ)+2) * x / 2 := by nlinarith
  have hcosgt : Real.cos (((k:ℝ)+2) * x / 2) < Real.cos ((k:ℝ) * x / 2) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hchi (by linarith) hlt
  have hcosnn : 0 ≤ Real.cos (((k:ℝ)+2) * x / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, hx⟩
  nlinarith

/-- Target 5, unit-circle case. -/
private theorem tetranomial_ne_zero_of_circle_root {g : ℕ} (hg : 10 ≤ g) {u : ℂ}
    (hroot : u ^ 2 - (gdgCandidateB g : ℂ) * u + 1 = 0) :
    criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g) u ≠ 0 := by
  obtain ⟨hB1, hB2⟩ := gdgCandidateB_mem_Ioo_neg_two_zero hg
  have hgR : (10:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg
  have hc0 : 0 < Real.cos (2 * Real.pi / (g : ℝ)) := by
    have := gdgCosCoeff_pos (by omega : 5 ≤ g)
    unfold gdgCosCoeff at this
    linarith
  have hc1 : Real.cos (2 * Real.pi / (g : ℝ)) < 1 := cos_two_pi_div_lt_one (by omega)
  set w := -(gdgCandidateB g) / 2 with hwdef
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hw1 : w < 1 := by rw [hwdef]; linarith
  set phi := Real.arccos w with hphidef
  have hcosphi : Real.cos phi = w := Real.cos_arccos (by linarith) (by linarith)
  have hphi0 : 0 < phi := Real.arccos_pos.2 hw1
  have hphile : phi ≤ Real.pi / (g:ℝ) := arccos_candidate_le hg
  -- factor the quadratic over the unit circle
  have hexp1 : Complex.exp ((phi:ℝ) * Complex.I) * Complex.exp (((-phi : ℝ)) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    push_cast
    rw [show (phi:ℂ) * Complex.I + -(phi:ℂ) * Complex.I = 0 by ring, Complex.exp_zero]
  have hexpsum : Complex.exp ((phi:ℝ) * Complex.I) + Complex.exp (((-phi : ℝ)) * Complex.I)
      = -(gdgCandidateB g : ℂ) := by
    have hneg : Complex.exp (((-phi : ℝ)) * Complex.I)
        = (Complex.exp ((phi:ℝ) * Complex.I))⁻¹ := by
      rw [← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [hneg, ← two_cos_eq phi, hcosphi, hwdef]
    push_cast
    ring
  have hfac : (u + Complex.exp ((phi:ℝ) * Complex.I)) *
      (u + Complex.exp (((-phi : ℝ)) * Complex.I)) = 0 := by
    have : (u + Complex.exp ((phi:ℝ) * Complex.I)) *
        (u + Complex.exp (((-phi : ℝ)) * Complex.I))
        = u^2 + (Complex.exp ((phi:ℝ) * Complex.I) + Complex.exp (((-phi : ℝ)) * Complex.I)) * u
          + Complex.exp ((phi:ℝ) * Complex.I) * Complex.exp (((-phi : ℝ)) * Complex.I) := by ring
    rw [this, hexpsum, hexp1]
    linear_combination hroot
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
  have hcast2 : ((k+2 : ℕ) : ℝ) = (k:ℝ) + 2 := by push_cast; ring
  have hpsi : ((k:ℝ)+2) * phi / 2 ≤ Real.pi / 2 := by
    have hpos : (0:ℝ) < (k:ℝ) + 2 := by positivity
    rw [hcast2] at hphile
    have := (le_div_iff₀ hpos).mp hphile
    linarith
  have hfactor : 2 * (gdgCosCoeff (k+2)) * Real.cos (((k:ℝ)+2) * phi / 2)
      - 4 * Real.cos ((k:ℝ) * phi / 2) < 0 := by
    have hcf := circle_factor_neg (k := k) hc0 hc1 hphi0 hpsi
    unfold gdgCosCoeff
    exact hcf
  rcases mul_eq_zero.1 hfac with h | h
  · have hu : u = -(Complex.exp ((phi:ℝ) * Complex.I)) := by linear_combination h
    rw [hu, tetranomial_exp_form k (gdgCosCoeff (k+2)) phi]
    apply mul_ne_zero (Complex.exp_ne_zero _)
    have : (2*((gdgCosCoeff (k+2)):ℂ)*(Real.cos (((k:ℝ)+2)*phi/2) : ℂ)
        - 4*(Real.cos ((k:ℝ)*phi/2) : ℂ))
        = ((2 * (gdgCosCoeff (k+2)) * Real.cos (((k:ℝ)+2) * phi / 2)
            - 4 * Real.cos ((k:ℝ) * phi / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_ne_zero]
    exact ne_of_lt hfactor
  · have hu : u = -(Complex.exp (((-phi : ℝ)) * Complex.I)) := by linear_combination h
    rw [hu, tetranomial_exp_form k (gdgCosCoeff (k+2)) (-phi)]
    apply mul_ne_zero (Complex.exp_ne_zero _)
    have hcos1 : Real.cos (((k:ℝ)+2)*(-phi)/2) = Real.cos (((k:ℝ)+2)*phi/2) := by
      rw [show ((k:ℝ)+2)*(-phi)/2 = -(((k:ℝ)+2)*phi/2) by ring, Real.cos_neg]
    have hcos2 : Real.cos ((k:ℝ)*(-phi)/2) = Real.cos ((k:ℝ)*phi/2) := by
      rw [show ((k:ℝ))*(-phi)/2 = -(((k:ℝ))*phi/2) by ring, Real.cos_neg]
    rw [hcos1, hcos2]
    have : (2*((gdgCosCoeff (k+2)):ℂ)*(Real.cos (((k:ℝ)+2)*phi/2) : ℂ)
        - 4*(Real.cos ((k:ℝ)*phi/2) : ℂ))
        = ((2 * (gdgCosCoeff (k+2)) * Real.cos (((k:ℝ)+2) * phi / 2)
            - 4 * Real.cos ((k:ℝ) * phi / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_ne_zero]
    exact ne_of_lt hfactor

set_option linter.unusedVariables false in
/-- **Target 5.** Neither reciprocal root of
`X² - gdgCandidateB g · X + 1` is a root of the specialized critical
tetranomial, for any `g ≥ 5`. This is the remaining squarefreeness step.

The hypothesis `hu : u ≠ 0` is kept as stated, although it is not needed: it follows
from `hroot`. -/
theorem gdgCandidateB_not_tetranomial_root {g : ℕ} (hg : 5 ≤ g) {u : ℂ}
    (hu : u ≠ 0)
    (hroot : u ^ 2 - (gdgCandidateB g : ℂ) * u + 1 = 0) :
    criticalTetranomial g (gdgCosCoeff g : ℂ) ((-1 : ℂ) ^ g) u ≠ 0 := by
  rcases Nat.lt_or_ge 9 g with hg10 | hg9
  · exact tetranomial_ne_zero_of_circle_root (by omega) hroot
  · -- real roots
    have hB : gdgCandidateB g < -2 := gdgCandidateB_lt_neg_two hg hg9
    set B := gdgCandidateB g with hBdef
    have hdisc : (0:ℝ) ≤ B ^ 2 - 4 := by nlinarith
    set D := Real.sqrt (B ^ 2 - 4) with hDdef
    have hD2 : D ^ 2 = B ^ 2 - 4 := Real.sq_sqrt hdisc
    have hD0 : 0 ≤ D := Real.sqrt_nonneg _
    have hDlt : D < -B := by nlinarith
    have hfac : (u - (((B + D)/2 : ℝ) : ℂ)) * (u - (((B - D)/2 : ℝ) : ℂ)) = 0 := by
      have hD2C : ((D:ℂ)) ^ 2 = (B:ℂ) ^ 2 - 4 := by
        have : ((D ^ 2 : ℝ) : ℂ) = ((B ^ 2 - 4 : ℝ) : ℂ) := by rw [hD2]
        push_cast at this
        exact this
      push_cast
      linear_combination hroot - (1/4 : ℂ) * hD2C
    rcases mul_eq_zero.1 hfac with h | h
    · have hueq : u = (((B + D)/2 : ℝ) : ℂ) := by linear_combination h
      rw [hueq]
      refine tetranomial_ne_zero_of_real_root hg (by nlinarith) ?_
      rw [← hBdef]
      nlinarith [hD2]
    · have hueq : u = (((B - D)/2 : ℝ) : ℂ) := by linear_combination h
      rw [hueq]
      refine tetranomial_ne_zero_of_real_root hg (by nlinarith) ?_
      rw [← hBdef]
      nlinarith [hD2]

end GdgSquarefree
