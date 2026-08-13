/-
gd_g completion roadmap, Phase 4D — removal of the odd fixed reciprocal root
`u = 1`, and the parity-correct squarefree self-reciprocal residual.

Phase 4C (`RequestProject.GdgForcedQuadratic`) removed the forced monic
quadratic channel factor `Q_g = 1 + a X + X²` (`a = gdgCosCoeff g`) from the
critical polynomial `P_g` and produced the exact factorization
`Q_g * H_g = P_g` with `H_g = gdgChannelQuotientPolynomial g` of exact degree
`g - 2`, squarefree and nonzero.

This module evaluates that exact factorization at the two reciprocal fixed
points `u = 1` and `u = -1`, showing `H_g(1) = 0` exactly when `g` is odd,
`H_g(1) = 2` when `g` is even, and `H_g(-1) = -2` always. It removes the single
linear factor `X - 1` exactly in the odd case (and nothing in the even case),
proves the signed reverse identity `reverse H_g = C ((-1)^g) * H_g`, and
concludes that the resulting parity-correct residual is self-reciprocal, of
exact even degree `2 * ((g-2)/2)`, squarefree, and nonvanishing at both
reciprocal fixed points.

It does NOT construct the descended block polynomial (Phase 4E), and makes no
claim about a block degree, an exact root count, all roots real, lobe
uniqueness, critical-value separation, monodromy, or a Galois group.
-/
import Mathlib
import RequestProject.GdgForcedQuadratic

namespace GdgSquarefree

open Polynomial

/-- **Definition 1.** The odd fixed-factor quotient: the channel quotient with
the reciprocal fixed root `u = 1` divided out. -/
noncomputable def gdgOddResidualPolynomial (g : ℕ) : Polynomial ℂ :=
  gdgChannelQuotientPolynomial g /ₘ (Polynomial.X - Polynomial.C 1)

/-- **Definition 2.** The parity-correct reciprocal residual: for odd `g` the
fixed factor `X - 1` is removed, for even `g` nothing is removed. -/
noncomputable def gdgReciprocalResidualPolynomial
    (g : ℕ) : Polynomial ℂ :=
  if Odd g then gdgOddResidualPolynomial g
  else gdgChannelQuotientPolynomial g

/-! ### The cosine coefficient lies strictly between `0` and `2` -/

/-- For `g ≥ 5` the coefficient `a = 2 cos (2π/g)` is strictly below `2`. -/
private theorem gdgCosCoeff_lt_two {g : ℕ} (hg : 5 ≤ g) :
    gdgCosCoeff g < 2 := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hthlt : gdgTheta g < Real.pi / 2 := gdgTheta_lt_pi_div_two hg
  have hpi := Real.pi_pos
  have hcos : Real.cos (gdgTheta g) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ))
      (by linarith : gdgTheta g ≤ Real.pi) hth
    rwa [Real.cos_zero] at this
  have hval : gdgCosCoeff g = 2 * Real.cos (gdgTheta g) := by
    simp only [gdgCosCoeff, gdgTheta]
  rw [hval]
  linarith

/-! ### Evaluations of the exact Phase 4C factorization -/

private theorem gdgQuadratic_eval_one (g : ℕ) :
    (gdgQuadraticPolynomial g).eval 1 = (gdgCosCoeff g : ℂ) + 2 := by
  simp only [gdgQuadraticPolynomial, eval_add, eval_mul, eval_pow, eval_C,
    eval_X, eval_one]
  ring

private theorem gdgQuadratic_eval_neg_one (g : ℕ) :
    (gdgQuadraticPolynomial g).eval (-1) = 2 - (gdgCosCoeff g : ℂ) := by
  simp only [gdgQuadraticPolynomial, eval_add, eval_mul, eval_pow, eval_C,
    eval_X, eval_one]
  ring

private theorem gdgQuadratic_eval_one_ne_zero {g : ℕ} (hg : 5 ≤ g) :
    (gdgQuadraticPolynomial g).eval 1 ≠ 0 := by
  have hpos : 0 < gdgCosCoeff g := gdgCosCoeff_pos hg
  rw [gdgQuadratic_eval_one]
  have : ((gdgCosCoeff g : ℝ) : ℂ) + 2 = ((gdgCosCoeff g + 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [this]
  exact Complex.ofReal_ne_zero.mpr (by linarith)

private theorem gdgQuadratic_eval_neg_one_ne_zero {g : ℕ} (hg : 5 ≤ g) :
    (gdgQuadraticPolynomial g).eval (-1) ≠ 0 := by
  have hlt : gdgCosCoeff g < 2 := gdgCosCoeff_lt_two hg
  rw [gdgQuadratic_eval_neg_one]
  have : (2 : ℂ) - ((gdgCosCoeff g : ℝ) : ℂ) = ((2 - gdgCosCoeff g : ℝ) : ℂ) := by
    push_cast; ring
  rw [this]
  exact Complex.ofReal_ne_zero.mpr (by linarith)

private theorem gdgCritical_eval_one (g : ℕ) :
    (gdgCriticalPolynomial g).eval 1 =
      ((gdgCosCoeff g : ℂ) + 2) * (1 + (-1 : ℂ) ^ g) := by
  simp only [gdgCriticalPolynomial, eval_add, eval_mul, eval_pow, eval_C,
    eval_X, one_pow]
  ring

private theorem gdgCritical_eval_neg_one {g : ℕ} (hg : 5 ≤ g) :
    (gdgCriticalPolynomial g).eval (-1) =
      2 * ((gdgCosCoeff g : ℂ) - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 5 := ⟨g - 5, by omega⟩
  have hidx : n + 5 - 1 = n + 4 := by omega
  have h4 : ((-1 : ℂ)) ^ (n + 4) = ((-1 : ℂ)) ^ n := by
    rw [pow_add]
    norm_num
  have h5 : ((-1 : ℂ)) ^ (n + 5) = -((-1 : ℂ)) ^ n := by
    rw [pow_add]
    norm_num
  have hsq : ((-1 : ℂ)) ^ n * ((-1 : ℂ)) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  simp only [gdgCriticalPolynomial, eval_add, eval_mul, eval_pow, eval_C,
    eval_X, hidx, h4, h5]
  linear_combination ((gdgCosCoeff (n + 5) : ℂ) - 2) * hsq

/-! ### Targets 1–3: the two reciprocal fixed points -/

/-- **Target 1.** For odd `g ≥ 5` the reciprocal fixed point `u = 1` is a root
of the channel quotient. -/
theorem gdgChannelQuotient_eval_one_of_odd
    {g : ℕ} (hg : 5 ≤ g) (hOdd : Odd g) :
    (gdgChannelQuotientPolynomial g).eval 1 = 0 := by
  have hfac := gdgCriticalPolynomial_eval_factorization hg 1
  rw [gdgCritical_eval_one, hOdd.neg_one_pow] at hfac
  have hQ := gdgQuadratic_eval_one_ne_zero hg
  have : (gdgQuadraticPolynomial g).eval 1 *
      (gdgChannelQuotientPolynomial g).eval 1 = 0 := by
    rw [← hfac]; ring
  exact (mul_eq_zero.mp this).resolve_left hQ

/-- **Target 2.** For even `g ≥ 5` the channel quotient takes the value `2` at
the reciprocal fixed point `u = 1`. -/
theorem gdgChannelQuotient_eval_one_of_even
    {g : ℕ} (hg : 5 ≤ g) (hEven : Even g) :
    (gdgChannelQuotientPolynomial g).eval 1 = 2 := by
  have hfac := gdgCriticalPolynomial_eval_factorization hg 1
  rw [gdgCritical_eval_one, hEven.neg_one_pow, gdgQuadratic_eval_one] at hfac
  have hQ : ((gdgCosCoeff g : ℂ) + 2) ≠ 0 := by
    have := gdgQuadratic_eval_one_ne_zero hg
    rwa [gdgQuadratic_eval_one] at this
  refine mul_left_cancel₀ hQ ?_
  rw [← hfac]
  ring

/-- **Target 3.** For every `g ≥ 5` the channel quotient takes the value `-2` at
the reciprocal fixed point `u = -1`; in particular `u = -1` is never a root. -/
theorem gdgChannelQuotient_eval_neg_one
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgChannelQuotientPolynomial g).eval (-1) = -2 := by
  have hfac := gdgCriticalPolynomial_eval_factorization hg (-1)
  rw [gdgCritical_eval_neg_one hg, gdgQuadratic_eval_neg_one] at hfac
  have hQ : (2 - (gdgCosCoeff g : ℂ)) ≠ 0 := by
    have := gdgQuadratic_eval_neg_one_ne_zero hg
    rwa [gdgQuadratic_eval_neg_one] at this
  refine mul_left_cancel₀ hQ ?_
  rw [← hfac]
  ring

/-! ### Targets 4–5: exact removal of the odd fixed factor -/

/-- **Target 4.** For odd `g ≥ 5` the monic linear factor `X - 1` splits off the
channel quotient exactly. -/
theorem gdgXSubOne_mul_oddResidual
    {g : ℕ} (hg : 5 ≤ g) (hOdd : Odd g) :
    (Polynomial.X - Polynomial.C 1) * gdgOddResidualPolynomial g =
      gdgChannelQuotientPolynomial g := by
  rw [gdgOddResidualPolynomial]
  exact mul_divByMonic_eq_iff_isRoot.mpr
    (gdgChannelQuotient_eval_one_of_odd hg hOdd)

/-- **Target 5.** For odd `g ≥ 5` the odd residual has exact degree `g - 3`. -/
theorem gdgOddResidualPolynomial_natDegree
    {g : ℕ} (hg : 5 ≤ g) (hOdd : Odd g) :
    (gdgOddResidualPolynomial g).natDegree = g - 3 := by
  have hfac := gdgXSubOne_mul_oddResidual hg hOdd
  have hHne := gdgChannelQuotientPolynomial_ne_zero hg
  have hJne : gdgOddResidualPolynomial g ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfac
    exact hHne hfac.symm
  have hLne : (Polynomial.X - Polynomial.C (1 : ℂ)) ≠ 0 := X_sub_C_ne_zero 1
  have hdeg := natDegree_mul hLne hJne
  rw [hfac, gdgChannelQuotientPolynomial_natDegree hg, natDegree_X_sub_C] at hdeg
  omega

/-! ### Target 6: the signed reciprocal identity -/

/-- `(-1)^g` squares to one, as a constant polynomial. -/
private theorem gdgSignC_sq (g : ℕ) :
    (Polynomial.C ((-1 : ℂ) ^ g)) * (Polynomial.C ((-1 : ℂ) ^ g)) = 1 := by
  rw [← C_mul, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- The critical polynomial reverses to `C ((-1)^g)` times itself. -/
private theorem gdgCriticalPolynomial_reverse {g : ℕ} (hg : 5 ≤ g) :
    (gdgCriticalPolynomial g).reverse =
      Polynomial.C ((-1 : ℂ) ^ g) * gdgCriticalPolynomial g := by
  have hP : gdgCriticalPolynomial g =
      C (gdgCosCoeff g : ℂ) * X ^ 0 + C 2 * X ^ 1 +
        C (2 * ((-1 : ℂ) ^ g)) * X ^ (g - 1) +
        C (((-1 : ℂ) ^ g) * (gdgCosCoeff g : ℂ)) * X ^ g := by
    unfold gdgCriticalPolynomial
    ring
  have h0 : revAt g 0 = g := by simp
  have h1 : revAt g 1 = g - 1 := revAt_le (by omega)
  have h2 : revAt g (g - 1) = 1 := by
    rw [revAt_le (by omega)]
    omega
  have h3 : revAt g g = 0 := by simp
  have hsq := gdgSignC_sq g
  rw [Polynomial.reverse, gdgCriticalPolynomial_natDegree hg]
  conv_lhs => rw [hP]
  rw [reflect_add, reflect_add, reflect_add, reflect_C_mul_X_pow,
    reflect_C_mul_X_pow, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
    h0, h1, h2, h3]
  conv_rhs => rw [hP]
  rw [C_mul, C_mul]
  linear_combination (-(C (gdgCosCoeff g : ℂ)) * X ^ g -
    C (2 : ℂ) * X ^ (g - 1)) * hsq

/-- The quadratic channel factor is palindromic: it reverses to itself. -/
private theorem gdgQuadraticPolynomial_reverse {g : ℕ} (hg : 5 ≤ g) :
    (gdgQuadraticPolynomial g).reverse = gdgQuadraticPolynomial g := by
  have hQ : gdgQuadraticPolynomial g =
      C (1 : ℂ) * X ^ 0 + C (gdgCosCoeff g : ℂ) * X ^ 1 + C (1 : ℂ) * X ^ 2 := by
    unfold gdgQuadraticPolynomial
    simp
  have h0 : revAt 2 0 = 2 := by simp
  have h1 : revAt 2 1 = 1 := revAt_le (by omega)
  have h2 : revAt 2 2 = 0 := by simp
  rw [Polynomial.reverse, gdgQuadraticPolynomial_natDegree hg]
  conv_lhs => rw [hQ]
  rw [reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
    reflect_C_mul_X_pow, h0, h1, h2]
  conv_rhs => rw [hQ]
  ring

/-- **Target 6.** The channel quotient satisfies the signed reciprocal identity:
it is self-reciprocal for even `g` and anti-reciprocal for odd `g`. -/
theorem gdgChannelQuotientPolynomial_reverse
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgChannelQuotientPolynomial g).reverse =
      Polynomial.C ((-1 : ℂ) ^ g) *
        gdgChannelQuotientPolynomial g := by
  have hfac := gdgQuadratic_mul_channelQuotient hg
  have hQne : gdgQuadraticPolynomial g ≠ 0 :=
    (gdgQuadraticPolynomial_monic hg).ne_zero
  refine mul_left_cancel₀ hQne ?_
  calc gdgQuadraticPolynomial g * (gdgChannelQuotientPolynomial g).reverse
      = (gdgQuadraticPolynomial g).reverse *
          (gdgChannelQuotientPolynomial g).reverse := by
        rw [gdgQuadraticPolynomial_reverse hg]
    _ = (gdgQuadraticPolynomial g * gdgChannelQuotientPolynomial g).reverse := by
        rw [reverse_mul_of_domain]
    _ = (gdgCriticalPolynomial g).reverse := by rw [hfac]
    _ = Polynomial.C ((-1 : ℂ) ^ g) * gdgCriticalPolynomial g :=
        gdgCriticalPolynomial_reverse hg
    _ = gdgQuadraticPolynomial g *
          (Polynomial.C ((-1 : ℂ) ^ g) * gdgChannelQuotientPolynomial g) := by
        rw [← hfac]; ring

/-! ### Target 7: the odd residual is self-reciprocal -/

/-- The monic linear fixed factor is anti-reciprocal. -/
private theorem gdgXSubOne_reverse :
    (Polynomial.X - Polynomial.C (1 : ℂ)).reverse =
      -(Polynomial.X - Polynomial.C (1 : ℂ)) := by
  have hL : (X - C (1 : ℂ)) = C (-1 : ℂ) * X ^ 0 + C (1 : ℂ) * X ^ 1 := by
    simp
    ring
  have h0 : revAt 1 0 = 1 := by simp
  have h1 : revAt 1 1 = 0 := by simp
  rw [Polynomial.reverse, natDegree_X_sub_C]
  conv_lhs => rw [hL]
  rw [reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow, h0, h1]
  simp
  ring

/-- **Target 7.** For odd `g ≥ 5` the odd residual is self-reciprocal. -/
theorem gdgOddResidualPolynomial_reverse
    {g : ℕ} (hg : 5 ≤ g) (hOdd : Odd g) :
    (gdgOddResidualPolynomial g).reverse =
      gdgOddResidualPolynomial g := by
  have hfac := gdgXSubOne_mul_oddResidual hg hOdd
  have hrev := gdgChannelQuotientPolynomial_reverse hg
  rw [hOdd.neg_one_pow] at hrev
  have hL : (Polynomial.X - Polynomial.C (1 : ℂ)) ≠ 0 := X_sub_C_ne_zero 1
  refine mul_left_cancel₀ (neg_ne_zero.mpr hL) ?_
  calc -(Polynomial.X - Polynomial.C (1 : ℂ)) *
        (gdgOddResidualPolynomial g).reverse
      = (Polynomial.X - Polynomial.C (1 : ℂ)).reverse *
          (gdgOddResidualPolynomial g).reverse := by
        rw [gdgXSubOne_reverse]
    _ = ((Polynomial.X - Polynomial.C (1 : ℂ)) *
          gdgOddResidualPolynomial g).reverse := by
        rw [reverse_mul_of_domain]
    _ = (gdgChannelQuotientPolynomial g).reverse := by rw [hfac]
    _ = Polynomial.C (-1 : ℂ) * gdgChannelQuotientPolynomial g := hrev
    _ = -(Polynomial.X - Polynomial.C (1 : ℂ)) *
          gdgOddResidualPolynomial g := by
        rw [← hfac]
        simp
        ring

/-! ### Targets 8–12: the parity-correct residual -/

/-- **Target 8.** The parity-correct residual has exact even degree
`2 * ((g-2)/2)`: degree `2` at `g = 5` and degree `4` at `g = 6`. -/
theorem gdgReciprocalResidualPolynomial_natDegree
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgReciprocalResidualPolynomial g).natDegree =
      2 * ((g - 2) / 2) := by
  by_cases hOdd : Odd g
  · obtain ⟨k, hk⟩ := hOdd
    rw [gdgReciprocalResidualPolynomial, if_pos ⟨k, hk⟩,
      gdgOddResidualPolynomial_natDegree hg ⟨k, hk⟩]
    omega
  · have hEven : Even g := Nat.not_odd_iff_even.mp hOdd
    obtain ⟨k, hk⟩ := hEven
    rw [gdgReciprocalResidualPolynomial, if_neg hOdd,
      gdgChannelQuotientPolynomial_natDegree hg]
    omega

/-- **Target 9.** The parity-correct residual is self-reciprocal. -/
theorem gdgReciprocalResidualPolynomial_reverse
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgReciprocalResidualPolynomial g).reverse =
      gdgReciprocalResidualPolynomial g := by
  by_cases hOdd : Odd g
  · rw [gdgReciprocalResidualPolynomial, if_pos hOdd]
    exact gdgOddResidualPolynomial_reverse hg hOdd
  · have hEven : Even g := Nat.not_odd_iff_even.mp hOdd
    rw [gdgReciprocalResidualPolynomial, if_neg hOdd,
      gdgChannelQuotientPolynomial_reverse hg, hEven.neg_one_pow, map_one,
      one_mul]

/-- **Target 10.** The parity-correct residual is squarefree. -/
theorem gdgReciprocalResidualPolynomial_squarefree
    {g : ℕ} (hg : 5 ≤ g) :
    Squarefree (gdgReciprocalResidualPolynomial g) := by
  by_cases hOdd : Odd g
  · rw [gdgReciprocalResidualPolynomial, if_pos hOdd]
    have hsq := gdgChannelQuotientPolynomial_squarefree hg
    rw [← gdgXSubOne_mul_oddResidual hg hOdd] at hsq
    exact hsq.of_mul_right
  · rw [gdgReciprocalResidualPolynomial, if_neg hOdd]
    exact gdgChannelQuotientPolynomial_squarefree hg

/-- **Target 11.** The reciprocal fixed point `u = 1` is not a root of the
parity-correct residual. -/
theorem gdgReciprocalResidualPolynomial_eval_one_ne_zero
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgReciprocalResidualPolynomial g).eval 1 ≠ 0 := by
  by_cases hOdd : Odd g
  · rw [gdgReciprocalResidualPolynomial, if_pos hOdd]
    intro hzero
    have hsq := gdgChannelQuotientPolynomial_squarefree hg
    rw [← gdgXSubOne_mul_oddResidual hg hOdd] at hsq
    have hrel : IsRelPrime (Polynomial.X - Polynomial.C (1 : ℂ))
        (gdgOddResidualPolynomial g) := (squarefree_mul_iff.mp hsq).1
    have hdvd : (Polynomial.X - Polynomial.C (1 : ℂ)) ∣
        gdgOddResidualPolynomial g := dvd_iff_isRoot.mpr hzero
    exact not_isUnit_X_sub_C (1 : ℂ) (hrel dvd_rfl hdvd)
  · have hEven : Even g := Nat.not_odd_iff_even.mp hOdd
    rw [gdgReciprocalResidualPolynomial, if_neg hOdd,
      gdgChannelQuotient_eval_one_of_even hg hEven]
    norm_num

/-- **Target 12.** The reciprocal fixed point `u = -1` is not a root of the
parity-correct residual: the factor `X + 1` is never removed. -/
theorem gdgReciprocalResidualPolynomial_eval_neg_one_ne_zero
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgReciprocalResidualPolynomial g).eval (-1) ≠ 0 := by
  by_cases hOdd : Odd g
  · rw [gdgReciprocalResidualPolynomial, if_pos hOdd]
    have hfac := congrArg (fun p : Polynomial ℂ => p.eval (-1))
      (gdgXSubOne_mul_oddResidual hg hOdd)
    simp only [eval_mul, eval_sub, eval_X, eval_C,
      gdgChannelQuotient_eval_neg_one hg] at hfac
    have hval : (gdgOddResidualPolynomial g).eval (-1) = 1 := by
      have h2 : ((-1 : ℂ) - 1) ≠ 0 := by norm_num
      refine mul_left_cancel₀ h2 ?_
      rw [hfac]
      ring
    rw [hval]
    norm_num
  · rw [gdgReciprocalResidualPolynomial, if_neg hOdd,
      gdgChannelQuotient_eval_neg_one hg]
    norm_num

end GdgSquarefree
