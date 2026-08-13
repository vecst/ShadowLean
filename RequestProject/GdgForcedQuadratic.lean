/-
gd_g completion roadmap, Phase 4C — exact removal of the forced quadratic
channel factor and the degree-`g-2` channel quotient.

Phase 4B (`RequestProject.GdgCriticalPolynomial`) realized the critical
tetranomial as a genuine `Polynomial ℂ`, proved its exact degree `g` for
`g ≥ 5`, and proved that it is separable, hence squarefree. Phase 3B
(`RequestProject.GdgCriticalBridge`) supplied the unit-circle coordinate
`gdgUnitCircle φ = exp (i φ)`.

This module proves that the declared monic quadratic channel factor
`gdgQuadraticPolynomial g = 1 + a X + X²` (with `a = gdgCosCoeff g = 2 cos θ_g`,
`θ_g = 2π/g`) is an EXACT factor of the critical polynomial, defines the monic
quotient `P /ₘ Q`, certifies its exact degree `g - 2`, its nonvanishing, and its
squarefreeness, proves that the two factors are coprime, and exposes the
evaluated factorization together with the nonchannel root equivalence.

The two forced roots are the unit-circle points
`gdgUnitCircle (π - θ_g)` and `gdgUnitCircle (θ_g - π)`; they are distinct
(opposite nonzero imaginary parts), their product is `1`, their sum is `-a`, and
each of them satisfies `u ^ g = (-1) ^ g` because `g θ_g = 2π`. Both are
therefore roots of `Q` and of the critical polynomial, and coprimality of the
two linear factors upgrades the two individual divisibilities to divisibility by
the product — the multiplicity bookkeeping is explicit, one root alone would not
suffice.

This completes forced quadratic removal and the degree-`g-2` channel quotient.
It does NOT remove the odd `u = 1` fixed factor, does NOT perform any
reciprocal/palindromic or block descent, and makes no claim about block degree,
root count, all roots real, lobe uniqueness, critical-value separation,
monodromy, or a Galois group.
-/
import Mathlib
import RequestProject.GdgCriticalPolynomial
import RequestProject.GdgCriticalBridge

namespace GdgSquarefree

open Polynomial

/-- **Definition.** The monic channel quotient obtained by dividing the critical
polynomial by the declared monic quadratic channel factor. -/
noncomputable def gdgChannelQuotientPolynomial (g : ℕ) : Polynomial ℂ :=
  gdgCriticalPolynomial g /ₘ gdgQuadraticPolynomial g

/-! ### The two forced unit-circle roots -/

/-- The two forced roots are reciprocal: their product is one. -/
private theorem gdgForcedRoots_mul_eq_one (g : ℕ) :
    gdgUnitCircle (Real.pi - gdgTheta g) *
        gdgUnitCircle (gdgTheta g - Real.pi) = 1 := by
  simp only [gdgUnitCircle, ← Complex.exp_add]
  rw [show ((Real.pi - gdgTheta g : ℝ) : ℂ) * Complex.I +
        ((gdgTheta g - Real.pi : ℝ) : ℂ) * Complex.I = 0 by push_cast; ring]
  exact Complex.exp_zero

/-- The two forced roots sum to `-gdgCosCoeff g`. -/
private theorem gdgForcedRoots_add (g : ℕ) :
    gdgUnitCircle (Real.pi - gdgTheta g) +
        gdgUnitCircle (gdgTheta g - Real.pi) = -(gdgCosCoeff g : ℂ) := by
  have hinv : gdgUnitCircle (gdgTheta g - Real.pi) =
      (gdgUnitCircle (Real.pi - gdgTheta g))⁻¹ :=
    eq_inv_of_mul_eq_one_right (gdgForcedRoots_mul_eq_one g)
  rw [hinv, gdgUnitCircle_add_inv_eq_blockCoord]
  simp only [gdgBlockCoord, gdgCosCoeff, gdgTheta, Real.cos_pi_sub]
  push_cast
  ring

/-- The forced root `exp (i (π - θ_g))` satisfies `u ^ g = (-1) ^ g`, because
`g θ_g = 2π`. -/
private theorem gdgForcedRoot_pow_left {g : ℕ} (hg : 1 ≤ g) :
    gdgUnitCircle (Real.pi - gdgTheta g) ^ g = (-1 : ℂ) ^ g := by
  have hg0 : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hth : (g : ℝ) * gdgTheta g = 2 * Real.pi := by
    unfold gdgTheta
    field_simp
  have hthC : (g : ℂ) * ((gdgTheta g : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hth
  have h1 : gdgUnitCircle (Real.pi - gdgTheta g) ^ g =
      Complex.exp ((g : ℂ) * (((Real.pi - gdgTheta g : ℝ) : ℂ) * Complex.I)) := by
    rw [gdgUnitCircle, ← Complex.exp_nat_mul]
  have h2 : (g : ℂ) * (((Real.pi - gdgTheta g : ℝ) : ℂ) * Complex.I) =
      (g : ℂ) * ((Real.pi : ℂ) * Complex.I) -
        2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    linear_combination (-Complex.I) * hthC
  rw [h1, h2, Complex.exp_sub, Complex.exp_nat_mul, Complex.exp_pi_mul_I,
    Complex.exp_two_pi_mul_I, div_one]

/-- `(-1) ^ g` squares to one. -/
private theorem gdgForcedSign_sq (g : ℕ) :
    ((-1 : ℂ) ^ g) * ((-1 : ℂ) ^ g) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- The forced root `exp (i (θ_g - π))` also satisfies `u ^ g = (-1) ^ g`. -/
private theorem gdgForcedRoot_pow_right {g : ℕ} (hg : 1 ≤ g) :
    gdgUnitCircle (gdgTheta g - Real.pi) ^ g = (-1 : ℂ) ^ g := by
  have hprod : (gdgUnitCircle (Real.pi - gdgTheta g) ^ g) *
      (gdgUnitCircle (gdgTheta g - Real.pi) ^ g) = 1 := by
    rw [← mul_pow, gdgForcedRoots_mul_eq_one, one_pow]
  rw [gdgForcedRoot_pow_left hg] at hprod
  linear_combination ((-1 : ℂ) ^ g) * hprod -
    (gdgUnitCircle (gdgTheta g - Real.pi) ^ g) * gdgForcedSign_sq g

/-- The two forced roots are distinct: their imaginary parts are `sin θ_g > 0`
and `-sin θ_g < 0`. -/
private theorem gdgForcedRoots_ne {g : ℕ} (hg : 5 ≤ g) :
    gdgUnitCircle (Real.pi - gdgTheta g) ≠
      gdgUnitCircle (gdgTheta g - Real.pi) := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hlt : gdgTheta g < Real.pi / 2 := gdgTheta_lt_pi_div_two hg
  have hpi := Real.pi_pos
  have hsin : 0 < Real.sin (gdgTheta g) :=
    Real.sin_pos_of_pos_of_lt_pi hth (by linarith)
  intro h
  have him := congrArg Complex.im h
  rw [gdgUnitCircle, gdgUnitCircle, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_im, Real.sin_pi_sub,
    show gdgTheta g - Real.pi = -(Real.pi - gdgTheta g) by ring,
    Real.sin_neg, Real.sin_pi_sub] at him
  linarith

/-! ### Both forced roots are roots of the quadratic and of the critical
polynomial -/

private theorem gdgQuadratic_isRoot_left (g : ℕ) :
    (gdgQuadraticPolynomial g).eval
      (gdgUnitCircle (Real.pi - gdgTheta g)) = 0 := by
  have hmul := gdgForcedRoots_mul_eq_one g
  have hadd := gdgForcedRoots_add g
  simp only [gdgQuadraticPolynomial, eval_add, eval_mul, eval_pow, eval_C,
    eval_X, eval_one]
  linear_combination (gdgUnitCircle (Real.pi - gdgTheta g)) * hadd - hmul

private theorem gdgQuadratic_isRoot_right (g : ℕ) :
    (gdgQuadraticPolynomial g).eval
      (gdgUnitCircle (gdgTheta g - Real.pi)) = 0 := by
  have hmul := gdgForcedRoots_mul_eq_one g
  have hadd := gdgForcedRoots_add g
  simp only [gdgQuadraticPolynomial, eval_add, eval_mul, eval_pow, eval_C,
    eval_X, eval_one]
  linear_combination (gdgUnitCircle (gdgTheta g - Real.pi)) * hadd - hmul

private theorem gdgCritical_isRoot_left {g : ℕ} (hg : 5 ≤ g) :
    (gdgCriticalPolynomial g).eval
      (gdgUnitCircle (Real.pi - gdgTheta g)) = 0 := by
  have hne := gdgUnitCircle_ne_zero (Real.pi - gdgTheta g)
  have hadd := gdgForcedRoots_add g
  have hpow := gdgForcedRoot_pow_left (g := g) (by omega)
  have hsq := gdgForcedSign_sq g
  have hstep : gdgUnitCircle (Real.pi - gdgTheta g) ^ (g - 1) *
      gdgUnitCircle (Real.pi - gdgTheta g) =
        gdgUnitCircle (Real.pi - gdgTheta g) ^ g := by
    rw [← pow_succ]
    congr 1
    omega
  have hsub : gdgUnitCircle (Real.pi - gdgTheta g) ^ (g - 1) =
      (-1 : ℂ) ^ g * gdgUnitCircle (gdgTheta g - Real.pi) := by
    refine mul_right_cancel₀ hne ?_
    rw [hstep, hpow]
    linear_combination (-((-1 : ℂ) ^ g)) * gdgForcedRoots_mul_eq_one g
  simp only [gdgCriticalPolynomial, eval_add, eval_mul, eval_pow, eval_C,
    eval_X]
  rw [hsub, hpow]
  linear_combination (2 : ℂ) * hadd +
    (2 * gdgUnitCircle (gdgTheta g - Real.pi) + (gdgCosCoeff g : ℂ)) * hsq

private theorem gdgCritical_isRoot_right {g : ℕ} (hg : 5 ≤ g) :
    (gdgCriticalPolynomial g).eval
      (gdgUnitCircle (gdgTheta g - Real.pi)) = 0 := by
  have hne := gdgUnitCircle_ne_zero (gdgTheta g - Real.pi)
  have hadd := gdgForcedRoots_add g
  have hpow := gdgForcedRoot_pow_right (g := g) (by omega)
  have hsq := gdgForcedSign_sq g
  have hstep : gdgUnitCircle (gdgTheta g - Real.pi) ^ (g - 1) *
      gdgUnitCircle (gdgTheta g - Real.pi) =
        gdgUnitCircle (gdgTheta g - Real.pi) ^ g := by
    rw [← pow_succ]
    congr 1
    omega
  have hsub : gdgUnitCircle (gdgTheta g - Real.pi) ^ (g - 1) =
      (-1 : ℂ) ^ g * gdgUnitCircle (Real.pi - gdgTheta g) := by
    refine mul_right_cancel₀ hne ?_
    rw [hstep, hpow]
    linear_combination (-((-1 : ℂ) ^ g)) * gdgForcedRoots_mul_eq_one g
  simp only [gdgCriticalPolynomial, eval_add, eval_mul, eval_pow, eval_C,
    eval_X]
  rw [hsub, hpow]
  linear_combination (2 : ℂ) * hadd +
    (2 * gdgUnitCircle (Real.pi - gdgTheta g) + (gdgCosCoeff g : ℂ)) * hsq

/-- The quadratic channel factor is the product of the two distinct forced
linear factors. -/
private theorem gdgQuadratic_eq_linear_mul (g : ℕ) :
    gdgQuadraticPolynomial g =
      (X - C (gdgUnitCircle (Real.pi - gdgTheta g))) *
        (X - C (gdgUnitCircle (gdgTheta g - Real.pi))) := by
  have h1 : (C (gdgUnitCircle (Real.pi - gdgTheta g)) : Polynomial ℂ) +
      C (gdgUnitCircle (gdgTheta g - Real.pi)) = -C ((gdgCosCoeff g : ℂ)) := by
    rw [← C_add, gdgForcedRoots_add, map_neg]
  have h2 : (C (gdgUnitCircle (Real.pi - gdgTheta g)) : Polynomial ℂ) *
      C (gdgUnitCircle (gdgTheta g - Real.pi)) = 1 := by
    rw [← C_mul, gdgForcedRoots_mul_eq_one, map_one]
  unfold gdgQuadraticPolynomial
  linear_combination (X : Polynomial ℂ) * h1 - h2

/-! ### Targets -/

/-- **Target 1.** The declared monic quadratic channel factor is an exact factor
of the critical polynomial for `g ≥ 5`. Both forced roots are tracked: the two
linear factors are coprime (the roots are distinct), so the product divides. -/
theorem gdgQuadraticPolynomial_dvd_critical
    {g : ℕ} (hg : 5 ≤ g) :
    gdgQuadraticPolynomial g ∣ gdgCriticalPolynomial g := by
  have hcop : IsCoprime (X - C (gdgUnitCircle (Real.pi - gdgTheta g)))
      (X - C (gdgUnitCircle (gdgTheta g - Real.pi))) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (gdgForcedRoots_ne hg)))
  have hd1 : (X - C (gdgUnitCircle (Real.pi - gdgTheta g))) ∣
      gdgCriticalPolynomial g :=
    dvd_iff_isRoot.mpr (gdgCritical_isRoot_left hg)
  have hd2 : (X - C (gdgUnitCircle (gdgTheta g - Real.pi))) ∣
      gdgCriticalPolynomial g :=
    dvd_iff_isRoot.mpr (gdgCritical_isRoot_right hg)
  rw [gdgQuadratic_eq_linear_mul]
  exact hcop.mul_dvd hd1 hd2

/-- **Target 2.** Exact factorization of the critical polynomial into the monic
quadratic channel factor times the monic channel quotient. No scalar
normalization factor appears. -/
theorem gdgQuadratic_mul_channelQuotient
    {g : ℕ} (hg : 5 ≤ g) :
    gdgQuadraticPolynomial g * gdgChannelQuotientPolynomial g =
      gdgCriticalPolynomial g := by
  have hmon := gdgQuadraticPolynomial_monic hg
  have hmod : gdgCriticalPolynomial g %ₘ gdgQuadraticPolynomial g = 0 :=
    (modByMonic_eq_zero_iff_dvd hmon).mpr (gdgQuadraticPolynomial_dvd_critical hg)
  have hid := modByMonic_add_div (gdgCriticalPolynomial g) (gdgQuadraticPolynomial g)
  rw [hmod, zero_add] at hid
  exact hid

/-- **Target 3.** The channel quotient has exact degree `g - 2`; at `g = 5` this
is degree `3`. -/
theorem gdgChannelQuotientPolynomial_natDegree
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgChannelQuotientPolynomial g).natDegree = g - 2 := by
  rw [gdgChannelQuotientPolynomial,
    natDegree_divByMonic _ (gdgQuadraticPolynomial_monic hg),
    gdgCriticalPolynomial_natDegree hg, gdgQuadraticPolynomial_natDegree hg]

/-- **Target 4.** The channel quotient is nonzero for `g ≥ 5`. -/
theorem gdgChannelQuotientPolynomial_ne_zero
    {g : ℕ} (hg : 5 ≤ g) :
    gdgChannelQuotientPolynomial g ≠ 0 := by
  intro h
  have hd : (gdgChannelQuotientPolynomial g).natDegree = g - 2 :=
    gdgChannelQuotientPolynomial_natDegree hg
  rw [h, natDegree_zero] at hd
  omega

/-- **Target 5.** The quadratic channel factor is squarefree, inherited from
squarefreeness of the critical polynomial. -/
theorem gdgQuadraticPolynomial_squarefree
    {g : ℕ} (hg : 5 ≤ g) :
    Squarefree (gdgQuadraticPolynomial g) := by
  have hsq := gdgCriticalPolynomial_squarefree hg
  rw [← gdgQuadratic_mul_channelQuotient hg] at hsq
  exact hsq.of_mul_left

/-- **Target 6.** The channel quotient is squarefree, inherited from
squarefreeness of the critical polynomial. -/
theorem gdgChannelQuotientPolynomial_squarefree
    {g : ℕ} (hg : 5 ≤ g) :
    Squarefree (gdgChannelQuotientPolynomial g) := by
  have hsq := gdgCriticalPolynomial_squarefree hg
  rw [← gdgQuadratic_mul_channelQuotient hg] at hsq
  exact hsq.of_mul_right

/-- **Target 7.** The quadratic channel factor and the channel quotient are
coprime. -/
theorem gdgQuadratic_channelQuotient_isCoprime
    {g : ℕ} (hg : 5 ≤ g) :
    IsCoprime (gdgQuadraticPolynomial g)
      (gdgChannelQuotientPolynomial g) := by
  have hsq := gdgCriticalPolynomial_squarefree hg
  rw [← gdgQuadratic_mul_channelQuotient hg] at hsq
  exact (squarefree_mul_iff.mp hsq).1.isCoprime

/-- **Target 8.** The evaluated factorization of the critical polynomial. -/
theorem gdgCriticalPolynomial_eval_factorization
    {g : ℕ} (hg : 5 ≤ g) (u : ℂ) :
    (gdgCriticalPolynomial g).eval u =
      (gdgQuadraticPolynomial g).eval u *
        (gdgChannelQuotientPolynomial g).eval u := by
  rw [← eval_mul, gdgQuadratic_mul_channelQuotient hg]

/-- **Target 9.** Away from the removed quadratic channel, the roots of the
channel quotient are exactly the roots of the critical polynomial. The
hypothesis `hQ` is essential: the two forced channel roots are roots of the
critical polynomial but not of the squarefree quotient. -/
theorem gdgChannelQuotient_eval_eq_zero_iff
    {g : ℕ} (hg : 5 ≤ g) {u : ℂ}
    (hQ : (gdgQuadraticPolynomial g).eval u ≠ 0) :
    (gdgChannelQuotientPolynomial g).eval u = 0 ↔
      (gdgCriticalPolynomial g).eval u = 0 := by
  rw [gdgCriticalPolynomial_eval_factorization hg u]
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hQ

end GdgSquarefree
