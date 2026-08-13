/-
gd_g completion roadmap, Phase 4B — polynomial realization of the critical
tetranomial, exact degree, separability and genuine squarefreeness.

Phase 4A (`RequestProject.GdgCriticalNoCommonRoot`) proved that the specialized
functional tetranomial `criticalTetranomial g (gdgCosCoeff g) ((-1)^g)` and its
declared derivative `criticalTetranomialDeriv` have no common complex root.
This module realizes those functions as honest `Polynomial ℂ` objects, proves
the exact degree for `g ≥ 5`, transfers the pointwise derivative statement to
`Polynomial.derivative`, and deduces `Polynomial.Separable` and the global
Mathlib `Squarefree` predicate.

It does NOT remove forced factors, does NOT define a quotient, does NOT descend
to the block coordinate `b = u + u⁻¹`, and makes no claim about the free block
degree, root count, all roots real, lobe uniqueness, critical-value separation,
monodromy, or a Galois group. No claim is made here that the quadratic channel
polynomial divides the critical polynomial.
-/
import Mathlib
import RequestProject.GdgCriticalNoCommonRoot

namespace GdgSquarefree

open Polynomial

/-- **Definition 1.** The critical tetranomial of the gd_g bridge cover realized
as a genuine polynomial over `ℂ`, with `a = gdgCosCoeff g` and
`epsilon = (-1)^g`. -/
noncomputable def gdgCriticalPolynomial (g : ℕ) : Polynomial ℂ :=
  Polynomial.C (gdgCosCoeff g : ℂ) + Polynomial.C 2 * Polynomial.X +
    Polynomial.C (2 * ((-1 : ℂ) ^ g)) * Polynomial.X ^ (g - 1) +
    Polynomial.C (((-1 : ℂ) ^ g) * (gdgCosCoeff g : ℂ)) *
      Polynomial.X ^ g

/-- **Definition 2.** The peeled quadratic channel factor `1 + a X + X²`
realized as a genuine polynomial over `ℂ`. -/
noncomputable def gdgQuadraticPolynomial (g : ℕ) : Polynomial ℂ :=
  1 + Polynomial.C (gdgCosCoeff g : ℂ) * Polynomial.X +
    Polynomial.X ^ 2

/-- **Target 1.** The critical polynomial evaluates to the specialized critical
tetranomial at every point. -/
theorem gdgCriticalPolynomial_eval (g : ℕ) (u : ℂ) :
    (gdgCriticalPolynomial g).eval u =
      criticalTetranomial g (gdgCosCoeff g : ℂ)
        ((-1 : ℂ) ^ g) u := by
  unfold gdgCriticalPolynomial criticalTetranomial
  simp

/-- **Target 2.** The formal derivative of the critical polynomial evaluates to
the declared functional derivative at every point, for every natural `g`
(including the natural-subtraction boundary cases `g = 0` and `g = 1`). -/
theorem gdgCriticalPolynomial_derivative_eval (g : ℕ) (u : ℂ) :
    (gdgCriticalPolynomial g).derivative.eval u =
      criticalTetranomialDeriv g (gdgCosCoeff g : ℂ)
        ((-1 : ℂ) ^ g) u := by
  have hexp : g - 1 - 1 = g - 2 := by omega
  unfold gdgCriticalPolynomial criticalTetranomialDeriv
  simp only [derivative_add, derivative_C, derivative_C_mul, derivative_X,
    derivative_X_pow, mul_one, zero_add, eval_add, eval_mul, eval_C, eval_X,
    eval_pow, hexp]
  ring

/-- **Target 3.** The quadratic channel polynomial evaluates to
`coverQuadratic` at every point. -/
theorem gdgQuadraticPolynomial_eval (g : ℕ) (u : ℂ) :
    (gdgQuadraticPolynomial g).eval u =
      coverQuadratic (gdgCosCoeff g : ℂ) u := by
  unfold gdgQuadraticPolynomial coverQuadratic
  simp

/-- The leading coefficient `epsilon * a` of the critical polynomial is nonzero
for `g ≥ 5`. -/
private theorem gdgCriticalPolynomial_lead_ne_zero {g : ℕ} (hg : 5 ≤ g) :
    ((-1 : ℂ) ^ g) * (gdgCosCoeff g : ℂ) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (gdgCosCoeff_pos hg)))

/-- **Target 4.** The critical polynomial has exact degree `g` for `g ≥ 5`. The
coefficient of `X ^ g` is `(-1)^g * gdgCosCoeff g ≠ 0`, and for `g ≥ 5` the
three remaining exponents `0`, `1`, `g - 1` are all distinct from `g`. -/
theorem gdgCriticalPolynomial_natDegree {g : ℕ} (hg : 5 ≤ g) :
    (gdgCriticalPolynomial g).natDegree = g := by
  have hlead := gdgCriticalPolynomial_lead_ne_zero hg
  have h0 : ¬ (g = 0) := by omega
  have h1 : ¬ (g = 1) := by omega
  have h2 : ¬ (g = g - 1) := by omega
  unfold gdgCriticalPolynomial
  compute_degree
  all_goals
    first
      | omega
      | (simp only [if_neg h0, if_neg h1, if_neg h2]
         simpa using hlead)

/-- **Target 5.** The quadratic channel polynomial is monic. (The hypothesis
`5 ≤ g` is part of the requested statement; monicity in fact holds for every
`g`.) -/
theorem gdgQuadraticPolynomial_monic {g : ℕ} (hg : 5 ≤ g) :
    (gdgQuadraticPolynomial g).Monic := by
  have : 5 ≤ g := hg
  unfold gdgQuadraticPolynomial
  monicity!

/-- **Target 6.** The quadratic channel polynomial has exact degree `2`. (The
hypothesis `5 ≤ g` is part of the requested statement; the degree is in fact
`2` for every `g`.) -/
theorem gdgQuadraticPolynomial_natDegree {g : ℕ} (hg : 5 ≤ g) :
    (gdgQuadraticPolynomial g).natDegree = 2 := by
  have : 5 ≤ g := hg
  unfold gdgQuadraticPolynomial
  compute_degree!

/-- **Target 7.** The critical polynomial is nonzero for `g ≥ 5`. -/
theorem gdgCriticalPolynomial_ne_zero {g : ℕ} (hg : 5 ≤ g) :
    gdgCriticalPolynomial g ≠ 0 := by
  intro h
  have hd : (gdgCriticalPolynomial g).natDegree = g :=
    gdgCriticalPolynomial_natDegree hg
  rw [h, Polynomial.natDegree_zero] at hd
  omega

/-- **Target 8.** The formal derivative of the critical polynomial is nonzero at
every root of the critical polynomial. -/
theorem gdgCriticalPolynomial_derivative_eval_ne_zero_of_root
    {g : ℕ} (hg : 5 ≤ g) {u : ℂ}
    (hu : (gdgCriticalPolynomial g).eval u = 0) :
    (gdgCriticalPolynomial g).derivative.eval u ≠ 0 := by
  rw [gdgCriticalPolynomial_eval] at hu
  rw [gdgCriticalPolynomial_derivative_eval]
  exact gdgCriticalTetranomial_deriv_ne_zero_of_root hg hu

/-- **Target 9.** The critical polynomial is separable for `g ≥ 5`. -/
theorem gdgCriticalPolynomial_separable {g : ℕ} (hg : 5 ≤ g) :
    (gdgCriticalPolynomial g).Separable := by
  rw [Polynomial.Separable,
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := ℂ) (K := ℂ)]
  intro z
  simp only [Polynomial.coe_aeval_eq_eval]
  by_cases hz : (gdgCriticalPolynomial g).eval z = 0
  · exact Or.inr (gdgCriticalPolynomial_derivative_eval_ne_zero_of_root hg hz)
  · exact Or.inl hz

/-- **Target 10.** The critical polynomial is squarefree for `g ≥ 5`, in the
global Mathlib sense. -/
theorem gdgCriticalPolynomial_squarefree {g : ℕ} (hg : 5 ≤ g) :
    Squarefree (gdgCriticalPolynomial g) :=
  (gdgCriticalPolynomial_separable hg).squarefree

end GdgSquarefree
