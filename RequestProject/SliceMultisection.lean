/-
General roots-of-unity backbone of the gd_g ladder (rung 2, arbitrary dimension g).

Two identities that underpin every rung of the circle↔hyperbola ladder, for an
arbitrary primitive g-th root of unity ζ:

* `char_product` — the geometric-mean normalization is exactly the trinomial
  polynomial: `∏_{j<g} (1 + ζ^j u) = 1 − (−1)^g u^g`. (g=2 → 1−u², g=3 → 1+u³,
  the same `1∓u^g` that gives the collapse roots `zᵍ = 7+7z`.)

* `zeroth_multisection` — the k=0 Pascal slice is the AVERAGE of the characters
  `(1+ζ^j u)^N` over all g-th roots of unity — the sign-free member of the
  roots-of-unity filter. Specialises to `binomEven = ½[(1+u)^N+(1−u)^N] = cosh`
  (g=2) and to `(1/3)[(1+u)^N + 2 Re(1+ωu)^N]` (g=3, the real-plus-spiral).

Everything is over ℂ; the discrete gd_g bridges are the (log|·|, arg) images of
the characters `1+ζ^j u`, whose product and average these two identities pin down.

Proof routes (keep every statement verbatim; minor lemma-name changes ok):
- char_product: rewrite `1 + ζ^j u = 1 - ζ^j (-u)`, then use the standard
  primitive-root factorisation `∏_{j<g} (1 - ζ^j x) = 1 - x^g` (derive from
  `∏_{j<g}(X - ζ^j) = X^g - 1`, `IsPrimitiveRoot`; or a direct
  `Finset.prod`/`geom` lemma) with `x = -u`; `(-u)^g = (-1)^g u^g`.
- zeroth_multisection: expand `(1 + ζ^j u)^N = ∑ i, C(N,i) (ζ^j)^i u^i`
  (`add_pow`), swap the sums (`Finset.sum_comm`), factor
  `∑_{j<g} (ζ^i)^j` inside. Roots-of-unity orthogonality: if `g ∣ i` then
  `ζ^i = 1` so the inner sum is `g`; else `ζ^i ≠ 1` (`hζ` primitive) and the
  geometric sum `∑_{j<g} (ζ^i)^j = (ζ^{i·g} − 1)/(ζ^i − 1) = 0` since
  `ζ^{i·g} = (ζ^g)^i = 1` (`geom_sum_eq`, `IsPrimitiveRoot.pow_eq_one`). Divide
  by `g` (`(g:ℂ) ≠ 0` from `hg`).
Certification: if a target cannot close, omit it and report its exact name; do
not weaken a statement.
-/
import Mathlib

open scoped BigOperators

namespace SliceHyperbolic

/-- Factorisation `∏_{i<g} (t - ζ^i) = t^g - 1` for a primitive `g`-th root of unity. -/
private theorem prod_sub_pow {g : ℕ} (hg : 0 < g) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ g) (t : ℂ) :
    ∏ i ∈ Finset.range g, (t - ζ ^ i) = t ^ g - 1 := by
  have h := X_pow_sub_C_eq_prod hζ (a := (1 : ℂ)) (α := 1) hg (by simp)
  have h2 := congrArg (Polynomial.eval t) h
  simp [Polynomial.eval_prod] at h2
  exact h2.symm

/-- Roots-of-unity orthogonality: `∑_{j<g} (ζ^i)^j` is `g` when `g ∣ i` and `0` otherwise. -/
private theorem sum_pow_eq_ite {g : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ g) (i : ℕ) :
    ∑ j ∈ Finset.range g, (ζ ^ i) ^ j = if g ∣ i then (g : ℂ) else 0 := by
  by_cases h : g ∣ i
  · obtain ⟨k, rfl⟩ := h
    have hone : ζ ^ (g * k) = 1 := by rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp [hone]
  · have hne : ζ ^ i ≠ 1 := fun hc => h ((hζ.pow_eq_one_iff_dvd i).mp hc)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm i g, pow_mul, hζ.pow_eq_one, one_pow]
    simp [h]

/-- The product of the `g` characters `1 + ζ^j u` is the trinomial normalization
polynomial `1 − (−1)^g u^g`. -/
theorem char_product {g : ℕ} (hg : 0 < g) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ g) (u : ℂ) :
    ∏ j ∈ Finset.range g, (1 + ζ ^ j * u) = 1 - (-1) ^ g * u ^ g := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [zero_pow hg.ne']
  · have key := prod_sub_pow hg hζ (-u⁻¹)
    have step : ∀ j ∈ Finset.range g, (1 + ζ ^ j * u) = (-u) * (-u⁻¹ - ζ ^ j) := by
      intro j _; field_simp; ring
    rw [Finset.prod_congr rfl step, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range, key, mul_sub, ← mul_pow]
    have h1 : (-u) * (-u⁻¹) = 1 := by field_simp
    rw [h1, one_pow, neg_pow]
    ring

/-- The zeroth Pascal multisection is the average of the characters over all
`g`-th roots of unity (the sign-free roots-of-unity filter). -/
theorem zeroth_multisection {g : ℕ} (hg : 0 < g) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ g)
    (N : ℕ) (u : ℂ) :
    (∑ i ∈ Finset.range (N + 1), if g ∣ i then (N.choose i : ℂ) * u ^ i else 0)
      = (g : ℂ)⁻¹ * ∑ j ∈ Finset.range g, (1 + ζ ^ j * u) ^ N := by
  have hgc : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have expand : ∀ j ∈ Finset.range g, (1 + ζ ^ j * u) ^ N
      = ∑ i ∈ Finset.range (N + 1), (ζ ^ i) ^ j * (u ^ i * (N.choose i : ℂ)) := by
    intro j _
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul, mul_comm j i, pow_mul]
    ring
  rw [Finset.sum_congr rfl expand, Finset.sum_comm]
  have inner : ∀ i ∈ Finset.range (N + 1),
      ∑ j ∈ Finset.range g, (ζ ^ i) ^ j * (u ^ i * (N.choose i : ℂ))
        = (if g ∣ i then (g : ℂ) else 0) * (u ^ i * (N.choose i : ℂ)) := by
    intro i _
    rw [← Finset.sum_mul, sum_pow_eq_ite hζ i]
  rw [Finset.sum_congr rfl inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : g ∣ i
  · simp [h]
    field_simp
  · simp [h]

end SliceHyperbolic
