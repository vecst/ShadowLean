/-
The full roots-of-unity multisection filter (gd_g ladder, rung 3, every residue k).

Generalises rung 2's `zeroth_multisection` (k = 0) to arbitrary `k < g`: EVERY
Pascal residue slice is a weighted average of the characters `(1+ζ^j u)^N` over the
g-th roots of unity,

    ∑_{i≡k (g)} C(N,i) u^i  =  (1/g) ∑_{j<g} ζ^{-jk} (1+ζ^j u)^N,

the classical multisection / roots-of-unity filter. The `ζ^{-jk}` twist is written
`ζ^{j(g-k)}` (equal since `ζ^g = 1`, and `g-k` is a natural number when `k < g`),
so the statement stays over natural powers — no `zpow`. Specialises: `k=0` gives
`zeroth_multisection`; `g=2,k=1` gives the odd slice `= sinh`; `g=3` gives the
real-plus-spiral `p_{3,k}`. This is the identity every rung of the ladder rests on.

Proof route (keep the statement verbatim; minor lemma-name changes ok):
- Expand each character by the binomial theorem: `(1+ζ^j u)^N = ∑ i, C(N,i) (ζ^j)^i u^i`
  (`add_pow`). Pull the `ζ^{j(g-k)}` in and swap the two sums (`Finset.sum_comm`);
  the `j`-sum becomes `∑_{j<g} (ζ^{(g-k)+i})^j` (combine `ζ^{j(g-k)}·ζ^{ji}` via
  `pow_add`/`← pow_add`, `mul_pow`).
- Roots-of-unity orthogonality: `∑_{j<g} (ζ^m)^j = if g ∣ m then g else 0`
  (helper: `g ∣ m` ⇒ `ζ^m = 1`; else `ζ^m ≠ 1` by `hζ.pow_eq_one_iff_dvd`, and
  `geom_sum_eq` with `(ζ^m)^g = (ζ^g)^m = 1`). Here `m = (g-k)+i`, and
  `g ∣ (g-k)+i ↔ i % g = k` (uses `k < g`); so the inner sum is `g·[i%g=k]`.
- Divide by `g` (`(g:ℂ) ≠ 0` from `hg`); the surviving terms are exactly the LHS.
Certification: if it cannot close, omit it and report its exact name; do not
weaken the statement.
-/
import Mathlib

open scoped BigOperators

namespace SliceHyperbolic

/-- **The roots-of-unity multisection filter.** For every residue `k < g`, the
`k`-th Pascal slice equals the character average `(1/g) ∑_{j<g} ζ^{j(g-k)} (1+ζ^j u)^N`
(with `ζ^{j(g-k)} = ζ^{-jk}`). Every rung of the circle–hyperbola ladder is a case
of this identity. -/
theorem multisection_filter {g : ℕ} (hg : 0 < g) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ g)
    (N : ℕ) {k : ℕ} (hk : k < g) (u : ℂ) :
    (∑ i ∈ Finset.range (N + 1), if i % g = k then (N.choose i : ℂ) * u ^ i else 0)
      = (g : ℂ)⁻¹ * ∑ j ∈ Finset.range g, ζ ^ (j * (g - k)) * (1 + ζ ^ j * u) ^ N := by
  have hg0 : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have orth : ∀ m : ℕ, ∑ j ∈ Finset.range g, (ζ ^ m) ^ j = if g ∣ m then (g : ℂ) else 0 := by
    intro m
    by_cases h : g ∣ m
    · simp [h, (hζ.pow_eq_one_iff_dvd m).mpr h]
    · have h1 : ζ ^ m ≠ 1 := fun hc => h ((hζ.pow_eq_one_iff_dvd m).mp hc)
      have h2 : (ζ ^ m) ^ g = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      rw [geom_sum_eq h1, h2, sub_self, zero_div, if_neg h]
  have hdvd : ∀ i : ℕ, (g ∣ (g - k) + i) ↔ i % g = k := by
    intro i
    have h1 : i % g < g := Nat.mod_lt _ hg
    have hmod : ((g - k) + i) % g = ((g - k) + i % g) % g := by
      conv_lhs => rw [Nat.add_mod]
      rw [Nat.add_mod (g - k) (i % g), Nat.mod_mod_of_dvd _ (dvd_refl g)]
    have hkey : ((g - k) + i % g) % g = 0 ↔ i % g = k := by
      rcases lt_or_ge ((g - k) + i % g) g with h | h
      · rw [Nat.mod_eq_of_lt h]; omega
      · have hx : ((g - k) + i % g) % g = ((g - k) + i % g) - g := by
          rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
        rw [hx]; omega
    rw [Nat.dvd_iff_mod_eq_zero, hmod, hkey]
  have expand : ∀ j ∈ Finset.range g, ζ ^ (j * (g - k)) * (1 + ζ ^ j * u) ^ N
      = ∑ i ∈ Finset.range (N + 1), (N.choose i : ℂ) * u ^ i * (ζ ^ ((g - k) + i)) ^ j := by
    intro j _
    rw [add_comm (1 : ℂ), add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [pow_add, mul_pow, mul_pow]
    ring
  rw [Finset.sum_congr rfl expand, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.mul_sum, orth ((g - k) + i)]
  by_cases h : i % g = k
  · rw [if_pos h, if_pos ((hdvd i).mpr h)]
    field_simp
  · rw [if_neg h, if_neg fun hc => h ((hdvd i).mp hc)]
    ring

end SliceHyperbolic
