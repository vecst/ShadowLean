/-
Algebraic reduction for the critical tetranomial of the gd_g bridge cover.

After pulling the normalized cover back to its reciprocal coordinate u, its
non-forced derivative factor is represented by

  G_g(u) = a + 2u + 2 epsilon u^(g-1) + epsilon a u^g.

The theorem below proves that a repeated root of G_g must lie on one explicit
reciprocal quadratic. It is the ring-algebra reduction behind the remaining
all-g squarefreeness problem; it does not assert that the quadratic candidates
are impossible.
-/
import Mathlib

namespace GdgSquarefree

/-- The four-term critical polynomial before the two peeled channel factors
are removed. In the gd_g application, `a = 2 cos (2 pi / g)` and
`epsilon = (-1)^g`. -/
noncomputable def criticalTetranomial
    (g : ℕ) (a epsilon u : ℂ) : ℂ :=
  a + 2 * u + 2 * epsilon * u ^ (g - 1) + epsilon * a * u ^ g

/-- The formal derivative of `criticalTetranomial`. -/
noncomputable def criticalTetranomialDeriv
    (g : ℕ) (a epsilon u : ℂ) : ℂ :=
  2 + 2 * epsilon * (g - 1 : ℕ) * u ^ (g - 2) +
    epsilon * a * g * u ^ (g - 1)

/-- Numerator in the pulled-back gd_g cover. -/
noncomputable def coverNumerator
    (g : ℕ) (epsilon u : ℂ) : ℂ :=
  1 - epsilon * u ^ g

/-- Quadratic denominator in the pulled-back gd_g cover. -/
noncomputable def coverQuadratic (a u : ℂ) : ℂ :=
  1 + a * u + u ^ 2

/-- The cross-multiplied derivative numerator of
`coverNumerator g epsilon u ^ 2 / coverQuadratic a u ^ g` is exactly the
critical tetranomial factor, up to `-g`. -/
theorem coverDerivativeNumerator_eq_criticalTetranomial
    {g : ℕ} (hg : 1 ≤ g) (a epsilon u : ℂ) :
    2 * (-(epsilon * g * u ^ (g - 1))) * coverQuadratic a u -
        g * coverNumerator g epsilon u * (a + 2 * u) =
      -(g : ℂ) * criticalTetranomial g a epsilon u := by
  have hpow1 : u * u ^ (g - 1) = u ^ g := by
    rw [← pow_succ']
    congr 1
    omega
  have hpow2 : u ^ 2 * u ^ (g - 1) = u * u ^ g := by
    calc
      u ^ 2 * u ^ (g - 1) = u * (u * u ^ (g - 1)) := by ring
      _ = u * u ^ g := by rw [hpow1]
  unfold coverQuadratic coverNumerator criticalTetranomial
  ring_nf
  linear_combination
    -(2 * epsilon * g * a) * hpow1 - (2 * epsilon * g) * hpow2

/-- `criticalTetranomialDeriv` is the complex derivative of the critical
tetranomial. -/
theorem criticalTetranomial_hasDerivAt
    (g : ℕ) (a epsilon u : ℂ) :
    HasDerivAt (criticalTetranomial g a epsilon)
      (criticalTetranomialDeriv g a epsilon u) u := by
  have hexp : g - 1 - 1 = g - 2 := by omega
  have h := (((hasDerivAt_const u a).add
      ((hasDerivAt_id u).const_mul 2)).add
      (((hasDerivAt_pow (g - 1) u).const_mul (2 * epsilon)).add
        ((hasDerivAt_pow g u).const_mul (epsilon * a))))
  convert h using 1 <;>
    first
    | rfl
    | (funext x
       unfold criticalTetranomial
       simp only [Pi.add_apply, id_eq]
       ring)
    | (unfold criticalTetranomialDeriv
       rw [hexp]
       ring)

/-- Any common root of the critical tetranomial and its derivative satisfies
one reciprocal quadratic. No condition on `epsilon` is required for this
algebraic elimination. -/
theorem criticalTetranomial_common_root_quadratic
    {g : ℕ} (hg : 2 ≤ g) {a epsilon u : ℂ}
    (hG : criticalTetranomial g a epsilon u = 0)
    (hG' : criticalTetranomialDeriv g a epsilon u = 0) :
    2 * a * (g - 1 : ℕ) * (u ^ 2 + 1) +
        ((g : ℂ) * (a ^ 2 + 4) - 8) * u = 0 := by
  have hpow1 : u ^ (g - 2) * u = u ^ (g - 1) := by
    rw [← pow_succ]
    congr 1
    omega
  have hpow2 : u ^ (g - 1) * u = u ^ g := by
    rw [← pow_succ]
    congr 1
    omega
  have hcast : ((g - 1 : ℕ) : ℂ) = (g : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ g)]
    norm_num
  have h1 :
      a + 2 * u + (epsilon * u ^ (g - 1)) * (2 + a * u) = 0 := by
    calc
      a + 2 * u + (epsilon * u ^ (g - 1)) * (2 + a * u) =
          criticalTetranomial g a epsilon u := by
            unfold criticalTetranomial
            rw [← hpow2]
            ring
      _ = 0 := hG
  have hu : criticalTetranomialDeriv g a epsilon u * u = 0 := by
    rw [hG', zero_mul]
  have h2 :
      2 * u + (epsilon * u ^ (g - 1)) *
        (2 * (g - 1 : ℕ) + a * g * u) = 0 := by
    calc
      2 * u + (epsilon * u ^ (g - 1)) *
          (2 * (g - 1 : ℕ) + a * g * u) =
          2 * u + 2 * epsilon * (g - 1 : ℕ) * u ^ (g - 1) +
              epsilon * a * g * (u ^ (g - 1) * u) := by
            ring
      _ = 2 * u + 2 * epsilon * (g - 1 : ℕ) *
              (u ^ (g - 2) * u) +
              epsilon * a * g * (u ^ (g - 1) * u) := by
            rw [hpow1]
      _ = criticalTetranomialDeriv g a epsilon u * u := by
            unfold criticalTetranomialDeriv
            ring
      _ = 0 := hu
  rw [hcast] at h2 ⊢
  linear_combination
    -(2 + a * u) * h2 + (2 * ((g : ℂ) - 1) + a * g * u) * h1

/-- A repeated nonzero root is one of the two reciprocal roots determined by
the displayed rational value. -/
theorem criticalTetranomial_common_root_reciprocal
    {g : ℕ} (hg : 2 ≤ g) {a epsilon u : ℂ} (ha : a ≠ 0) (hu : u ≠ 0)
    (hG : criticalTetranomial g a epsilon u = 0)
    (hG' : criticalTetranomialDeriv g a epsilon u = 0) :
    u + u⁻¹ =
      (8 - (g : ℂ) * (a ^ 2 + 4)) / (2 * a * (g - 1 : ℕ)) := by
  have hq := criticalTetranomial_common_root_quadratic hg hG hG'
  have hgm1nat : g - 1 ≠ 0 := by omega
  have hgm1 : ((g - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hgm1nat
  have hden : (2 * a * (g - 1 : ℕ) : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hgm1
  apply (eq_div_iff hden).2
  field_simp [hu] at hq ⊢
  linear_combination hq

end GdgSquarefree
