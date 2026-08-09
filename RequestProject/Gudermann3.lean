/-
gd₃ — the g=3 circle↔hyperbola bridge as a genuine special function (gd_g ladder).

The mod-3 character `1 + ω u` (ω = e^{2πi/3}) has circular part `ψ = arg(1+ωu)`
and hyperbolic part `s = log|1+ωu| − (1/3)log(1+u³)` (deviation from the geometric
mean `(1+u³)^{1/3}`). On the arc `u ∈ (0,1)` these are the elementary functions

  gd3Psi u = arctan( √3·u / (2−u) ),   gd3S u = ½·log(1−u+u²) − ⅓·log(1+u³),

and the bridge `ψ(s)` satisfies its OWN clean autonomous ODE — the g=3 analog of
the gudermannian's badge `ψ' = cos ψ` (from `sin(gd r) = tanh r`):

  dψ/ds = −3·cot(π/3 − ψ),      integrating to    cos(π/3 − ψ) = ½·e^{−3s}.

Both verified numerically to machine precision. This certifies that gd₃ is a
bona-fide special function, not a repackaging. (gd₄ analog: `dψ/ds = 2 cot 2ψ`,
`cos 2ψ = e^{−4s}`.)

Proof routes (keep every statement verbatim; minor lemma-name changes ok):
- gd3Psi_hasDerivAt: chain rule. `d/du (√3 u/(2−u)) = 2√3/(2−u)²`
  (`HasDerivAt.div`, `hasDerivAt_id`, const); compose with
  `Real.hasDerivAt_arctan` (deriv `1/(1+T²)`); `1+T² = 4(1−u+u²)/(2−u)²`, so the
  product simplifies to `√3/(2(1−u+u²))` (`field_simp`/`ring`, using `2−u ≠ 0`).
- gd3S_hasDerivAt: `Real.hasDerivAt_log` at `1−u+u² > 0` and `1+u³ > 0` (both from
  `0<u<1`), times the inner derivatives (`2u−1`, `3u²`); combine and simplify to
  `(u−1)/(2(1+u³))` via `1+u³ = (1+u)(1−u+u²)` (`field_simp`/`ring`).
- gd3_cos / gd3_sin: `Real.cos_arctan`, `Real.sin_arctan` give
  `cos ψ = (√(1+T²))⁻¹`, `sin ψ = T·(√(1+T²))⁻¹` with `T = √3 u/(2−u)`; then
  `Real.cos_sub`/`Real.sin_sub` with `cos(π/3)=½`, `sin(π/3)=√3/2`
  (`Real.cos_pi_div_three`, `Real.sin_pi_div_three`); `√(1+T²) = 2√(1−u+u²)/(2−u)`
  (`Real.sqrt`, `2−u>0`); algebra to the stated forms.
- gd3_ode: substitute gd3_cos and gd3_sin; the ODE reduces to the identity
  `(1−u)(1+u³) = (1−u²)(1−u+u²)` i.e. `1+u³ = (1+u)(1−u+u²)` (`ring` after clearing
  the common `√(1−u+u²) > 0`). No calculus here — it is the derivative *values*
  (from the two `hasDerivAt` lemmas) satisfying the autonomous relation.
Certification: if a target cannot close, omit it and report its exact name; do
not weaken a statement.
-/
import Mathlib

open scoped Real

namespace SliceHyperbolic

/-- Circular part of the g=3 character `1+ωu`: `ψ = arg(1+ωu) = arctan(√3 u/(2−u))`. -/
noncomputable def gd3Psi (u : ℝ) : ℝ := Real.arctan (Real.sqrt 3 * u / (2 - u))

/-- Hyperbolic part of the g=3 character (deviation from the geometric mean):
`s = ½ log(1−u+u²) − ⅓ log(1+u³)`. -/
noncomputable def gd3S (u : ℝ) : ℝ :=
  Real.log (1 - u + u ^ 2) / 2 - Real.log (1 + u ^ 3) / 3

/-- Derivative of the circular part: `ψ'(u) = √3 / (2(1−u+u²))`. -/
theorem gd3Psi_hasDerivAt {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt gd3Psi (Real.sqrt 3 / (2 * (1 - u + u ^ 2))) u := by
  have h2 : (2 : ℝ) - u ≠ 0 := by nlinarith
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnum : HasDerivAt (fun x : ℝ => Real.sqrt 3 * x) (Real.sqrt 3 * 1) u :=
    (hasDerivAt_id u).const_mul _
  have hde : HasDerivAt (fun x : ℝ => 2 - x) (0 - 1) u :=
    (hasDerivAt_const u (2 : ℝ)).sub (hasDerivAt_id u)
  have hq : HasDerivAt (fun x : ℝ => Real.sqrt 3 * x / (2 - x))
      ((Real.sqrt 3 * 1 * (2 - u) - Real.sqrt 3 * u * (0 - 1)) / (2 - u) ^ 2) u :=
    hnum.div hde h2
  have h := (Real.hasDerivAt_arctan (Real.sqrt 3 * u / (2 - u))).comp u hq
  have key : 1 + (Real.sqrt 3 * u / (2 - u)) ^ 2 = 4 * (1 - u + u ^ 2) / (2 - u) ^ 2 := by
    field_simp
    linear_combination u ^ 2 * hr
  rw [key] at h
  have hden : (0 : ℝ) < 1 - u + u ^ 2 := by nlinarith
  convert h using 1 <;> first | rfl | (field_simp [hden.ne', h2]; ring)

/-- Derivative of the hyperbolic part: `s'(u) = (u−1) / (2(1+u³))`. -/
theorem gd3S_hasDerivAt {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt gd3S ((u - 1) / (2 * (1 + u ^ 3))) u := by
  have hA : (0 : ℝ) < 1 - u + u ^ 2 := by nlinarith
  have hB : (0 : ℝ) < 1 + u ^ 3 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => 1 - x + x ^ 2) (0 - 1 + 2 * u ^ 1) u :=
    ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).add (hasDerivAt_pow 2 u)
  have h2 : HasDerivAt (fun x : ℝ => 1 + x ^ 3) (0 + 3 * u ^ 2) u :=
    (hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_pow 3 u)
  have hl1 : HasDerivAt (fun x : ℝ => Real.log (1 - x + x ^ 2))
      ((0 - 1 + 2 * u ^ 1) / (1 - u + u ^ 2)) u := h1.log hA.ne'
  have hl2 : HasDerivAt (fun x : ℝ => Real.log (1 + x ^ 3))
      ((0 + 3 * u ^ 2) / (1 + u ^ 3)) u := h2.log hB.ne'
  have h := (hl1.div_const 2).sub (hl2.div_const 3)
  convert h using 1 <;> first | rfl | (field_simp [hA.ne', hB.ne']; ring)

/-- Closed form of the character's circular image (cosine):
`cos(π/3 − ψ) = (1+u) / (2√(1−u+u²))`. -/
theorem gd3_cos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Real.cos (π / 3 - gd3Psi u) = (1 + u) / (2 * Real.sqrt (1 - u + u ^ 2)) := by
  have h2 : (0 : ℝ) < 2 - u := by linarith
  have h2' : (2 : ℝ) - u ≠ 0 := ne_of_gt h2
  have hA : (0 : ℝ) < 1 - u + u ^ 2 := by nlinarith
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsA : (0 : ℝ) < Real.sqrt (1 - u + u ^ 2) := Real.sqrt_pos.mpr hA
  have hsA' : Real.sqrt (1 - u + u ^ 2) ≠ 0 := ne_of_gt hsA
  have hsqA : Real.sqrt (1 - u + u ^ 2) ^ 2 = 1 - u + u ^ 2 := Real.sq_sqrt hA.le
  have key : 1 + (Real.sqrt 3 * u / (2 - u)) ^ 2
      = (2 * Real.sqrt (1 - u + u ^ 2) / (2 - u)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, mul_pow, hsqA, hr]
    field_simp
    ring
  have hS : Real.sqrt (1 + (Real.sqrt 3 * u / (2 - u)) ^ 2)
      = 2 * Real.sqrt (1 - u + u ^ 2) / (2 - u) := by
    rw [key, Real.sqrt_sq (by positivity)]
  rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three, gd3Psi,
    Real.cos_arctan, Real.sin_arctan, hS]
  field_simp
  linear_combination u * hr

/-- Closed form of the character's circular image (sine):
`sin(π/3 − ψ) = √3(1−u) / (2√(1−u+u²))`. -/
theorem gd3_sin {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Real.sin (π / 3 - gd3Psi u) = Real.sqrt 3 * (1 - u) / (2 * Real.sqrt (1 - u + u ^ 2)) := by
  have h2 : (0 : ℝ) < 2 - u := by linarith
  have h2' : (2 : ℝ) - u ≠ 0 := ne_of_gt h2
  have hA : (0 : ℝ) < 1 - u + u ^ 2 := by nlinarith
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsA : (0 : ℝ) < Real.sqrt (1 - u + u ^ 2) := Real.sqrt_pos.mpr hA
  have hsA' : Real.sqrt (1 - u + u ^ 2) ≠ 0 := ne_of_gt hsA
  have hsqA : Real.sqrt (1 - u + u ^ 2) ^ 2 = 1 - u + u ^ 2 := Real.sq_sqrt hA.le
  have key : 1 + (Real.sqrt 3 * u / (2 - u)) ^ 2
      = (2 * Real.sqrt (1 - u + u ^ 2) / (2 - u)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, mul_pow, hsqA, hr]
    field_simp
    ring
  have hS : Real.sqrt (1 + (Real.sqrt 3 * u / (2 - u)) ^ 2)
      = 2 * Real.sqrt (1 - u + u ^ 2) / (2 - u) := by
    rw [key, Real.sqrt_sq (by positivity)]
  rw [Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three, gd3Psi,
    Real.cos_arctan, Real.sin_arctan, hS]
  field_simp
  ring

/-- **The gd₃ autonomous ODE.** The bridge derivatives satisfy
`ψ'·sin(π/3 − ψ) = −3·s'·cos(π/3 − ψ)`, i.e. `dψ/ds = −3 cot(π/3 − ψ)` — the
g=3 analog of the gudermannian's `ψ' = cos ψ`. -/
theorem gd3_ode {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (Real.sqrt 3 / (2 * (1 - u + u ^ 2))) * Real.sin (π / 3 - gd3Psi u)
      = -3 * ((u - 1) / (2 * (1 + u ^ 3))) * Real.cos (π / 3 - gd3Psi u) := by
  have hA : (0 : ℝ) < 1 - u + u ^ 2 := by nlinarith
  have hA' : (1 : ℝ) - u + u ^ 2 ≠ 0 := ne_of_gt hA
  have hB : (0 : ℝ) < 1 + u ^ 3 := by positivity
  have hB' : (1 : ℝ) + u ^ 3 ≠ 0 := ne_of_gt hB
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsA : (0 : ℝ) < Real.sqrt (1 - u + u ^ 2) := Real.sqrt_pos.mpr hA
  have hsA' : Real.sqrt (1 - u + u ^ 2) ≠ 0 := ne_of_gt hsA
  rw [gd3_sin hu0 hu1, gd3_cos hu0 hu1]
  field_simp
  ring_nf
  linear_combination (1 - u) * (1 + u ^ 3) * hr

end SliceHyperbolic
