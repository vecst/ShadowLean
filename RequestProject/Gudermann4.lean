/-
gd₄ — the g=4 circle↔hyperbola bridge as a special function (gd_g ladder, last
elementary rung).

The mod-4 character `1 + i u` (i = e^{2πi/4}) has circular part `ψ = arg(1+iu) =
arctan u` and hyperbolic part `s = log|1+iu| − ¼·log(1−u⁴) = ½log(1+u²) −
¼log(1−u⁴)` (deviation from the geometric mean, since `∏_j (1+i^j u) = 1−u⁴`). On
the arc `u ∈ (0,1)` the bridge `ψ(s)` satisfies its own clean autonomous ODE, the
g=4 sibling of `gd₃`'s `dψ/ds = −3cot(π/3−ψ)` and of the gudermannian's `ψ'=cosψ`:

  dψ/ds = 2·cot(2ψ),      integrating to    cos(2ψ) = e^{−4s}.

Together with `gd₃` this certifies the ELEMENTARY (single-cot) rungs of the ladder.
Numerically the ODE holds for g=3,4 exactly but FAILS for g≥5 (dF/dψ is not a
low-degree polynomial in F) — a solvability threshold coinciding with radicals
(quartic solvable, quintic not); gd₄ is the last elementary rung.

Proof routes (keep every statement verbatim; minor lemma-name changes ok):
- gd4Psi_hasDerivAt: `gd4Psi = Real.arctan`, so this is `Real.hasDerivAt_arctan u`
  (value `1/(1+u²)`); `simpa`/`exact` as needed.
- gd4S_hasDerivAt: `HasDerivAt.log` at `1+u² > 0` and `1−u⁴ > 0` (from `0<u<1`),
  inner derivs `2u`, `-4u³`, combined by `.div_const`/`.sub`; simplify
  `u/(1+u²) + u³/(1−u⁴) = u/(1−u⁴)` via `1−u⁴ = (1−u²)(1+u²)`. NOTE: on the RC,
  `convert h using 1` can leave extra defeq goals (a module-instance eq, a
  function eq) that older Mathlib auto-closed — close them uniformly with
  `convert h using 1 <;> first | rfl | (field_simp [<ne hyps>]; ring)`.
- gd4_cos: `Real.cos_two_mul` + `Real.cos_arctan` (`cos(arctan u) = (√(1+u²))⁻¹`):
  `cos(2ψ) = 2cos²ψ − 1 = 2/(1+u²) − 1 = (1−u²)/(1+u²)`.
- gd4_sin: `Real.sin_two_mul` + `Real.sin_arctan`/`Real.cos_arctan`:
  `sin(2ψ) = 2 sinψ cosψ = 2u/(1+u²)`.
- gd4_ode: substitute gd4_cos and gd4_sin; reduces to `1−u⁴ = (1−u²)(1+u²)`
  (`field_simp` with `1+u² ≠ 0`, `1−u⁴ ≠ 0`; `ring`).
Certification: if a target cannot close, omit it and report its exact name; do
not weaken a statement.
-/
import Mathlib

open scoped Real

namespace SliceHyperbolic

/-- Circular part of the g=4 character `1+iu`: `ψ = arg(1+iu) = arctan u`. -/
noncomputable def gd4Psi (u : ℝ) : ℝ := Real.arctan u

/-- Hyperbolic part of the g=4 character: `s = ½ log(1+u²) − ¼ log(1−u⁴)`. -/
noncomputable def gd4S (u : ℝ) : ℝ :=
  Real.log (1 + u ^ 2) / 2 - Real.log (1 - u ^ 4) / 4

/-- Derivative of the circular part: `ψ'(u) = 1/(1+u²)`. -/
theorem gd4Psi_hasDerivAt (u : ℝ) :
    HasDerivAt gd4Psi (1 / (1 + u ^ 2)) u := by
  show HasDerivAt Real.arctan (1 / (1 + u ^ 2)) u
  exact Real.hasDerivAt_arctan u

/-- Derivative of the hyperbolic part: `s'(u) = u/(1−u⁴)`. -/
theorem gd4S_hasDerivAt {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt gd4S (u / (1 - u ^ 4)) u := by
  have h1 : (0:ℝ) < 1 + u ^ 2 := by positivity
  have hu2 : u ^ 2 < 1 := by nlinarith
  have h2 : (0:ℝ) < 1 - u ^ 4 := by nlinarith [sq_nonneg u]
  have hA : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).const_add 1
  have hB : HasDerivAt (fun x : ℝ => 1 - x ^ 4) (-(4 * u ^ 3)) u := by
    simpa using (hasDerivAt_pow 4 u).const_sub 1
  have h := ((hA.log h1.ne').div_const 2).sub ((hB.log h2.ne').div_const 4)
  convert h using 1 <;> first | rfl | (field_simp [h1.ne', h2.ne']; ring)

/-- Closed form of the character's circular image (cosine):
`cos(2ψ) = (1−u²)/(1+u²)`. -/
theorem gd4_cos (u : ℝ) :
    Real.cos (2 * gd4Psi u) = (1 - u ^ 2) / (1 + u ^ 2) := by
  have h1 : (0:ℝ) < 1 + u ^ 2 := by positivity
  rw [Real.cos_two_mul, gd4Psi, Real.cos_arctan]
  have hsq : Real.sqrt (1 + u ^ 2) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt (by positivity)
  rw [div_pow, hsq]
  field_simp
  ring

/-- Closed form of the character's circular image (sine):
`sin(2ψ) = 2u/(1+u²)`. -/
theorem gd4_sin (u : ℝ) :
    Real.sin (2 * gd4Psi u) = 2 * u / (1 + u ^ 2) := by
  have h1 : (0:ℝ) < 1 + u ^ 2 := by positivity
  rw [Real.sin_two_mul, gd4Psi, Real.sin_arctan, Real.cos_arctan]
  have h : Real.sqrt (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) = 1 + u ^ 2 :=
    Real.mul_self_sqrt (by positivity)
  have key : 2 * (u / Real.sqrt (1 + u ^ 2)) * (1 / Real.sqrt (1 + u ^ 2))
      = 2 * u / (Real.sqrt (1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) := by ring
  rw [key, h]

/-- **The gd₄ autonomous ODE.** The bridge derivatives satisfy
`ψ'·sin(2ψ) = 2·s'·cos(2ψ)`, i.e. `dψ/ds = 2 cot(2ψ)` — the g=4 sibling of
`gd₃`'s law and the last elementary rung of the ladder. -/
theorem gd4_ode {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (1 / (1 + u ^ 2)) * Real.sin (2 * gd4Psi u)
      = 2 * (u / (1 - u ^ 4)) * Real.cos (2 * gd4Psi u) := by
  have h1 : (0:ℝ) < 1 + u ^ 2 := by positivity
  have hu2 : u ^ 2 < 1 := by nlinarith
  have h2 : (0:ℝ) < 1 - u ^ 4 := by nlinarith [sq_nonneg u]
  rw [gd4_sin, gd4_cos]
  field_simp
  ring

end SliceHyperbolic
