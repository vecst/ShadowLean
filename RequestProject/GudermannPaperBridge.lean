import RequestProject.Gudermann3
import RequestProject.Gudermann4

open scoped Real

namespace SliceHyperbolic

/-- The displayed `gd₃` cosine/exponential bridge from the ladder paper. -/
theorem gd3_exponential_bridge {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Real.cos (Real.pi / 3 - gd3Psi u) =
      (1 / 2 : ℝ) * Real.exp (-3 * gd3S u) := by
  have hA : (0 : ℝ) < 1 - u + u ^ 2 := by nlinarith
  have hB : (0 : ℝ) < 1 + u ^ 3 := by positivity
  have hsA : (0 : ℝ) < Real.sqrt (1 - u + u ^ 2) := Real.sqrt_pos.mpr hA
  have hfactor : 1 + u ^ 3 = (1 + u) * (1 - u + u ^ 2) := by ring
  have hexp : Real.exp (-3 * gd3S u) =
      (1 + u) / Real.sqrt (1 - u + u ^ 2) := by
    have hlog : -3 * gd3S u =
        Real.log (1 + u ^ 3) - Real.log (1 - u + u ^ 2) -
          Real.log (Real.sqrt (1 - u + u ^ 2)) := by
      unfold gd3S
      rw [Real.log_sqrt hA.le]
      ring
    rw [hlog, Real.exp_sub, Real.exp_sub, Real.exp_log hB,
      Real.exp_log hA, Real.exp_log hsA, hfactor]
    field_simp
  rw [gd3_cos hu0 hu1, hexp]
  ring

/-- The displayed `gd₄` cosine/exponential bridge from the ladder paper. -/
theorem gd4_exponential_bridge {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Real.cos (2 * gd4Psi u) = Real.exp (-4 * gd4S u) := by
  have hA : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have hu2 : u ^ 2 < 1 := by nlinarith
  have hB : (0 : ℝ) < 1 - u ^ 4 := by nlinarith [sq_nonneg u]
  have hfactor : 1 - u ^ 4 = (1 - u ^ 2) * (1 + u ^ 2) := by ring
  rw [gd4_cos]
  have hlog : -4 * gd4S u =
      Real.log (1 - u ^ 4) -
        (Real.log (1 + u ^ 2) + Real.log (1 + u ^ 2)) := by
    unfold gd4S
    ring
  rw [hlog, Real.exp_sub, Real.exp_add, Real.exp_log hB,
    Real.exp_log hA, hfactor]
  field_simp

/-- The `gd₃` autonomous law in the paper's quotient form `dψ/ds = -3 cot`. -/
theorem gd3_quotient_ode {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (Real.sqrt 3 / (2 * (1 - u + u ^ 2))) /
        ((u - 1) / (2 * (1 + u ^ 3))) =
      -3 * (Real.cos (Real.pi / 3 - gd3Psi u) /
        Real.sin (Real.pi / 3 - gd3Psi u)) := by
  have hA : (0 : ℝ) < 1 - u + u ^ 2 := by nlinarith
  have hB : (0 : ℝ) < 1 + u ^ 3 := by positivity
  have hsA : (0 : ℝ) < Real.sqrt (1 - u + u ^ 2) := Real.sqrt_pos.mpr hA
  have hu1ne : u - 1 ≠ 0 := by linarith
  have h1u : 1 - u ≠ 0 := by linarith
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [gd3_cos hu0 hu1, gd3_sin hu0 hu1]
  field_simp
  rw [hr]
  ring

/-- The `gd₄` autonomous law in the paper's quotient form `dψ/ds = 2 cot`. -/
theorem gd4_quotient_ode {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (1 / (1 + u ^ 2)) / (u / (1 - u ^ 4)) =
      2 * (Real.cos (2 * gd4Psi u) / Real.sin (2 * gd4Psi u)) := by
  have hA : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have hu2 : u ^ 2 < 1 := by nlinarith
  have hB : (0 : ℝ) < 1 - u ^ 4 := by nlinarith [sq_nonneg u]
  have hu : u ≠ 0 := ne_of_gt hu0
  rw [gd4_cos, gd4_sin]
  field_simp
  ring

end SliceHyperbolic
