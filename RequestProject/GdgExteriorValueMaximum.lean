/-
gd_g reduced block cover — Phase 8A: the positive exterior critical parameter is
the GLOBAL maximizer of the exterior cover value on `t > 0`.

Write `V_g(t) = gdgExteriorCoverValue g t` and
`R_g(t) = gdgExteriorCriticalRatio g t = cosh ((g-2) t / 2) / cosh (g t / 2)`.

Direct differentiation of the exact definition of `V_g` gives, for `t > 0`,

  `V_g'(t) = g * V_g(t) * L_g(t)`,
  `L_g(t) = sinh (g t) / (cosh (g t) - 1) - sinh t / (cosh t - cos θ_g)`,

every divided quantity being legitimate on `t > 0`: `cosh (g t) - 1 > 0` since
`g t > 0`, and `cosh t - cos θ_g > 0` since `cosh t ≥ 1 > cos θ_g`.

The half-angle identities `sinh (g t) / (cosh (g t) - 1) = cosh (g t/2) / sinh (g t/2)`
and `cosh (g t/2) cosh t - sinh (g t/2) sinh t = cosh ((g-2) t / 2)` show that

  `L_g(t) = cosh (g t/2) * (R_g(t) - cos θ_g) / (sinh (g t/2) * (cosh t - cos θ_g))`,

so `L_g(t)` has exactly the sign of `R_g(t) - cos θ_g`.  Strict antitonicity of
`R_g` on `(0, ∞)` (`gdgExteriorCriticalRatio_strictAntiOn`) therefore turns a
positive critical parameter `t⋆` (i.e. `R_g(t⋆) = cos θ_g`) into a sign change of
`V_g'`: positive on `(0, t⋆)`, negative on `(t⋆, ∞)`.  The mean-value monotonicity
API then yields the GLOBAL statement `IsGreatest (V_g '' Set.Ioi 0) (V_g t⋆)`, and
in particular `V_g (θ_g) ≤ V_g (t⋆)` for the explicit exterior test point.

Nothing about the interior uniform bound, the exterior/interior separation,
critical-value injectivity, monodromy, or a Galois group is claimed here.
-/
import RequestProject.GdgCriticalValuePairwise

namespace GdgSquarefree

/-- Local reproof (the `GdgExteriorRoot` version is private): `cos θ_g < 1`. -/
private theorem cos_gdgTheta_lt_one_local {g : ℕ} (hg : 5 ≤ g) :
    Real.cos (gdgTheta g) < 1 := by
  have h0 : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have h1 : gdgTheta g < Real.pi / 2 := gdgTheta_lt_pi_div_two hg
  have hpi := Real.pi_pos
  have h2 : gdgTheta g ≤ Real.pi := by linarith
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) h2 h0
  simpa using this

/-- The exterior denominator `cosh t - cos θ_g` is strictly positive. -/
private theorem exterior_denom_pos {g : ℕ} (hg : 5 ≤ g) (t : ℝ) :
    0 < Real.cosh t - Real.cos (gdgTheta g) := by
  have h1 : (1 : ℝ) ≤ Real.cosh t := Real.one_le_cosh t
  have h2 := cos_gdgTheta_lt_one_local hg
  linarith

/-- **Target 1.** Exact derivative of the exterior cover value at a positive
parameter, in factored logarithmic-derivative form. -/
theorem gdgExteriorCoverValue_hasDerivAt
    {g : ℕ} (hg : 5 ≤ g) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gdgExteriorCoverValue g)
      ((g : ℝ) * gdgExteriorCoverValue g t *
        (Real.sinh ((g : ℝ) * t) /
            (Real.cosh ((g : ℝ) * t) - 1) -
          Real.sinh t /
            (Real.cosh t - Real.cos (gdgTheta g)))) t := by
  obtain ⟨m, rfl⟩ : ∃ m, g = m + 1 := ⟨g - 1, by omega⟩
  have hg0 : (0 : ℝ) < ((m : ℝ) + 1) := by positivity
  have hDpos : 0 < Real.cosh t - Real.cos (gdgTheta (m + 1)) := exterior_denom_pos hg t
  have hD : (0 : ℝ) < 2 * (Real.cosh t - Real.cos (gdgTheta (m + 1))) := by linarith
  have hgt : ((m : ℝ) + 1) * t ≠ 0 := by positivity
  have hcgt : 1 < Real.cosh (((m : ℝ) + 1) * t) := Real.one_lt_cosh.mpr hgt
  have hN : HasDerivAt (fun s : ℝ => 2 * (Real.cosh (((m : ℝ) + 1) * s) - 1))
      (2 * (Real.sinh (((m : ℝ) + 1) * t) * ((m : ℝ) + 1))) t := by
    have h0 : HasDerivAt (fun s : ℝ => ((m : ℝ) + 1) * s) ((m : ℝ) + 1) t := by
      simpa using (hasDerivAt_id t).const_mul ((m : ℝ) + 1)
    have h1 := (Real.hasDerivAt_cosh (((m : ℝ) + 1) * t)).comp t h0
    simpa using (h1.sub_const 1).const_mul 2
  have hDd : HasDerivAt
      (fun s : ℝ => (2 * (Real.cosh s - Real.cos (gdgTheta (m + 1)))) ^ (m + 1))
      (((m : ℝ) + 1) * (2 * (Real.cosh t - Real.cos (gdgTheta (m + 1)))) ^ m *
        (2 * Real.sinh t)) t := by
    have h0 : HasDerivAt (fun s : ℝ => 2 * (Real.cosh s - Real.cos (gdgTheta (m + 1))))
        (2 * Real.sinh t) t := by
      simpa using
        ((Real.hasDerivAt_cosh t).sub_const (Real.cos (gdgTheta (m + 1)))).const_mul 2
    simpa using h0.fun_pow (m + 1)
  have hquot := hN.div hDd (by positivity)
  have main : HasDerivAt (gdgExteriorCoverValue (m + 1))
      ((2 * (Real.sinh (((m : ℝ) + 1) * t) * ((m : ℝ) + 1)) *
            (2 * (Real.cosh t - Real.cos (gdgTheta (m + 1)))) ^ (m + 1) -
          2 * (Real.cosh (((m : ℝ) + 1) * t) - 1) *
            (((m : ℝ) + 1) * (2 * (Real.cosh t - Real.cos (gdgTheta (m + 1)))) ^ m *
              (2 * Real.sinh t))) /
        ((2 * (Real.cosh t - Real.cos (gdgTheta (m + 1)))) ^ (m + 1)) ^ 2) t := by
    have hfun : gdgExteriorCoverValue (m + 1) =
        fun s : ℝ => 2 * (Real.cosh (((m : ℝ) + 1) * s) - 1) /
          (2 * (Real.cosh s - Real.cos (gdgTheta (m + 1)))) ^ (m + 1) := by
      funext s
      simp only [gdgExteriorCoverValue, Nat.cast_add, Nat.cast_one]
    rw [hfun]
    exact hquot
  have hDne : (2 * (Real.cosh t - Real.cos (gdgTheta (m + 1)))) ≠ 0 := ne_of_gt hD
  have hcne : Real.cosh (((m : ℝ) + 1) * t) - 1 ≠ 0 := by
    intro h; linarith [h]
  have hdne : Real.cosh t - Real.cos (gdgTheta (m + 1)) ≠ 0 := ne_of_gt hDpos
  have hEq :
      (2 * (Real.sinh (((m : ℝ) + 1) * t) * ((m : ℝ) + 1)) *
            (2 * (Real.cosh t - Real.cos (gdgTheta (m + 1)))) ^ (m + 1) -
          2 * (Real.cosh (((m : ℝ) + 1) * t) - 1) *
            (((m : ℝ) + 1) * (2 * (Real.cosh t - Real.cos (gdgTheta (m + 1)))) ^ m *
              (2 * Real.sinh t))) /
        ((2 * (Real.cosh t - Real.cos (gdgTheta (m + 1)))) ^ (m + 1)) ^ 2 =
      ((m + 1 : ℕ) : ℝ) * gdgExteriorCoverValue (m + 1) t *
        (Real.sinh (((m + 1 : ℕ) : ℝ) * t) /
            (Real.cosh (((m + 1 : ℕ) : ℝ) * t) - 1) -
          Real.sinh t /
            (Real.cosh t - Real.cos (gdgTheta (m + 1)))) := by
    simp only [gdgExteriorCoverValue, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  exact hEq ▸ main

/-- The logarithmic slope, rewritten as a positive multiple of
`gdgExteriorCriticalRatio g t - cos θ_g`. -/
private theorem gdgExterior_logSlope_eq {g : ℕ} (hg : 5 ≤ g) {t : ℝ} (ht : 0 < t) :
    Real.sinh ((g : ℝ) * t) / (Real.cosh ((g : ℝ) * t) - 1) -
        Real.sinh t / (Real.cosh t - Real.cos (gdgTheta g)) =
      Real.cosh ((g : ℝ) * t / 2) *
          (gdgExteriorCriticalRatio g t - Real.cos (gdgTheta g)) /
        (Real.sinh ((g : ℝ) * t / 2) *
          (Real.cosh t - Real.cos (gdgTheta g))) := by
  have hg0 : (0 : ℝ) < (g : ℝ) := by
    have : (5 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    linarith
  have hhalf : 0 < (g : ℝ) * t / 2 := by positivity
  have hs : 0 < Real.sinh ((g : ℝ) * t / 2) := Real.sinh_pos_iff.mpr hhalf
  have hch : 0 < Real.cosh ((g : ℝ) * t / 2) := Real.cosh_pos _
  have hDpos : 0 < Real.cosh t - Real.cos (gdgTheta g) := exterior_denom_pos hg t
  have h2 : (g : ℝ) * t = 2 * ((g : ℝ) * t / 2) := by ring
  have hsinh : Real.sinh ((g : ℝ) * t) =
      2 * Real.sinh ((g : ℝ) * t / 2) * Real.cosh ((g : ℝ) * t / 2) := by
    conv_lhs => rw [h2, Real.sinh_two_mul]
  have hcosh : Real.cosh ((g : ℝ) * t) - 1 = 2 * Real.sinh ((g : ℝ) * t / 2) ^ 2 := by
    have hc2 : Real.cosh ((g : ℝ) * t) =
        Real.cosh ((g : ℝ) * t / 2) ^ 2 + Real.sinh ((g : ℝ) * t / 2) ^ 2 := by
      conv_lhs => rw [h2, Real.cosh_two_mul]
    rw [hc2]
    nlinarith [Real.cosh_sq_sub_sinh_sq ((g : ℝ) * t / 2)]
  have hsub : Real.cosh (((g : ℝ) - 2) * t / 2) =
      Real.cosh ((g : ℝ) * t / 2) * Real.cosh t -
        Real.sinh ((g : ℝ) * t / 2) * Real.sinh t := by
    have he : ((g : ℝ) - 2) * t / 2 = (g : ℝ) * t / 2 - t := by ring
    rw [he, Real.cosh_sub]
  have hsne : Real.sinh ((g : ℝ) * t / 2) ≠ 0 := ne_of_gt hs
  have hchne : Real.cosh ((g : ℝ) * t / 2) ≠ 0 := ne_of_gt hch
  have hDne : Real.cosh t - Real.cos (gdgTheta g) ≠ 0 := ne_of_gt hDpos
  rw [gdgExteriorCriticalRatio, hsinh, hcosh, hsub]
  field_simp
  ring

/-- **Target 2.** Strictly positive logarithmic slope strictly below the
critical parameter. -/
theorem gdgExterior_logSlope_pos_of_lt_critical
    {g : ℕ} (hg : 5 ≤ g) {t tstar : ℝ}
    (ht : 0 < t) (htstar : 0 < tstar) (hlt : t < tstar)
    (hcritical :
      gdgExteriorCriticalRatio g tstar = Real.cos (gdgTheta g)) :
    0 <
      Real.sinh ((g : ℝ) * t) /
          (Real.cosh ((g : ℝ) * t) - 1) -
        Real.sinh t /
          (Real.cosh t - Real.cos (gdgTheta g)) := by
  have hg0 : (0 : ℝ) < (g : ℝ) := by
    have : (5 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    linarith
  have hratio : Real.cos (gdgTheta g) < gdgExteriorCriticalRatio g t := by
    have := (gdgExteriorCriticalRatio_strictAntiOn hg) (Set.mem_Ioi.mpr ht)
      (Set.mem_Ioi.mpr htstar) hlt
    rwa [hcritical] at this
  have hs : 0 < Real.sinh ((g : ℝ) * t / 2) :=
    Real.sinh_pos_iff.mpr (by positivity)
  have hch : 0 < Real.cosh ((g : ℝ) * t / 2) := Real.cosh_pos _
  have hDpos : 0 < Real.cosh t - Real.cos (gdgTheta g) := exterior_denom_pos hg t
  rw [gdgExterior_logSlope_eq hg ht]
  apply div_pos
  · exact mul_pos hch (by linarith)
  · exact mul_pos hs hDpos

/-- **Target 3.** Strictly negative logarithmic slope strictly above the
critical parameter. -/
theorem gdgExterior_logSlope_neg_of_critical_lt
    {g : ℕ} (hg : 5 ≤ g) {tstar t : ℝ}
    (htstar : 0 < tstar) (ht : 0 < t) (hlt : tstar < t)
    (hcritical :
      gdgExteriorCriticalRatio g tstar = Real.cos (gdgTheta g)) :
    Real.sinh ((g : ℝ) * t) /
          (Real.cosh ((g : ℝ) * t) - 1) -
        Real.sinh t /
          (Real.cosh t - Real.cos (gdgTheta g)) < 0 := by
  have hg0 : (0 : ℝ) < (g : ℝ) := by
    have : (5 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    linarith
  have hratio : gdgExteriorCriticalRatio g t < Real.cos (gdgTheta g) := by
    have := (gdgExteriorCriticalRatio_strictAntiOn hg) (Set.mem_Ioi.mpr htstar)
      (Set.mem_Ioi.mpr ht) hlt
    rwa [hcritical] at this
  have hs : 0 < Real.sinh ((g : ℝ) * t / 2) :=
    Real.sinh_pos_iff.mpr (by positivity)
  have hch : 0 < Real.cosh ((g : ℝ) * t / 2) := Real.cosh_pos _
  have hDpos : 0 < Real.cosh t - Real.cos (gdgTheta g) := exterior_denom_pos hg t
  rw [gdgExterior_logSlope_eq hg ht]
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_pos_of_neg hch (by linarith)
  · exact mul_pos hs hDpos

/-- Strict increase of the exterior cover value strictly below the critical
parameter. -/
private theorem gdgExteriorCoverValue_strictMonoOn_below
    {g : ℕ} (hg : 5 ≤ g) {a tstar : ℝ} (ha : 0 < a) (htstar : 0 < tstar)
    (hcritical : gdgExteriorCriticalRatio g tstar = Real.cos (gdgTheta g)) :
    StrictMonoOn (gdgExteriorCoverValue g) (Set.Icc a tstar) := by
  have hg0 : (0 : ℝ) < (g : ℝ) := by
    have : (5 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    linarith
  refine strictMonoOn_of_deriv_pos (convex_Icc a tstar) ?_ ?_
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    exact ((gdgExteriorCoverValue_hasDerivAt hg hx0).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := lt_trans ha hx.1
    rw [(gdgExteriorCoverValue_hasDerivAt hg hx0).deriv]
    exact mul_pos (mul_pos hg0 (gdgExteriorCoverValue_pos hg hx0))
      (gdgExterior_logSlope_pos_of_lt_critical hg hx0 htstar hx.2 hcritical)

/-- Strict decrease of the exterior cover value strictly above the critical
parameter. -/
private theorem gdgExteriorCoverValue_strictAntiOn_above
    {g : ℕ} (hg : 5 ≤ g) {tstar b : ℝ} (htstar : 0 < tstar)
    (hcritical : gdgExteriorCriticalRatio g tstar = Real.cos (gdgTheta g)) :
    StrictAntiOn (gdgExteriorCoverValue g) (Set.Icc tstar b) := by
  have hg0 : (0 : ℝ) < (g : ℝ) := by
    have : (5 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    linarith
  refine strictAntiOn_of_deriv_neg (convex_Icc tstar b) ?_ ?_
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le htstar hx.1
    exact ((gdgExteriorCoverValue_hasDerivAt hg hx0).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := lt_trans htstar hx.1
    rw [(gdgExteriorCoverValue_hasDerivAt hg hx0).deriv]
    have hneg := gdgExterior_logSlope_neg_of_critical_lt hg htstar hx0 hx.1 hcritical
    have hpos := mul_pos hg0 (gdgExteriorCoverValue_pos hg hx0)
    exact mul_neg_of_pos_of_neg hpos hneg

/-- **Target 4.** The exterior cover value at a positive critical parameter is
the global maximum of the exterior cover value over the whole positive ray. -/
theorem gdgExteriorCoverValue_isGreatest_of_critical
    {g : ℕ} (hg : 5 ≤ g) {tstar : ℝ}
    (htstar : 0 < tstar)
    (hcritical :
      gdgExteriorCriticalRatio g tstar = Real.cos (gdgTheta g)) :
    IsGreatest
      (gdgExteriorCoverValue g '' Set.Ioi 0)
      (gdgExteriorCoverValue g tstar) := by
  refine ⟨⟨tstar, Set.mem_Ioi.mpr htstar, rfl⟩, ?_⟩
  rintro v ⟨t, ht, rfl⟩
  have ht0 : 0 < t := ht
  rcases lt_trichotomy t tstar with hlt | heq | hgt
  · have hmono := gdgExteriorCoverValue_strictMonoOn_below hg ht0 htstar hcritical
    exact le_of_lt
      (hmono (Set.left_mem_Icc.mpr (le_of_lt hlt)) (Set.right_mem_Icc.mpr (le_of_lt hlt)) hlt)
  · rw [heq]
  · have hanti := gdgExteriorCoverValue_strictAntiOn_above (b := t) hg htstar hcritical
    exact le_of_lt
      (hanti (Set.left_mem_Icc.mpr (le_of_lt hgt)) (Set.right_mem_Icc.mpr (le_of_lt hgt)) hgt)

/-- **Target 5.** In particular the critical exterior value dominates the
explicit exterior test value at `t = θ_g`. -/
theorem gdgExteriorCoverValue_theta_le_of_critical
    {g : ℕ} (hg : 5 ≤ g) {tstar : ℝ}
    (htstar : 0 < tstar)
    (hcritical :
      gdgExteriorCriticalRatio g tstar = Real.cos (gdgTheta g)) :
    gdgExteriorCoverValue g (gdgTheta g) ≤
      gdgExteriorCoverValue g tstar := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  exact (gdgExteriorCoverValue_isGreatest_of_critical hg htstar hcritical).2
    ⟨gdgTheta g, Set.mem_Ioi.mpr hth, rfl⟩

end GdgSquarefree
