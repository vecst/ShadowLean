/-
# Phase 8B — quantitative ODD-row exterior/interior separation

For odd `g ≥ 7` we bound the interior magnitude uniformly on every retained
lobe, evaluate the exterior cover exactly at `t = θ_g`, and combine with the
already-proved powered scalar inequality `gdg_one_lt_powered` to obtain a strict
separation between the exterior critical value and the interior magnitude at
EVERY point of every retained odd lobe.

Contents:
* `gdgOdd_retained_lobeRight_le_pi_sub_two_theta`
* `gdgOdd_retained_interior_denominator_lower_bound`
* `gdgOdd_retained_interior_magnitude_le`
* `gdgExteriorCoverValue_at_theta`
* `gdg_uniformInteriorBound_lt_exterior_theta`
* `gdgOdd_retained_lobe_magnitude_lt_exterior_critical`

NOT proved here: the `g = 5` case, the even-parity sign separation, the final
all-parity noncollision, critical-value injectivity, monodromy, or any Galois
statement.
-/
import RequestProject.GdgExteriorValueMaximum

namespace GdgSquarefree

/-- `π` expressed through the period step: `π = g · θ_g / 2`. -/
private theorem gdg_pi_eq_mul_theta {g : ℕ} (hg : 1 ≤ g) :
    Real.pi = (g : ℝ) * gdgTheta g / 2 := by
  have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  simp only [gdgTheta]
  field_simp

/-- For `g ≥ 7` the period step satisfies `0 < θ_g ≤ 2π/7`. -/
private theorem gdg_theta_bounds {g : ℕ} (hg : 7 ≤ g) :
    0 < gdgTheta g ∧ gdgTheta g ≤ 2 * Real.pi / 7 := by
  have hg1 : 1 ≤ g := by omega
  refine ⟨gdgTheta_pos hg1, ?_⟩
  have hg7 : (7 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have h7 : (0 : ℝ) < 7 := by norm_num
  simpa [gdgTheta] using
    div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 * Real.pi) h7 hg7

/-- Positivity of the interior scalar gap `cos θ - cos 2θ` for `g ≥ 7`. -/
private theorem gdg_cos_gap_pos {g : ℕ} (hg : 7 ≤ g) :
    0 < Real.cos (gdgTheta g) - Real.cos (2 * gdgTheta g) := by
  obtain ⟨h0, h7⟩ := gdg_theta_bounds hg
  have hden : 0 < Real.cosh (gdgTheta g) - Real.cos (gdgTheta g) :=
    gdg_cosh_sub_cos_pos h0 h7
  have hratio := gdg_one_lt_ratio h0 h7
  rw [lt_div_iff₀ hden] at hratio
  linarith

/-- **Target 1.** On an odd retained lobe the right endpoint stays below
`π - 2θ_g`. Equality is attained at the last retained lobe (e.g. `g = 7`). -/
theorem gdgOdd_retained_lobeRight_le_pi_sub_two_theta
    {g j : ℕ} (hg : 7 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) :
    gdgLobeRight g j ((1 : ℝ) / 2) ≤
      Real.pi - 2 * gdgTheta g := by
  have hjlt : j < gdgRetainedLobeCount g := gdg_mem_retainedLobeIndices_iff.mp hj
  have hnat : 2 * j + 7 ≤ g := by
    obtain ⟨m, rfl⟩ := hOdd
    unfold gdgRetainedLobeCount at hjlt
    omega
  have hcast : 2 * (j : ℝ) + 7 ≤ (g : ℝ) := by exact_mod_cast hnat
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hpi : Real.pi = (g : ℝ) * gdgTheta g / 2 := gdg_pi_eq_mul_theta (by omega)
  have hmul : (2 * (j : ℝ) + 7) * gdgTheta g ≤ (g : ℝ) * gdgTheta g :=
    mul_le_mul_of_nonneg_right hcast hth.le
  simp only [gdgLobeRight, gdgLobeLeft]
  rw [hpi]
  linarith

/-- **Target 2.** Uniform lower bound for the interior denominator on a
retained odd lobe (closed interval, endpoints included). -/
theorem gdgOdd_retained_interior_denominator_lower_bound
    {g j : ℕ} (hg : 7 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Icc
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2))) :
    2 *
        (Real.cos (gdgTheta g) -
          Real.cos (2 * gdgTheta g)) ≤
      gdgInteriorDenominator g phi := by
  have hth : 0 < gdgTheta g := gdgTheta_pos (by omega)
  have hleft0 : 0 ≤ gdgLobeLeft g j ((1 : ℝ) / 2) := by
    have : (0 : ℝ) ≤ (j : ℝ) + 1 / 2 := by positivity
    simpa [gdgLobeLeft] using mul_nonneg this hth.le
  have hphi0 : 0 ≤ phi := le_trans hleft0 hphi.1
  have hupper : phi ≤ Real.pi - 2 * gdgTheta g :=
    le_trans hphi.2 (gdgOdd_retained_lobeRight_le_pi_sub_two_theta hg hOdd hj)
  have hpile : Real.pi - 2 * gdgTheta g ≤ Real.pi := by linarith
  have hcos : Real.cos (Real.pi - 2 * gdgTheta g) ≤ Real.cos phi :=
    Real.cos_le_cos_of_nonneg_of_le_pi hphi0 hpile hupper
  rw [Real.cos_pi_sub] at hcos
  simp only [gdgInteriorDenominator]
  linarith

/-- **Target 3.** Uniform upper bound for the interior magnitude on a retained
odd lobe (closed interval, endpoints included). -/
theorem gdgOdd_retained_interior_magnitude_le
    {g j : ℕ} (hg : 7 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi : ℝ}
    (hphi : phi ∈ Set.Icc
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2))) :
    gdgInteriorMagnitude g phi ≤
      4 /
        (2 *
          (Real.cos (gdgTheta g) -
            Real.cos (2 * gdgTheta g))) ^ g := by
  have hnum : gdgInteriorNumeratorAbs g phi ≤ 4 := by
    have hc : |Real.cos ((g : ℝ) * phi)| ≤ 1 := Real.abs_cos_le_one _
    have hsign : |((-1 : ℝ) ^ g)| = 1 := by
      simp [abs_pow]
    simp only [gdgInteriorNumeratorAbs]
    have h1 : |2 * Real.cos ((g : ℝ) * phi)| ≤ 2 := by
      rw [abs_mul]; simp only [abs_two]; linarith
    have h2 : |2 * ((-1 : ℝ) ^ g)| ≤ 2 := by
      rw [abs_mul, hsign]; simp
    calc |2 * Real.cos ((g : ℝ) * phi) - 2 * ((-1 : ℝ) ^ g)|
        ≤ |2 * Real.cos ((g : ℝ) * phi)| + |2 * ((-1 : ℝ) ^ g)| := abs_sub _ _
      _ ≤ 4 := by linarith
  have hA : 0 < Real.cos (gdgTheta g) - Real.cos (2 * gdgTheta g) := gdg_cos_gap_pos hg
  have hbase : 0 < 2 * (Real.cos (gdgTheta g) - Real.cos (2 * gdgTheta g)) := by linarith
  have hden := gdgOdd_retained_interior_denominator_lower_bound hg hOdd hj hphi
  have hpow :
      (2 * (Real.cos (gdgTheta g) - Real.cos (2 * gdgTheta g))) ^ g ≤
        (gdgInteriorDenominator g phi) ^ g :=
    pow_le_pow_left₀ hbase.le hden g
  have hpowpos : 0 < (2 * (Real.cos (gdgTheta g) - Real.cos (2 * gdgTheta g))) ^ g :=
    pow_pos hbase g
  simp only [gdgInteriorMagnitude]
  exact div_le_div₀ (by norm_num) hnum hpowpos hpow

/-- **Target 4.** Exact value of the exterior cover at `t = θ_g`, using the
exact identity `g · θ_g = 2π`. -/
theorem gdgExteriorCoverValue_at_theta
    {g : ℕ} (hg : 1 ≤ g) :
    gdgExteriorCoverValue g (gdgTheta g) =
      2 * (Real.cosh (2 * Real.pi) - 1) /
        (2 *
          (Real.cosh (gdgTheta g) -
            Real.cos (gdgTheta g))) ^ g := by
  have hg0 : (g : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
    exact ne_of_gt this
  have hid : (g : ℝ) * gdgTheta g = 2 * Real.pi := by
    simp only [gdgTheta]
    field_simp
  simp only [gdgExteriorCoverValue, hid]

/-- **Target 5.** The uniform interior upper bound is strictly below the
exterior cover value at `t = θ_g`. -/
theorem gdg_uniformInteriorBound_lt_exterior_theta
    {g : ℕ} (hg : 7 ≤ g) :
    4 /
        (2 *
          (Real.cos (gdgTheta g) -
            Real.cos (2 * gdgTheta g))) ^ g <
      gdgExteriorCoverValue g (gdgTheta g) := by
  obtain ⟨h0, h7⟩ := gdg_theta_bounds hg
  have hg1 : 1 ≤ g := by omega
  have hA : 0 < Real.cos (gdgTheta g) - Real.cos (2 * gdgTheta g) := gdg_cos_gap_pos hg
  have hB : 0 < Real.cosh (gdgTheta g) - Real.cos (gdgTheta g) :=
    gdg_cosh_sub_cos_pos h0 h7
  have hpowered := gdg_one_lt_powered h0 h7 hg1
  rw [div_pow] at hpowered
  have hAg : 0 < (Real.cos (gdgTheta g) - Real.cos (2 * gdgTheta g)) ^ g := pow_pos hA g
  have hBg : 0 < (Real.cosh (gdgTheta g) - Real.cos (gdgTheta g)) ^ g := pow_pos hB g
  have hkey :
      2 * (Real.cosh (gdgTheta g) - Real.cos (gdgTheta g)) ^ g <
        (Real.cosh (2 * Real.pi) - 1) *
          (Real.cos (gdgTheta g) - Real.cos (2 * gdgTheta g)) ^ g := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hBg] at hpowered
    linarith
  rw [gdgExteriorCoverValue_at_theta hg1]
  have h2g : (0 : ℝ) < (2 : ℝ) ^ g := by positivity
  have hL : (2 * (Real.cos (gdgTheta g) - Real.cos (2 * gdgTheta g))) ^ g
      = 2 ^ g * (Real.cos (gdgTheta g) - Real.cos (2 * gdgTheta g)) ^ g := by
    rw [mul_pow]
  have hR : (2 * (Real.cosh (gdgTheta g) - Real.cos (gdgTheta g))) ^ g
      = 2 ^ g * (Real.cosh (gdgTheta g) - Real.cos (gdgTheta g)) ^ g := by
    rw [mul_pow]
  rw [hL, hR, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey, h2g, hAg, hBg]

/-- **Target 6.** Strict separation: at every point of every retained odd lobe
the interior magnitude is strictly smaller than the exterior cover value at any
positive exterior critical parameter. -/
theorem gdgOdd_retained_lobe_magnitude_lt_exterior_critical
    {g j : ℕ} (hg : 7 ≤ g) (hOdd : Odd g)
    (hj : j ∈ gdgRetainedLobeIndices g) {phi tstar : ℝ}
    (hphi : phi ∈ Set.Icc
      (gdgLobeLeft g j ((1 : ℝ) / 2))
      (gdgLobeRight g j ((1 : ℝ) / 2)))
    (htstar : 0 < tstar)
    (hcritical :
      gdgExteriorCriticalRatio g tstar = Real.cos (gdgTheta g)) :
    gdgInteriorMagnitude g phi <
      gdgExteriorCoverValue g tstar :=
  lt_of_le_of_lt (gdgOdd_retained_interior_magnitude_le hg hOdd hj hphi)
    (lt_of_lt_of_le (gdg_uniformInteriorBound_lt_exterior_theta hg)
      (gdgExteriorCoverValue_theta_le_of_critical (by omega) htstar hcritical))

end GdgSquarefree
