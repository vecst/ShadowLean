/-
Dual-slice logarithm construction: convergence to `Real.log`.

The finite evaluator `binomialLog` uses only integer powers, binomial
coefficients, arithmetic, and division. Its fixed-`g` row limit is the
`logSurrogate` (NOT `Real.log x`); the surrogate then tends to `Real.log x`
as `g → ∞`, giving a genuine two-stage (iterated) convergence theorem.

Reuses `slice`, `tendsto_slice_ratio_rpow`, `tendstoUniformlyOn_slice_ratio`;
does not redefine the residue-slice construction or reprove slice-ratio
convergence.  The power in `logSurrogate` is `Real.rpow` (`x ^ (…: ℝ)`).

All requested results below preserve their mathematical content and boundary hypotheses.
-/
import RequestProject.CompactUniform

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace ResidueSlices

/-- Finite-row numerator: `2g·(x·Q_{g-1} − Q_1)`. -/
noncomputable def logNumerator (g N : ℕ) (x : ℝ) : ℝ :=
  2 * (g : ℝ) * (x * slice g (g - 1) N x - slice g 1 N x)

/-- Finite-row denominator: `x·Q_{g-1} + 2·Q_0 + Q_1`. -/
noncomputable def logDenominator (g N : ℕ) (x : ℝ) : ℝ :=
  x * slice g (g - 1) N x + 2 * slice g 0 N x + slice g 1 N x

/-- The finite dual-slice logarithm evaluator (integer powers only). -/
noncomputable def binomialLog (g N : ℕ) (x : ℝ) : ℝ :=
  logNumerator g N x / logDenominator g N x

/-- Fixed-`g` limiting surrogate `2g·(x^(1/g) − 1)/(x^(1/g) + 1)` (`rpow`). -/
noncomputable def logSurrogate (g : ℕ) (x : ℝ) : ℝ :=
  2 * (g : ℝ) * (x ^ ((g : ℝ)⁻¹) - 1) / (x ^ ((g : ℝ)⁻¹) + 1)

/-- **Target 1 — fixed-`g` row limit.**  For `g ≥ 2`, `x > 0`,
`binomialLog g N x → logSurrogate g x` as `N → ∞`. -/
theorem tendsto_binomialLog_row {g : ℕ} (hg : 2 ≤ g) {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (fun N : ℕ => binomialLog g N x)
      Filter.atTop (nhds (logSurrogate g x)) := by
  unfold binomialLog logNumerator logDenominator logSurrogate
  -- Define the slice ratios that appear in the limit
  let R1 : ℕ → ℝ := fun N => slice g (g - 1) N x / slice g 0 N x
  let R2 : ℕ → ℝ := fun N => slice g 1 N x / slice g 0 N x
  -- The key limits: slice ratios converge
  have hR1 : Filter.Tendsto R1 Filter.atTop (nhds (x ^ (-(↑(g - 1) : ℝ) / ↑g))) := by
    have hkg : g - 1 < g := by omega
    exact tendsto_slice_ratio_rpow (by linarith : 0 < g) hkg hx
  have hR2 : Filter.Tendsto R2 Filter.atTop (nhds (x ^ (-(1 : ℝ) / ↑g))) := by
    simpa using tendsto_slice_ratio_rpow (by linarith : 0 < g) (by omega : 1 < g) hx
  -- Rewrite the function using R1 and R2
  have goal_eq : (2 : ℝ) * ↑g * (x ^ (↑g : ℝ)⁻¹ - 1) / (x ^ (↑g : ℝ)⁻¹ + 1) =
      (2 : ℝ) * ↑g * (x ^ (g⁻¹ : ℝ) - 1) / (x ^ (g⁻¹ : ℝ) + 1) := rfl
  rw [goal_eq]
  suffices h : Filter.Tendsto (fun N => 2 * ↑g * (x * R1 N - R2 N) / (x * R1 N + 2 + R2 N))
      Filter.atTop (nhds (2 * ↑g * (x ^ (g⁻¹ : ℝ) - 1) / (x ^ (g⁻¹ : ℝ) + 1))) by
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hz : slice g 0 N x ≠ 0 := ne_of_gt (slice_zero_pos g N hx.le)
    simp only [R1, R2]
    field_simp
  -- Limits of numerator and denominator
  have hnum : Filter.Tendsto (fun N => x * R1 N - R2 N) Filter.atTop
      (nhds (x * x ^ (-(↑(g - 1) : ℝ) / ↑g) - x ^ (-(1 : ℝ) / ↑g))) :=
    Filter.Tendsto.sub (hR1.const_mul x) hR2
  have hden : Filter.Tendsto (fun N => x * R1 N + 2 + R2 N) Filter.atTop
      (nhds (x * x ^ (-(↑(g - 1) : ℝ) / ↑g) + 2 + x ^ (-(1 : ℝ) / ↑g))) :=
    Filter.Tendsto.add (Filter.Tendsto.add (hR1.const_mul x) tendsto_const_nhds) hR2
  -- Simplify the limit values
  have hx_g : x * x ^ (-(↑(g - 1) : ℝ) / ↑g) = x ^ ((g : ℝ)⁻¹) := by
    have hexp : (1 : ℝ) + (-(↑(g - 1) : ℝ) / ↑g) = (g : ℝ)⁻¹ := by
      rw [Nat.cast_sub (by linarith : 1 ≤ g)]
      field_simp
      ring
    calc x * x ^ (-(↑(g - 1) : ℝ) / ↑g)
        = x ^ (1 : ℝ) * x ^ (-(↑(g - 1) : ℝ) / ↑g) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (-(↑(g - 1) : ℝ) / ↑g)) := by rw [← Real.rpow_add hx]
      _ = x ^ ((g : ℝ)⁻¹) := by rw [hexp]
  have neg_inv_eq : (-(↑g : ℝ)⁻¹) = (-1 : ℝ) / ↑g := by ring
  -- Simplify hnum and hden using hx_g
  have hnum' : Filter.Tendsto (fun N => x * R1 N - R2 N) Filter.atTop
      (nhds (x ^ ((g : ℝ)⁻¹) - x ^ (-(↑g : ℝ)⁻¹))) := by
    convert hnum using 1
    congr 1; rw [hx_g]; rw [neg_inv_eq]
  have hden' : Filter.Tendsto (fun N => x * R1 N + 2 + R2 N) Filter.atTop
      (nhds (x ^ ((g : ℝ)⁻¹) + 2 + x ^ (-(↑g : ℝ)⁻¹))) := by
    convert hden using 1
    congr 1; rw [hx_g]; rw [neg_inv_eq]
  -- Algebraic identity: (y - 1/y) / (y + 2 + 1/y) = (y - 1) / (y + 1) for y > 0
  set y := x ^ ((g : ℝ)⁻¹) with hy_def
  have hy_pos : 0 < y := Real.rpow_pos_of_pos hx _
  have hy_inv : x ^ (-(↑g : ℝ)⁻¹) = y⁻¹ := by
    rw [hy_def, ← Real.rpow_neg hx.le]
  have algebraic_id : (y - y⁻¹) / (y + 2 + y⁻¹) = (y - 1) / (y + 1) := by
    have h1 : y + 1 ≠ 0 := by linarith
    have h2 : y + 2 + y⁻¹ ≠ 0 := by nlinarith [inv_pos.mpr hy_pos]
    field_simp [h1, h2]
    ring
  -- Rewrite hnum' and hden' using hy_inv
  have hnum'' : Filter.Tendsto (fun N => x * R1 N - R2 N) Filter.atTop (nhds (y - y⁻¹)) := by
    convert hnum' using 1
    rw [hy_inv]
  have hden'' : Filter.Tendsto (fun N => x * R1 N + 2 + R2 N) Filter.atTop (nhds (y + 2 + y⁻¹)) := by
    convert hden' using 1
    rw [hy_inv]
  -- The denominator is positive
  have hden_pos : y + 2 + y⁻¹ > 0 := by nlinarith [inv_pos.mpr hy_pos]
  -- Use Filter.Tendsto.div
  have hdiv : Filter.Tendsto (fun N => (x * R1 N - R2 N) / (x * R1 N + 2 + R2 N)) Filter.atTop
      (nhds ((y - y⁻¹) / (y + 2 + y⁻¹))) :=
    Filter.Tendsto.div hnum'' hden'' (by linarith)
  -- Rewrite using algebraic_id
  rw [algebraic_id] at hdiv
  -- Multiply by 2 * g
  have hfinal := hdiv.const_mul (2 * (g : ℝ))
  convert hfinal using 2 <;> ring

/-- **Target 2 — exact tanh closed form.**  `logSurrogate g x
= 2g·tanh(log x / (2g))` (analytic identification only). -/
theorem logSurrogate_eq_tanh {g : ℕ} (hg : 1 ≤ g) {x : ℝ} (hx : 0 < x) :
    logSurrogate g x = 2 * (g : ℝ) * Real.tanh (Real.log x / (2 * (g : ℝ))) := by
  unfold logSurrogate
  rw [Real.tanh_eq_sinh_div_cosh]
  have hg_pos : (0 : ℝ) < g := Nat.cast_pos.mpr (by linarith)
  -- Key: sinh(y)/cosh(y) = (e^y - e^(-y))/(e^y + e^(-y)) where y = log x / (2g)
  -- e^y = x^(1/(2g)), e^(-y) = x^(-1/(2g))
  -- Let u = x^(1/(2g)), then (u - 1/u)/(u + 1/u) = (u² - 1)/(u² + 1) = (x^(1/g) - 1)/(x^(1/g) + 1)
  set y := Real.log x / (2 * (g : ℝ)) with hy_def
  set u := x ^ ((g : ℝ)⁻¹ / 2) with hu_def
  have hu_pos : 0 < u := Real.rpow_pos_of_pos hx _
  -- Show y = log u
  have hy_eq_log_u : y = Real.log u := by
    rw [hu_def, Real.log_rpow hx]
    ring
  -- Show sinh(y) / cosh(y) = (u - 1/u) / (u + 1/u)
  have h_sinh_cosh : Real.sinh y / Real.cosh y = (u - u⁻¹) / (u + u⁻¹) := by
    rw [hy_eq_log_u]
    have h1 : Real.sinh (Real.log u) = (u - u⁻¹) / 2 := by
      rw [Real.sinh_log hu_pos]
    have h2 : Real.cosh (Real.log u) = (u + u⁻¹) / 2 := by
      rw [Real.cosh_log hu_pos]
    rw [h1, h2]
    field_simp
  -- Show (u - 1/u) / (u + 1/u) = (u² - 1) / (u² + 1)
  have h_frac_eq : (u - u⁻¹) / (u + u⁻¹) = (u^2 - 1) / (u^2 + 1) := by
    field_simp
  -- Show u² = x^(1/g)
  have hu_sq : u^2 = x ^ ((g : ℝ)⁻¹) := by
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hx)]
    congr 1
    ring
  -- Combine everything
  rw [h_sinh_cosh, h_frac_eq, hu_sq]
  ring

/-- **Target 3 — surrogate → natural log.**  For `x > 0`,
`logSurrogate g x → Real.log x` as `g → ∞`. -/
theorem tendsto_logSurrogate {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (fun g : ℕ => logSurrogate g x)
      Filter.atTop (nhds (Real.log x)) := by
  unfold logSurrogate
  -- Key: (x^h - 1) / h → log x as h → 0, so g * (x^(1/g) - 1) → log x
  have h_deriv : HasDerivAt (fun h : ℝ => x ^ h) (Real.log x) 0 := by
    have heq : (fun h : ℝ => x ^ h) = (fun h => Real.exp (h * Real.log x)) := funext fun h => by
      rw [Real.rpow_def_of_pos hx, mul_comm]
    rw [heq]
    have h1 : HasDerivAt (fun h => h * Real.log x) (Real.log x) 0 := by
      simpa using hasDerivAt_id (0 : ℝ) |>.mul_const (Real.log x)
    exact h1.exp |> fun h => by simpa using h
  -- Use HasDerivAt to get the slope limit
  have h_slope : Filter.Tendsto (fun h : ℝ => (x ^ h - 1) / h) (nhdsWithin 0 {0}ᶜ) (nhds (Real.log x)) := by
    convert h_deriv.tendsto_slope_zero using 2; simp [div_eq_inv_mul]
  -- Compose with h = 1/g: as g → ∞, 1/g → 0+
  have h_tendsto_inv : Filter.Tendsto (fun g : ℕ => (g : ℝ)⁻¹) Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Filter.Tendsto.comp tendsto_inv_atTop_zero tendsto_natCast_atTop_atTop
    · filter_upwards [Filter.eventually_ge_atTop 1] with g hg
      have : (0 : ℝ) < g := Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 1) hg)
      exact inv_pos.mpr this
  -- Compose: g * (x^(1/g) - 1) → log x
  have h_g_slope : Filter.Tendsto (fun g : ℕ => (x ^ (g : ℝ)⁻¹ - 1) / (g : ℝ)⁻¹) Filter.atTop (nhds (Real.log x)) := by
    have h_subset : Set.Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := fun y hy => ne_of_gt hy
    exact h_slope.comp (h_tendsto_inv.mono_right (nhdsWithin_mono _ h_subset))
  -- Simplify: g * (x^(1/g) - 1) → log x
  have h_g_slope' : Filter.Tendsto (fun g : ℕ => (g : ℝ) * (x ^ (g : ℝ)⁻¹ - 1)) Filter.atTop (nhds (Real.log x)) := by
    convert h_g_slope using 1
    ext g
    field_simp
  -- 2 * g * (x^(1/g) - 1) → 2 * log x
  have h_two_g_slope : Filter.Tendsto (fun g : ℕ => 2 * (g : ℝ) * (x ^ (g : ℝ)⁻¹ - 1)) Filter.atTop (nhds (2 * Real.log x)) := by
    convert h_g_slope'.const_mul 2 using 2; ring
  -- x^(1/g) → 1
  have h_x_rpow : Filter.Tendsto (fun g : ℕ => x ^ (g : ℝ)⁻¹) Filter.atTop (nhds 1) := by
    have htendsto : Filter.Tendsto (fun g : ℕ => (g : ℝ)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hcont : Continuous (fun h : ℝ => x ^ h) := by
      have : (fun h : ℝ => x ^ h) = (fun h => Real.exp (h * Real.log x)) := funext fun h => by rw [Real.rpow_def_of_pos hx, mul_comm]
      rw [this]
      exact Real.continuous_exp.comp (continuous_id.mul_const _)
    have ht := hcont.continuousAt.tendsto.comp htendsto
    have hfun : ((fun h : ℝ => x ^ h) ∘ fun g : ℕ => (g : ℝ)⁻¹) =
        (fun g : ℕ => x ^ (g : ℝ)⁻¹) := by
      funext g
      rfl
    rw [hfun] at ht
    simpa only [Real.rpow_zero] using ht
  -- x^(1/g) + 1 → 2
  have h_denom : Filter.Tendsto (fun g : ℕ => x ^ (g : ℝ)⁻¹ + 1) Filter.atTop (nhds 2) := by
    convert h_x_rpow.add_const 1 using 1; norm_num
  -- Final: quotient → (2 * log x) / 2 = log x
  have h_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_final := h_two_g_slope.div h_denom h_ne
  have hfun : ((fun g : ℕ => 2 * (g : ℝ) * (x ^ (g : ℝ)⁻¹ - 1)) /
      (fun g : ℕ => x ^ (g : ℝ)⁻¹ + 1)) =
      (fun g : ℕ => 2 * (g : ℝ) * (x ^ (g : ℝ)⁻¹ - 1) /
        (x ^ (g : ℝ)⁻¹ + 1)) := by
    funext g
    rfl
  rw [hfun] at h_final
  convert h_final using 1
  norm_num

/-- **Target 4 — flagship iterated convergence.**  For `x > 0` and every
`ε > 0` there is `G` such that for all `g ≥ G` there is `N₀(g)` with
`|binomialLog g N x − Real.log x| < ε` for all `N ≥ N₀`. -/
theorem binomialLog_iterated_converges_to_log {x : ℝ} (hx : 0 < x) :
    ∀ ε : ℝ, 0 < ε → ∃ G : ℕ, ∀ g : ℕ, G ≤ g →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        |binomialLog g N x - Real.log x| < ε := by
  intro ε hε
  -- Use tendsto_logSurrogate to find G such that |logSurrogate g x - log x| < ε/2 for g ≥ G
  have h1 := Metric.tendsto_atTop.mp (tendsto_logSurrogate hx) (ε / 2) (half_pos hε)
  obtain ⟨G, hG⟩ := h1
  -- Ensure G ≥ 2 so we can use tendsto_binomialLog_row
  use max G 2
  intro g hg
  have hgG : G ≤ g := le_trans (le_max_left _ _) hg
  have hg2 : g ≥ 2 := le_trans (le_max_right _ _) hg
  -- Use tendsto_binomialLog_row to find N0 for this g
  have h2 := Metric.tendsto_atTop.mp (tendsto_binomialLog_row hg2 hx) (ε / 2) (half_pos hε)
  obtain ⟨N0, hN0⟩ := h2
  use N0
  intro N hN
  specialize hN0 N hN
  specialize hG g hgG
  rw [Real.dist_eq] at hN0 hG
  have htri : |binomialLog g N x - Real.log x| ≤ |binomialLog g N x - logSurrogate g x| + |logSurrogate g x - Real.log x| := abs_sub_le _ _ _
  have hsum : |binomialLog g N x - logSurrogate g x| + |logSurrogate g x - Real.log x| < ε / 2 + ε / 2 := add_lt_add hN0 hG
  linarith

/-- **Target 5 — compact-uniform fixed-`g` row limit.**  For `g ≥ 2` and
compact `K ⊆ (0,∞)`, `binomialLog g N → logSurrogate g` uniformly on `K`. -/
theorem tendstoUniformlyOn_binomialLog_row {g : ℕ} (hg : 2 ≤ g) {K : Set ℝ}
    (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi (0 : ℝ)) :
    TendstoUniformlyOn (fun N x => binomialLog g N x)
      (fun x => logSurrogate g x) Filter.atTop K := by
  -- Key: binomialLog = rational function of slice ratios
  -- r_k(N, x) = slice g k N x / slice g 0 N x → x^(-k/g) uniformly
  -- Denominator x * r_{g-1} + 2 + r_1 is bounded below on K
  have hg_pos : 0 < g := by linarith
  have hg_sub : g - 1 < g := Nat.pred_lt (by linarith : g ≠ 0)
  -- Get uniform convergence of slice ratios
  have h_ratios := tendstoUniformlyOn_slice_ratio hg_pos hg_sub hK hKpos
  have h_ratio1 := tendstoUniformlyOn_slice_ratio hg_pos (by omega : 1 < g) hK hKpos
  rw [Metric.tendstoUniformlyOn_iff] at h_ratios h_ratio1 ⊢
  -- Key algebraic identity: binomialLog can be written in terms of slice ratios
  have binomLog_ratio_id : ∀ N : ℕ, ∀ x : ℝ, x > 0 →
      binomialLog g N x = 2 * (g : ℝ) * (x * (slice g (g - 1) N x / slice g 0 N x) - slice g 1 N x / slice g 0 N x) /
                         (x * (slice g (g - 1) N x / slice g 0 N x) + 2 + slice g 1 N x / slice g 0 N x) := by
    intro N x hx
    unfold binomialLog logNumerator logDenominator
    have hslice0 : slice g 0 N x ≠ 0 := by
      apply ne_of_gt
      exact lt_of_lt_of_le zero_lt_one (one_le_slice_zero g N hx.le)
    field_simp [hslice0]
  -- Also, logSurrogate equals the same rational function at the limit values
  have logSurrogate_limit_id : ∀ x : ℝ, x > 0 →
      logSurrogate g x = 2 * (g : ℝ) * (x * x ^ (-(g - 1 : ℝ) / (g : ℝ)) - x ^ (-(1 : ℝ) / (g : ℝ))) /
                         (x * x ^ (-(g - 1 : ℝ) / (g : ℝ)) + 2 + x ^ (-(1 : ℝ) / (g : ℝ))) := by
    intro x hx
    unfold logSurrogate
    have hy : x ^ ((g : ℝ)⁻¹) > 0 := Real.rpow_pos_of_pos hx _
    have h1 : x * x ^ (-(g - 1 : ℝ) / (g : ℝ)) = x ^ ((g : ℝ)⁻¹) := by
      calc x * x ^ (-(g - 1 : ℝ) / (g : ℝ))
          = x ^ (1 : ℝ) * x ^ (-(g - 1 : ℝ) / (g : ℝ)) := by rw [Real.rpow_one]
        _ = x ^ (1 + (-(g - 1 : ℝ) / (g : ℝ))) := by rw [Real.rpow_add hx]
        _ = x ^ ((g : ℝ)⁻¹) := by congr 1; field_simp; ring
    have h2 : x ^ (-(1 : ℝ) / (g : ℝ)) = (x ^ ((g : ℝ)⁻¹))⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
      congr 1 ; ring
    rw [h1, h2]
    field_simp
    ring
  -- Now prove uniform convergence using continuity of rational functions
  -- We need to show the denominator is bounded away from 0
  -- Since K ⊆ (0, ∞) is compact, x^(1/g) is bounded below by some positive constant
  by_cases hne : K.Nonempty
  · -- K is nonempty, get lower bound a for x ∈ K
    obtain ⟨x₀, hx₀⟩ := hK.exists_isLeast hne
    obtain ⟨a, ha_pos, ha_bound⟩ : ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, a ≤ x := by
      use x₀
      exact ⟨hKpos hx₀.1, fun x hx => hx₀.2 hx⟩
    -- Since K is compact and x ↦ x is continuous, x is bounded above on K
    obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ x ∈ K, x ≤ b := hK.bddAbove
    -- L₁(x) = x^(-(g-1)/g) and L₂(x) = x^(-1/g) are continuous on K ⊆ (0,∞), hence bounded
    -- Get upper bounds for L₁ and L₂ on K
    have hL₁_cont : ContinuousOn (fun x : ℝ => x ^ (-(g - 1 : ℝ) / (g : ℝ))) K := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      exact ContinuousAt.rpow continuousAt_id continuousAt_const (Or.inl (hKpos hx).out.ne')
    have hL₂_cont : ContinuousOn (fun x : ℝ => x ^ (-(1 : ℝ) / (g : ℝ))) K := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      exact ContinuousAt.rpow continuousAt_id continuousAt_const (Or.inl (hKpos hx).out.ne')
    -- L₁ is decreasing, so max is at x = a; L₂ is decreasing, so max is at x = a
    -- But we just need some upper bound
    have hL₁_bdd : ∃ M₁ : ℝ, ∀ x ∈ K, x ^ (-(g - 1 : ℝ) / (g : ℝ)) ≤ M₁ := by
      exact ⟨ _, fun x hx => le_csSup (IsCompact.bddAbove (hK.image_of_continuousOn hL₁_cont)) (Set.mem_image_of_mem _ hx) ⟩
    have hL₂_bdd : ∃ M₂ : ℝ, ∀ x ∈ K, x ^ (-(1 : ℝ) / (g : ℝ)) ≤ M₂ := by
      exact ⟨ _, fun x hx => le_csSup (IsCompact.bddAbove (hK.image_of_continuousOn hL₂_cont)) (Set.mem_image_of_mem _ hx) ⟩
    obtain ⟨M₁, hM₁⟩ := hL₁_bdd
    obtain ⟨M₂, hM₂⟩ := hL₂_bdd
    -- The slice ratios are nonnegative for x > 0
    have slice_ratio_nonneg : ∀ N : ℕ, ∀ x : ℝ, x > 0 →
        0 ≤ slice g (g - 1) N x / slice g 0 N x ∧ 0 ≤ slice g 1 N x / slice g 0 N x := by
      intro N x hx
      have hslice0 : 0 < slice g 0 N x := lt_of_lt_of_le zero_lt_one (one_le_slice_zero g N hx.le)
      exact ⟨div_nonneg (slice_nonneg g (g-1) N hx.le) hslice0.le,
             div_nonneg (slice_nonneg g 1 N hx.le) hslice0.le⟩
    -- The denominator x * r_{g-1} + 2 + r_1 ≥ 2 > 0
    have denom_bound : ∀ N : ℕ, ∀ x : ℝ, x > 0 →
        2 ≤ x * (slice g (g - 1) N x / slice g 0 N x) + 2 + slice g 1 N x / slice g 0 N x := by
      intro N x hx
      have hn := slice_ratio_nonneg N x hx
      have h1 : 0 ≤ x * (slice g (g - 1) N x / slice g 0 N x) := mul_nonneg hx.le hn.1
      linarith [hn.1, hn.2]
    -- Compute an upper bound for the coefficient in our error estimate
    -- The bound is: g * (2 * x * δ + 2 * δ + 2 * x * (L₁ * δ + L₂ * δ)) ≤ g * δ * C
    -- where C = 2 * b + 2 + 2 * b * (M₁ + M₂)
    set C := 2 * b + 2 + 2 * b * (M₁ + M₂) with hC_def
    -- Choose δ = ε / (4 * g * C + 1) to ensure the error is < ε
    -- (we add 1 to avoid division by zero issues)
    intro ε hε
    set δ := ε / (4 * (g : ℝ) * max C 1 + 1) with hδ_def
    have hδ_pos : δ > 0 := by positivity
    -- Get N₀ such that both slice ratios are within δ of their limits
    have hevt1 := h_ratios δ hδ_pos
    have hevt2 := h_ratio1 δ hδ_pos
    filter_upwards [hevt1, hevt2] with N hN1 hN2 x hx
    -- Get the bounds on slice ratios
    have hr1 := hN1 x hx
    have hr2 := hN2 x hx
    -- Get x > 0
    have hx_pos : x > 0 := hKpos hx
    -- Use the identities first
    rw [binomLog_ratio_id N x hx_pos, logSurrogate_limit_id x hx_pos]
    -- Set up shorthand
    set L₁ := x ^ (-(g - 1 : ℝ) / (g : ℝ)) with hL₁
    set L₂ := x ^ (-(1 : ℝ) / (g : ℝ)) with hL₂
    set r₁ := slice g (g - 1) N x / slice g 0 N x with hr₁
    set r₂ := slice g 1 N x / slice g 0 N x with hr₂
    -- The exponent forms match since g ≥ 2
    have exp_equiv1 : x ^ (-(↑(g - 1) : ℝ) / ↑g) = L₁ := by
      simp [L₁]
      congr 1
      have h : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := Nat.cast_pred (by linarith : g ≥ 1)
      field_simp
      linarith
    have exp_equiv2 : x ^ (-(1 : ℕ) / ↑g : ℝ) = L₂ := by simp [L₂]
    -- We have |r₁ - L₁| < δ, |r₂ - L₂| < δ
    have hL₁_pos : L₁ > 0 := Real.rpow_pos_of_pos hx_pos _
    have hL₂_pos : L₂ > 0 := Real.rpow_pos_of_pos hx_pos _
    have denom_L : x * L₁ + 2 + L₂ ≥ 2 := by
      have : x * L₁ ≥ 0 := mul_nonneg hx_pos.le hL₁_pos.le
      linarith
    have denom_r : x * r₁ + 2 + r₂ ≥ 2 := denom_bound N x hx_pos
    -- Convert hr1, hr2 to use L₁, L₂
    rw [exp_equiv1] at hr1
    rw [exp_equiv2] at hr2
    -- |r₁ - L₁| < δ, |r₂ - L₂| < δ
    have hr1' : |r₁ - L₁| < δ := by simpa [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hr1
    have hr2' : |r₂ - L₂| < δ := by simpa [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hr2
    -- Both denominators are positive
    have denom_L_pos : x * L₁ + 2 + L₂ > 0 := by linarith
    have denom_r_pos : x * r₁ + 2 + r₂ > 0 := by linarith
    rw [dist_eq_norm, Real.norm_eq_abs]
    -- Rewrite using div_sub_div and simplify
    have key_eq : |2 * (g : ℝ) * (x * L₁ - L₂) / (x * L₁ + 2 + L₂) -
                   2 * (g : ℝ) * (x * r₁ - r₂) / (x * r₁ + 2 + r₂)| =
                  |(2 * (g : ℝ) * (x * L₁ - L₂) * (x * r₁ + 2 + r₂) -
                    (x * L₁ + 2 + L₂) * (2 * (g : ℝ) * (x * r₁ - r₂)))| /
                  ((x * L₁ + 2 + L₂) * (x * r₁ + 2 + r₂)) := by
      rw [div_sub_div _ _ denom_L_pos.ne' denom_r_pos.ne']
      rw [abs_div]
      rw [abs_of_nonneg (by positivity : (x * L₁ + 2 + L₂) * (x * r₁ + 2 + r₂) ≥ 0)]
    rw [key_eq]
    have denom_prod_ge_4 : (x * L₁ + 2 + L₂) * (x * r₁ + 2 + r₂) ≥ 4 := by nlinarith
    have denom_pos : (x * L₁ + 2 + L₂) * (x * r₁ + 2 + r₂) > 0 := by linarith
    -- Algebraic simplification of numerator
    have num_simp : 2 * (g : ℝ) * (x * L₁ - L₂) * (x * r₁ + 2 + r₂) -
                    (x * L₁ + 2 + L₂) * (2 * (g : ℝ) * (x * r₁ - r₂)) =
                    2 * (g : ℝ) * (2 * x * (L₁ - r₁) + 2 * (r₂ - L₂) + 2 * x * (L₁ * r₂ - L₂ * r₁)) := by ring
    rw [num_simp]
    -- Bound the numerator
    have cross_term : L₁ * r₂ - L₂ * r₁ = L₁ * (r₂ - L₂) + L₂ * (L₁ - r₁) := by ring
    have hnum_bound : |2 * (g : ℝ) * (2 * x * (L₁ - r₁) + 2 * (r₂ - L₂) + 2 * x * (L₁ * r₂ - L₂ * r₁))| ≤
        2 * g * (2 * x * |L₁ - r₁| + 2 * |r₂ - L₂| + 2 * x * (L₁ * |r₂ - L₂| + L₂ * |L₁ - r₁|)) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * g)]
      gcongr
      have step1 : |2 * x * (L₁ - r₁) + 2 * (r₂ - L₂) + 2 * x * (L₁ * r₂ - L₂ * r₁)| ≤
          |2 * x * (L₁ - r₁)| + |2 * (r₂ - L₂)| + |2 * x * (L₁ * r₂ - L₂ * r₁)| := by
        calc |2 * x * (L₁ - r₁) + 2 * (r₂ - L₂) + 2 * x * (L₁ * r₂ - L₂ * r₁)|
            ≤ |2 * x * (L₁ - r₁) + 2 * (r₂ - L₂)| + |2 * x * (L₁ * r₂ - L₂ * r₁)| := abs_add_le _ _
          _ ≤ |2 * x * (L₁ - r₁)| + |2 * (r₂ - L₂)| + |2 * x * (L₁ * r₂ - L₂ * r₁)| := by
              gcongr; apply abs_add_le
      have step2 : |2 * x * (L₁ - r₁)| + |2 * (r₂ - L₂)| + |2 * x * (L₁ * r₂ - L₂ * r₁)| =
          2 * x * |L₁ - r₁| + 2 * |r₂ - L₂| + 2 * x * |L₁ * r₂ - L₂ * r₁| := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hx_pos]
      have step3 : 2 * x * |L₁ - r₁| + 2 * |r₂ - L₂| + 2 * x * |L₁ * r₂ - L₂ * r₁| ≤
          2 * x * |L₁ - r₁| + 2 * |r₂ - L₂| + 2 * x * (L₁ * |r₂ - L₂| + L₂ * |L₁ - r₁|) := by
        gcongr
        rw [cross_term]
        calc |L₁ * (r₂ - L₂) + L₂ * (L₁ - r₁)| ≤ |L₁ * (r₂ - L₂)| + |L₂ * (L₁ - r₁)| := abs_add_le _ _
          _ = L₁ * |r₂ - L₂| + L₂ * |L₁ - r₁| := by
              rw [abs_mul, abs_mul, abs_of_pos hL₁_pos, abs_of_pos hL₂_pos]
      linarith [step1, step2, step3]
    -- Now use the bounds to show the ratio is < ε
    have hL1r1 : |L₁ - r₁| ≤ δ := by simpa [abs_sub_comm] using hr1'.le
    have hL2r2 : |L₂ - r₂| ≤ δ := by simpa [abs_sub_comm] using hr2'.le
    have hL1r2_bound : L₁ * |r₂ - L₂| ≤ L₁ * δ := by gcongr
    have hL2r1_bound : L₂ * |L₁ - r₁| ≤ L₂ * δ := by gcongr
    have hr2_L2 : |r₂ - L₂| = |L₂ - r₂| := abs_sub_comm _ _
    have hr1_L1 : |r₁ - L₁| = |L₁ - r₁| := abs_sub_comm _ _
    have hg_nonneg : (0 : ℝ) ≤ g := by positivity
    have hnum_final_bound : |2 * (g : ℝ) * (2 * x * (L₁ - r₁) + 2 * (r₂ - L₂) + 2 * x * (L₁ * r₂ - L₂ * r₁))| ≤
        2 * g * (2 * x * δ + 2 * δ + 2 * x * (L₁ * δ + L₂ * δ)) := by
      have h1 : 2 * x * |L₁ - r₁| + 2 * |r₂ - L₂| + 2 * x * (L₁ * |r₂ - L₂| + L₂ * |L₁ - r₁|) ≤
          2 * x * δ + 2 * δ + 2 * x * (L₁ * δ + L₂ * δ) := by
        gcongr
      nlinarith [hnum_bound, h1]
    -- Simplify the bound
    have hnum_simplified : 2 * (g : ℝ) * (2 * x * δ + 2 * δ + 2 * x * (L₁ * δ + L₂ * δ)) =
        4 * g * δ * (x + 1 + x * (L₁ + L₂)) := by ring
    -- Use that x ≤ b and L₁, L₂ ≤ M₁, M₂ to get a uniform bound
    have hx_le_b : x ≤ b := hb x hx
    have hL₁_le : L₁ ≤ M₁ := hM₁ x hx
    have hL₂_le : L₂ ≤ M₂ := hM₂ x hx
    have hbound : x + 1 + x * (L₁ + L₂) ≤ b + 1 + b * (M₁ + M₂) := by nlinarith
    have hC_ge : C ≥ b + 1 + b * (M₁ + M₂) := by simp [hC_def]; nlinarith
    have hdenom_ge_4 : (x * L₁ + 2 + L₂) * (x * r₁ + 2 + r₂) ≥ 4 := denom_prod_ge_4
    -- Final bound: |num|/denom ≤ 4 * g * δ * C / 4 = g * δ * C ≤ g * ε / (4 * g * C) = ε / 4 < ε
    -- Step 1: |num|/denom ≤ |num|/4 since denom ≥ 4
    have step1 : |2 * (g : ℝ) * (2 * x * (L₁ - r₁) + 2 * (r₂ - L₂) + 2 * x * (L₁ * r₂ - L₂ * r₁))| /
         ((x * L₁ + 2 + L₂) * (x * r₁ + 2 + r₂)) ≤
        |2 * (g : ℝ) * (2 * x * (L₁ - r₁) + 2 * (r₂ - L₂) + 2 * x * (L₁ * r₂ - L₂ * r₁))| / 4 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num : (0 : ℝ) < 4) hdenom_ge_4
    -- Step 2: |num|/4 ≤ (2*g*(...))/4 using hnum_final_bound
    have step2 : |2 * (g : ℝ) * (2 * x * (L₁ - r₁) + 2 * (r₂ - L₂) + 2 * x * (L₁ * r₂ - L₂ * r₁))| / 4 ≤
        2 * g * (2 * x * δ + 2 * δ + 2 * x * (L₁ * δ + L₂ * δ)) / 4 := by
          apply div_le_div_of_nonneg_right hnum_final_bound (by norm_num : (0 : ℝ) ≤ 4)
    -- Step 3: Simplify 2*g*(...)/4 = g*(...)/2 = g*δ*(x+1+x*(L₁+L₂))/2
    have step3 : 2 * (g : ℝ) * (2 * x * δ + 2 * δ + 2 * x * (L₁ * δ + L₂ * δ)) / 4 =
        g * δ * (x + 1 + x * (L₁ + L₂)) := by ring
    -- Step 4: g*δ*(x+1+x*(L₁+L₂)) ≤ g*δ*C using hbound
    have step4 : g * δ * (x + 1 + x * (L₁ + L₂)) ≤ g * δ * C := by
      gcongr
      linarith [hbound, hC_ge]
    -- Step 5: g*δ*C ≤ ε/4
    have step5 : g * δ * C ≤ ε / 4 := by
      have hg_pos : (0 : ℝ) < g := by positivity
      have hC_le_max : C ≤ max C 1 := le_max_left _ _
      have hdenom_pos : (4 : ℝ) * (g : ℝ) * max C 1 + 1 > 0 := by positivity
      rw [hδ_def]
      have h1 : g * (ε / ((4 : ℝ) * g * max C 1 + 1)) * C = ε * (g * C) / ((4 : ℝ) * g * max C 1 + 1) := by ring
      rw [h1]
      rw [div_le_iff₀ hdenom_pos]
      have h2 : ε * (g * C) * 4 ≤ ε * (4 * g * max C 1 + 1) := by
        have := mul_le_mul_of_nonneg_left hC_le_max (by positivity : (0 : ℝ) ≤ ε * g * 4)
        linarith
      linarith
    linarith [step1, step2, step3, step4, step5]

  · -- K is empty, statement is vacuously true
    simp [Set.not_nonempty_iff_eq_empty.mp hne]
end ResidueSlices
