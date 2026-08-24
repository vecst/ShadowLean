/-
Metallic cutoff Phase C2B: sharp asymptotic coefficient of the canonical
metallic fixed point.

Building on RequestProject.MetallicFixedPointConvergence (the exact two-eigenvalue
formula ratio_spectral_decomposition, rowSpectralRatio in (0,1), uniform
convergence, evenFixedPoint m -> silver, and the coarse bound
0 <= evenFixedPoint m - silver <= 18*silver*spectralRatio^(2m)), this module
proves the SHARP leading coefficient

  spectralBase^(2m) * (evenFixedPoint m - silver) -> 4*silver.

The transverse moving-pole cutoff (feeding scale -8 into
tendsto_even_moving_pole_signed) is the next phase.
-/
import RequestProject.MetallicFixedPointConvergence

open Set

namespace MetallicCutoff

noncomputable def evenFixedPointDelta (m : ℕ) : ℝ :=
  1 + beta * evenFixedPoint m

noncomputable def evenFixedPointRoot (m : ℕ) : ℝ :=
  positiveFixedRoot (evenFixedPointDelta m)

noncomputable def evenFixedPointSpectralRatio (m : ℕ) : ℝ :=
  rowSpectralRatio (evenFixedPointDelta m)

/-! ### Numeric preliminaries (re-derived locally) -/

private lemma sharp_sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma sharp_sqrt_two_lb : (1.4142 : ℝ) < Real.sqrt 2 := by
  have h0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [sharp_sqrt_two_sq]

private lemma sharp_sqrt_two_ub : Real.sqrt 2 < 1.4143 := by
  have h0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [sharp_sqrt_two_sq]

private lemma sharp_silver_eq : silver = 1 + Real.sqrt 2 := rfl

private lemma sharp_spectralRatio_eq : spectralRatio = 3 - 2 * Real.sqrt 2 := rfl

private lemma sharp_silver_pos : 0 < silver := silver_identities.1

private lemma sharp_beta_silver : beta * silver = 2 := silver_identities.2.1

private lemma sharp_beta_eq : beta = 2 * (Real.sqrt 2 - 1) := by
  have h1 := sharp_sqrt_two_lb
  rw [beta, sharp_silver_eq, div_eq_iff (by nlinarith)]
  nlinarith [sharp_sqrt_two_sq]

private lemma sharp_beta_pos : 0 < beta := by
  rw [sharp_beta_eq]; linarith [sharp_sqrt_two_lb]

private lemma sharp_one_sub_beta : 1 - beta = spectralRatio := by
  rw [sharp_beta_eq, sharp_spectralRatio_eq]; ring

private lemma sharp_spectralRatio_pos : 0 < spectralRatio := by
  rw [sharp_spectralRatio_eq]; linarith [sharp_sqrt_two_ub]

private lemma sharp_spectralRatio_lt_one : spectralRatio < 1 := by
  rw [sharp_spectralRatio_eq]; linarith [sharp_sqrt_two_lb]

private lemma sharp_spectralBase_mul : spectralBase * spectralRatio = 1 :=
  silver_identities.2.2.2

private lemma sharp_one_sub_beta_silver_sq : (1 - beta) * silver ^ 2 = 1 := by
  rw [sharp_one_sub_beta, ← silver_identities.2.2.1]
  linarith [sharp_spectralBase_mul]

private lemma sharp_disc_sq (delta : ℝ) :
    Real.sqrt ((delta - 1) ^ 2 + 4) ^ 2 = (delta - 1) ^ 2 + 4 :=
  Real.sq_sqrt (by positivity)

private lemma sharp_positiveFixedRoot_sq (delta : ℝ) :
    positiveFixedRoot delta ^ 2 = (delta - 1) * positiveFixedRoot delta + 1 := by
  rw [positiveFixedRoot]
  linear_combination (1 / 4 : ℝ) * sharp_disc_sq delta

/-! ### Two elementary comparisons for `rowSpectralRatio` near `delta = 3` -/

private lemma sharp_ratio_le_aux {t D s : ℝ} (hs : s ^ 2 = 2) (hslb : (1.4142 : ℝ) < s)
    (hD0 : 0 ≤ D) (hD2 : D ^ 2 = t ^ 2 + 4 * t + 8)
    (hpos : 0 < 4 + t) :
    (4 + t) * (2 * s - 2) ≤ D * (4 - 2 * s) := by
  have hid : D ^ 2 * (4 - 2 * s) ^ 2 - ((4 + t) * (2 * s - 2)) ^ 2 = (12 - 8 * s) * t ^ 2 := by
    linear_combination (4 - 2 * s) ^ 2 * hD2 + (-16 * t - 32) * hs
  have hL0 : 0 ≤ (4 + t) * (2 * s - 2) := by nlinarith
  have hR0 : 0 ≤ D * (4 - 2 * s) := by nlinarith
  nlinarith [hid, sq_nonneg t, hL0, hR0]

private lemma sharp_lipschitz_aux {t D s : ℝ} (ht : 0 ≤ t) (hs : s ^ 2 = 2)
    (hslb : (1.4142 : ℝ) < s) (hsub : s < 1.4143) (hD0 : 0 ≤ D)
    (hD2 : D ^ 2 = t ^ 2 + 4 * t + 8) :
    (4 - 2 * s - t) * D ≤ t ^ 2 + (2 + 2 * s) * t + 8 * s - 8 := by
  have hR : 0 < t ^ 2 + (2 + 2 * s) * t + 8 * s - 8 := by nlinarith
  by_cases hc : 4 - 2 * s - t ≤ 0
  · nlinarith [mul_nonneg (neg_nonneg.mpr hc) hD0]
  · replace hc : 0 < 4 - 2 * s - t := by linarith [not_le.mp hc]
    have hid : (t ^ 2 + (2 + 2 * s) * t + 8 * s - 8) ^ 2 - ((4 - 2 * s - t) * D) ^ 2 =
        t * (8 * t ^ 2 + (24 * s - 4) * t + 32 * s) := by
      linear_combination (-(4 - 2 * s - t) ^ 2) * hD2 + (16 * t + 32) * hs
    have hcd : 0 ≤ (4 - 2 * s - t) * D := mul_nonneg hc.le hD0
    have hnn : 0 ≤ t * (8 * t ^ 2 + (24 * s - 4) * t + 32 * s) := by nlinarith
    nlinarith [hid, hcd, hR]

private lemma sharp_rowSpectralRatio_le {delta : ℝ} (hdelta : 1 < delta) :
    rowSpectralRatio delta ≤ spectralRatio := by
  set D := Real.sqrt ((delta - 1) ^ 2 + 4) with hDdef
  have hD2 : D ^ 2 = (delta - 1) ^ 2 + 4 := sharp_disc_sq delta
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hDlb : 2 ≤ D := by nlinarith [sq_nonneg (delta - 1)]
  have hden : 0 < (delta + 1) + D := by linarith
  have hkey := sharp_ratio_le_aux (t := delta - 3) (D := D) (s := Real.sqrt 2)
    sharp_sqrt_two_sq sharp_sqrt_two_lb hD0 (by rw [hD2]; ring)
    (by linarith)
  rw [rowSpectralRatio, ← hDdef, div_le_iff₀ hden, sharp_spectralRatio_eq]
  nlinarith [hkey]

private lemma sharp_spectralRatio_sub_rowSpectralRatio {delta : ℝ} (hdelta : 3 ≤ delta) :
    spectralRatio - rowSpectralRatio delta ≤ delta - 3 := by
  set D := Real.sqrt ((delta - 1) ^ 2 + 4) with hDdef
  have hD2 : D ^ 2 = (delta - 1) ^ 2 + 4 := sharp_disc_sq delta
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hDlb : 2 ≤ D := by nlinarith [sq_nonneg (delta - 1)]
  have hden : 0 < (delta + 1) + D := by linarith
  have hkey := sharp_lipschitz_aux (t := delta - 3) (D := D) (s := Real.sqrt 2)
    (by linarith) sharp_sqrt_two_sq sharp_sqrt_two_lb sharp_sqrt_two_ub hD0
    (by rw [hD2]; ring)
  have hle : spectralRatio - (delta - 3) ≤ ((delta + 1) - D) / ((delta + 1) + D) := by
    rw [le_div_iff₀ hden, sharp_spectralRatio_eq]
    nlinarith [hkey]
  rw [rowSpectralRatio, ← hDdef]
  linarith

/-! ### Strict location of the canonical fixed point -/

theorem silver_lt_evenFixedPoint {m : ℕ} (hm : 1 ≤ m) :
    silver < evenFixedPoint m := by
  obtain ⟨hmem, -, hfix⟩ := evenFixedPoint_spec hm
  rcases lt_or_eq_of_le hmem.1 with h | h
  · exact h
  · exfalso
    have hgt := recoveryMap_silver_gt hm
    rw [← h] at hfix
    rw [hfix] at hgt
    exact lt_irrefl _ hgt

/-! ### Convergence of the induced data -/

theorem tendsto_evenFixedPointDelta :
    Filter.Tendsto evenFixedPointDelta Filter.atTop (nhds 3) := by
  have hfun : evenFixedPointDelta = fun m : ℕ => 1 + beta * evenFixedPoint m := rfl
  have h2 : Filter.Tendsto (fun m : ℕ => 1 + beta * evenFixedPoint m) Filter.atTop
      (nhds (1 + beta * silver)) :=
    (tendsto_evenFixedPoint.const_mul beta).const_add 1
  have h3 : 1 + beta * silver = 3 := by linarith [sharp_beta_silver]
  rw [h3] at h2
  rw [hfun]
  exact h2

private lemma sharp_continuous_positiveFixedRoot : Continuous positiveFixedRoot := by
  unfold positiveFixedRoot
  fun_prop

theorem tendsto_evenFixedPointRoot :
    Filter.Tendsto evenFixedPointRoot Filter.atTop (nhds silver) := by
  have hfun : evenFixedPointRoot = fun m : ℕ => positiveFixedRoot (evenFixedPointDelta m) := rfl
  have h := (sharp_continuous_positiveFixedRoot.tendsto 3).comp tendsto_evenFixedPointDelta
  rw [roots_and_ratio_at_three.1] at h
  rw [hfun]
  exact h

/-! ### Quantitative facts about the moving spectral ratio -/

private lemma sharp_delta_bounds {m : ℕ} (hm : 1 ≤ m) :
    3 ≤ evenFixedPointDelta m ∧
      evenFixedPointDelta m - 3 ≤ 36 * spectralRatio ^ (2 * m) := by
  obtain ⟨hlow, hhigh⟩ := evenFixedPoint_sub_silver_bound hm
  have hbs : beta * silver = 2 := sharp_beta_silver
  have hb : 0 < beta := sharp_beta_pos
  have hkey : evenFixedPointDelta m - 3 = beta * (evenFixedPoint m - silver) := by
    rw [evenFixedPointDelta]; linarith [hbs]
  constructor
  · nlinarith [mul_nonneg hb.le hlow]
  · rw [hkey]
    have hstep : beta * (evenFixedPoint m - silver) ≤
        beta * (18 * silver * spectralRatio ^ (2 * m)) :=
      mul_le_mul_of_nonneg_left hhigh hb.le
    have hval : beta * (18 * silver * spectralRatio ^ (2 * m)) =
        36 * spectralRatio ^ (2 * m) := by
      linear_combination (18 * spectralRatio ^ (2 * m)) * hbs
    linarith [hstep, hval]

private lemma sharp_ratio_facts {m : ℕ} (hm : 1 ≤ m) :
    0 < evenFixedPointSpectralRatio m ∧
      evenFixedPointSpectralRatio m ≤ spectralRatio ∧
      spectralRatio - evenFixedPointSpectralRatio m ≤ 36 * spectralRatio ^ (2 * m) := by
  obtain ⟨h3, hd⟩ := sharp_delta_bounds hm
  have hdelta : 1 < evenFixedPointDelta m := by linarith
  refine ⟨(rowSpectralRatio_mem_unitInterval hdelta).1, sharp_rowSpectralRatio_le hdelta, ?_⟩
  exact le_trans (sharp_spectralRatio_sub_rowSpectralRatio h3) hd

private lemma sharp_tendsto_geom :
    Filter.Tendsto (fun m : ℕ => spectralRatio ^ (2 * m)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun m : ℕ => (spectralRatio ^ 2) ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (by nlinarith [sharp_spectralRatio_pos, sharp_spectralRatio_lt_one])
  have h2 : (fun m : ℕ => spectralRatio ^ (2 * m)) = fun m : ℕ => (spectralRatio ^ 2) ^ m := by
    funext m; rw [← pow_mul]
  rw [h2]
  exact h1

private lemma sharp_tendsto_lin_geom :
    Filter.Tendsto (fun m : ℕ => (72 / spectralRatio) * ((m : ℝ) * (spectralRatio ^ 2) ^ m))
      Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun m : ℕ => (m : ℝ) * (spectralRatio ^ 2) ^ m) Filter.atTop
      (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one (by positivity)
      (by nlinarith [sharp_spectralRatio_pos, sharp_spectralRatio_lt_one])
  simpa using h1.const_mul (72 / spectralRatio)

private lemma sharp_one_sub_pow_le {x : ℝ} (hx0 : 0 ≤ x) (n : ℕ) :
    1 - x ^ n ≤ n * (1 - x) := by
  have h := one_add_mul_le_pow (a := x - 1) (by linarith) n
  have hx : (1 : ℝ) + (x - 1) = x := by ring
  rw [hx] at h
  linarith

theorem tendsto_scaled_evenFixedPointSpectralRatio_pow :
    Filter.Tendsto
      (fun m : ℕ =>
        spectralBase ^ (2 * m) * evenFixedPointSpectralRatio m ^ (2 * m))
      Filter.atTop (nhds 1) := by
  have hrho0 : 0 < spectralRatio := sharp_spectralRatio_pos
  have hrho1 : spectralRatio < 1 := sharp_spectralRatio_lt_one
  have hrewrite : ∀ m : ℕ,
      spectralBase ^ (2 * m) * evenFixedPointSpectralRatio m ^ (2 * m) =
        (evenFixedPointSpectralRatio m / spectralRatio) ^ (2 * m) := by
    intro m
    have hstep : spectralBase * evenFixedPointSpectralRatio m =
        evenFixedPointSpectralRatio m / spectralRatio := by
      rw [eq_div_iff hrho0.ne']
      linear_combination (evenFixedPointSpectralRatio m) * sharp_spectralBase_mul
    rw [← mul_pow, hstep]
  have hzero : Filter.Tendsto
      (fun m : ℕ => 1 - (evenFixedPointSpectralRatio m / spectralRatio) ^ (2 * m))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ sharp_tendsto_lin_geom
    · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
      obtain ⟨hpos, hle, -⟩ := sharp_ratio_facts hm
      have hx0 : 0 ≤ evenFixedPointSpectralRatio m / spectralRatio :=
        div_nonneg hpos.le hrho0.le
      have hx1 : evenFixedPointSpectralRatio m / spectralRatio ≤ 1 :=
        (div_le_one hrho0).mpr hle
      have hple := pow_le_one₀ hx0 hx1 (n := 2 * m)
      linarith
    · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
      obtain ⟨hpos, hle, hgap⟩ := sharp_ratio_facts hm
      have hx0 : 0 ≤ evenFixedPointSpectralRatio m / spectralRatio :=
        div_nonneg hpos.le hrho0.le
      have hx1 : evenFixedPointSpectralRatio m / spectralRatio ≤ 1 :=
        (div_le_one hrho0).mpr hle
      have hbern := sharp_one_sub_pow_le hx0 (2 * m)
      have hgap' : 1 - evenFixedPointSpectralRatio m / spectralRatio ≤
          36 * spectralRatio ^ (2 * m) / spectralRatio := by
        have hclear : (1 - evenFixedPointSpectralRatio m / spectralRatio) * spectralRatio =
            spectralRatio - evenFixedPointSpectralRatio m := by
          field_simp
        rw [le_div_iff₀ hrho0, hclear]
        exact hgap
      have hmul : ((2 * m : ℕ) : ℝ) * (1 - evenFixedPointSpectralRatio m / spectralRatio) ≤
          ((2 * m : ℕ) : ℝ) * (36 * spectralRatio ^ (2 * m) / spectralRatio) := by
        apply mul_le_mul_of_nonneg_left hgap'
        positivity
      have hcast : ((2 * m : ℕ) : ℝ) * (36 * spectralRatio ^ (2 * m) / spectralRatio) =
          (72 / spectralRatio) * ((m : ℝ) * (spectralRatio ^ 2) ^ m) := by
        rw [pow_mul]
        push_cast
        field_simp
        ring
      calc 1 - (evenFixedPointSpectralRatio m / spectralRatio) ^ (2 * m)
          ≤ ((2 * m : ℕ) : ℝ) * (1 - evenFixedPointSpectralRatio m / spectralRatio) := hbern
        _ ≤ ((2 * m : ℕ) : ℝ) * (36 * spectralRatio ^ (2 * m) / spectralRatio) := hmul
        _ = (72 / spectralRatio) * ((m : ℝ) * (spectralRatio ^ 2) ^ m) := hcast
  have hone : Filter.Tendsto
      (fun m : ℕ => (evenFixedPointSpectralRatio m / spectralRatio) ^ (2 * m))
      Filter.atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop (α := ℕ))).sub hzero
    simpa using this
  simpa only [hrewrite] using hone

/-! ### The scaled finite-row recovery defect -/

private lemma sharp_tendsto_disc :
    Filter.Tendsto (fun m : ℕ => Real.sqrt ((evenFixedPointDelta m - 1) ^ 2 + 4))
      Filter.atTop (nhds (2 * Real.sqrt 2)) := by
  have hcont : Continuous fun delta : ℝ => Real.sqrt ((delta - 1) ^ 2 + 4) := by fun_prop
  have h := (hcont.tendsto 3).comp tendsto_evenFixedPointDelta
  have hval : Real.sqrt (((3 : ℝ) - 1) ^ 2 + 4) = 2 * Real.sqrt 2 := by
    rw [show ((3 : ℝ) - 1) ^ 2 + 4 = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [hval] at h
  exact h

private lemma sharp_tendsto_ratio_pow_zero :
    Filter.Tendsto (fun m : ℕ => evenFixedPointSpectralRatio m ^ (2 * m)) Filter.atTop
      (nhds 0) := by
  refine squeeze_zero' ?_ ?_ sharp_tendsto_geom
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact (pow_pos (sharp_ratio_facts hm).1 _).le
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    obtain ⟨hpos, hle, -⟩ := sharp_ratio_facts hm
    exact pow_le_pow_left₀ hpos.le hle _

theorem tendsto_scaled_evenFixedPoint_recovery_defect :
    Filter.Tendsto
      (fun m : ℕ =>
        spectralBase ^ (2 * m) *
          (recoveryMap m (evenFixedPoint m) - evenFixedPointRoot m))
      Filter.atTop (nhds (2 * Real.sqrt 2)) := by
  have hden : Filter.Tendsto
      (fun m : ℕ => 1 - evenFixedPointSpectralRatio m ^ (2 * m)) Filter.atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop (α := ℕ))).sub
      sharp_tendsto_ratio_pow_zero
    simpa using this
  have hprod : Filter.Tendsto
      (fun m : ℕ =>
        Real.sqrt ((evenFixedPointDelta m - 1) ^ 2 + 4) *
            (spectralBase ^ (2 * m) * evenFixedPointSpectralRatio m ^ (2 * m)) /
          (1 - evenFixedPointSpectralRatio m ^ (2 * m)))
      Filter.atTop (nhds (2 * Real.sqrt 2 * 1 / 1)) :=
    (sharp_tendsto_disc.mul tendsto_scaled_evenFixedPointSpectralRatio_pow).div hden one_ne_zero
  have hlim : 2 * Real.sqrt 2 * 1 / 1 = 2 * Real.sqrt 2 := by ring
  rw [hlim] at hprod
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  obtain ⟨h3, -⟩ := sharp_delta_bounds hm
  obtain ⟨hpos, hle, -⟩ := sharp_ratio_facts hm
  have hdelta : 1 < evenFixedPointDelta m := by linarith
  have hpow_lt : evenFixedPointSpectralRatio m ^ (2 * m) < 1 := by
    have hlt1 : evenFixedPointSpectralRatio m < 1 :=
      lt_of_le_of_lt hle sharp_spectralRatio_lt_one
    exact pow_lt_one₀ hpos.le hlt1 (by omega)
  have hne : (1 : ℝ) - evenFixedPointSpectralRatio m ^ (2 * m) ≠ 0 := by linarith
  have hdec := ratio_spectral_decomposition hdelta (N := 2 * m) (by omega)
  have hrec : recoveryMap m (evenFixedPoint m) = ratio (evenFixedPointDelta m) (2 * m) := rfl
  have hroot : evenFixedPointRoot m = positiveFixedRoot (evenFixedPointDelta m) := rfl
  have hrho : evenFixedPointSpectralRatio m = rowSpectralRatio (evenFixedPointDelta m) := rfl
  rw [hrec, hdec, hroot, ← hrho]
  field_simp
  ring

/-! ### The exact factorization and the correction factor -/

theorem evenFixedPoint_factorization {m : ℕ} (hm : 1 ≤ m) :
    (1 - beta) * (evenFixedPoint m - silver) *
        (evenFixedPoint m + silver) =
      (evenFixedPoint m - evenFixedPointRoot m) *
        (evenFixedPoint m + evenFixedPointRoot m - beta * evenFixedPoint m) := by
  -- The identity is purely algebraic; `hm` is retained as part of the required interface.
  have _hm : 1 ≤ m := hm
  have hroot : evenFixedPointRoot m ^ 2 =
      beta * evenFixedPoint m * evenFixedPointRoot m + 1 := by
    have h := sharp_positiveFixedRoot_sq (evenFixedPointDelta m)
    have hr : evenFixedPointRoot m = positiveFixedRoot (evenFixedPointDelta m) := rfl
    have hd : evenFixedPointDelta m - 1 = beta * evenFixedPoint m := by
      rw [evenFixedPointDelta]; ring
    rw [← hr, hd] at h
    exact h
  have hsilv := sharp_one_sub_beta_silver_sq
  linear_combination hroot - hsilv

theorem tendsto_evenFixedPoint_correctionFactor :
    Filter.Tendsto
      (fun m : ℕ =>
        (evenFixedPoint m + evenFixedPointRoot m - beta * evenFixedPoint m) /
          ((1 - beta) * (evenFixedPoint m + silver)))
      Filter.atTop (nhds (silver * Real.sqrt 2)) := by
  have hnum : Filter.Tendsto
      (fun m : ℕ => evenFixedPoint m + evenFixedPointRoot m - beta * evenFixedPoint m)
      Filter.atTop (nhds (silver + silver - beta * silver)) :=
    (tendsto_evenFixedPoint.add tendsto_evenFixedPointRoot).sub
      (tendsto_evenFixedPoint.const_mul beta)
  have hden : Filter.Tendsto
      (fun m : ℕ => (1 - beta) * (evenFixedPoint m + silver)) Filter.atTop
      (nhds ((1 - beta) * (silver + silver))) :=
    (tendsto_evenFixedPoint.add tendsto_const_nhds).const_mul (1 - beta)
  have hbeta1 : 0 < 1 - beta := by rw [sharp_one_sub_beta]; exact sharp_spectralRatio_pos
  have hne : (1 - beta) * (silver + silver) ≠ 0 := by
    have := sharp_silver_pos
    positivity
  have hlim : (silver + silver - beta * silver) / ((1 - beta) * (silver + silver)) =
      silver * Real.sqrt 2 := by
    rw [div_eq_iff hne]
    linear_combination (-2 * Real.sqrt 2) * sharp_one_sub_beta_silver_sq +
      2 * sharp_silver_eq - sharp_beta_silver
  have := hnum.div hden hne
  rw [hlim] at this
  exact this

/-! ### The sharp coefficient -/

theorem tendsto_scaled_evenFixedPoint_sub_silver :
    Filter.Tendsto
      (fun m : ℕ =>
        spectralBase ^ (2 * m) * (evenFixedPoint m - silver))
      Filter.atTop (nhds (4 * silver)) := by
  have hmul := tendsto_scaled_evenFixedPoint_recovery_defect.mul
    tendsto_evenFixedPoint_correctionFactor
  have hlim : 2 * Real.sqrt 2 * (silver * Real.sqrt 2) = 4 * silver := by
    linear_combination (2 * silver) * sharp_sqrt_two_sq
  rw [hlim] at hmul
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  obtain ⟨-, -, hfix⟩ := evenFixedPoint_spec hm
  have hbeta1 : 0 < 1 - beta := by rw [sharp_one_sub_beta]; exact sharp_spectralRatio_pos
  have hzpos : silver < evenFixedPoint m := silver_lt_evenFixedPoint hm
  have hspos : 0 < silver := sharp_silver_pos
  have hne : (1 - beta) * (evenFixedPoint m + silver) ≠ 0 := by
    have : 0 < evenFixedPoint m + silver := by linarith
    positivity
  have hfact := evenFixedPoint_factorization hm
  have hz : (evenFixedPoint m - evenFixedPointRoot m) *
      ((evenFixedPoint m + evenFixedPointRoot m - beta * evenFixedPoint m) /
        ((1 - beta) * (evenFixedPoint m + silver))) = evenFixedPoint m - silver := by
    rw [mul_comm, div_mul_eq_mul_div, div_eq_iff hne]
    linear_combination -hfact
  rw [hfix, mul_assoc, hz]

end MetallicCutoff
