/-
Metallic cutoff Phase C1: the canonical even-row recovery fixed point.

Building on RequestProject.MetallicCutoff (the metallic recurrence, ratio,
silver = 1 + sqrt 2, beta = 2/silver, spectralBase, silver_identities,
ratio_three_closed_form), this module constructs and characterizes the unique
fixed point of the even-row recovery map F_m(z) = ratio (1 + beta*z) (2*m) in
[silver, 3], for m >= 1.

This phase constructs the fixed point only; it does NOT attempt the moving-row
asymptotic spectralBase^(2m) * (evenFixedPoint m - silver) -> 4*silver (a later
phase).
-/
import RequestProject.MetallicCutoff

open Set

namespace MetallicCutoff

noncomputable def recoveryMap (m : ℕ) (z : ℝ) : ℝ :=
  ratio (1 + beta * z) (2 * m)

noncomputable def scaledRecoveryRatio (m : ℕ) (delta : ℝ) : ℝ :=
  beta * ratio delta (2 * m) / (delta - 1)

/-! ### Positivity of the two channels -/

private lemma state_pos (delta : ℝ) (hd : 0 < delta) (n : ℕ) :
    0 < (state delta (n + 1)).1 ∧ 0 < (state delta (n + 1)).2 := by
  induction n with
  | zero =>
    rw [state_succ]
    refine ⟨?_, ?_⟩
    · simpa [state] using hd
    · simp [state]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [state_succ]
    refine ⟨?_, ?_⟩
    · simp only
      positivity
    · simp only
      linarith

private lemma numerator_pos (delta : ℝ) (hd : 0 < delta) {n : ℕ} (hn : 1 ≤ n) :
    0 < numerator delta n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (state_pos delta hd k).1

private lemma denominator_pos_of_pos (delta : ℝ) (hd : 0 < delta) {n : ℕ} (hn : 1 ≤ n) :
    0 < denominator delta n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (state_pos delta hd k).2

private lemma ratio_pos (delta : ℝ) (hd : 0 < delta) {n : ℕ} (hn : 1 ≤ n) :
    0 < ratio delta n :=
  div_pos (numerator_pos delta hd hn) (denominator_pos_of_pos delta hd hn)

/-! ### The scalar row recurrence -/

private lemma ratio_one (delta : ℝ) : ratio delta 1 = delta := by
  simp [ratio, numerator, denominator, state]

private lemma ratio_succ (delta : ℝ) (hd : 0 < delta) {n : ℕ} (hn : 1 ≤ n) :
    ratio delta (n + 1) = (delta * ratio delta n + 1) / (ratio delta n + 1) := by
  have hden : 0 < denominator delta n := denominator_pos_of_pos delta hd hn
  have hnum : 0 < numerator delta n := numerator_pos delta hd hn
  have h1 : numerator delta (n + 1) = delta * numerator delta n + denominator delta n := by
    simp [numerator, denominator, state_succ]
  have h2 : denominator delta (n + 1) = numerator delta n + denominator delta n := by
    simp [numerator, denominator, state_succ]
  have hsum : 0 < numerator delta n + denominator delta n := by linarith
  rw [ratio, h1, h2, ratio, div_eq_div_iff hsum.ne' (by positivity)]
  field_simp

/-- For `delta > 1` every row ratio from row 1 on exceeds `delta - 1`. -/
private lemma sub_one_lt_ratio (delta : ℝ) (hd : 1 < delta) {n : ℕ} (hn : 1 ≤ n) :
    delta - 1 < ratio delta n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction k with
  | zero =>
    rw [ratio_one]
    linarith
  | succ k ih =>
    have hd0 : (0:ℝ) < delta := by linarith
    have hr : 0 < ratio delta (k + 1) := ratio_pos delta hd0 (by omega)
    rw [ratio_succ delta hd0 (by omega), lt_div_iff₀ (by linarith)]
    nlinarith

/-- Under the uniform cap `3 * delta < 11` and the row-2 bound
`delta ^ 2 < 3 * delta + 2`, every row from row 2 on stays below 3. -/
private lemma ratio_lt_three (delta : ℝ) (hd : 1 < delta) (hcap : 3 * delta < 11)
    (hbase : delta ^ 2 < 3 * delta + 2) {n : ℕ} (hn : 2 ≤ n) :
    ratio delta n < 3 := by
  have hd0 : (0:ℝ) < delta := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  clear hn
  induction k with
  | zero =>
    rw [show (0:ℕ) + 2 = 1 + 1 from rfl, ratio_succ delta hd0 le_rfl, ratio_one,
      div_lt_iff₀ (by linarith)]
    nlinarith
  | succ k ih =>
    have hr : 0 < ratio delta (k + 2) := ratio_pos delta hd0 (by omega)
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, ratio_succ delta hd0 (by omega),
      div_lt_iff₀ (by linarith)]
    rcases le_or_gt delta 3 with h | h
    · nlinarith
    · nlinarith

/-- Elasticity comparison: `ratio delta n / (delta - 1)` strictly decreases in `delta`. -/
private lemma scaled_ratio_cmp {a b : ℝ} (ha : 1 < a) (hab : a < b) {n : ℕ} (hn : 1 ≤ n) :
    (a - 1) * ratio b n < (b - 1) * ratio a n := by
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hb : 1 < b := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction k with
  | zero =>
    rw [ratio_one, ratio_one]
    nlinarith
  | succ k ih =>
    set x := ratio a (k + 1) with hx
    set y := ratio b (k + 1) with hy
    have hxpos : 0 < x := ratio_pos a ha0 (by omega)
    have hyb : b - 1 < y := sub_one_lt_ratio b hb (by omega)
    have hy0 : 0 < y := by linarith
    have hstep : (b - 1) * x ≤ (x + 1) * (y + 1) := by
      nlinarith [mul_pos hxpos (show (0:ℝ) < y - (b - 1) by linarith)]
    have key : (b - 1) * ((a - 1) * (y - x)) < (b - a) * ((x + 1) * (y + 1)) := by
      have h1 : (a - 1) * (y - x) < (b - a) * x := by nlinarith
      calc (b - 1) * ((a - 1) * (y - x)) < (b - 1) * ((b - a) * x) := by nlinarith
        _ ≤ (b - a) * ((x + 1) * (y + 1)) := by nlinarith
    rw [ratio_succ a ha0 (by omega), ratio_succ b hb0 (by omega), ← hx, ← hy,
      ← mul_div_assoc, ← mul_div_assoc, div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith [key]

/-! ### Continuity of the two channels -/

private lemma continuous_state (n : ℕ) :
    Continuous (fun d : ℝ => (state d n).1) ∧ Continuous (fun d : ℝ => (state d n).2) := by
  induction n with
  | zero => constructor <;> simpa [state] using continuous_const
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [state_succ]
      exact (continuous_id.mul h1).add h2
    · simp only [state_succ]
      exact h1.add h2

/-! ### Numeric facts about `silver` and `beta` -/

private lemma sqrt_two_bounds : (1.4142 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  constructor <;> nlinarith

private lemma beta_value : beta = 2 * (Real.sqrt 2 - 1) := by
  obtain ⟨h1, _⟩ := sqrt_two_bounds
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [beta, silver, div_eq_iff (by nlinarith)]
  nlinarith

private lemma beta_pos : 0 < beta := by
  rw [beta_value]
  have h1 := sqrt_two_bounds.1
  linarith

private lemma silver_le_three : silver ≤ 3 := by
  have h2 := sqrt_two_bounds.2
  rw [silver]
  linarith

private lemma silver_pos : 0 < silver := silver_identities.1

/-- For `z` in the working interval the shifted parameter is at least 3. -/
private lemma three_le_delta {z : ℝ} (hz : z ∈ Set.Icc silver 3) : 3 ≤ 1 + beta * z := by
  have hb := beta_pos
  have hs : beta * silver = 2 := silver_identities.2.1
  have : beta * silver ≤ beta * z := by
    exact mul_le_mul_of_nonneg_left hz.1 hb.le
  linarith [hs ▸ this]

/-! ### The recovery map -/

theorem recovery_denominator_pos {m : ℕ} (hm : 1 ≤ m) {z : ℝ}
    (hz : z ∈ Set.Icc silver 3) :
    0 < denominator (1 + beta * z) (2 * m) := by
  have hd : (0:ℝ) < 1 + beta * z := by linarith [three_le_delta hz]
  exact denominator_pos_of_pos _ hd (by omega)

theorem continuousOn_recoveryMap {m : ℕ} (hm : 1 ≤ m) :
    ContinuousOn (recoveryMap m) (Set.Icc silver 3) := by
  have hshift : Continuous (fun z : ℝ => 1 + beta * z) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hnum : Continuous (fun z : ℝ => numerator (1 + beta * z) (2 * m)) :=
    (continuous_state (2 * m)).1.comp hshift
  have hden : Continuous (fun z : ℝ => denominator (1 + beta * z) (2 * m)) :=
    (continuous_state (2 * m)).2.comp hshift
  have hEq : recoveryMap m = fun z : ℝ =>
      numerator (1 + beta * z) (2 * m) / denominator (1 + beta * z) (2 * m) := rfl
  rw [hEq]
  exact hnum.continuousOn.div hden.continuousOn
    fun z hz => (recovery_denominator_pos hm hz).ne'

theorem recoveryMap_silver_gt {m : ℕ} (hm : 1 ≤ m) :
    silver < recoveryMap m silver := by
  have hb : beta * silver = 2 := silver_identities.2.1
  have h3 : 1 + beta * silver = 3 := by rw [hb]; norm_num
  have hN : 1 ≤ 2 * m := by omega
  have hsb := sqrt_two_bounds
  have hsr0 : 0 < spectralRatio := by
    rw [spectralRatio]
    linarith [hsb.2]
  have hsr1 : spectralRatio < 1 := by
    rw [spectralRatio]
    linarith [hsb.1]
  have hp : 0 < spectralRatio ^ (2 * m) := pow_pos hsr0 _
  have hp1 : spectralRatio ^ (2 * m) < 1 := pow_lt_one₀ hsr0.le hsr1 (by omega)
  have hcorr : 0 < 2 * Real.sqrt 2 * spectralRatio ^ (2 * m) / (1 - spectralRatio ^ (2 * m)) := by
    apply div_pos _ (by linarith)
    have : 0 < Real.sqrt 2 := by linarith [hsb.1]
    positivity
  rw [recoveryMap, h3, ratio_three_closed_form hN]
  linarith

theorem recoveryMap_three_lt {m : ℕ} (hm : 1 ≤ m) :
    recoveryMap m 3 < 3 := by
  obtain ⟨hlow, hhigh⟩ := sqrt_two_bounds
  have hd : 1 + beta * 3 = 6 * Real.sqrt 2 - 5 := by
    rw [beta_value]; ring
  rw [recoveryMap]
  refine ratio_lt_three _ ?_ ?_ ?_ (by omega)
  · rw [hd]; linarith
  · rw [hd]; linarith
  · rw [hd]; nlinarith

theorem strictAntiOn_scaledRecoveryRatio {m : ℕ} (hm : 1 ≤ m) :
    StrictAntiOn (scaledRecoveryRatio m) (Set.Ioi (1 : ℝ)) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hkey := scaled_ratio_cmp ha hab (show 1 ≤ 2 * m by omega)
  have hb0 := beta_pos
  rw [scaledRecoveryRatio, scaledRecoveryRatio,
    div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hkey]

/-- A fixed point of the recovery map is exactly a solution of
`scaledRecoveryRatio m delta = 1` at `delta = 1 + beta * z`. -/
private lemma scaled_eq_one_of_fixed {m : ℕ} {z : ℝ} (hz : z ∈ Set.Icc silver 3)
    (hfix : recoveryMap m z = z) : scaledRecoveryRatio m (1 + beta * z) = 1 := by
  have hz0 : 0 < z := lt_of_lt_of_le silver_pos hz.1
  have hbz : 0 < beta * z := mul_pos beta_pos hz0
  have hr : ratio (1 + beta * z) (2 * m) = z := hfix
  rw [scaledRecoveryRatio, hr, add_sub_cancel_left]
  exact div_self hbz.ne'

theorem existsUnique_even_fixed_point {m : ℕ} (hm : 1 ≤ m) :
    ∃! z : ℝ,
      z ∈ Set.Icc silver 3 ∧
      denominator (1 + beta * z) (2 * m) ≠ 0 ∧
      recoveryMap m z = z := by
  have hcont : ContinuousOn (fun z : ℝ => recoveryMap m z - z) (Set.Icc silver 3) :=
    (continuousOn_recoveryMap hm).sub continuousOn_id
  have hlow : 0 < recoveryMap m silver - silver := by
    linarith [recoveryMap_silver_gt hm]
  have hhigh : recoveryMap m 3 - 3 < 0 := by
    linarith [recoveryMap_three_lt hm]
  have hmem : (0 : ℝ) ∈ Set.Icc (recoveryMap m 3 - 3) (recoveryMap m silver - silver) :=
    ⟨hhigh.le, hlow.le⟩
  obtain ⟨z, hzmem, hzval⟩ := intermediate_value_Icc' silver_le_three hcont hmem
  have hfix : recoveryMap m z = z := by
    have : recoveryMap m z - z = 0 := hzval
    linarith
  refine ⟨z, ⟨hzmem, (recovery_denominator_pos hm hzmem).ne', hfix⟩, ?_⟩
  rintro y ⟨hymem, -, hyfix⟩
  have hy1 : (1 : ℝ) + beta * y ∈ Set.Ioi (1 : ℝ) := by
    have : 0 < beta * y := mul_pos beta_pos (lt_of_lt_of_le silver_pos hymem.1)
    simp only [Set.mem_Ioi]
    linarith
  have hz1 : (1 : ℝ) + beta * z ∈ Set.Ioi (1 : ℝ) := by
    have : 0 < beta * z := mul_pos beta_pos (lt_of_lt_of_le silver_pos hzmem.1)
    simp only [Set.mem_Ioi]
    linarith
  have heq : 1 + beta * y = 1 + beta * z :=
    (strictAntiOn_scaledRecoveryRatio hm).injOn hy1 hz1
      ((scaled_eq_one_of_fixed hymem hyfix).trans (scaled_eq_one_of_fixed hzmem hfix).symm)
  have := beta_pos
  have hbeta : beta * y = beta * z := by linarith
  exact mul_left_cancel₀ beta_pos.ne' hbeta

noncomputable def evenFixedPoint (m : ℕ) : ℝ :=
  if hm : 1 ≤ m then
    Classical.choose (existsUnique_even_fixed_point hm)
  else
    silver

theorem evenFixedPoint_spec {m : ℕ} (hm : 1 ≤ m) :
    evenFixedPoint m ∈ Set.Icc silver 3 ∧
    denominator (1 + beta * evenFixedPoint m) (2 * m) ≠ 0 ∧
    recoveryMap m (evenFixedPoint m) = evenFixedPoint m := by
  rw [evenFixedPoint, dif_pos hm]
  exact (Classical.choose_spec (existsUnique_even_fixed_point hm)).1

theorem eq_evenFixedPoint_of_fixed {m : ℕ} (hm : 1 ≤ m) {z : ℝ}
    (hz : z ∈ Set.Icc silver 3)
    (hden : denominator (1 + beta * z) (2 * m) ≠ 0)
    (hfix : recoveryMap m z = z) :
    z = evenFixedPoint m := by
  rw [evenFixedPoint, dif_pos hm]
  exact (Classical.choose_spec (existsUnique_even_fixed_point hm)).2 z ⟨hz, hden, hfix⟩

end MetallicCutoff
