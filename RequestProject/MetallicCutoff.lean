/-
Aristotle targets: deterministic foundation for the selector-controlled
metallic tail experiment.

The recurrence is

  P_{N+1} = delta * P_N + Q_N,
  Q_{N+1} = P_N + Q_N,
  (P_0,Q_0) = (1,0),

and R_N(delta) = P_N(delta) / Q_N(delta).  Put

  u    = 1 + sqrt 2,
  beta = 2/u,
  B    = 3 + 2 sqrt 2 = u^2.

Numerics at 200 decimal digits support the following even-row picture.  The
map z |-> R_N(1 + beta*z) has a unique fixed point z_N just below u, with

  B^N (u-z_N) -> 4u.

Consequently the transverse pulse delta = 1-beta*z_N approaches the even-row
pole delta=-1 at speed

  B^N ((1-beta*z_N)-(-1)) -> 8,

and

  N * |R_N(1-beta*z_N)| / B^N -> 1/2.

The file deliberately separates exact algebra, the moving-pole estimate, and
the fixed-point asymptotic.  Please prove actual named constants.  Do not move
an unproved target into a comment block; if a target cannot be completed,
leave it out of the returned file and report it explicitly.

Suggested order:

  Pass A: Targets 1--4 (exact algebra and static pole).
  Pass B: Target 5 (uniform moving-pole asymptotic).
  Pass C: Targets 6--8 (fixed point and cutoff constant).

Minor changes to Mathlib lemma names and harmless strengthening of hypotheses
are fine.  Do not weaken the constants 4u, 8, or 1/2, and preserve the even
row and m>=1 boundaries.
-/

import Mathlib

open Filter Set Topology

set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

namespace MetallicCutoff

noncomputable def state (delta : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 =>
      let previous := state delta n
      (delta * previous.1 + previous.2, previous.1 + previous.2)

noncomputable def numerator (delta : ℝ) (N : ℕ) : ℝ :=
  (state delta N).1

noncomputable def denominator (delta : ℝ) (N : ℕ) : ℝ :=
  (state delta N).2

noncomputable def ratio (delta : ℝ) (N : ℕ) : ℝ :=
  numerator delta N / denominator delta N

noncomputable def silver : ℝ := 1 + Real.sqrt 2
noncomputable def beta : ℝ := 2 / silver
noncomputable def spectralBase : ℝ := 3 + 2 * Real.sqrt 2
noncomputable def spectralRatio : ℝ := 3 - 2 * Real.sqrt 2

lemma state_succ (delta : ℝ) (n : ℕ) :
    state delta (n + 1) =
      (delta * (state delta n).1 + (state delta n).2,
        (state delta n).1 + (state delta n).2) := by
  rw [state]

lemma state_neg_one_pair (m : ℕ) :
    state (-1) (2 * m) = ((2 : ℝ) ^ m, 0) ∧
      state (-1) (2 * m + 1) = (-((2 : ℝ) ^ m), (2 : ℝ) ^ m) := by
  induction m with
  | zero => norm_num [state]
  | succ m ih =>
    rcases ih with ⟨heven, hodd⟩
    constructor
    · rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        state_succ, hodd]
      simp [pow_succ]
      ring
    · rw [show 2 * (m + 1) + 1 = ((2 * m + 1) + 1) + 1 by omega,
        state_succ, state_succ, hodd]
      simp [pow_succ]
      constructor <;> ring

/- Target 1: the exact parity degeneration at the static pole delta=-1. -/
theorem state_neg_one_even (m : ℕ) :
    state (-1) (2 * m) = ((2 : ℝ) ^ m, 0) := by
  exact (state_neg_one_pair m).1

theorem state_neg_one_odd (m : ℕ) :
    state (-1) (2 * m + 1) = (-((2 : ℝ) ^ m), (2 : ℝ) ^ m) := by
  exact (state_neg_one_pair m).2

/- Target 2: exact silver identities needed to normalize every later limit. -/
theorem silver_identities :
    0 < silver ∧
    beta * silver = 2 ∧
    spectralBase = silver ^ 2 ∧
    spectralBase * spectralRatio = 1 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsilver : 0 < silver := by
    unfold silver
    positivity
  refine ⟨hsilver, ?_, ?_, ?_⟩
  · unfold beta
    field_simp
  · unfold spectralBase silver
    nlinarith
  · unfold spectralBase spectralRatio
    nlinarith

/- Target 3: closed form on the recovery channel delta=3. -/

private lemma state_three_closed_form (N : Nat) :
    state 3 N =
      (((1 + Real.sqrt 2) * (2 + Real.sqrt 2) ^ N -
          (1 - Real.sqrt 2) * (2 - Real.sqrt 2) ^ N) /
        (2 * Real.sqrt 2),
       ((2 + Real.sqrt 2) ^ N - (2 - Real.sqrt 2) ^ N) /
        (2 * Real.sqrt 2)) := by
  induction N with
  | zero =>
    simp [state]
    ring_nf
    norm_num
  | succ N ih =>
    rw [state_succ, ih]
    simp only
    ext
    all_goals field_simp
    all_goals ring_nf
    all_goals rw [Real.sq_sqrt]
    all_goals norm_num
    all_goals ring

theorem ratio_three_closed_form {N : Nat} (hN : 1 <= N) :
    ratio 3 N =
      silver +
        (2 * Real.sqrt 2 * spectralRatio ^ N) /
          (1 - spectralRatio ^ N) := by
  rw [ratio, numerator, denominator, state_three_closed_form]
  have sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
  have sqrt2_ne_zero : Real.sqrt 2 ≠ 0 := sqrt2_pos.ne'
  have silver_eq : silver = 1 + Real.sqrt 2 := rfl
  have spectralRatio_eq : spectralRatio = 3 - 2 * Real.sqrt 2 := rfl
  have h1 : (2 - Real.sqrt 2) / (2 + Real.sqrt 2) = spectralRatio := by
    rw [spectralRatio_eq]
    have h2 : (2 + Real.sqrt 2) * (3 - 2 * Real.sqrt 2) = 2 - Real.sqrt 2 := by
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
      ring
    rw [div_eq_iff (show (2 + Real.sqrt 2) ≠ 0 by linarith [Real.sqrt_nonneg 2])]
    rw [mul_comm]
    exact h2.symm
  have h2pos : 2 + Real.sqrt 2 > 0 := by linarith [Real.sqrt_nonneg 2]
  have h2ne : 2 + Real.sqrt 2 ≠ 0 := ne_of_gt h2pos
  have hdenom_eq : (2 - Real.sqrt 2) ^ N = spectralRatio ^ N * (2 + Real.sqrt 2) ^ N := by
    have := congrArg (· ^ N) h1
    simp only [div_pow] at this
    field_simp at this
    rw [mul_comm] at this
    exact this
  -- Use these facts in the main simplification
  have sqrt2_ne_zero' : Real.sqrt 2 ≠ 0 := sqrt2_ne_zero
  -- First show 1 - spectralRatio^N ≠ 0
  have h_sqrt2_gt_1 : Real.sqrt 2 > 1 := by
    norm_num [Real.lt_sqrt]
  have h_sqrt2_lt_2 : Real.sqrt 2 < 2 := by
    norm_num [Real.sqrt_lt]
  have h_spec_lt_one : spectralRatio < 1 := by
    rw [spectralRatio_eq]
    nlinarith
  have h_spec_pos : 0 < spectralRatio := by
    rw [spectralRatio_eq]
    nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
  have h_spec_pow_pos : 0 < spectralRatio ^ N := pow_pos h_spec_pos N
  have h_spec_pow_lt_one : spectralRatio ^ N < 1 := pow_lt_one₀ (le_of_lt h_spec_pos) h_spec_lt_one (by omega)
  have h_denom_ne_zero : 1 - spectralRatio ^ N ≠ 0 := by linarith
  -- Also need (2 + √2)^N ≠ 0 and (2 + √2)^N - (2 - √2)^N ≠ 0
  have h_base_pos : 0 < (2 + Real.sqrt 2) ^ N := pow_pos h2pos N
  have h_base_ne : (2 + Real.sqrt 2) ^ N ≠ 0 := ne_of_gt h_base_pos
  have h_denom_ne : (2 + Real.sqrt 2) ^ N - (2 - Real.sqrt 2) ^ N ≠ 0 := by
    have h_lt : (2 - Real.sqrt 2) ^ N < (2 + Real.sqrt 2) ^ N := by
      gcongr
      · nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
    linarith
  -- Now use field_simp to clear denominators
  rw [silver_eq]
  field_simp [sqrt2_ne_zero, h_denom_ne_zero, h_denom_ne]
  -- Substitute hdenom_eq to replace (2 - √2)^N with spectralRatio^N * (2 + √2)^N
  rw [hdenom_eq]
  ring

/- For two recurrence steps, `evenNumerator` and `evenDenominatorFactor`
record the numerator and the denominator after removing its factor `delta+1`. -/
mutual
  private noncomputable def evenNumerator (delta : Real) : Nat → Real
    | 0 => 1
    | m + 1 => (delta ^ 2 + 1) * evenNumerator delta m +
        (delta + 1) ^ 2 * evenDenominatorFactor delta m
  private noncomputable def evenDenominatorFactor (delta : Real) : Nat → Real
    | 0 => 0
    | m + 1 => evenNumerator delta m + 2 * evenDenominatorFactor delta m
end

private lemma state_even_factorization (delta : Real) (m : Nat) :
    state delta (2 * m) =
      (evenNumerator delta m, (delta + 1) * evenDenominatorFactor delta m) := by
  induction m with
  | zero => simp [state, evenNumerator, evenDenominatorFactor]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    rw [state_succ, state_succ, ih]
    simp [evenNumerator, evenDenominatorFactor]
    ring_nf
    trivial

private lemma even_data_neg_one (m : Nat) :
    evenNumerator (-1) m = (2 : Real) ^ m ∧
    evenDenominatorFactor (-1) m = (m : Real) * 2 ^ (m - 1) := by
  induction m with
  | zero =>
    simp [evenNumerator, evenDenominatorFactor]
  | succ m ih =>
    rcases ih with ⟨hnum, hdenom⟩
    constructor
    · simp [evenNumerator, hnum]
      ring
    · simp [evenDenominatorFactor, hnum, hdenom]
      rcases m with _ | m
      · norm_num
      · simp [pow_succ]
        ring

private lemma continuous_evenNumerator (m : Nat) :
    Continuous (fun delta : Real => evenNumerator delta m) := by
  have hboth : ∀ m, Continuous (fun delta : Real => evenNumerator delta m) ∧
                       Continuous (fun delta : Real => evenDenominatorFactor delta m) := by
    intro m
    induction m with
    | zero =>
      simp [evenNumerator, evenDenominatorFactor]
      exact ⟨continuous_const, continuous_const⟩
    | succ m ih =>
      rcases ih with ⟨hnum, hdenom⟩
      constructor
      · simp [evenNumerator]
        apply Continuous.add
        · apply Continuous.mul
          · exact Continuous.add (continuous_pow 2) continuous_const
          · exact hnum
        · apply Continuous.mul
          · exact Continuous.pow (continuous_id.add continuous_const) 2
          · exact hdenom
      · simp [evenDenominatorFactor]
        apply Continuous.add
        · exact hnum
        · exact Continuous.mul continuous_const hdenom
  exact (hboth m).1

private lemma continuous_evenDenominatorFactor (m : Nat) :
    Continuous (fun delta : Real => evenDenominatorFactor delta m) := by
  have hboth : ∀ m, Continuous (fun delta : Real => evenNumerator delta m) ∧
                       Continuous (fun delta : Real => evenDenominatorFactor delta m) := by
    intro m
    induction m with
    | zero =>
      simp [evenNumerator, evenDenominatorFactor]
      exact ⟨continuous_const, continuous_const⟩
    | succ m ih =>
      rcases ih with ⟨hnum, hdenom⟩
      constructor
      · simp [evenNumerator]
        apply Continuous.add
        · apply Continuous.mul
          · exact Continuous.add (continuous_pow 2) continuous_const
          · exact hnum
        · apply Continuous.mul
          · exact Continuous.pow (continuous_id.add continuous_const) 2
          · exact hdenom
      · simp [evenDenominatorFactor]
        apply Continuous.add
        · exact hnum
        · exact Continuous.mul continuous_const hdenom
  exact (hboth m).2

/- Target 4: the residue of the positive even-row pole is exactly 2/m,
equivalently 4/N for N = 2*m. -/
theorem even_pole_residue {m : Nat} (hm : 1 <= m) :
    Tendsto
      (fun delta : Real => (delta + 1) * ratio delta (2 * m))
      (nhdsWithin (-1) ({-1}ᶜ))
      (nhds (2 / (m : Real))) := by
  -- The key insight: ratio delta (2*m) = evenNumerator delta m / ((delta+1) * evenDenominatorFactor delta m)
  -- So (delta+1) * ratio = evenNumerator delta m / evenDenominatorFactor delta m for delta ≠ -1
  have hcont_num := continuous_evenNumerator m
  have hcont_denom : Continuous (fun delta : Real => evenDenominatorFactor delta m) := by
    have hboth : ∀ m, Continuous (fun delta : Real => evenNumerator delta m) ∧
                           Continuous (fun delta : Real => evenDenominatorFactor delta m) := by
      intro m
      induction m with
      | zero =>
        simp [evenNumerator, evenDenominatorFactor]
        exact ⟨continuous_const, continuous_const⟩
      | succ m ih =>
        rcases ih with ⟨hnum, hdenom⟩
        constructor
        · simp [evenNumerator]
          apply Continuous.add
          · apply Continuous.mul
            · exact Continuous.add (continuous_pow 2) continuous_const
            · exact hnum
          · apply Continuous.mul
            · exact Continuous.pow (continuous_id.add continuous_const) 2
            · exact hdenom
        · simp [evenDenominatorFactor]
          apply Continuous.add
          · exact hnum
          · exact Continuous.mul continuous_const hdenom
    exact (hboth m).2
  -- The limit equals 2^m / (m * 2^(m-1)) = 2/m
  have hval : evenNumerator (-1) m / evenDenominatorFactor (-1) m = 2 / (m : Real) := by
    rw [even_data_neg_one m |>.1, even_data_neg_one m |>.2]
    rcases m with _ | m
    · simp at hm
    · simp only [Nat.add_sub_cancel]
      rw [show (m + 1 : ℕ) = m + 1 from rfl, pow_succ]
      field_simp
  -- Use continuity: the limit equals hval
  have hdenom_ne : evenDenominatorFactor (-1) m ≠ 0 := by
    rw [even_data_neg_one m |>.2]
    positivity
  have hlim : Tendsto (fun delta => evenNumerator delta m / evenDenominatorFactor delta m)
      (nhds (-1)) (nhds (evenNumerator (-1) m / evenDenominatorFactor (-1) m)) :=
    hcont_num.continuousAt.div hcont_denom.continuousAt hdenom_ne
  rw [hval] at hlim
  refine hlim.mono_left nhdsWithin_le_nhds |>.congr' ?_
  rw [Filter.EventuallyEq]
  apply eventually_nhdsWithin_of_forall
  intro x hx
  simp only [ratio, numerator, denominator]
  rw [state_even_factorization]
  field_simp [show x + 1 ≠ 0 from add_eq_zero_iff_eq_neg.not.mpr hx]

end MetallicCutoff
