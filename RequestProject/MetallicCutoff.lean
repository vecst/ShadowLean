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

CORRECTED even-row picture.  An earlier version of this header placed the
even-row recovery fixed point below u and recorded the transverse limits with
the wrong signs.  High-precision signed tests (180 decimal digits) show the
opposite: the local positive fixed point z_N of the map z |-> R_N(1 + beta*z)
lies ABOVE u, and the corrected asymptotics are

  B^N (z_N - u) -> 4u,
  B^N ((1 - beta*z_N) - (-1)) -> -8,
  N * |R_N(1 - beta*z_N)| / B^N -> 1/2.

The exact landed formula R_N(3) > u (Target 3) is consistent with this
corrected picture.  In particular there is no fixed point in
[u - 1/10, u]; that existence claim is false and must not be formalized.

Status of the targets in this file.

  Targets 1--4 (proved here): exact parity degeneration at delta = -1, the
    silver normalizations, the closed form on the recovery channel delta = 3,
    and the static even-pole residue.
  Target 5 (proved here, Pass B): the two-sided signed moving-pole law
    `tendsto_even_moving_pole_signed` together with its absolute companion
    `tendsto_even_moving_pole`.  For any perturbation sequence with
    B^(2m) * epsilon m -> c and c ≠ 0 (either sign, in particular c = -8),

      (2m) * R_{2m}(-1 + epsilon m) / B^(2m) -> 4/c,
      (2m) * |R_{2m}(-1 + epsilon m)| / B^(2m) -> 4/|c|.

    This is strong enough to accept the transverse scale c = -8, but it does
    not prove existence of the fixed point.
  Targets 6--8: FUTURE CORRECTED WORK, not proved here and not claimed.  They
    concern existence and uniqueness of the even-row fixed point z_N above u,
    the asymptotic B^N (z_N - u) -> 4u, and the resulting cutoff constant
    obtained by feeding c = -8 into Target 5.  Nothing in this file asserts
    any of them.
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
      all_goals
        first
          | omega
          | nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_nonneg 2]
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


/- Target 5 (Pass B): the corrected two-sided signed moving-pole law.

The proof runs through uniform (in the row index) estimates for the two-step
data at `delta = -1 + e`, where the perturbation `e` is allowed to vary with
the row.  Writing `P k = evenNumerator (-1+e) k` and
`D k = evenDenominatorFactor (-1+e) k`, the recurrences read

  P (k+1) = (e^2 - 2e + 2) * P k + e^2 * D k,
  D (k+1) = P k + 2 * D k,

so `P k` is an `O(|e| k (2+4|e|)^k)` perturbation of `2^k` and `D k` is an
`O(|e| k^2 (2+4|e|)^k)` perturbation of `k * 2^k / 2`.  Since
`spectralBase * spectralRatio = 1`, the scale hypothesis forces
`k * |e k| -> 0`, which makes both relative errors vanish along the diagonal. -/

private lemma evenNumerator_succ (delta : ℝ) (k : ℕ) :
    evenNumerator delta (k + 1) =
      (delta ^ 2 + 1) * evenNumerator delta k +
        (delta + 1) ^ 2 * evenDenominatorFactor delta k := by
  rw [evenNumerator]

private lemma evenDenominatorFactor_succ (delta : ℝ) (k : ℕ) :
    evenDenominatorFactor delta (k + 1) =
      evenNumerator delta k + 2 * evenDenominatorFactor delta k := by
  rw [evenDenominatorFactor]

/-- Uniform growth of the two-step data at `delta = -1 + e`, valid for every
row index `k` and every perturbation `e` with `|e| ≤ 1`. -/
private lemma even_two_step_growth_bound (e : ℝ) (he : |e| ≤ 1) (k : ℕ) :
    |evenNumerator (-1 + e) k| + |e| * |evenDenominatorFactor (-1 + e) k| ≤
      (2 + 4 * |e|) ^ k := by
  have ha : (0 : ℝ) ≤ |e| := abs_nonneg e
  induction k with
  | zero => simp [evenNumerator, evenDenominatorFactor]
  | succ k ih =>
    have hP : evenNumerator (-1 + e) (k + 1) =
        ((-1 + e) ^ 2 + 1) * evenNumerator (-1 + e) k +
          e ^ 2 * evenDenominatorFactor (-1 + e) k := by
      rw [evenNumerator_succ]
      ring_nf
    have hD : evenDenominatorFactor (-1 + e) (k + 1) =
        evenNumerator (-1 + e) k + 2 * evenDenominatorFactor (-1 + e) k :=
      evenDenominatorFactor_succ _ k
    set P := evenNumerator (-1 + e) k
    set D := evenDenominatorFactor (-1 + e) k
    have hp0 : (0 : ℝ) ≤ |P| := abs_nonneg _
    have hd0 : (0 : ℝ) ≤ |D| := abs_nonneg _
    have hcoef : |(-1 + e) ^ 2 + 1| ≤ 2 + 2 * |e| + |e| ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [neg_abs_le e, le_abs_self e, sq_abs e]
    have h1 : |evenNumerator (-1 + e) (k + 1)| ≤
        (2 + 2 * |e| + |e| ^ 2) * |P| + |e| ^ 2 * |D| := by
      rw [hP]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_pow]
      gcongr
    have h2 : |e| * |evenDenominatorFactor (-1 + e) (k + 1)| ≤ |e| * (|P| + 2 * |D|) := by
      rw [hD]
      have htri : |P + 2 * D| ≤ |P| + 2 * |D| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        simp
      exact mul_le_mul_of_nonneg_left htri ha
    have hsq : |e| ^ 2 ≤ |e| := by nlinarith
    have hkey :
        (2 + 2 * |e| + |e| ^ 2) * |P| + |e| ^ 2 * |D| + |e| * (|P| + 2 * |D|) ≤
          (2 + 4 * |e|) * (|P| + |e| * |D|) := by
      nlinarith [mul_le_mul_of_nonneg_right hsq hp0, mul_nonneg (mul_nonneg ha ha) hd0]
    calc |evenNumerator (-1 + e) (k + 1)| + |e| * |evenDenominatorFactor (-1 + e) (k + 1)|
        ≤ ((2 + 2 * |e| + |e| ^ 2) * |P| + |e| ^ 2 * |D|) + |e| * (|P| + 2 * |D|) := by
          linarith
      _ ≤ (2 + 4 * |e|) * (|P| + |e| * |D|) := hkey
      _ ≤ (2 + 4 * |e|) * (2 + 4 * |e|) ^ k :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (2 + 4 * |e|) ^ (k + 1) := by ring

/-- The numerator of the two-step data is a controlled perturbation of `2^k`,
uniformly in the row index. -/
private lemma even_numerator_error_bound (e : ℝ) (he : |e| ≤ 1) (k : ℕ) :
    |evenNumerator (-1 + e) k - 2 ^ k| ≤ 2 * |e| * k * (2 + 4 * |e|) ^ k := by
  have ha : (0 : ℝ) ≤ |e| := abs_nonneg e
  induction k with
  | zero => simp [evenNumerator]
  | succ k ih =>
    have hgrow := even_two_step_growth_bound e he k
    have hbase : (0 : ℝ) ≤ 2 + 4 * |e| := by linarith
    have hbasepow : (0 : ℝ) ≤ (2 + 4 * |e|) ^ k := pow_nonneg hbase k
    have hP : evenNumerator (-1 + e) (k + 1) - 2 ^ (k + 1) =
        2 * (evenNumerator (-1 + e) k - 2 ^ k) +
            (e ^ 2 - 2 * e) * evenNumerator (-1 + e) k +
          e ^ 2 * evenDenominatorFactor (-1 + e) k := by
      rw [evenNumerator_succ]
      ring
    set P := evenNumerator (-1 + e) k
    set D := evenDenominatorFactor (-1 + e) k
    have hp0 : (0 : ℝ) ≤ |P| := abs_nonneg _
    have hd0 : (0 : ℝ) ≤ |D| := abs_nonneg _
    have hcoef : |e ^ 2 - 2 * e| ≤ 3 * |e| := by
      rw [abs_le]
      constructor <;> nlinarith [neg_abs_le e, le_abs_self e, sq_abs e]
    have habs : |evenNumerator (-1 + e) (k + 1) - 2 ^ (k + 1)| ≤
        2 * |P - 2 ^ k| + 3 * |e| * |P| + |e| * (|e| * |D|) := by
      rw [hP]
      have t1 := abs_add_three (2 * (P - 2 ^ k)) ((e ^ 2 - 2 * e) * P) (e ^ 2 * D)
      have t2 : |2 * (P - 2 ^ k)| = 2 * |P - 2 ^ k| := by
        rw [abs_mul]
        norm_num
      have t3 : |(e ^ 2 - 2 * e) * P| ≤ 3 * |e| * |P| := by
        rw [abs_mul]
        gcongr
      have t4 : |e ^ 2 * D| = |e| * (|e| * |D|) := by
        rw [abs_mul, abs_pow]
        ring
      linarith
    have hsum : 3 * |e| * |P| + |e| * (|e| * |D|) ≤ 4 * |e| * (2 + 4 * |e|) ^ k := by
      have hstep : 3 * |e| * |P| + |e| * (|e| * |D|) ≤ 4 * |e| * (|P| + |e| * |D|) := by
        nlinarith [mul_nonneg ha hp0, mul_nonneg ha (mul_nonneg ha hd0)]
      have hstep2 : 4 * |e| * (|P| + |e| * |D|) ≤ 4 * |e| * (2 + 4 * |e|) ^ k :=
        mul_le_mul_of_nonneg_left hgrow (by linarith)
      linarith
    have hpow2 : 2 * (2 + 4 * |e|) ^ k ≤ (2 + 4 * |e|) ^ (k + 1) := by
      have hexp : (2 + 4 * |e|) ^ (k + 1) = (2 + 4 * |e|) * (2 + 4 * |e|) ^ k := by ring
      nlinarith
    have hfinal : 2 * (2 * |e| * k * (2 + 4 * |e|) ^ k) + 4 * |e| * (2 + 4 * |e|) ^ k ≤
        2 * |e| * ((k : ℝ) + 1) * (2 + 4 * |e|) ^ (k + 1) := by
      have hcoef2 : (0 : ℝ) ≤ 2 * |e| * ((k : ℝ) + 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hpow2 hcoef2]
    push_cast
    calc |evenNumerator (-1 + e) (k + 1) - 2 ^ (k + 1)|
        ≤ 2 * |P - 2 ^ k| + 3 * |e| * |P| + |e| * (|e| * |D|) := habs
      _ ≤ 2 * (2 * |e| * k * (2 + 4 * |e|) ^ k) + 4 * |e| * (2 + 4 * |e|) ^ k := by
          linarith
      _ ≤ 2 * |e| * ((k : ℝ) + 1) * (2 + 4 * |e|) ^ (k + 1) := hfinal

/-- The reduced denominator of the two-step data is a controlled perturbation
of `k * 2^k / 2`, uniformly in the row index. -/
private lemma even_denominator_error_bound (e : ℝ) (he : |e| ≤ 1) (k : ℕ) :
    |evenDenominatorFactor (-1 + e) k - (k : ℝ) * 2 ^ k / 2| ≤
      |e| * (k : ℝ) ^ 2 * (2 + 4 * |e|) ^ k := by
  have ha : (0 : ℝ) ≤ |e| := abs_nonneg e
  induction k with
  | zero => simp [evenDenominatorFactor]
  | succ k ih =>
    have hnum := even_numerator_error_bound e he k
    have hbase : (0 : ℝ) ≤ 2 + 4 * |e| := by linarith
    have hbasepow : (0 : ℝ) ≤ (2 + 4 * |e|) ^ k := pow_nonneg hbase k
    have hD : evenDenominatorFactor (-1 + e) (k + 1) - ((k : ℝ) + 1) * 2 ^ (k + 1) / 2 =
        (evenNumerator (-1 + e) k - 2 ^ k) +
          2 * (evenDenominatorFactor (-1 + e) k - (k : ℝ) * 2 ^ k / 2) := by
      rw [evenDenominatorFactor_succ]
      ring
    have habs : |evenDenominatorFactor (-1 + e) (k + 1) - ((k : ℝ) + 1) * 2 ^ (k + 1) / 2| ≤
        |evenNumerator (-1 + e) k - 2 ^ k| +
          2 * |evenDenominatorFactor (-1 + e) k - (k : ℝ) * 2 ^ k / 2| := by
      rw [hD]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      norm_num
    have hpow2 : 2 * (2 + 4 * |e|) ^ k ≤ (2 + 4 * |e|) ^ (k + 1) := by
      have hexp : (2 + 4 * |e|) ^ (k + 1) = (2 + 4 * |e|) * (2 + 4 * |e|) ^ k := by ring
      nlinarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hfinal :
        2 * |e| * k * (2 + 4 * |e|) ^ k + 2 * (|e| * (k : ℝ) ^ 2 * (2 + 4 * |e|) ^ k) ≤
          |e| * ((k : ℝ) + 1) ^ 2 * (2 + 4 * |e|) ^ (k + 1) := by
      have hcoef : (0 : ℝ) ≤ |e| * ((k : ℝ) + 1) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hpow2 hcoef,
        mul_nonneg (mul_nonneg ha hk0) hbasepow]
    push_cast
    calc |evenDenominatorFactor (-1 + e) (k + 1) - ((k : ℝ) + 1) * 2 ^ (k + 1) / 2|
        ≤ |evenNumerator (-1 + e) k - 2 ^ k| +
            2 * |evenDenominatorFactor (-1 + e) k - (k : ℝ) * 2 ^ k / 2| := habs
      _ ≤ 2 * |e| * k * (2 + 4 * |e|) ^ k + 2 * (|e| * (k : ℝ) ^ 2 * (2 + 4 * |e|) ^ k) := by
          linarith
      _ ≤ |e| * ((k : ℝ) + 1) ^ 2 * (2 + 4 * |e|) ^ (k + 1) := hfinal

private lemma one_add_two_abs_pow_le_exp (e : ℝ) (k : ℕ) :
    (1 + 2 * |e|) ^ k ≤ Real.exp (2 * ((k : ℝ) * |e|)) := by
  have ha : (0 : ℝ) ≤ |e| := abs_nonneg e
  have h1 : 1 + 2 * |e| ≤ Real.exp (2 * |e|) := by
    linarith [Real.add_one_le_exp (2 * |e|)]
  calc (1 + 2 * |e|) ^ k ≤ (Real.exp (2 * |e|)) ^ k :=
        pow_le_pow_left₀ (by linarith) h1 k
    _ = Real.exp (2 * ((k : ℝ) * |e|)) := by
        rw [show (2 : ℝ) * ((k : ℝ) * |e|) = (k : ℝ) * (2 * |e|) by ring, Real.exp_nat_mul]

/-- The scale hypothesis at the even pole forces the perturbation to decay
faster than any polynomial rate; this is the form used below. -/
private lemma tendsto_nat_mul_abs_epsilon {epsilon : ℕ → ℝ} {c : ℝ}
    (hepsilon_scale :
      Tendsto (fun m : ℕ => spectralBase ^ (2 * m) * epsilon m) atTop (nhds c)) :
    Tendsto (fun m : ℕ => (m : ℝ) * |epsilon m|) atTop (nhds 0) := by
  obtain ⟨-, -, -, hBr⟩ := silver_identities
  have hsqrt : Real.sqrt 2 < 3 / 2 := by
    have h2 : Real.sqrt 2 < 2 := by
      norm_num [Real.sqrt_lt']
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hrpos : 0 < spectralRatio := by
    unfold spectralRatio
    linarith
  have hr1 : spectralRatio < 1 := by
    unfold spectralRatio
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2,
      Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 2),
      Real.sqrt_one]
  have hgeo : Tendsto (fun m : ℕ => (m : ℝ) * (spectralRatio ^ 2) ^ m) atTop (nhds 0) := by
    refine tendsto_self_mul_const_pow_of_abs_lt_one ?_
    rw [abs_of_pos (by positivity)]
    nlinarith
  have habs := hepsilon_scale.abs
  have hmul := habs.mul hgeo
  rw [mul_zero] at hmul
  refine hmul.congr ?_
  intro m
  have hBpow : spectralBase ^ (2 * m) * (spectralRatio ^ 2) ^ m = 1 := by
    have : spectralBase ^ (2 * m) * (spectralRatio ^ 2) ^ m =
        (spectralBase * spectralRatio) ^ (2 * m) := by
      rw [mul_pow]
      rw [show (spectralRatio ^ 2) ^ m = spectralRatio ^ (2 * m) by
        rw [← pow_mul, mul_comm]]
    rw [this, hBr, one_pow]
  have hBnonneg : (0 : ℝ) ≤ spectralBase ^ (2 * m) := by
    have : (0 : ℝ) < spectralBase := by
      unfold spectralBase
      positivity
    positivity
  calc |spectralBase ^ (2 * m) * epsilon m| * ((m : ℝ) * (spectralRatio ^ 2) ^ m)
      = (spectralBase ^ (2 * m) * (spectralRatio ^ 2) ^ m) * ((m : ℝ) * |epsilon m|) := by
        rw [abs_mul, abs_of_nonneg hBnonneg]
        ring
    _ = (m : ℝ) * |epsilon m| := by rw [hBpow, one_mul]

/-- Varying-row limit for the numerator of the two-step data. -/
private lemma tendsto_evenNumerator_div_two_pow {epsilon : ℕ → ℝ}
    (hsmall : Tendsto (fun m : ℕ => (m : ℝ) * |epsilon m|) atTop (nhds 0)) :
    Tendsto (fun m : ℕ => evenNumerator (-1 + epsilon m) m / 2 ^ m) atTop (nhds 1) := by
  have hbound : ∀ᶠ m : ℕ in atTop,
      ‖evenNumerator (-1 + epsilon m) m / 2 ^ m - 1‖ ≤
        2 * ((m : ℝ) * |epsilon m|) * Real.exp (2 * ((m : ℝ) * |epsilon m|)) := by
    filter_upwards [hsmall.eventually_lt_const (by norm_num : (0:ℝ) < 1),
      eventually_ge_atTop 1] with m hm1 hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have habs1 : |epsilon m| ≤ 1 := by
      nlinarith [abs_nonneg (epsilon m)]
    have hbnd := even_numerator_error_bound (epsilon m) habs1 m
    have h2pow : (0 : ℝ) < 2 ^ m := by positivity
    have hsplit : (2 + 4 * |epsilon m|) ^ m = 2 ^ m * (1 + 2 * |epsilon m|) ^ m := by
      rw [← mul_pow]
      ring_nf
    have hrewrite : evenNumerator (-1 + epsilon m) m / 2 ^ m - 1 =
        (evenNumerator (-1 + epsilon m) m - 2 ^ m) / 2 ^ m := by
      field_simp
    have hkey : ‖evenNumerator (-1 + epsilon m) m / 2 ^ m - 1‖ =
        |evenNumerator (-1 + epsilon m) m - 2 ^ m| / 2 ^ m := by
      rw [Real.norm_eq_abs, hrewrite, abs_div, abs_of_pos h2pow]
    rw [hkey, div_le_iff₀ h2pow]
    calc |evenNumerator (-1 + epsilon m) m - 2 ^ m|
        ≤ 2 * |epsilon m| * m * (2 + 4 * |epsilon m|) ^ m := hbnd
      _ = (2 * ((m : ℝ) * |epsilon m|) * (1 + 2 * |epsilon m|) ^ m) * 2 ^ m := by
          rw [hsplit]; ring
      _ ≤ (2 * ((m : ℝ) * |epsilon m|) * Real.exp (2 * ((m : ℝ) * |epsilon m|))) * 2 ^ m := by
          have hco : (0 : ℝ) ≤ 2 * ((m : ℝ) * |epsilon m|) := by positivity
          have := one_add_two_abs_pow_le_exp (epsilon m) m
          have hmul := mul_le_mul_of_nonneg_left this hco
          nlinarith [h2pow.le]
  have hg : Tendsto
      (fun m : ℕ => 2 * ((m : ℝ) * |epsilon m|) * Real.exp (2 * ((m : ℝ) * |epsilon m|)))
      atTop (nhds 0) := by
    have hcont : Continuous fun t : ℝ => 2 * t * Real.exp (2 * t) := by
      fun_prop
    have := (hcont.tendsto 0).comp hsmall
    simpa [Function.comp_def] using this
  have hzero := squeeze_zero_norm' hbound hg
  have hshift := hzero.add_const 1
  simpa using hshift

/-- Varying-row limit for the reduced denominator of the two-step data. -/
private lemma tendsto_evenDenominatorFactor_div {epsilon : ℕ → ℝ}
    (hsmall : Tendsto (fun m : ℕ => (m : ℝ) * |epsilon m|) atTop (nhds 0)) :
    Tendsto (fun m : ℕ => evenDenominatorFactor (-1 + epsilon m) m / (2 ^ m * (m : ℝ)))
      atTop (nhds (1 / 2)) := by
  have hbound : ∀ᶠ m : ℕ in atTop,
      ‖evenDenominatorFactor (-1 + epsilon m) m / (2 ^ m * (m : ℝ)) - 1 / 2‖ ≤
        ((m : ℝ) * |epsilon m|) * Real.exp (2 * ((m : ℝ) * |epsilon m|)) := by
    filter_upwards [hsmall.eventually_lt_const (by norm_num : (0:ℝ) < 1),
      eventually_ge_atTop 1] with m hm1 hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have habs1 : |epsilon m| ≤ 1 := by
      nlinarith [abs_nonneg (epsilon m)]
    have hbnd := even_denominator_error_bound (epsilon m) habs1 m
    have h2pow : (0 : ℝ) < 2 ^ m := by positivity
    have hprod : (0 : ℝ) < 2 ^ m * (m : ℝ) := by positivity
    have hsplit : (2 + 4 * |epsilon m|) ^ m = 2 ^ m * (1 + 2 * |epsilon m|) ^ m := by
      rw [← mul_pow]
      ring_nf
    have hrewrite : evenDenominatorFactor (-1 + epsilon m) m / (2 ^ m * (m : ℝ)) - 1 / 2 =
        (evenDenominatorFactor (-1 + epsilon m) m - (m : ℝ) * 2 ^ m / 2) / (2 ^ m * (m : ℝ)) := by
      field_simp
    have hkey : ‖evenDenominatorFactor (-1 + epsilon m) m / (2 ^ m * (m : ℝ)) - 1 / 2‖ =
        |evenDenominatorFactor (-1 + epsilon m) m - (m : ℝ) * 2 ^ m / 2| / (2 ^ m * (m : ℝ)) := by
      rw [Real.norm_eq_abs, hrewrite, abs_div, abs_of_pos hprod]
    rw [hkey, div_le_iff₀ hprod]
    calc |evenDenominatorFactor (-1 + epsilon m) m - (m : ℝ) * 2 ^ m / 2|
        ≤ |epsilon m| * (m : ℝ) ^ 2 * (2 + 4 * |epsilon m|) ^ m := hbnd
      _ = (((m : ℝ) * |epsilon m|) * (1 + 2 * |epsilon m|) ^ m) * (2 ^ m * (m : ℝ)) := by
          rw [hsplit]; ring
      _ ≤ (((m : ℝ) * |epsilon m|) * Real.exp (2 * ((m : ℝ) * |epsilon m|))) *
            (2 ^ m * (m : ℝ)) := by
          have hco : (0 : ℝ) ≤ (m : ℝ) * |epsilon m| := by positivity
          have := one_add_two_abs_pow_le_exp (epsilon m) m
          have hmul := mul_le_mul_of_nonneg_left this hco
          nlinarith [hprod.le]
  have hg : Tendsto
      (fun m : ℕ => ((m : ℝ) * |epsilon m|) * Real.exp (2 * ((m : ℝ) * |epsilon m|)))
      atTop (nhds 0) := by
    have hcont : Continuous fun t : ℝ => t * Real.exp (2 * t) := by
      fun_prop
    have := (hcont.tendsto 0).comp hsmall
    simpa [Function.comp_def] using this
  have hzero := squeeze_zero_norm' hbound hg
  have hshift := hzero.add_const (1 / 2)
  simpa using hshift

theorem tendsto_even_moving_pole_signed
    {epsilon : ℕ → ℝ} {c : ℝ}
    (hc : c ≠ 0)
    (hepsilon_scale :
      Tendsto
        (fun m : ℕ => spectralBase ^ (2 * m) * epsilon m)
        atTop (nhds c)) :
    Tendsto
      (fun m : ℕ =>
        (((2 * m : ℕ) : ℝ) * ratio (-1 + epsilon m) (2 * m)) /
          spectralBase ^ (2 * m))
      atTop (nhds (4 / c)) := by
  have hsmall := tendsto_nat_mul_abs_epsilon hepsilon_scale
  have hnum := tendsto_evenNumerator_div_two_pow hsmall
  have hden := tendsto_evenDenominatorFactor_div hsmall
  have hG : Tendsto
      (fun m : ℕ =>
        2 * (evenNumerator (-1 + epsilon m) m / 2 ^ m) /
          (evenDenominatorFactor (-1 + epsilon m) m / (2 ^ m * (m : ℝ))))
      atTop (nhds 4) := by
    have h := (hnum.const_mul (2 : ℝ)).div hden (by norm_num)
    norm_num at h
    exact h
  have hquot := hG.div hepsilon_scale hc
  have hlim : Tendsto
      (fun m : ℕ =>
        (2 * (evenNumerator (-1 + epsilon m) m / 2 ^ m) /
            (evenDenominatorFactor (-1 + epsilon m) m / (2 ^ m * (m : ℝ)))) /
          (spectralBase ^ (2 * m) * epsilon m))
      atTop (nhds (4 / c)) := hquot
  refine hlim.congr' ?_
  filter_upwards [hepsilon_scale.eventually_ne hc, eventually_ge_atTop 1] with m hne hm
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℕ) ≤ m := hm
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hBpos : (0 : ℝ) < spectralBase := by
    unfold spectralBase
    positivity
  have hBpow : (0 : ℝ) < spectralBase ^ (2 * m) := by positivity
  have heps : epsilon m ≠ 0 := by
    intro h
    apply hne
    rw [h, mul_zero]
  have h2pow : (0 : ℝ) < 2 ^ m := by positivity
  have hratio : ratio (-1 + epsilon m) (2 * m) =
      evenNumerator (-1 + epsilon m) m /
        (epsilon m * evenDenominatorFactor (-1 + epsilon m) m) := by
    rw [ratio, numerator, denominator, state_even_factorization]
    norm_num
  rw [hratio]
  push_cast
  rcases eq_or_ne (evenDenominatorFactor (-1 + epsilon m) m) 0 with hD | hD
  · rw [hD]
    simp
  · field_simp

theorem tendsto_even_moving_pole
    {epsilon : ℕ → ℝ} {c : ℝ}
    (hc : c ≠ 0)
    (hepsilon_scale :
      Tendsto
        (fun m : ℕ => spectralBase ^ (2 * m) * epsilon m)
        atTop (nhds c)) :
    Tendsto
      (fun m : ℕ =>
        (((2 * m : ℕ) : ℝ) * |ratio (-1 + epsilon m) (2 * m)|) /
          spectralBase ^ (2 * m))
      atTop (nhds (4 / |c|)) := by
  have hsigned := tendsto_even_moving_pole_signed hc hepsilon_scale
  have habs := hsigned.abs
  have hval : |4 / c| = 4 / |c| := by
    rw [abs_div]
    norm_num
  rw [hval] at habs
  refine habs.congr ?_
  intro m
  have hBpos : (0 : ℝ) < spectralBase := by
    unfold spectralBase
    positivity
  have hBpow : (0 : ℝ) < spectralBase ^ (2 * m) := by positivity
  rw [abs_div, abs_mul, abs_of_pos hBpow, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * m : ℕ) : ℝ))]

end MetallicCutoff
