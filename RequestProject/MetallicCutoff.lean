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

end MetallicCutoff
