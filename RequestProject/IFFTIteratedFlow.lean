/-
Finite-time IFFT coordinate-flow bridge. Iterates the one-step results of
`IFFTCoordinateBridge`: `n` coordinate steps carry the `n`th power of the
channel multiplier `1 + α·ζ^k`, the IFFT-evolved packet equals the `n`-fold
coordinate iterate, and the resulting flow has the expected semigroup and
support laws. Finite `g`, finite `n` only — no convergence/positivity/Poisson.

Notation `f^[n]` is `Function.iterate f n`.

Proof routes (keep every statement verbatim; close all seven):
- T1 packetSpectrum_packetCoordinateStep_iterate: induction on `n`. Base
  `Function.iterate_zero`, `pow_zero`, `mul_one`. Step `Function.iterate_succ'`
  (outer step) then `packetSpectrum_packetCoordinateStep` + IH + `pow_succ`;
  no α ≠ 0.
- T2 evolvedPreparedPacket_zero: base case of `evolvedPreparedPacket`'s
  recursion — `simp [evolvedPreparedPacket]` / definitional; no α ≠ 0.
- T3 evolvedPreparedPacket_eq_packetCoordinateStep_iterate (α ≠ 0): induction on
  `n`. Base T2 + `Function.iterate_zero`. Step
  `evolvedPreparedPacket_succ_eq_packetCoordinateStep hα` + IH +
  `Function.iterate_succ'`.
- T4 packetCoordinateStep_iterate_evolvedPreparedPacket (α ≠ 0): rewrite both
  sides through T3 and use `Function.iterate_add_apply` (order n + m), or induct
  on `m` with `Function.iterate_succ'` and `evolvedPreparedPacket` succ.
- T5 packetCoordinateStep_iterate_no_spectral_leakage: from T1, the transformed
  channel is `packetSpectrum α C k * mult^n`; `hC` gives the left factor `0`,
  so `zero_mul`; no α ≠ 0.
- T6 packetSpectrum_packetCoordinateStep_iterate_eq_zero_iff: rewrite with T1,
  then `mul_eq_zero` + `pow_ne_zero _ hmult` (the `mult^n` factor is nonzero).
- T7 packetCoordinateStep_iterate_support_eq: `Set.ext k`,
  `Function.mem_support`, then T6 with `hmult k` (contrapositive of the iff).
Certification: T1/T2/T5 take NO α ≠ 0; T3/T4 keep it; T6/T7 use multiplier
nonvanishing, not α ≠ 0; order `n + m` preserved in T4. If a target cannot
close, omit it and report its exact name; never weaken a statement.
-/
import RequestProject.IFFTCoordinateBridge

open scoped BigOperators

namespace ResidueSlices

theorem packetSpectrum_packetCoordinateStep_iterate
    {g : ℕ} [NeZero g]
    (alpha : ℝ) (C : ZMod g → ℂ) (n : ℕ) (k : ZMod g) :
    packetSpectrum alpha (((packetCoordinateStep alpha)^[n]) C) k =
      packetSpectrum alpha C k *
        (1 + (alpha : ℂ) * ZMod.stdAddChar k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply,
        packetSpectrum_packetCoordinateStep, ih, pow_succ, mul_assoc]

theorem evolvedPreparedPacket_zero
    {g : ℕ} [NeZero g]
    (alpha : ℝ) (V : ZMod g → ℂ) :
    evolvedPreparedPacket alpha V 0 = preparedPacket alpha V := by
  rw [evolvedPreparedPacket, packetSpectralFlow_zero]

theorem evolvedPreparedPacket_eq_packetCoordinateStep_iterate
    {g : ℕ} [NeZero g]
    {alpha : ℝ} (halpha : alpha ≠ 0) (V : ZMod g → ℂ) (n : ℕ) :
    evolvedPreparedPacket alpha V n =
      ((packetCoordinateStep alpha)^[n]) (preparedPacket alpha V) := by
  induction n with
  | zero => rw [evolvedPreparedPacket_zero, Function.iterate_zero_apply]
  | succ n ih =>
      rw [evolvedPreparedPacket_succ_eq_packetCoordinateStep halpha, ih,
        Function.iterate_succ', Function.comp_apply]

theorem packetCoordinateStep_iterate_evolvedPreparedPacket
    {g : ℕ} [NeZero g]
    {alpha : ℝ} (halpha : alpha ≠ 0) (V : ZMod g → ℂ) (m n : ℕ) :
    ((packetCoordinateStep alpha)^[m])
        (evolvedPreparedPacket alpha V n) =
      evolvedPreparedPacket alpha V (n + m) := by
  rw [evolvedPreparedPacket_eq_packetCoordinateStep_iterate halpha,
    evolvedPreparedPacket_eq_packetCoordinateStep_iterate halpha,
    ← Function.iterate_add_apply, Nat.add_comm m n]

theorem packetCoordinateStep_iterate_no_spectral_leakage
    {g : ℕ} [NeZero g]
    (alpha : ℝ) (C : ZMod g → ℂ) (S : Set (ZMod g))
    (hC : ∀ k, k ∉ S → packetSpectrum alpha C k = 0) :
    ∀ n k, k ∉ S →
      packetSpectrum alpha (((packetCoordinateStep alpha)^[n]) C) k = 0 := by
  intro n k hk
  rw [packetSpectrum_packetCoordinateStep_iterate, hC k hk, zero_mul]

theorem packetSpectrum_packetCoordinateStep_iterate_eq_zero_iff
    {g : ℕ} [NeZero g]
    (alpha : ℝ) (C : ZMod g → ℂ) (n : ℕ) (k : ZMod g)
    (hmult : 1 + (alpha : ℂ) * ZMod.stdAddChar k ≠ 0) :
    packetSpectrum alpha (((packetCoordinateStep alpha)^[n]) C) k = 0 ↔
      packetSpectrum alpha C k = 0 := by
  rw [packetSpectrum_packetCoordinateStep_iterate, mul_eq_zero,
    or_iff_left (pow_ne_zero n hmult)]

theorem packetCoordinateStep_iterate_support_eq
    {g : ℕ} [NeZero g]
    (alpha : ℝ) (C : ZMod g → ℂ) (n : ℕ)
    (hmult : ∀ k : ZMod g,
      1 + (alpha : ℂ) * ZMod.stdAddChar k ≠ 0) :
    Function.support
        (packetSpectrum alpha (((packetCoordinateStep alpha)^[n]) C)) =
      Function.support (packetSpectrum alpha C) := by
  ext k
  simp only [Function.mem_support, ne_eq]
  rw [packetSpectrum_packetCoordinateStep_iterate_eq_zero_iff alpha C n k (hmult k)]

end ResidueSlices
