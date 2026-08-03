/-
IFFT-prepared spectral support under packet flow. The exact channel evolution
`F_n(α·ζ^k) = V_k·(1 + α·ζ^k)^n` keeps an initially zero channel zero, so a
spectrum supported in `S` stays supported in `S` (containment — an evolution
factor may vanish and shrink support, but no new nonzero channel appears).
Finite algebra over `IFFTPreparation`. This module does NOT formalize the
coordinate recurrence `C_{0,n+1}=C_{0,n}+x·C_{g-1,n}`, `C_{j,n+1}=C_{j-1,n}+
C_{j,n}` — that bridge is a separate later target.

Proof routes: 1 `pow_zero`; 2 `pow_succ`; 3 `0 * _ = 0`; 4 Target 3
off-support; 5 `packetSpectrum_preparedPacket` at `packetSpectralFlow α V n`
(needs `α ≠ 0`); 6 Target 5 + Target 2; 7 Target 5 + Target 4.

Certification scope: every target below is an active declaration; keep the
multiplier exactly `1 + (α:ℂ)·stdAddChar k`; Targets 1–4 take no `α ≠ 0`,
Targets 5–7 keep it (scaled reconstruction needs it); `S` arbitrary; no
nonvanishing/positivity/symmetry hypothesis. If a target cannot be closed,
omit it and report it explicitly.
-/
import RequestProject.IFFTPreparation

open scoped BigOperators

namespace ResidueSlices

/-- Exact channel evolution of a spectrum: `V_k · (1 + α·ζ^k)^n`. -/
noncomputable def packetSpectralFlow {g : ℕ} [NeZero g]
    (α : ℝ) (V : ZMod g → ℂ) (n : ℕ) : ZMod g → ℂ :=
  fun k => V k * (1 + (α : ℂ) * ZMod.stdAddChar k) ^ n

/-- The prepared packet whose spectrum has flowed for `n` steps. -/
noncomputable def evolvedPreparedPacket {g : ℕ} [NeZero g]
    (α : ℝ) (V : ZMod g → ℂ) (n : ℕ) : ZMod g → ℂ :=
  preparedPacket α (packetSpectralFlow α V n)

/-- Target 1: time-zero spectral state. -/
theorem packetSpectralFlow_zero {g : ℕ} [NeZero g]
    (α : ℝ) (V : ZMod g → ℂ) :
    packetSpectralFlow α V 0 = V := by
  funext k
  simp [packetSpectralFlow]

/-- Target 2: exact one-step channel recurrence. -/
theorem packetSpectralFlow_succ {g : ℕ} [NeZero g]
    (α : ℝ) (V : ZMod g → ℂ) (n : ℕ) (k : ZMod g) :
    packetSpectralFlow α V (n + 1) k =
      packetSpectralFlow α V n k *
        (1 + (α : ℂ) * ZMod.stdAddChar k) := by
  simp [packetSpectralFlow, pow_succ, mul_assoc]

/-- Target 3: a zero initial channel remains zero. -/
theorem packetSpectralFlow_zero_of_initial_zero {g : ℕ} [NeZero g]
    (α : ℝ) (V : ZMod g → ℂ) (n : ℕ) {k : ZMod g} (hV : V k = 0) :
    packetSpectralFlow α V n k = 0 := by
  simp [packetSpectralFlow, hV]

/-- Target 4: support containment for every time. -/
theorem packetSpectralFlow_supported {g : ℕ} [NeZero g]
    (α : ℝ) (V : ZMod g → ℂ) (S : Set (ZMod g))
    (hV : ∀ k, k ∉ S → V k = 0) :
    ∀ n k, k ∉ S → packetSpectralFlow α V n k = 0 := by
  intro n k hk
  exact packetSpectralFlow_zero_of_initial_zero α V n (hV k hk)

/-- Target 5: exact IFFT reconstruction of the evolved spectrum. -/
theorem packetSpectrum_evolvedPreparedPacket {g : ℕ} [NeZero g]
    {α : ℝ} (hα : α ≠ 0) (V : ZMod g → ℂ) (n : ℕ) :
    packetSpectrum α (evolvedPreparedPacket α V n) =
      packetSpectralFlow α V n := by
  exact packetSpectrum_preparedPacket hα (packetSpectralFlow α V n)

/-- Target 6: the reconstructed packet realizes the exact channel recurrence. -/
theorem packetSpectrum_evolvedPreparedPacket_succ {g : ℕ} [NeZero g]
    {α : ℝ} (hα : α ≠ 0) (V : ZMod g → ℂ) (n : ℕ) (k : ZMod g) :
    packetSpectrum α (evolvedPreparedPacket α V (n + 1)) k =
      packetSpectrum α (evolvedPreparedPacket α V n) k *
        (1 + (α : ℂ) * ZMod.stdAddChar k) := by
  rw [packetSpectrum_evolvedPreparedPacket hα V (n + 1),
    packetSpectrum_evolvedPreparedPacket hα V n]
  exact packetSpectralFlow_succ α V n k

/-- Target 7: no spectral leakage at any time. -/
theorem evolvedPreparedPacket_no_spectral_leakage {g : ℕ} [NeZero g]
    {α : ℝ} (hα : α ≠ 0) (V : ZMod g → ℂ) (S : Set (ZMod g))
    (hV : ∀ k, k ∉ S → V k = 0) :
    ∀ n k, k ∉ S →
      packetSpectrum α (evolvedPreparedPacket α V n) k = 0 := by
  intro n k hk
  rw [packetSpectrum_evolvedPreparedPacket hα V n]
  exact packetSpectralFlow_supported α V S hV n k hk

end ResidueSlices
