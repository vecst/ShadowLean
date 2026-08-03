/-
Nonzero-frequency divided high-pass bounds. At `ℓ ≠ 0` the character factor
`‖χ(ℓ)−1‖` is strictly positive (via `ZMod.injective_stdAddChar` and
`χ(0) = 1`), so the exact product-form bounds of `PacketHighPass.lean` divide
into clean `‖DFT‖ ≤ variation / ‖χ(ℓ)−1‖` estimates. Finite cyclic Fourier
algebra only — no asymptotics.

Proof routes:
- Target 1: `stdAddChar` injective + `stdAddChar 0 = 1` ⟹ `χ(ℓ) ≠ 1` ⟹
  `χ(ℓ) − 1 ≠ 0` ⟹ `0 < ‖χ(ℓ)−1‖`. Vacuously fine at `g = 1` (`ℓ ≠ 0`
  impossible), no `2 ≤ g` needed.
- Target 2: `dft_norm_mul_le_cyclicVariation` + Target 1 via `le_div_iff₀`
  (positive-denominator division). Keep the denominator exactly as displayed.
- Target 3: `movingPacket_dft_highpass_bound` + Target 1, same division.
  Selector `a` arbitrary; no positivity/regularity on the blocks `b`.

Certification scope: every target below is an active declaration; keep the
`ℓ ≠ 0` hypothesis (no divided theorem at `ℓ = 0`); keep the denominator
exactly `‖χ(ℓ)−1‖` (do not replace by an unspecified constant or `2 sin(π/g)`);
the product-form theorems in `PacketHighPass.lean` stay unchanged. If a target
cannot be closed, omit it and report it explicitly.
-/
import RequestProject.PacketHighPass

open scoped BigOperators

namespace ResidueSlices

/-- Target 1: the character factor is strictly positive at a nonzero
frequency. -/
theorem stdAddChar_sub_one_norm_pos {g : ℕ} [NeZero g]
    {ell : ZMod g} (hell : ell ≠ 0) :
    0 < ‖(ZMod.stdAddChar ell : ℂ) - 1‖ := by
  rw [norm_pos_iff, sub_ne_zero]
  intro h
  have h' : ZMod.stdAddChar ell = ZMod.stdAddChar (0 : ZMod g) := by
    simpa using h
  exact hell (ZMod.injective_stdAddChar h')

/-- Target 2: divided one-block high-pass bound. -/
theorem dft_norm_le_cyclicVariation_div {g : ℕ} [NeZero g]
    (f : ZMod g → ℂ) {ell : ZMod g} (hell : ell ≠ 0) :
    ‖ZMod.dft f ell‖ ≤
      cyclicVariation f / ‖(ZMod.stdAddChar ell : ℂ) - 1‖ := by
  apply (le_div_iff₀ (stdAddChar_sub_one_norm_pos hell)).2
  rw [mul_comm]
  exact dft_norm_mul_le_cyclicVariation f ell

/-- Target 3: divided moving-packet high-pass bound. -/
theorem movingPacket_dft_divided_bound {g : ℕ} [NeZero g]
    {iota : Type*} [Fintype iota]
    (b : iota → ZMod g → ℂ) (a : iota → ZMod g)
    {ell : ZMod g} (hell : ell ≠ 0) :
    ‖ZMod.dft (movingPacketMass b a) ell‖ ≤
      (∑ q, cyclicVariation (b q)) /
        ‖(ZMod.stdAddChar ell : ℂ) - 1‖ := by
  apply (le_div_iff₀ (stdAddChar_sub_one_norm_pos hell)).2
  rw [mul_comm]
  exact movingPacket_dft_highpass_bound b a ell

end ResidueSlices
