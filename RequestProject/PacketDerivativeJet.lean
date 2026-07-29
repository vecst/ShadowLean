/-
Exact residue-packet derivative-jet algebra. Order-r forward differences of a
packet `M : ZMod g → ℂ`, their exact `(z-1)^r` Fourier symbol, the DFT
reconstruction (with the zero channel annihilated for `r > 0`), the moving-
packet bridge, and the Stirling moment identities. All exact finite algebra —
no asymptotics. Reuses Mathlib `ZMod.dft`/`ZMod.stdAddChar` and
`Nat.stirlingSecond`.

Proof routes:
- Target 1: binomial theorem, `(z-1)^r = ∑_j C(r,j) z^j (-1)^(r-j)`; forwardDiffCoeff
  is Int before coercion; `r = 0` gives `1 = 1`.
- Target 2: `stdAddChar (ell * j) = (stdAddChar ell)^j` via `map_nsmul_eq_pow`
  (`j • ell`), then Target 1 at `z = stdAddChar ell`. No `r < g` needed.
- Target 3: Fourier inversion (`dft.symm (dft M) = M`, `invDFT_apply`, positive
  character `stdAddChar (ell*j)`), swap the `j`/`ell` sums, apply Target 2;
  normalization `/(g:ℂ)`.
- Target 4: Target 2 + `stdAddChar 0 = 1` gives `(1-1)^r = 0` for `r > 0` (not `r=0`).
- Target 5: Target 3, split `univ = {0} ∪ univ.erase 0`, Target 4 kills the `0`
  term; `g=1` ⇒ erased sum empty, both sides `0`.
- Target 6: unfold forwardDiffPacket/movingPacketMass, distribute, Fubini the
  `j`/`q` sums, normalize `ZMod` addition.
- Target 7: `Δ^r(x^m)(0) = r!·S(m,r)` — induction via Pascal + the
  `stirlingSecond` recurrence; do not introduce a second Stirling definition.
- Target 8: Target 7 + `stirlingSecond_eq_zero_of_lt`.
- Target 9: Target 7 + `stirlingSecond_self`.

Honesty: no sorry/admit/unsafe/implemented_by/new axioms; every target an
active declaration; do not weaken (no `r < g`, no `2 ≤ g`, DFT sign unchanged);
if a target cannot be closed, omit it and report it explicitly.
-/
import RequestProject.PacketHighPass
import Mathlib.Combinatorics.Enumerative.Stirling

open scoped BigOperators

namespace ResidueSlices

def forwardDiffCoeff (r j : Nat) : Int :=
  (-1 : Int) ^ (r - j) * (Nat.choose r j : Int)

noncomputable def forwardDiffPacket {g : Nat} [NeZero g]
    (r : Nat) (M : ZMod g -> Complex) : Complex :=
  Finset.sum (Finset.range (r + 1)) (fun j =>
    (forwardDiffCoeff r j : Complex) * M (j : ZMod g))

noncomputable def forwardDiffSymbol {g : Nat} [NeZero g]
    (r : Nat) (ell : ZMod g) : Complex :=
  Finset.sum (Finset.range (r + 1)) (fun j =>
    (forwardDiffCoeff r j : Complex) *
      (ZMod.stdAddChar (ell * (j : ZMod g)) : Complex))

/-- Target 1: exact binomial symbol. -/
theorem forwardDiff_binomial_symbol (r : Nat) (z : Complex) :
    Finset.sum (Finset.range (r + 1)) (fun j =>
      (forwardDiffCoeff r j : Complex) * z ^ j) =
      (z - 1) ^ r := by
  simp [forwardDiffCoeff, sub_eq_add_neg]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Target 2: exact packet Fourier symbol. -/
theorem forwardDiffSymbol_eq_pow {g : Nat} [NeZero g]
    (r : Nat) (ell : ZMod g) :
    forwardDiffSymbol r ell =
      ((ZMod.stdAddChar ell : Complex) - 1) ^ r := by
  unfold forwardDiffSymbol forwardDiffCoeff
  rw [Finset.sum_congr rfl]
  · exact forwardDiff_binomial_symbol r (ZMod.stdAddChar ell)
  · intro x _
    rw [mul_comm ell _, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    simp [forwardDiffCoeff]

/-- Target 3: exact DFT reconstruction of the derivative packet. -/
theorem forwardDiffPacket_eq_dft_sum {g : Nat} [NeZero g]
    (r : Nat) (M : ZMod g -> Complex) :
    forwardDiffPacket r M =
      (Finset.sum Finset.univ (fun ell : ZMod g =>
        ((ZMod.stdAddChar ell : Complex) - 1) ^ r *
          ZMod.dft M ell)) / (g : Complex) := by
  unfold forwardDiffPacket
  -- M = dft.symm (dft M), so M j = g⁻¹ * ∑ ell, (dft M ell) * stdAddChar(-(ell * j))
  have hInvDFT : ∀ j : ZMod g, M j = (g : ℂ)⁻¹ * ∑ ell : ZMod g, ZMod.dft M ell * ZMod.stdAddChar (ell * j) := by
    intro j
    have hM : ZMod.dft.symm (ZMod.dft M) = M := ZMod.dft.leftInverse_symm M
    have := ZMod.invDFT_apply (ZMod.dft M) j
    simp only [smul_eq_mul] at this
    rw [hM] at this
    rw [this]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_comm x j, mul_comm]
  -- Substitute M j using hInvDFT
  simp_rw [hInvDFT]
  -- Goal: ∑ x, coeff * (g⁻¹ * ∑ ell, dft M ell * stdAddChar (ell * x)) = (∑ ell, (stdAddChar ell - 1)^r * dft M ell) / g
  -- Pull out g⁻¹ using Finset.mul_sum
  have h1 : ∀ x : ℕ, ↑(forwardDiffCoeff r x) * ((↑g : ℂ)⁻¹ * ∑ ell : ZMod g, ZMod.dft M ell * ZMod.stdAddChar (ell * ((x : ℕ) : ZMod g))) =
            (↑g : ℂ)⁻¹ * (↑(forwardDiffCoeff r x) * ∑ ell : ZMod g, ZMod.dft M ell * ZMod.stdAddChar (ell * ((x : ℕ) : ZMod g))) := by
    intro x; ring
  simp_rw [h1]
  simp_rw [← Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_div]
  rw [Finset.sum_comm]
  -- Now: ∑ y, ∑ x, g⁻¹ * (coeff * (dft M y * stdAddChar (y * x))) = ∑ i, (stdAddChar i - 1)^r * dft M i / g
  -- Pull out g⁻¹ from inner sum
  simp_rw [← Finset.mul_sum]
  -- Now need: g⁻¹ * ∑ y, ∑ x, coeff * (dft M y * stdAddChar (y * x)) = ∑ i, (stdAddChar i - 1)^r * dft M i / g
  -- We have stdAddChar (y * x) = (stdAddChar y)^x
  have hchar : ∀ y : ZMod g, ∀ x : ℕ, ZMod.stdAddChar (y * (x : ZMod g)) = (ZMod.stdAddChar y) ^ x := by
    intro y x
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    simp [mul_comm]
  -- Rewrite stdAddChar using hchar
  simp_rw [hchar]
  -- Apply forwardDiff_binomial_symbol
  have hbinom := forwardDiff_binomial_symbol r
  -- The goal is:
  -- g⁻¹ * ∑ x, ∑ i, coeff * (dft M x * stdAddChar x ^ i) = ∑ i, (stdAddChar i - 1)^r * dft M i / g
  -- First pull out dft M x from each inner sum
  -- Rearrange each term: coeff * (dft M x * stdAddChar x ^ i) = dft M x * (coeff * stdAddChar x ^ i)
  have hrearr : ∀ x : ZMod g, ∀ i : ℕ, ↑(forwardDiffCoeff r i) * (ZMod.dft M x * ZMod.stdAddChar x ^ i) =
                ZMod.dft M x * (↑(forwardDiffCoeff r i) * ZMod.stdAddChar x ^ i) := by
    intro x i; ring
  simp_rw [hrearr]
  simp_rw [← Finset.mul_sum]
  -- Now: g⁻¹ * ∑ x, dft M x * ∑ i, coeff * stdAddChar x ^ i = ∑ i, (stdAddChar i - 1)^r * dft M i / g
  -- Apply hbinom
  simp_rw [hbinom]
  -- Goal: g⁻¹ * ∑ x, dft M x * (stdAddChar x - 1)^r = ∑ i, (stdAddChar i - 1)^r * dft M i / g
  rw [mul_comm, ← div_eq_mul_inv, ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Target 4: exact zero-frequency annihilation for positive order. -/
theorem forwardDiffSymbol_zero {g : Nat} [NeZero g]
    {r : Nat} (hr : 0 < r) :
    forwardDiffSymbol r (0 : ZMod g) = 0 := by
  rw [forwardDiffSymbol_eq_pow]
  simp [hr.ne']

/-- Target 5: DFT reconstruction with the zero channel removed. -/
theorem forwardDiffPacket_eq_dft_sum_erase_zero
    {g : Nat} [NeZero g] {r : Nat} (hr : 0 < r)
    (M : ZMod g -> Complex) :
    forwardDiffPacket r M =
      (Finset.sum (Finset.univ.erase (0 : ZMod g))
        (fun ell : ZMod g =>
          ((ZMod.stdAddChar ell : Complex) - 1) ^ r *
            ZMod.dft M ell)) / (g : Complex) := by
  rw [forwardDiffPacket_eq_dft_sum]
  have key : ((ZMod.stdAddChar (0 : ZMod g) : Complex) - 1) ^ r * ZMod.dft M 0 = 0 := by
    have := @forwardDiffSymbol_zero g _ r hr
    rw [← @forwardDiffSymbol_eq_pow g _ r 0]
    simp [this]
  have h2 : ∑ x : ZMod g, (ZMod.stdAddChar x - 1) ^ r * ZMod.dft M x =
    ∑ x ∈ Finset.univ.erase 0, (ZMod.stdAddChar x - 1) ^ r * ZMod.dft M x +
    ((ZMod.stdAddChar (0 : ZMod g) : Complex) - 1) ^ r * ZMod.dft M 0 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod g))]
  rw [h2, key, add_zero]

/-- Target 6: bridge to arbitrary moving packet masses. -/
theorem forwardDiffPacket_movingPacketMass {g : Nat} [NeZero g]
    {iota : Type*} [Fintype iota]
    (r : Nat) (b : iota -> ZMod g -> Complex)
    (a : iota -> ZMod g) :
    forwardDiffPacket r (movingPacketMass b a) =
      Finset.sum Finset.univ (fun q =>
        Finset.sum (Finset.range (r + 1)) (fun j =>
          (forwardDiffCoeff r j : Complex) *
            b q (a q + (j : ZMod g)))) := by
  unfold forwardDiffPacket movingPacketMass
  simp_rw [Finset.mul_sum]
  apply Finset.sum_comm

/-
Targets 7-9 (the Stirling moment identities `forwardDiff_moment_*`) are NOT
included: the run that produced this module was budget-limited before the
`stirlingSecond` induction (Target 7) closed, and Targets 8-9 are its
corollaries. They are deferred to a follow-up run. Only the six exact
Fourier/high-pass core theorems above are certified here.
-/

end ResidueSlices
