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

Certification scope: every target is an active declaration; do not weaken
(no `r < g`, no `2 ≤ g`, DFT sign unchanged);
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

lemma forwardDiffCoeff_succ_mul_index (r j : Nat) :
    (j + 1 : Int) * forwardDiffCoeff (r + 1) (j + 1) =
      (r + 1 : Int) * forwardDiffCoeff r j := by
  unfold forwardDiffCoeff
  simp only [Nat.add_sub_add_right]
  have key : (j + 1) * Nat.choose (r + 1) (j + 1) = (r + 1) * Nat.choose r j := by
    rw [mul_comm]
    exact (Nat.add_one_mul_choose_eq r j).symm
  have key' : ((j + 1 : Nat) : Int) * ((r + 1).choose (j + 1) : Int) =
              ((r + 1 : Nat) : Int) * (r.choose j : Int) := by norm_cast
  rw [show (↑j + 1 : Int) = ((j + 1 : Nat) : Int) by norm_cast]
  rw [show (↑r + 1 : Int) = ((r + 1 : Nat) : Int) by norm_cast]
  rw [mul_comm ((-1 : Int) ^ (r - j)) _, mul_comm ((-1 : Int) ^ (r - j)) _]
  rw [← mul_assoc, ← mul_assoc]
  rw [key']

lemma forwardDiff_moment_zero (r : Nat) :
    Finset.sum (Finset.range (r + 1)) (fun j =>
      forwardDiffCoeff r j * (j : Int) ^ 0) =
      if r = 0 then 1 else 0 := by
  have h := forwardDiff_binomial_symbol r 1
  simp at h
  have key : (∑ j ∈ Finset.range (r + 1), forwardDiffCoeff r j * (j : Int) ^ 0 : Int) =
      ∑ j ∈ Finset.range (r + 1), forwardDiffCoeff r j := by
    simp [mul_one]
  rw [key]
  split_ifs with hr
  · simp [hr] at h ⊢
    exact h
  · rw [zero_pow hr] at h
    exact_mod_cast h

lemma forwardDiff_moment_succ_shift (r m : Nat) :
    Finset.sum (Finset.range (r + 2)) (fun j =>
      forwardDiffCoeff (r + 1) j * (j : Int) ^ (m + 1)) =
      (r + 1 : Int) * Finset.sum (Finset.range (r + 1)) (fun j =>
        forwardDiffCoeff r j * (j + 1 : Int) ^ m) := by
  -- Split off j = 0 term (which is 0) and reindex
  have h0 : forwardDiffCoeff (r + 1) 0 * ((0 : Nat) : Int) ^ (m + 1) = 0 := by
    simp [zero_pow (Nat.succ_ne_zero m)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr (Nat.zero_lt_succ (r + 1))), h0, add_zero]
  have hreindex : (Finset.range (r + 2)).erase 0 = Finset.image (fun k => k + 1) (Finset.range (r + 1)) := by
    ext x
    simp [Finset.mem_erase, Finset.mem_range, Finset.mem_image]
    constructor
    · intro ⟨hx_pos, hx_bound⟩
      exact ⟨x - 1, by omega, by omega⟩
    · intro ⟨y, hy_bound, hy_eq⟩
      rw [← hy_eq]
      constructor <;> omega
  rw [hreindex, Finset.sum_image (by intro a _ b _ h; simp at h; exact h)]
  have hterm : ∀ j : Nat, forwardDiffCoeff (r + 1) (j + 1) * ((j + 1 : Nat) : Int) ^ (m + 1) =
               (r + 1 : Int) * (forwardDiffCoeff r j * ((j + 1 : Nat) : Int) ^ m) := by
    intro j
    have h := forwardDiffCoeff_succ_mul_index r j
    rw [show ((j + 1 : Nat) : Int) = (j : Int) + 1 by simp]
    calc forwardDiffCoeff (r + 1) (j + 1) * ((j : Int) + 1) ^ (m + 1)
        = forwardDiffCoeff (r + 1) (j + 1) * ((j : Int) + 1)^m * ((j : Int) + 1) := by ring
      _ = ((j : Int) + 1) * forwardDiffCoeff (r + 1) (j + 1) * ((j : Int) + 1)^m := by ring
      _ = (r + 1 : Int) * forwardDiffCoeff r j * ((j : Int) + 1)^m := by rw [h]
      _ = (r + 1 : Int) * (forwardDiffCoeff r j * ((j : Int) + 1)^m) := by ring
  simp_rw [hterm]
  rw [Finset.mul_sum]
  simp [Nat.cast_add]

lemma forwardDiff_moment_shift_eq_add (r m : Nat) :
    Finset.sum (Finset.range (r + 1)) (fun j =>
        forwardDiffCoeff r j * (j + 1 : Int) ^ m) =
      Finset.sum (Finset.range (r + 2)) (fun j =>
          forwardDiffCoeff (r + 1) j * (j : Int) ^ m) +
        Finset.sum (Finset.range (r + 1)) (fun j =>
          forwardDiffCoeff r j * (j : Int) ^ m) := by
  have h : ∀ j : ℕ, forwardDiffCoeff r j * ((j + 1 : Int) ^ m) =
           forwardDiffCoeff r j * (j : Int) ^ m +
           forwardDiffCoeff r j * (((j + 1 : Int) ^ m) - (j : Int) ^ m) := by
    intro j; ring
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  -- Goal: sum_c + sum_diff = sum_diff' + sum_c
  -- Need: sum_diff = sum_diff'
  have cancel : ∑ x ∈ Finset.range (r + 1), forwardDiffCoeff r x * (x : ℤ) ^ m +
                ∑ x ∈ Finset.range (r + 1), forwardDiffCoeff r x * (((x + 1) : ℤ) ^ m - (x : ℤ) ^ m) =
                ∑ j ∈ Finset.range (r + 2), forwardDiffCoeff (r + 1) j * (j : ℤ) ^ m +
                ∑ j ∈ Finset.range (r + 1), forwardDiffCoeff r j * (j : ℤ) ^ m ↔
                ∑ x ∈ Finset.range (r + 1), forwardDiffCoeff r x * (((x + 1) : ℤ) ^ m - (x : ℤ) ^ m) =
                ∑ j ∈ Finset.range (r + 2), forwardDiffCoeff (r + 1) j * (j : ℤ) ^ m := by
    constructor <;> intro h <;> linarith
  rw [cancel]
  -- Need: ∑_{x=0}^{r} forwardDiffCoeff(r,x) * ((x+1)^m - x^m) = ∑_{j=0}^{r+1} forwardDiffCoeff(r+1,j) * j^m
  unfold forwardDiffCoeff
  -- Distribute multiplication
  have dist : ∀ x : ℕ, (-1 : ℤ) ^ (r - x) * ↑(r.choose x) * ((↑x + 1) ^ m - ↑x ^ m) =
              (-1 : ℤ) ^ (r - x) * ↑(r.choose x) * (↑x + 1) ^ m -
              (-1 : ℤ) ^ (r - x) * ↑(r.choose x) * ↑x ^ m := by
    intro x; ring
  rw [Finset.sum_congr rfl (fun x _ => dist x)]
  rw [Finset.sum_sub_distrib]
  -- We need to prove:
  -- ∑_{x=0}^{r} (-1)^{r-x} * C(r,x) * (x+1)^m - ∑_{x=0}^{r} (-1)^{r-x} * C(r,x) * x^m = ∑_{j=0}^{r+1} (-1)^{r+1-j} * C(r+1,j) * j^m
  -- Use the binomial identity: C(r+1,j) = C(r,j) + C(r,j-1)
  have binom_id : ∀ j : ℕ, ((r + 1).choose j : ℤ) = (r.choose j : ℤ) + (if j > 0 then r.choose (j - 1) else 0) := by
    intro j
    cases j with
    | zero => simp [Nat.choose_zero_right]
    | succ j => simp [Nat.choose_succ_succ]; ring
  -- Rewrite RHS using binom_id
  have rhs_cong : ∀ j ∈ Finset.range (r + 2),
      (-1 : ℤ) ^ (r + 1 - j) * ↑((r + 1).choose j) * ↑j ^ m =
      (-1 : ℤ) ^ (r + 1 - j) * (↑(r.choose j) + ↑(if j > 0 then r.choose (j - 1) else 0)) * ↑j ^ m := by
    intro j _; rw [binom_id j]
  rw [Finset.sum_congr rfl rhs_cong]
  -- Now split the sum using (a + b) * c = a*c + b*c
  have split_sum : ∀ x ∈ Finset.range (r + 2),
      (-1 : ℤ) ^ (r + 1 - x) * (↑(r.choose x) + ↑(if x > 0 then r.choose (x - 1) else 0)) * ↑x ^ m =
      (-1 : ℤ) ^ (r + 1 - x) * ↑(r.choose x) * ↑x ^ m +
      (-1 : ℤ) ^ (r + 1 - x) * ↑(if x > 0 then r.choose (x - 1) else 0) * ↑x ^ m := by
    intro x _; ring
  rw [Finset.sum_congr rfl split_sum]
  rw [Finset.sum_add_distrib]
  -- First RHS sum: extend to r+2 but C(r, r+1) = 0
  have sum1_eq : ∑ x ∈ Finset.range (r + 2), (-1 : ℤ) ^ (r + 1 - x) * ↑(r.choose x) * ↑x ^ m =
                 ∑ x ∈ Finset.range (r + 1), (-1 : ℤ) ^ (r + 1 - x) * ↑(r.choose x) * ↑x ^ m := by
    rw [Finset.sum_range_succ]
    simp
  rw [sum1_eq]
  -- Second RHS sum: reindex x → k+1
  have sum2_eq : ∑ x ∈ Finset.range (r + 2), (-1 : ℤ) ^ (r + 1 - x) * ↑(if x > 0 then r.choose (x - 1) else 0) * ↑x ^ m =
                 ∑ k ∈ Finset.range (r + 1), (-1 : ℤ) ^ (r - k) * ↑(r.choose k) * ↑(k + 1) ^ m := by
    rw [Finset.sum_range_succ']
    simp [Nat.succ_sub_succ_eq_sub]
  rw [sum2_eq]
  -- Note: (-1)^{r+1-x} = -(-1)^{r-x}
  have sign_flip : ∀ x : ℕ, x ≤ r → (-1 : ℤ) ^ (r + 1 - x) = -(-1) ^ (r - x) := by
    intro x hx
    have : r + 1 - x = r - x + 1 := by omega
    rw [this, pow_succ]
    ring
  have sum1_flip : ∑ x ∈ Finset.range (r + 1), (-1 : ℤ) ^ (r + 1 - x) * ↑(r.choose x) * ↑x ^ m =
                   -∑ x ∈ Finset.range (r + 1), (-1 : ℤ) ^ (r - x) * ↑(r.choose x) * ↑x ^ m := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [sign_flip x (Finset.mem_range_succ_iff.mp hx)]
    ring
  rw [sum1_flip]
  -- Goal: ∑ (x+1)^m term - ∑ x^m term = -∑ x^m term + ∑ (k+1)^m term
  rw [sub_eq_iff_eq_add]
  rw [add_comm]
  rw [add_right_comm]
  simp [add_comm]

lemma forwardDiff_moment_succ_recurrence (r m : Nat) :
    Finset.sum (Finset.range (r + 2)) (fun j =>
      forwardDiffCoeff (r + 1) j * (j : Int) ^ (m + 1)) =
      (r + 1 : Int) *
        (Finset.sum (Finset.range (r + 2)) (fun j =>
            forwardDiffCoeff (r + 1) j * (j : Int) ^ m) +
          Finset.sum (Finset.range (r + 1)) (fun j =>
            forwardDiffCoeff r j * (j : Int) ^ m)) := by
  rw [forwardDiff_moment_succ_shift, forwardDiff_moment_shift_eq_add]

/-- Target 7: exact moment formula through Stirling numbers. -/
theorem forwardDiff_moment_eq_factorial_mul_stirlingSecond
    (r m : Nat) :
    Finset.sum (Finset.range (r + 1)) (fun j =>
      forwardDiffCoeff r j * (j : Int) ^ m) =
      (Nat.factorial r : Int) * (Nat.stirlingSecond m r : Int) := by
  induction m generalizing r with
  | zero =>
    rw [forwardDiff_moment_zero]
    split_ifs with hr
    · subst hr; simp [Nat.stirlingSecond]
    · cases r with
      | zero => contradiction
      | succ r => simp [Nat.stirlingSecond]
  | succ m ih =>
    induction r with
    | zero =>
      simp [zero_pow (Nat.succ_ne_zero m)]
    | succ r ih' =>
      rw [forwardDiff_moment_succ_recurrence]
      rw [ih (r + 1), ih r]
      rw [Nat.stirlingSecond_succ_succ]
      rw [show (r + 1).factorial = (r + 1) * r.factorial from rfl]
      push_cast
      ring

/-- Target 8: lower-moment annihilation. -/
theorem forwardDiff_moment_vanish {r m : Nat} (hm : m < r) :
    Finset.sum (Finset.range (r + 1)) (fun j =>
      forwardDiffCoeff r j * (j : Int) ^ m) = 0 := by
  rw [forwardDiff_moment_eq_factorial_mul_stirlingSecond]
  rw [Nat.stirlingSecond_eq_zero_of_lt hm]
  simp

/-- Target 9: normalized top moment. -/
theorem forwardDiff_top_moment (r : Nat) :
    Finset.sum (Finset.range (r + 1)) (fun j =>
      forwardDiffCoeff r j * (j : Int) ^ r) =
      (Nat.factorial r : Int) := by
  rw [forwardDiff_moment_eq_factorial_mul_stirlingSecond]
  rw [Nat.stirlingSecond_self]
  simp

/-
Targets 1-9 are all active and certified here: the exact Fourier/high-pass
core (1-6), the Stirling moment identity `∑_j c(r,j)·j^m = r!·S(m,r)` (7),
and its corollaries — lower-moment annihilation for `m < r` (8) and the
normalized top moment `= r!` at `m = r` (9).
-/

end ResidueSlices
