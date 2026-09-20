/-
Non-archimedean channel rigidity for residue packets.

Context. `RequestProject.BirootChannels` proves the archimedean half of the
channel story: the slice ratio `polySlice P g k x / polySlice P g 0 x` converges
to the reciprocal power of the DOMINANT roots-of-unity channel, and for
nonnegative weights dominance is a phase-separation condition.  The channels of
the Pascal row `(1+X)^N` at `x = y^g` are

    c_l = 1 + ζ^l y,   ζ a primitive g-th root of unity,

and over the reals with `y > 0` the channel `c_0` dominates, which is what makes
the modular slice ratio theorem work.

This file asks the same dominance question at a NON-ARCHIMEDEAN place, i.e. with
channel size measured by a valuation `v` of residue characteristic `p`.  The
answer is rigid: a strictly dominant channel exists only for `g = 2`.  This is
Section 1 of `Research/cartier_padic_slice_ratio_note.md` in the Shadow
repository.

Numerical evidence (PARI, exact): over `g = 2..6` and 90 values of `x`, at every
place above the primes dividing `g`, `x`, the channel product and 2, 3, 5, 7,
11, 13, a unique dominant channel occurs 128 times for `g = 2` and 0 times out
of about 2,400 places for `g >= 3`.

The five Goals are stated for a general valuation, so they cover every finite
place of every number field at once; no number-field API is needed.
-/
import Mathlib

namespace ResidueSlices
namespace NonArchimedean

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- The `l`-th roots-of-unity channel of the residue-packet filter at `y`,
matching `c_l = 1 + ζ^l y` in the archimedean treatment. -/
noncomputable def channel (ζ y : K) (l : ℕ) : K := 1 + ζ ^ l * y

/-- `v` has residue characteristic `p`: only the prime `p` is contracted. -/
structure IsResidueChar (v : Valuation K Γ₀) (p : ℕ) : Prop where
  prime : p.Prime
  contracts : v (p : K) < 1
  others : ∀ q : ℕ, q.Prime → q ≠ p → v (q : K) = 1

/-- Channel `l` is strictly dominant: it is strictly larger than every other
channel in `|·|_v`. -/
def Dominant (v : Valuation K Γ₀) (ζ y : K) (g l : ℕ) : Prop :=
  l < g ∧ ∀ m < g, m ≠ l → v (channel ζ y m) < v (channel ζ y l)

/-! ### Shared steps

A root of unity has valuation `1`, and the distance from `1` to a root of unity
only depends on its order (more precisely, it is unchanged when the root is
raised to a power coprime to its order).
-/

/-- A root of unity has valuation `1`. -/
private theorem val_root_of_unity {v : Valuation K Γ₀} {ξ : K} {d : ℕ} (hd : d ≠ 0)
    (h : ξ ^ d = 1) : v ξ = 1 := by
  have : (v ξ) ^ d = 1 := by rw [← Valuation.map_pow, h, Valuation.map_one]
  exact (pow_eq_one_iff_left hd).mp this

/-- A root of unity is at distance at most `1` from `1`. -/
private theorem val_one_sub_le_one {v : Valuation K Γ₀} {ξ : K} {d : ℕ} (hd : d ≠ 0)
    (h : ξ ^ d = 1) : v (1 - ξ) ≤ 1 := by
  have hs := v.map_sub 1 ξ
  rw [Valuation.map_one, val_root_of_unity hd h] at hs
  simpa using hs

/-- Raising a root of unity to a power can only decrease its distance from `1`. -/
private theorem val_one_sub_pow_le {v : Valuation K Γ₀} {ξ : K} {d : ℕ} (hd : d ≠ 0)
    (h : ξ ^ d = 1) (n : ℕ) : v (1 - ξ ^ n) ≤ v (1 - ξ) := by
  have key : (1 : K) - ξ ^ n = (1 - ξ) * (∑ i ∈ Finset.range n, ξ ^ i) :=
    (mul_neg_geom_sum ξ n).symm
  have hsum : v (∑ i ∈ Finset.range n, ξ ^ i) ≤ 1 := by
    refine Valuation.map_sum_le v ?_
    intro i _
    rw [Valuation.map_pow, val_root_of_unity hd h, one_pow]
  calc v (1 - ξ ^ n) = v (1 - ξ) * v (∑ i ∈ Finset.range n, ξ ^ i) := by
        rw [key, Valuation.map_mul]
    _ ≤ v (1 - ξ) * 1 := by gcongr
    _ = v (1 - ξ) := mul_one _

/-- If `a` is coprime to `d` and `ξ ^ d = 1`, then `ξ` is a power of `ξ ^ a`. -/
private theorem pow_pow_eq_self_of_coprime {ξ : K} {d a : ℕ} (hd : d ≠ 0) (hξ : ξ ^ d = 1)
    (hcop : Nat.Coprime a d) : ∃ b, (ξ ^ a) ^ b = ξ := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hd) with h1 | h1
  · refine ⟨1, ?_⟩
    have hone : ξ = 1 := by rw [← pow_one ξ, h1, hξ]
    simp [hone]
  · have ha : a ≠ 0 := by
      rintro rfl
      simp only [Nat.Coprime, Nat.gcd_zero_left] at hcop
      omega
    have h2 : a ^ d.totient ≡ 1 [MOD d] := Nat.ModEq.pow_totient hcop
    have hge : 1 ≤ a ^ d.totient := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero ha)
    obtain ⟨k, hk⟩ : ∃ k, a ^ d.totient = 1 + d * k := by
      obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hge).mp h2.symm
      exact ⟨k, by omega⟩
    have hphi : 1 ≤ d.totient := Nat.totient_pos.mpr (by omega)
    refine ⟨a ^ (d.totient - 1), ?_⟩
    rw [← pow_mul, show a * a ^ (d.totient - 1) = a ^ d.totient by
      rw [← pow_succ']; congr 1; omega]
    rw [hk, pow_add, pow_one, pow_mul, hξ, one_pow, mul_one]

/-- The distance from `1` is unchanged under raising to a power coprime to the order. -/
private theorem val_one_sub_pow_eq_of_coprime {v : Valuation K Γ₀} {ξ : K} {d a : ℕ} (hd : d ≠ 0)
    (hξ : ξ ^ d = 1) (hcop : Nat.Coprime a d) : v (1 - ξ ^ a) = v (1 - ξ) := by
  refine le_antisymm (val_one_sub_pow_le hd hξ a) ?_
  obtain ⟨b, hb⟩ := pow_pow_eq_self_of_coprime hd hξ hcop
  have hpow : (ξ ^ a) ^ d = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ, one_pow]
  have h := val_one_sub_pow_le (v := v) hd hpow b
  rwa [hb] at h

/-! ### The cyclotomic computation -/

open Polynomial in
/-- All primitive `d`-th roots of unity are at the same distance from `1`, and the product
of those distances is the value at `1` of the `d`-th cyclotomic polynomial. -/
private theorem val_one_sub_totient (v : Valuation K Γ₀) {ξ : K} {d : ℕ} (hd : 0 < d)
    (hξ : IsPrimitiveRoot ξ d) :
    v (1 - ξ) ^ d.totient = v ((cyclotomic d K).eval 1) := by
  have hprod : (cyclotomic d K).eval 1 = ∏ μ ∈ primitiveRoots d K, (1 - μ) := by
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots hξ]
    simp [eval_prod]
  rw [hprod, map_prod, Finset.prod_congr rfl (g := fun _ => v (1 - ξ)) ?_, Finset.prod_const,
    hξ.card_primitiveRoots]
  intro μ hμ
  have hm : IsPrimitiveRoot μ d := (mem_primitiveRoots hd).mp hμ
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hm.pow_eq_one
  exact val_one_sub_pow_eq_of_coprime hd.ne' hξ.pow_eq_one ((hξ.pow_iff_coprime hd i).mp hm)

open Polynomial in
/-- If `d > 1` is not a positive power of the residue characteristic, the `d`-th cyclotomic
polynomial takes at `1` a value of valuation `1`. -/
private theorem val_eval_cyclotomic_of_not_ppow {v : Valuation K Γ₀} {p d : ℕ}
    (hp : IsResidueChar v p) (hd : 1 < d) (hnot : ¬ ∃ s, 1 ≤ s ∧ d = p ^ s) :
    v ((cyclotomic d K).eval 1) = 1 := by
  by_cases hq : ∃ q k : ℕ, q.Prime ∧ d = q ^ k
  · obtain ⟨q, k, hqp, rfl⟩ := hq
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hd
      · exact h
    have hqp' : q ≠ p := by
      rintro rfl
      exact hnot ⟨k, hk, rfl⟩
    have : Fact q.Prime := ⟨hqp⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [eval_one_cyclotomic_prime_pow (R := K) k']
    exact hp.others q hqp hqp'
  · push Not at hq
    rw [eval_one_cyclotomic_not_prime_pow (R := K) (n := d) fun {q} hq' k => (hq q k hq').symm]
    simp

open Polynomial in
/-- The `p ^ s`-th cyclotomic polynomial takes the value `p` at `1`. -/
private theorem val_eval_cyclotomic_ppow (v : Valuation K Γ₀) {p s : ℕ} (hs : 1 ≤ s)
    (hp : p.Prime) : v ((cyclotomic (p ^ s) K).eval 1) = v (p : K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [eval_one_cyclotomic_prime_pow (R := K) k]

/-- Quantitative form of Goal 1: for a primitive `p ^ s`-th root of unity,
`v (1 - ξ) ^ φ(p ^ s) = v p`. -/
private theorem val_one_sub_primitive_ppow {v : Valuation K Γ₀} {p s : ℕ}
    (hp : IsResidueChar v p) (hs : 1 ≤ s) {ξ : K} (hξ : IsPrimitiveRoot ξ (p ^ s)) :
    v (1 - ξ) ^ (p ^ s).totient = v (p : K) := by
  have hpos : 0 < p ^ s := Nat.pow_pos hp.prime.pos
  rw [val_one_sub_totient v hpos hξ, val_eval_cyclotomic_ppow v hs hp.prime]

/-- **Goal 1.** A root of unity is `v`-close to `1` exactly when its order is a
positive power of the residue characteristic.  Both directions are needed. -/
theorem valuation_one_sub_root_lt_one_iff
    {v : Valuation K Γ₀} {p g j : ℕ} (hp : IsResidueChar v p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ g) (hg : 0 < g) (hj : ζ ^ j ≠ 1) :
    v (1 - ζ ^ j) < 1 ↔ ∃ s : ℕ, 1 ≤ s ∧ orderOf (ζ ^ j) = p ^ s := by
  have hξg : (ζ ^ j) ^ g = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hfin : IsOfFinOrder (ζ ^ j) := isOfFinOrder_iff_pow_eq_one.mpr ⟨g, hg, hξg⟩
  have hd0 : 0 < orderOf (ζ ^ j) := hfin.orderOf_pos
  have hd1 : 1 < orderOf (ζ ^ j) := by
    have hne1 : orderOf (ζ ^ j) ≠ 1 := fun h => hj (orderOf_eq_one_iff.mp h)
    omega
  have hprim : IsPrimitiveRoot (ζ ^ j) (orderOf (ζ ^ j)) := IsPrimitiveRoot.orderOf _
  have hquant := val_one_sub_totient v hd0 hprim
  have hφ : (orderOf (ζ ^ j)).totient ≠ 0 := (Nat.totient_pos.mpr hd0).ne'
  have hle : v (1 - ζ ^ j) ≤ 1 := val_one_sub_le_one hg.ne' hξg
  constructor
  · intro hlt
    by_contra hnot
    rw [val_eval_cyclotomic_of_not_ppow hp hd1 hnot] at hquant
    exact absurd ((pow_eq_one_iff_left hφ).mp hquant) hlt.ne
  · rintro ⟨s, hs, hds⟩
    rw [hds, val_eval_cyclotomic_ppow v hs hp.prime] at hquant
    refine lt_of_le_of_ne hle fun hone => ?_
    rw [hone, one_pow] at hquant
    exact absurd hquant.symm hp.contracts.ne

/-- **Goal 2.** In a ramified tower of height at least two the distances from
`1` are not all equal: `ζ` and the primitive `p`-th root `ζ^(p^(e-1))` have
different valuations.  Equivalently `φ(p^e) * v(1-ζ) = v(p) = φ(p) *
v(1-ζ^(p^(e-1)))` with `φ(p^e) ≠ φ(p)`. -/
theorem valuation_one_sub_distinct_in_tower
    {v : Valuation K Γ₀} {p e : ℕ} (hp : IsResidueChar v p) (he : 2 ≤ e)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ e)) :
    v (1 - ζ) ≠ v (1 - ζ ^ p ^ (e - 1)) := by
  have hp1 : 1 < p := hp.prime.one_lt
  have hppos : 0 < p ^ e := Nat.pow_pos hp.prime.pos
  have hA := val_one_sub_primitive_ppow hp (by omega : 1 ≤ e) hζ
  have hBprim : IsPrimitiveRoot (ζ ^ p ^ (e - 1)) (p ^ 1) := by
    refine hζ.pow hppos ?_
    rw [pow_one, ← pow_succ]
    congr 1
    omega
  have hB := val_one_sub_primitive_ppow hp le_rfl hBprim
  intro heq
  rw [← heq] at hB
  set w := v (1 - ζ) with hw
  have hζne : ζ ≠ 1 := hζ.ne_one (by calc 1 < p := hp1
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ e := Nat.pow_le_pow_right hp.prime.pos (by omega))
  have hwne : w ≠ 0 := by
    rw [hw, Valuation.ne_zero_iff]
    exact sub_ne_zero_of_ne (Ne.symm hζne)
  have hlt : (p ^ 1).totient < (p ^ e).totient := by
    rw [Nat.totient_prime_pow hp.prime (by omega), Nat.totient_prime_pow hp.prime (by omega)]
    have : p ^ (1 - 1) < p ^ (e - 1) := by
      refine Nat.pow_lt_pow_right hp1 ?_
      omega
    exact Nat.mul_lt_mul_of_lt_of_le this le_rfl (by omega)
  have hsplit : w ^ (p ^ e).totient
      = w ^ (p ^ 1).totient * w ^ ((p ^ e).totient - (p ^ 1).totient) := by
    rw [← pow_add]
    congr 1
    omega
  have hone : w ^ ((p ^ e).totient - (p ^ 1).totient) = 1 := by
    have := hA.trans hB.symm
    rw [hsplit] at this
    have hcancel := mul_left_cancel₀ (pow_ne_zero (p ^ 1).totient hwne)
      (this.trans (mul_one (w ^ (p ^ 1).totient)).symm)
    exact hcancel
  have : w = 1 := (pow_eq_one_iff_left (by omega)).mp hone
  rw [this, one_pow] at hA
  exact absurd hA.symm hp.contracts.ne

/-- The valuation of a difference of two channels only depends on the difference of
the indices. -/
private theorem val_channel_sub {v : Valuation K Γ₀} {ζ y : K} {g : ℕ} (hg : 0 < g)
    (hζ : ζ ^ g = 1) {a b : ℕ} (hab : b ≤ a) :
    v (channel ζ y a - channel ζ y b) = v (1 - ζ ^ (a - b)) * v y := by
  have hfac : channel ζ y a - channel ζ y b = ζ ^ b * ((ζ ^ (a - b) - 1) * y) := by
    have : ζ ^ a = ζ ^ b * ζ ^ (a - b) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [channel, this]
    ring
  rw [hfac, Valuation.map_mul, Valuation.map_mul, Valuation.map_pow,
    val_root_of_unity hg.ne' hζ, one_pow, one_mul, Valuation.map_sub_swap]

/-- Replacing the difference index `j` by `g - j` does not change the distance from `1`. -/
private theorem val_one_sub_pow_symm {v : Valuation K Γ₀} {ζ : K} {g j : ℕ} (hg : 0 < g)
    (hζ : ζ ^ g = 1) (hj : j ≤ g) : v (1 - ζ ^ (g - j)) = v (1 - ζ ^ j) := by
  have hfac : ζ ^ j * (1 - ζ ^ (g - j)) = ζ ^ j - 1 := by
    rw [mul_sub, mul_one, ← pow_add, show j + (g - j) = g by omega, hζ]
  have h2 := congrArg v hfac
  rw [Valuation.map_mul, Valuation.map_pow, val_root_of_unity hg.ne' hζ, one_pow, one_mul] at h2
  rw [Valuation.map_sub_swap v 1 (ζ ^ j)]
  exact h2

/-- **Goal 3 (main).** Non-archimedean channel rigidity: at a finite place a
strictly dominant channel forces `g = 2`.  Compare `BirootChannels`, where the
archimedean place has a dominant channel for every `g`. -/
theorem eq_two_of_dominant
    {v : Valuation K Γ₀} {p g l : ℕ} (hp : IsResidueChar v p) (hg : 2 ≤ g)
    {ζ y : K} (hζ : IsPrimitiveRoot ζ g)
    (hne : ∀ m < g, channel ζ y m ≠ 0)
    (hdom : Dominant v ζ y g l) : g = 2 := by
  -- The proof below uses only the ultrametric inequality, so the residue-characteristic
  -- hypothesis `hp` and the nonvanishing hypothesis `hne` are not needed; they are kept
  -- in the statement as specified and are referenced here only to silence the linter.
  have _hp := hp
  have _hne := hne
  obtain ⟨hl, hdm⟩ := hdom
  by_contra hg2
  have hg3 : 3 ≤ g := by omega
  have hgpos : 0 < g := by omega
  have hζg : ζ ^ g = 1 := hζ.pow_eq_one
  -- two indices `m' < m' + j`, both `< g` and both different from `l`
  obtain ⟨b, j, hbj, hj0, hbjne, hbne⟩ :
      ∃ b j, b + j < g ∧ 0 < j ∧ b + j ≠ l ∧ b ≠ l := by
    rcases (show l = 0 ∨ l = 1 ∨ 2 ≤ l from by omega) with h | h | h
    · exact ⟨1, 1, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, 2, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, 1, by omega, by omega, by omega, by omega⟩
  have hjg : j < g := by omega
  -- the common value of `v (1 - ζ ^ j) * v y` is the dominant channel's value
  have key : v (1 - ζ ^ j) * v y = v (channel ζ y l) := by
    by_cases hc : l + j < g
    · have h1 := val_channel_sub (v := v) (y := y) hgpos hζg (a := l + j) (b := l) (by omega)
      rw [show l + j - l = j by omega] at h1
      rw [← h1]
      exact Valuation.map_sub_eq_of_lt_right v (hdm _ hc (by omega))
    · have h1 := val_channel_sub (v := v) (y := y) hgpos hζg (a := l) (b := l + j - g) (by omega)
      rw [show l - (l + j - g) = g - j by omega, val_one_sub_pow_symm hgpos hζg (by omega)] at h1
      rw [← h1]
      exact Valuation.map_sub_eq_of_lt_left v (hdm _ (by omega) (by omega))
  -- but the difference of two dominated channels is strictly smaller
  have hd := val_channel_sub (v := v) (y := y) hgpos hζg (a := b + j) (b := b) (by omega)
  rw [show b + j - b = j by omega] at hd
  have hlt : v (channel ζ y (b + j) - channel ζ y b) < v (channel ζ y l) :=
    Valuation.map_sub_lt v (hdm _ hbj hbjne) (hdm _ (by omega) hbne)
  rw [hd, key] at hlt
  exact lt_irrefl _ hlt

/-- **Goal 4.** For `g = 2` dominance is exactly the failure of the two channels
to have equal valuation.  With `ζ = -1` the channels are `1 + y` and `1 - y`. -/
theorem dominant_two_iff {v : Valuation K Γ₀} {y : K}
    (hpos : (1 : K) + y ≠ 0) (hneg : (1 : K) - y ≠ 0) :
    (∃ l, Dominant v (-1 : K) y 2 l) ↔ v (1 + y) ≠ v (1 - y) := by
  -- The two channels are automatically nonzero for the argument below, so `hpos` and `hneg`
  -- are not needed; they are kept in the statement as specified.
  have _hpos := hpos
  have _hneg := hneg
  have h0 : channel (-1 : K) y 0 = 1 + y := by simp [channel]
  have h1 : channel (-1 : K) y 1 = 1 - y := by simp [channel, sub_eq_add_neg]
  constructor
  · rintro ⟨l, hl, hdm⟩
    have hl' : l = 0 ∨ l = 1 := by omega
    rcases hl' with rfl | rfl
    · have h := hdm 1 (by norm_num) (by norm_num)
      rw [h0, h1] at h
      exact h.ne'
    · have h := hdm 0 (by norm_num) (by norm_num)
      rw [h0, h1] at h
      exact h.ne
  · intro h
    rcases lt_or_gt_of_ne h with hlt | hlt
    · refine ⟨1, by norm_num, ?_⟩
      intro m hm hm1
      obtain rfl : m = 0 := by omega
      rw [h0, h1]
      exact hlt
    · refine ⟨0, by norm_num, ?_⟩
      intro m hm hm0
      obtain rfl : m = 1 := by omega
      rw [h0, h1]
      exact hlt

/-- The height-one prime `(3)` of `ℤ`, used to exhibit a 3-adic valuation of `ℚ`. -/
private noncomputable def idealThree : IsDedekindDomain.HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(3 : ℤ)}
  isPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]
    exact Int.prime_three
  ne_bot := by simp

/-- An integer outside `(3)` has valuation `1` for the 3-adic valuation of `ℚ`. -/
private theorem valuation_int_eq_one {n : ℤ} (hn : ¬ (3 : ℤ) ∣ n) :
    (idealThree.valuation ℚ) (n : ℚ) = 1 := by
  have h : ((n : ℚ)) = algebraMap ℤ ℚ n := by simp
  rw [h]
  refine le_antisymm (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _) ?_
  by_contra hc
  push Not at hc
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem] at hc
  exact hn ((Ideal.mem_span_singleton).mp hc)

/-- An integer inside `(3)` has valuation `< 1` for the 3-adic valuation of `ℚ`. -/
private theorem valuation_int_lt_one {n : ℤ} (hn : (3 : ℤ) ∣ n) :
    (idealThree.valuation ℚ) (n : ℚ) < 1 := by
  have h : ((n : ℚ)) = algebraMap ℤ ℚ n := by simp
  rw [h, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact (Ideal.mem_span_singleton).mpr hn

/-- **Goal 5 (nonvacuity).** The hypotheses of Goal 3 are satisfiable: the
3-adic valuation of `ℚ` with `y = 4` has channel `0` strictly dominant, since
`v(1+4) = 1` and `v(1-4) < 1`.  Any valuation construction is acceptable as long
as `IsResidueChar` is proved for it; the height-one-spectrum valuation of `ℤ` at
`(3)` is one route. -/
theorem exists_dominant_two :
    ∃ v : Valuation ℚ (WithZero (Multiplicative ℤ)),
      IsResidueChar v 3 ∧ Dominant v (-1 : ℚ) 4 2 0 := by
  refine ⟨idealThree.valuation ℚ, ⟨by norm_num, ?_, ?_⟩, by norm_num, ?_⟩
  · have h : ((3 : ℕ) : ℚ) = ((3 : ℤ) : ℚ) := by norm_num
    rw [h]
    exact valuation_int_lt_one dvd_rfl
  · intro q hq hq3
    have h : ((q : ℕ) : ℚ) = ((q : ℤ) : ℚ) := by norm_num
    rw [h]
    refine valuation_int_eq_one ?_
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast]
    intro hdvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq 3 hdvd) with h1 | h1
    · omega
    · exact hq3 h1.symm
  · intro m hm hm0
    obtain rfl : m = 1 := by omega
    have hc1 : channel (-1 : ℚ) 4 1 = ((-3 : ℤ) : ℚ) := by norm_num [channel]
    have hc0 : channel (-1 : ℚ) 4 0 = ((5 : ℤ) : ℚ) := by norm_num [channel]
    rw [hc0, hc1, valuation_int_eq_one (n := 5) (by omega)]
    exact valuation_int_lt_one (n := -3) (by omega)

end NonArchimedean
end ResidueSlices
