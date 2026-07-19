import Mathlib

open scoped BigOperators

namespace ResidueSlices

/-- The `r`-th residue packet of the `N`-th binomial row, with exponents
compressed by a factor `g`.  The definition is meaningful without assuming
`r < g`; the main decomposition uses the canonical residues `0, …, g-1`. -/
def slice {R : Type*} [CommSemiring R] (g r N : ℕ) (x : R) : R :=
  ∑ j ∈ Finset.range (N + 1), if j % g = r then (N.choose j : R) * x ^ (j / g) else 0

/-
Selecting every `g`-th binomial coefficient and then restoring its residue
power exactly reconstructs the binomial expansion.  This is the finite
algebraic core of residue packetization; no analytic limit or choice of roots
is involved.
-/
theorem packet_decomposition {R : Type*} [CommSemiring R]
    (g N : ℕ) (hg : 0 < g) (t : R) :
    ∑ r ∈ Finset.range g, t ^ r * slice g r N (t ^ g) = (1 + t) ^ N := by
  unfold slice;
  simp +decide only [Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm, add_comm 1 t, add_pow ];
  simp +decide [← pow_mul];
  exact Finset.sum_congr rfl fun x hx => by rw [ if_pos ( Nat.mod_lt _ hg ) ] ; rw [ show t ^ x = t ^ ( x % g ) * t ^ ( g * ( x / g ) ) by rw [ ← pow_add, Nat.mod_add_div ] ] ; ring;

/-
A coefficient belongs to exactly one packet.  This coefficient-level
form is useful when applying the decomposition in other semirings.
-/
theorem unique_residue_packet (g j : ℕ) (hg : 0 < g) :
    ∑ r ∈ Finset.range g, (if j % g = r then 1 else 0) = 1 := by
  simp +decide [Nat.mod_lt j hg]

/-
Residue slices are nonnegative on the nonnegative real axis.
-/
theorem slice_nonneg (g r N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ slice g r N x := by
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity;

/-
The zeroth packet has constant term one, hence is strictly positive on the
nonnegative real axis.  This is the elementary pole-freeness fact behind the
positive-axis rational approximants.
-/
theorem one_le_slice_zero (g N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ slice g 0 N x := by
  convert Finset.single_le_sum ( fun j _ => ?_ ) ( Finset.mem_range.mpr ( Nat.succ_pos ( N : ℕ ) ) ) using 1;
  · norm_num
  · infer_instance
  · positivity

/-
For `g = 2`, the two packets are the even and odd parts of the binomial
expansion.  This is the alternating-Pascal-row identity in its direct form.
-/
theorem square_even_odd (N : ℕ) (t : ℝ) :
    slice 2 0 N (t ^ 2) + t * slice 2 1 N (t ^ 2) = (1 + t) ^ N := by
  convert packet_decomposition 2 N ( by norm_num ) t using 1 ; norm_num [ Finset.sum_range_succ', slice ] ; ring;

/-
Reflecting `t` to `-t` changes the sign of the odd packet and leaves the
even packet fixed.
-/
theorem square_even_odd_reflected (N : ℕ) (t : ℝ) :
    slice 2 0 N (t ^ 2) - t * slice 2 1 N (t ^ 2) = (1 - t) ^ N := by
  convert square_even_odd N ( -t ) using 1 ; ring

/-
Exact error identity for the square-root packet ratio.  When `t > 0`, the
zeroth packet is positive, so division by it turns this into a rational
approximation of `t⁻¹`; the reflected power `(1-t)^N` is the complete error
term before division.
-/
theorem square_ratio_cross_error (N : ℕ) (t : ℝ) :
    t * slice 2 1 N (t ^ 2) - slice 2 0 N (t ^ 2) = -(1 - t) ^ N := by
  convert congr_arg Neg.neg ( square_even_odd_reflected N t ) using 1 ; ring

/-
The even packet is the average of the direct and reflected binomial
waves.
-/
theorem two_mul_square_even (N : ℕ) (t : ℝ) :
    2 * slice 2 0 N (t ^ 2) = (1 + t) ^ N + (1 - t) ^ N := by
  convert congr_arg₂ ( · + · ) ( square_even_odd N t ) ( square_even_odd_reflected N t ) using 1 ; ring

/-
The square-root packet ratio has an exact relative-error formula.
-/
theorem square_ratio_error (N : ℕ) (t : ℝ) :
    t * (slice 2 1 N (t ^ 2) / slice 2 0 N (t ^ 2)) - 1 =
      -((1 - t) ^ N / slice 2 0 N (t ^ 2)) := by
  rw [ mul_div ];
  rw [ div_sub_one, ← neg_div, ← square_ratio_cross_error ];
  exact ne_of_gt ( lt_of_lt_of_le zero_lt_one ( one_le_slice_zero 2 N ( sq_nonneg t ) ) )

/-
The ratio of the odd and even Pascal packets converges to the reciprocal
square root.  Equivalently, after substituting `x = t²`, residue selection
constructs `x⁻¹ᐟ²` on the positive axis.
-/
theorem tendsto_square_ratio {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun N : ℕ => slice 2 1 N (t ^ 2) / slice 2 0 N (t ^ 2))
      Filter.atTop (nhds t⁻¹) := by
  set q : ℝ := (1 - t) / (1 + t)
  have hq : |q| < 1 := by
    exact abs_lt.mpr ⟨ by rw [ lt_div_iff₀ ] <;> linarith, by rw [ div_lt_iff₀ ] <;> linarith ⟩;
  have h_ratio : ∀ N : ℕ, (slice 2 1 N (t ^ 2) / slice 2 0 N (t ^ 2)) = t⁻¹ * (1 - q^N) / (1 + q^N) := by
    intro N
    have h_even_odd : slice 2 0 N (t ^ 2) = ((1 + t) ^ N + (1 - t) ^ N) / 2 ∧ slice 2 1 N (t ^ 2) = ((1 + t) ^ N - (1 - t) ^ N) / (2 * t) := by
      grind +suggestions;
    rw [ h_even_odd.1, h_even_odd.2, div_pow ];
    field_simp;
  simpa [ h_ratio ] using Filter.Tendsto.div ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub ( tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq ) ) ) ( tendsto_const_nhds.add ( tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq ) ) ( by norm_num ) |> fun h => h.trans <| by norm_num;

end ResidueSlices