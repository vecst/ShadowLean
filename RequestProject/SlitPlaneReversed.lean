/-
Targets for Aristotle: complete the correspondence with
`residue_slice_rational_approximation.tex`, Theorem
[Principal-branch convergence on the slit plane].

The existing theorem `tendsto_slice_ratio_cpow` proves only the forward ratio

  slice g k N x⁻¹ / slice g 0 N x⁻¹  ⟶  x ^ (k/g).

The paper's approximant is the reversed/shifted quotient `A_N/B_N`, whose
denominator deletes the `g ∣ N` endpoint.  This file asks for that missing
endpoint analysis over ℂ and then for compact-local uniformity.

Important k = 0 convention.
The paper simplifies `A_N(x,0,g)/B_N(x,g)` to the rational function 1 because
the numerator and denominator polynomials are identical.  Lean's field
division is total, so a literal value `0/0` is 0 rather than 1.  This matters
on the complex domain: for example, with g = 1 and

  x = exp(π i / 3) - 1 ∈ Complex.slitPlane,

`revAComplex 1 0 N x = 0` for every positive multiple N of 6.  Therefore the
raw quotient cannot converge to 1.  `reversedRatioComplex` below encodes the
paper's explicitly stated cancellation at k = 0 and uses the literal quotient
for 1 ≤ k < g.

Suggested staging:

Pass A (priority): Targets 1--4 close the pointwise paper theorem.
Pass B: Targets 5--7 close its local-uniform clause.

Existing ingredients:

* `qIdx`, `epsIdx`, and the real analogues `revA_eq_slice`, `revB_eq_slice`,
  `tendsto_reversed_ratio` in `ReversedApproximants.lean`;
* `norm_one_add_root_mul_lt` and `tendsto_slice_ratio_cpow` in
  `SlitPlane.lean`;
* the real compact-uniform proof architecture in `CompactUniform.lean`.

For k ≠ 0, `hk : k < g` implies `2 ≤ g`.  With
`s = (x⁻¹)^((g : ℂ)⁻¹)`, this puts s in the strict sector
`|arg s| < π/g ≤ π/2`, so `|s| < |1+s|`.  The endpoint channel therefore
decays like `(|s|/|1+s|)^N`.  Split off k = 0 before using this fact; it is
false as an all-g endpoint lemma when g = 1.

For compact-local uniformity, use compactness of K inside the open slit plane
to obtain one strict upper bound below 1 for both:

* the finitely many nonprincipal channel ratios
  `‖1 + ω^ℓ s(x)‖ / ‖1 + s(x)‖`, and
* the endpoint ratio `‖s(x)‖ / ‖1 + s(x)‖` (only in the k ≠ 0 branch).

Every proof placeholder marks a requested result.  Minor Mathlib-name adjustments are fine;
keep the mathematical content and all boundary hypotheses of the statements.
-/

import RequestProject.SlitPlane
import RequestProject.CompactUniform

open scoped BigOperators

set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

namespace ResidueSlices

/-- Complex version of the paper's reversed polynomial
`A_N(x,k,g) = ∑_{j=0}^{q_N} C(N,gj+k)x^(q_N-j)`.
The denominator polynomial is `revAComplex g 0 N x`. -/
noncomputable def revAComplex (g k N : ℕ) (x : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (qIdx g N + 1),
    (N.choose (g * j + k) : ℂ) * x ^ (qIdx g N - j)

/-- The paper's complex reversed approximant.  At k = 0 this records the
paper's cancellation `A_N/B_N ≡ 1`; for positive k it is the literal
polynomial quotient. -/
noncomputable def reversedRatioComplex (g k N : ℕ) (x : ℂ) : ℂ :=
  if k = 0 then 1 else revAComplex g k N x / revAComplex g 0 N x

@[simp] theorem reversedRatioComplex_zero (g N : ℕ) (x : ℂ) :
    reversedRatioComplex g 0 N x = 1 := by
  simp [reversedRatioComplex]

/- Target 1: complex numerator reversal identity, valid away from x = 0. -/
theorem revAComplex_eq_slice {g k N : ℕ} (hg : 0 < g)
    (hk1 : 1 ≤ k) (hkg : k < g) {x : ℂ} (hx : x ≠ 0) :
    revAComplex g k N x = x ^ qIdx g N * slice g k N x⁻¹ := by
  unfold revAComplex slice qIdx;
  rw [ Finset.mul_sum _ _ _ ];
  rw [ ← Finset.sum_subset ( Finset.subset_iff.mpr _ ) ];
  any_goals exact Finset.filter ( fun j => g * j + k < N + 1 ) ( Finset.range ( ( N - 1 ) / g + 1 ) );
  · rw [ ← Finset.sum_subset ( show Finset.image ( fun j => g * j + k ) ( Finset.filter ( fun j => g * j + k < N + 1 ) ( Finset.range ( ( N - 1 ) / g + 1 ) ) ) ⊆ Finset.range ( N + 1 ) from ?_ ) ];
    · rw [ Finset.sum_image ] <;> norm_num;
      · rw [ if_pos ( Nat.mod_eq_of_lt hkg ) ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ show ( g * i + k ) / g = i by nlinarith [ Nat.div_mul_le_self ( g * i + k ) g, Nat.div_add_mod ( g * i + k ) g, Nat.mod_lt ( g * i + k ) hg ] ] ; ring;
        rw [ mul_assoc, show x ^ ( ( N - 1 ) / g ) = x ^ ( ( N - 1 ) / g - i ) * x ^ i by rw [ ← pow_add, Nat.sub_add_cancel ( show i ≤ ( N - 1 ) / g from Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hi |>.1 ) ) ] ] ; ring;
        simp only [inv_pow];
        field_simp [pow_ne_zero i hx];
      · exact fun a ha b hb hab => by nlinarith;
    · intro j hj₁ hj₂; contrapose! hj₂; simp_all +decide ;
      exact ⟨ j / g, ⟨ Nat.le_div_iff_mul_le hg |>.2 <| Nat.le_sub_one_of_lt <| by nlinarith [ Nat.mod_add_div j g ], by nlinarith [ Nat.mod_add_div j g ] ⟩, by linarith [ Nat.mod_add_div j g ] ⟩;
    · exact Finset.image_subset_iff.mpr fun j hj => Finset.mem_range.mpr <| Finset.mem_filter.mp hj |>.2;
  · simp +contextual [ Nat.choose_eq_zero_of_lt ];
  · aesop




/- Target 2: complex denominator identity with the divisibility endpoint. -/
theorem revBComplex_eq_slice {g N : ℕ} (hg : 0 < g) (hN : 1 ≤ N)
    {x : ℂ} (hx : x ≠ 0) :
    revAComplex g 0 N x =
      x ^ qIdx g N *
        (slice g 0 N x⁻¹ -
          (epsIdx g N : ℂ) * (x⁻¹) ^ (qIdx g N + 1)) := by
  unfold revAComplex slice epsIdx qIdx
  have hx_inv : x⁻¹ ≠ 0 := inv_ne_zero hx
  have h_split : ∑ j ∈ Finset.range (N + 1), (if j % g = 0 then (N.choose j : ℂ) * x⁻¹ ^ (j / g) else 0) =
      ∑ j ∈ Finset.range ((N - 1) / g + 1), (N.choose (g * j) : ℂ) * x⁻¹ ^ j +
        (if g ∣ N then (N.choose N : ℂ) * x⁻¹ ^ (N / g) else 0) := by
    have h_split : Finset.filter (fun j => j % g = 0) (Finset.range (N + 1)) =
        Finset.image (fun j => g * j) (Finset.range ((N - 1) / g + 1)) ∪ (if g ∣ N then {N} else ∅) := by
      ext j
      simp [Finset.mem_union, Finset.mem_image]
      constructor
      · intro hj
        by_cases h_div : j = N
        · exact Or.inr (by rw [if_pos (Nat.dvd_of_mod_eq_zero (by aesop))] ; aesop)
        · exact Or.inl ⟨j / g, Nat.le_div_iff_mul_le hg |>.2 <| Nat.le_sub_one_of_lt <| by
              linarith [Nat.mod_add_div j g, Nat.lt_of_le_of_ne hj.1 h_div],
            Nat.mul_div_cancel' <| Nat.dvd_of_mod_eq_zero hj.2⟩
      · rintro (⟨a, ha, rfl⟩ | h) <;> simp_all +decide [Nat.dvd_iff_mod_eq_zero]
        · nlinarith [Nat.div_mul_le_self (N - 1) g, Nat.sub_add_cancel hN]
        · split_ifs at h <;> simp_all +decide
    rw [← Finset.sum_filter, h_split, Finset.sum_union] <;> norm_num
    · split_ifs <;> simp_all +decide [Finset.sum_image, hg.ne']
    · split_ifs <;> simp_all +decide [Finset.disjoint_left]
      intro a ha; nlinarith [Nat.div_mul_le_self (N - 1) g, Nat.sub_add_cancel hN, Nat.le_of_dvd hN ‹_›]
  split_ifs at * <;> simp_all +decide [Nat.dvd_iff_mod_eq_zero]
  · rw [show N / g = (N - 1) / g + 1 from ?_]
    · simp +decide [Finset.mul_sum _ _ _, mul_assoc, mul_comm, pow_add]
      exact Finset.sum_congr rfl fun i hi => by
        rw [inv_mul_eq_div, eq_div_iff (pow_ne_zero _ hx), mul_assoc, ← pow_add,
          tsub_add_cancel_of_le (Finset.mem_range_succ_iff.mp hi)]
    · cases N <;> simp_all +decide [Nat.succ_div]
      exact Nat.dvd_of_mod_eq_zero ‹_›
  · rw [Finset.mul_sum _ _ _]
    refine' Finset.sum_congr rfl fun i hi => _
    have h : x ^ i ≠ 0 := pow_ne_zero _ hx
    field_simp
    rw [mul_assoc, mul_comm (x ^ ((N - 1) / g - i)) (x ^ i), ← pow_add]
    rw [add_tsub_cancel_of_le (Finset.mem_range_succ_iff.mp hi)]



/- Target 3: pointwise disappearance of the deleted endpoint.  The hypothesis
`2 ≤ g` is essential; the final theorem obtains it from k ≠ 0 and k < g. -/
theorem tendsto_endpointCorrection_cpow {g : ℕ} (hg : 2 ≤ g)
    {x : ℂ} (hx : x ∈ Complex.slitPlane) :
    Filter.Tendsto
      (fun N : ℕ =>
        (epsIdx g N : ℂ) * (x⁻¹) ^ (qIdx g N + 1) /
          slice g 0 N x⁻¹)
      Filter.atTop (nhds 0) := by
  -- Set s = (x⁻¹)^(1/g) which is in the principal sector
  set s := (x⁻¹) ^ ((g : ℂ)⁻¹)
  have hg_pos : (0 : ℕ) < g := by linarith
  have hx_ne_zero : x ≠ 0 := by
    simp only [Complex.slitPlane] at hx
    rcases hx with hx | hx
    · exact fun h => hx.ne' (h.symm ▸ by simp)
    · exact fun h => hx (h.symm ▸ by simp)
  have hx_inv_slit : x⁻¹ ∈ Complex.slitPlane := by
    simp only [Complex.slitPlane] at hx ⊢
    rcases hx with hx | hx
    · left
      rw [Complex.inv_re]
      apply div_pos hx
      exact Complex.normSq_pos.mpr (fun h => hx.ne' (h ▸ by simp))
    · right
      intro h
      have := Complex.inv_im x
      rw [this] at h
      have h' : x.im = 0 ∨ x = 0 := by simpa using h
      rcases h' with h' | h'
      · exact hx h'
      · simp [h'] at hx
  have hs_arg : |s.arg| < Real.pi / (g : ℝ) := by
    have hs_arg_inner : |Complex.arg (x⁻¹)| < Real.pi := by
      have hs_arg : |Complex.arg x| < Real.pi := by
        cases hx <;> simp_all +decide [ Complex.arg ]
        · split_ifs <;> norm_num [ abs_lt ]
          · constructor <;> linarith [ Real.neg_pi_div_two_le_arcsin ( x.im / ‖x‖ ), Real.arcsin_le_pi_div_two ( x.im / ‖x‖ ), Real.pi_pos ]
          · linarith
          · linarith
        · split_ifs <;> norm_num [ abs_lt ]
          · constructor <;> linarith [ Real.neg_pi_div_two_le_arcsin ( x.im / ‖x‖ ), Real.arcsin_le_pi_div_two ( x.im / ‖x‖ ), Real.pi_pos ]
          · exact ⟨ by linarith [ Real.neg_pi_div_two_le_arcsin ( -x.im / ‖x‖ ), Real.arcsin_le_pi_div_two ( -x.im / ‖x‖ ), Real.pi_pos ], div_neg_of_neg_of_pos ( neg_neg_of_pos ( lt_of_le_of_ne ‹_› ( Ne.symm ‹_› ) ) ) ( norm_pos_iff.mpr ( show x ≠ 0 from by aesop ) ) ⟩
          · exact ⟨ div_pos ( neg_pos.mpr ( lt_of_not_ge ‹_› ) ) ( norm_pos_iff.mpr ( by aesop ) ), by linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( -x.im / ‖x‖ ) ] ⟩
      rw [ Complex.arg_inv ]
      split_ifs <;> simp_all +decide [ abs_lt ]
    have hs_arg_eq : s.arg = Complex.arg (x⁻¹) / (g : ℝ) := by
      change ((x⁻¹) ^ ((g : ℂ)⁻¹)).arg = Complex.arg (x⁻¹) / (g : ℝ)
      convert Complex.arg_mul_cos_add_sin_mul_I _ _ using 2
      rotate_left
      exact ‖x⁻¹‖ ^ ( ( g : ℝ ) ⁻¹ )
      · exact Real.rpow_pos_of_pos ( norm_pos_iff.mpr ( inv_ne_zero hx_ne_zero ) ) _
      · constructor <;> nlinarith [ abs_lt.mp hs_arg_inner, show ( g : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( Complex.arg (x⁻¹) ) ( by positivity : ( g : ℝ ) ≠ 0 ) ]
      · rw [ Complex.cpow_def_of_ne_zero ( inv_ne_zero hx_ne_zero ) ]
        rw [ Complex.log ] ; ring_nf
        rw [ Complex.exp_eq_exp_re_mul_sin_add_cos ] ; norm_num ; ring_nf
        rw [ Real.rpow_def_of_pos ( inv_pos.mpr ( norm_pos_iff.mpr hx_ne_zero ) ) ] ; norm_num ; ring_nf
    rw [ hs_arg_eq, abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ g ) ] ; gcongr
  -- Show s^g = x⁻¹
  have hs_pow : s ^ g = x⁻¹ := by
    rw [← Complex.cpow_nat_mul, mul_comm]
    norm_num [hg_pos.ne']
  -- Let t = ‖s‖
  set t := ‖s‖ with ht_def
  have ht_pos : 0 ≤ t := norm_nonneg s
  have hs_ne_zero : s ≠ 0 := by
    show x⁻¹ ^ (↑g : ℂ)⁻¹ ≠ 0
    rw [Complex.cpow_def_of_ne_zero (inv_ne_zero hx_ne_zero)]
    exact Complex.exp_ne_zero _
  -- When g ∣ N, qIdx g N + 1 = N / g, so (x⁻¹)^(qIdx+1) = s^N
  have h.endpoint_bound : ∀ N : ℕ, ‖(x⁻¹) ^ (qIdx g N + 1)‖ ≤ max 1 t ^ g * t ^ N := by
    intro N
    rw [← hs_pow]
    rw [← pow_mul]
    rw [norm_pow, ht_def]
    have hqIdx : qIdx g N = (N - 1) / g := rfl
    have hg_pos : 0 < g := by linarith
    have h_exp : g * (qIdx g N + 1) ≥ N := by
      simp only [qIdx]
      rcases N with _ | N
      · norm_num
      · simp only [Nat.add_sub_cancel]
        have : g * ((N / g) + 1) = g * (N / g) + g := by ring
        rw [this]
        linarith [Nat.div_add_mod N g, Nat.mod_lt N hg_pos]
    have h_exp2 : g * (qIdx g N + 1) ≤ N + g := by
      simp only [qIdx]
      rcases N with _ | N
      · simp
      · simp only [Nat.add_sub_cancel]
        have : g * ((N / g) + 1) = g * (N / g) + g := by ring
        rw [this]
        linarith [Nat.div_mul_le_self N g, Nat.mod_lt N hg_pos]
    by_cases ht_le_one : t ≤ 1
    · have hmax : max 1 t = 1 := by rw [max_eq_left ht_le_one]
      rw [ht_def] at *
      rw [hmax]
      norm_num
      exact pow_le_pow_of_le_one (norm_nonneg s) ht_le_one h_exp
    · push_neg at ht_le_one
      have h_max : max 1 t = t := by rw [max_eq_right (le_of_lt ht_le_one)]
      rw [ht_def] at *
      rw [h_max]
      have ht_le_one' : 1 ≤ t := le_of_lt ht_le_one
      calc t ^ (g * (qIdx g N + 1)) ≤ t ^ (N + g) := pow_le_pow_right₀ ht_le_one' h_exp2
        _ = t ^ N * t ^ g := by ring
        _ = t ^ g * ‖s‖ ^ N := by rw [ht_def]; ring
  -- We need t < ‖1 + s‖ to get decay. This holds because Re(s) > 0.
  have hs_re_pos : 0 < s.re := by
    have hcos_pos : Real.cos s.arg > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [abs_lt.mp hs_arg, Real.pi_pos, show (g : ℝ) ≥ 2 by norm_cast,
        mul_div_cancel₀ (Real.pi : ℝ) (by positivity : (g : ℝ) ≠ 0)]
    calc 0 < ‖s‖ * Real.cos s.arg := by exact mul_pos (norm_pos_iff.mpr hs_ne_zero) hcos_pos
      _ = s.re := by rw [Complex.norm_mul_cos_arg]
  have hnorm_1s_gt_t : t < ‖1 + s‖ := by
    have h1 : ‖1 + s‖ ^ 2 = 1 + t ^ 2 + 2 * s.re := by
      simp [Complex.normSq_add, Complex.sq_norm, ht_def]
    have h2 : t ^ 2 = ‖s‖ ^ 2 := rfl
    have h3 : ‖1 + s‖ ^ 2 > t ^ 2 := by nlinarith
    nlinarith [norm_nonneg (1 + s)]
  -- Define r = t / ‖1+s‖ < 1
  set r := t / ‖1 + s‖ with hr_def
  have hr_lt_one : r < 1 := by
    have hnorm_pos : 0 < ‖1 + s‖ := by linarith
    rw [hr_def, div_lt_one hnorm_pos]
    exact hnorm_1s_gt_t
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  -- Use squeeze theorem: the norm of the ratio is bounded by C * r^N → 0
  -- Use the filter formula to get a lower bound on the slice
  have h_filter_zero : ∀ N : ℕ, (g : ℂ) * slice g 0 N x⁻¹ = 
      ∑ a ∈ Finset.range g, (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N := by
    intro N
    have hg' : (0 : ℕ) < g := hg_pos
    -- Expand using binomial theorem
    have h_expand : ∑ a ∈ Finset.range g, (1 + s * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))) ^ N = 
        ∑ a ∈ Finset.range g, ∑ j ∈ Finset.range (N + 1), (N.choose j : ℂ) * s ^ j * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * j / (g : ℂ)) := by
      simp +decide [add_comm (1 : ℂ), add_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm, ← Complex.exp_nat_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf
    have h_swap : ∑ a ∈ Finset.range g, ∑ j ∈ Finset.range (N + 1), (N.choose j : ℂ) * s ^ j * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * j / (g : ℂ)) = 
        ∑ j ∈ Finset.range (N + 1), (N.choose j : ℂ) * s ^ j * ∑ a ∈ Finset.range g, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * j / (g : ℂ)) := by
      rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _]
    have h_roots : ∀ j ∈ Finset.range (N + 1), ∑ a ∈ Finset.range g, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * j / (g : ℂ)) = if j % g = 0 then (g : ℂ) else 0 := by
      intro j hj; split_ifs <;> simp_all +decide;
      · obtain ⟨ k, rfl ⟩ := Nat.dvd_of_mod_eq_zero ‹_›; norm_num [ mul_assoc, mul_left_comm, mul_div_cancel₀, hg'.ne' ] ;
        exact Eq.trans ( Finset.sum_congr rfl fun _ _ => by rw [ Complex.exp_eq_one_iff ] ; use k * ‹ℕ›; push_cast; rw [ div_eq_iff ( Nat.cast_ne_zero.mpr hg'.ne' ) ] ; ring ) ( by norm_num )
      · have h_geom_sum : ∑ a ∈ Finset.range g, (Complex.exp (2 * Real.pi * Complex.I * j / g)) ^ a = 0 := by
          rw [ geom_sum_eq ] <;> norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀, hg'.ne' ];
          · exact Or.inl ( sub_eq_zero_of_eq <| Complex.exp_eq_one_iff.mpr ⟨ j, by push_cast; ring ⟩ )
          · rw [ Complex.exp_eq_one_iff ]
            field_simp
            exact fun ⟨ n, hn ⟩ => ‹¬j % g = 0› <| Nat.mod_eq_zero_of_dvd <| Int.natCast_dvd_natCast.mp <| ⟨ n, by rw [ div_eq_iff ( Nat.cast_ne_zero.mpr hg'.ne' ) ] at hn; norm_cast at *; linarith ⟩
        exact Eq.trans ( Finset.sum_congr rfl fun _ _ => by rw [ ← Complex.exp_nat_mul ] ; ring_nf ) h_geom_sum
    simp_all +decide [Finset.sum_ite]
    unfold slice
    simp +decide [Finset.sum_ite]
    rw [Finset.mul_sum _ _ _]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi_dvd : g ∣ i := Nat.dvd_of_mod_eq_zero (Finset.mem_filter.mp hi |>.2)
    have hi_eq : g * (i / g) = i := Nat.mul_div_cancel' hi_dvd
    calc (g : ℂ) * ((N.choose i : ℂ) * (x ^ (i / g))⁻¹) 
        = (g : ℂ) * ((N.choose i : ℂ) * (x⁻¹) ^ (i / g)) := by simp
      _ = (g : ℂ) * ((N.choose i : ℂ) * (s ^ g) ^ (i / g)) := by rw [hs_pow]
      _ = (g : ℂ) * ((N.choose i : ℂ) * s ^ (g * (i / g))) := by rw [pow_mul]
      _ = (g : ℂ) * ((N.choose i : ℂ) * s ^ i) := by rw [hi_eq]
      _ = (N.choose i : ℂ) * s ^ i * (g : ℂ) := by ring
  -- epsIdx is bounded by 1
  have h_eps_bound : ∀ N : ℕ, ‖(epsIdx g N : ℂ)‖ ≤ 1 := by
    intro N
    simp [epsIdx]
    split_ifs <;> norm_num
  -- epsIdx = 0 when g ∤ N, so we only care about g ∣ N
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  -- We'll use squeeze theorem: numerator ≤ C * t^N and denominator ≥ c * ‖1+s‖^N
  -- First, simplify the norm of the ratio
  suffices h : Filter.Tendsto (fun N : ℕ => ‖(epsIdx g N : ℂ)‖ * ‖(x⁻¹) ^ (qIdx g N + 1)‖ / ‖slice g 0 N x⁻¹‖) Filter.atTop (nhds 0) by
    convert h using 1
    ext N
    simp
  -- Bound the numerator
  have hnum_bound : ∀ N : ℕ, ‖(epsIdx g N : ℂ)‖ * ‖(x⁻¹) ^ (qIdx g N + 1)‖ ≤ max 1 t ^ g * t ^ N := by
    intro N
    calc ‖(epsIdx g N : ℂ)‖ * ‖(x⁻¹) ^ (qIdx g N + 1)‖ 
        ≤ 1 * (max 1 t ^ g * t ^ N) := by
          apply mul_le_mul (h_eps_bound N) (h.endpoint_bound N) (by positivity) (by positivity)
      _ = max 1 t ^ g * t ^ N := by ring
  -- For the denominator, use triangle inequality on h_filter_zero
  -- The dominant term is (1+s)^N, others are smaller
  set ω := fun a : ℕ => Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ))
  -- ‖1 + s * ω^a‖ < ‖1+s‖ for a ≠ 0 (mod g)
  have hdom : ∀ a : ℕ, a ∈ Finset.range g \ {0} → ‖1 + s * ω a‖ < ‖1 + s‖ := by
    intro a ha
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at ha
    have := norm_one_add_root_mul_lt hg_pos (by norm_cast; exact ha.2) ha.1 hs_ne_zero hs_arg
    convert this using 2
    simp [ω]
    ring
  -- Let M = max of ‖1 + s * ω a‖ for a ∈ {1, ..., g-1}
  have hN : ∀ N, (g : ℂ) * slice g 0 N x⁻¹ = 
      ∑ a ∈ Finset.range g, (1 + s * ω a) ^ N := fun N => h_filter_zero N
  set M := sSup { ‖1 + s * ω a‖ | a ∈ Finset.range g \ {0} } with hM_def
  have hM_lt : M < ‖1 + s‖ := by
    rw [hM_def]
    have hne : Set.Nonempty { ‖1 + s * ω a‖ | a ∈ Finset.range g \ {0} } := by
      use ‖1 + s * ω 1‖
      exact ⟨1, by norm_num; linarith, rfl⟩
    have hbdd : BddAbove { ‖1 + s * ω a‖ | a ∈ Finset.range g \ {0} } := by
      use ‖1 + s‖
      intro y hy
      rcases hy with ⟨ a, ha, rfl ⟩
      exact le_of_lt (hdom a ha)
    have hfin : ({ ‖1 + s * ω a‖ | a ∈ Finset.range g \ {0} } : Set ℝ).Finite := by
      apply Set.Finite.subset (Finset.finite_toSet (Finset.image (fun a => ‖1 + s * ω a‖) (Finset.range g \ {0})))
      simp [Set.subset_def]
    have ⟨a, ha, ha_max⟩ : ∃ a ∈ Finset.range g \ {0}, ∀ b ∈ Finset.range g \ {0}, ‖1 + s * ω a‖ ≥ ‖1 + s * ω b‖ := by
      have h1in : (1 : ℕ) ∈ Finset.range g \ {0} := by norm_num; linarith
      have hnefin : (Finset.range g \ {0}).Nonempty := ⟨1, h1in⟩
      have := Finset.exists_max_image (Finset.range g \ {0}) (fun a => ‖1 + s * ω a‖) hnefin
      exact this
    have hIsGreatest : IsGreatest { ‖1 + s * ω a‖ | a ∈ Finset.range g \ {0} } ‖1 + s * ω a‖ := by
      constructor
      · exact ⟨a, ha, rfl⟩
      · intro y hy
        rcases hy with ⟨ b, hb, rfl ⟩
        exact ha_max b hb
    rw [hIsGreatest.csSup_eq]
    exact hdom a ha
  have hM_nonneg : 0 ≤ M := by
    rw [hM_def]
    apply Real.sSup_nonneg
    intro y hy
    rcases hy with ⟨ a, ha, rfl ⟩
    exact norm_nonneg _
  -- For all a in range g, ‖1 + s * ω a‖ ≤ max(‖1+s‖, M) = ‖1+s‖
  have h_all_bound : ∀ a ∈ Finset.range g, ‖1 + s * ω a‖ ≤ ‖1 + s‖ := by
    intro a ha
    by_cases ha0 : a = 0
    · simp [ha0, ω, Complex.exp_zero]
    · exact le_of_lt (hdom a (by simpa [ha0] using ha))
  -- Lower bound on denominator using reverse triangle inequality
  have hdenom_lower : ∀ N : ℕ, ‖slice g 0 N x⁻¹‖ ≥ (‖1 + s‖ ^ N - (g - 1) * M ^ N) / g := by
    intro N
    have hsum := h_filter_zero N
    -- Split the sum: a = 0 term plus a ≠ 0 terms
    have hsplit : ∑ a ∈ Finset.range g, (1 + s * ω a) ^ N = 
        (1 + s) ^ N + ∑ a ∈ (Finset.range g \ {0}), (1 + s * ω a) ^ N := by
      rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_range.mpr hg_pos)]
      simp [ω, Complex.exp_zero]
    rw [hsplit] at hsum
    -- Take norms and use triangle inequality
    have hnorm_triangle : ‖(1 + s) ^ N + ∑ a ∈ (Finset.range g \ {0}), (1 + s * ω a) ^ N‖ ≥ 
        ‖(1 + s) ^ N‖ - ‖∑ a ∈ (Finset.range g \ {0}), (1 + s * ω a) ^ N‖ := by
      have h := norm_sub_le ((1 + s) ^ N + ∑ a ∈ (Finset.range g \ {0}), (1 + s * ω a) ^ N) (∑ a ∈ (Finset.range g \ {0}), (1 + s * ω a) ^ N)
      simp at h
      rw [norm_pow]
      linarith
    have hg_eq : ‖(g : ℂ) * slice g 0 N x⁻¹‖ = ‖(1 + s) ^ N + ∑ a ∈ (Finset.range g \ {0}), (1 + s * ω a) ^ N‖ := by
      rw [← hsum]
    have h1 : ‖(g : ℂ) * slice g 0 N x⁻¹‖ = g * ‖slice g 0 N x⁻¹‖ := by
      rw [norm_mul, Complex.norm_natCast]
    have h2 : ‖(1 + s) ^ N‖ = ‖1 + s‖ ^ N := norm_pow _ _
    have h3 : ‖∑ a ∈ (Finset.range g \ {0}), (1 + s * ω a) ^ N‖ ≤ 
        ∑ a ∈ (Finset.range g \ {0}), ‖1 + s * ω a‖ ^ N := by
      convert norm_sum_le _ _ using 2
      exact (norm_pow _ _).symm
    have hM_bdd : BddAbove { ‖1 + s * ω a‖ | a ∈ Finset.range g \ {0} } := by
      use ‖1 + s‖
      intro y hy
      rcases hy with ⟨ a, ha, rfl ⟩
      exact le_of_lt (hdom a ha)
    have h1_mem : (1 : ℕ) ∈ Finset.range g \ {0} := by
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
      exact ⟨by linarith, by norm_num⟩
    have h_le_M : ∀ a ∈ Finset.range g \ {0}, ‖1 + s * ω a‖ ≤ M := by
      intro a ha
      rw [hM_def]
      exact le_csSup hM_bdd ⟨a, ha, rfl⟩
    have h4 : ∑ a ∈ (Finset.range g \ {0}), ‖1 + s * ω a‖ ^ N ≤ (g - 1) * M ^ N := by
      apply le_trans (Finset.sum_le_sum fun a ha => pow_le_pow_left₀ (norm_nonneg _) 
        (h_le_M a ha) _) _
      simp [Finset.card_sdiff, hg_pos]
    calc ‖slice g 0 N x⁻¹‖ = ‖slice g 0 N x⁻¹‖ := rfl
      _ = g * ‖slice g 0 N x⁻¹‖ / g := by rw [mul_div_cancel_left₀ _ (by positivity)]
      _ = ‖(g : ℂ) * slice g 0 N x⁻¹‖ / g := by rw [h1]
      _ = ‖(1 + s) ^ N + ∑ a ∈ (Finset.range g \ {0}), (1 + s * ω a) ^ N‖ / g := by rw [hg_eq]
      _ ≥ (‖(1 + s) ^ N‖ - ‖∑ a ∈ (Finset.range g \ {0}), (1 + s * ω a) ^ N‖) / g := by
          apply div_le_div_of_nonneg_right hnorm_triangle (by positivity)
      _ = (‖1 + s‖ ^ N - ‖∑ a ∈ (Finset.range g \ {0}), (1 + s * ω a) ^ N‖) / g := by rw [h2]
      _ ≥ (‖1 + s‖ ^ N - (g - 1) * M ^ N) / g := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply sub_le_sub_left
          exact le_trans h3 h4
  -- Since M < ‖1+s‖, we have (g-1) * M^N / ‖1+s‖^N → 0
  -- So for large N, ‖1+s‖^N - (g-1) * M^N ≥ (1/2) * ‖1+s‖^N
  have hM_ltNorm : M < ‖1 + s‖ := hM_lt
  have hM_nonneg' : 0 ≤ M := hM_nonneg
  have hnorm_1s_pos : 0 < ‖1 + s‖ := by linarith [hM_nonneg']
  -- Use that (M / ‖1+s‖)^N → 0
  have hratio_zero : Filter.Tendsto (fun N => (g - 1 : ℝ) * (M / ‖1 + s‖) ^ N) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => (M / ‖1 + s‖) ^ N) Filter.atTop (nhds 0) := 
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by rwa [div_lt_one hnorm_1s_pos])
    simpa using h1.const_mul (g - 1 : ℝ)
  -- Get a constant C > 0 and N₀ such that for N ≥ N₀, denominator ≥ C * ‖1+s‖^N
  have hdenom_eventually : ∃ C > 0, ∀ᶠ N in Filter.atTop, 
      ‖slice g 0 N x⁻¹‖ ≥ C * ‖1 + s‖ ^ N := by
    -- (g-1) * (M/‖1+s‖)^N → 0, so eventually < 1/2
    have h_eventually : ∀ᶠ N in Filter.atTop, (g - 1 : ℝ) * (M / ‖1 + s‖) ^ N < 1/2 := by
      exact hratio_zero.eventually (gt_mem_nhds (by norm_num))
    use (1/4 : ℝ) / g
    constructor
    · positivity
    · filter_upwards [h_eventually] with N hN
      have hdenom_bound := hdenom_lower N
      have hpos : (0 : ℝ) < ‖1 + s‖ := hnorm_1s_pos
      have h1 : (‖1 + s‖ ^ N - (g - 1) * M ^ N) / g = (1 - (g-1) * (M/‖1+s‖)^N) * ‖1+s‖ ^ N / g := by
        rw [div_pow]
        field_simp
      rw [h1] at hdenom_bound
      have h2 : 1 - (g-1) * (M/‖1+s‖)^N > 1/2 := by linarith
      calc ‖slice g 0 N x⁻¹‖ ≥ (1 - (g-1) * (M/‖1+s‖)^N) * ‖1+s‖ ^ N / g := hdenom_bound
        _ ≥ (1/2) * ‖1+s‖ ^ N / g := by gcongr
        _ ≥ (1/4 : ℝ) / g * ‖1+s‖ ^ N := by
            ring_nf
            have hpos' : 0 ≤ ‖1 + s‖ ^ N * (↑g)⁻¹ := by positivity
            linarith
  obtain ⟨C, hC_pos, hC_eventually⟩ := hdenom_eventually
  -- Squeeze: ratio ≤ (max 1 t ^ g * t^N) / (C * ‖1+s‖^N) = (max 1 t ^ g / C) * r^N
  have hratio_zero' : Filter.Tendsto (fun N => r ^ N) Filter.atTop (nhds 0) := 
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one
  refine squeeze_zero_norm' ?_ (by simpa using hratio_zero'.const_mul (max 1 t ^ g / C))
  filter_upwards [hC_eventually] with N hN
  have h1 : ‖(epsIdx g N : ℂ)‖ * ‖(x⁻¹) ^ (qIdx g N + 1)‖ / ‖slice g 0 N x⁻¹‖ ≤ 
            max 1 t ^ g * t ^ N / (C * ‖1 + s‖ ^ N) := by
    have hdenom_pos : 0 < ‖slice g 0 N x⁻¹‖ := by
      have : 0 < C * ‖1 + s‖ ^ N := by positivity
      linarith
    have hdenom_min_pos : 0 < C * ‖1 + s‖ ^ N := by positivity
    calc ‖(epsIdx g N : ℂ)‖ * ‖(x⁻¹) ^ (qIdx g N + 1)‖ / ‖slice g 0 N x⁻¹‖ 
        ≤ ‖(epsIdx g N : ℂ)‖ * ‖(x⁻¹) ^ (qIdx g N + 1)‖ / (C * ‖1 + s‖ ^ N) := by
          apply div_le_div_of_nonneg_left _ hdenom_min_pos hN
          exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      _ ≤ max 1 t ^ g * t ^ N / (C * ‖1 + s‖ ^ N) := by
          apply div_le_div_of_nonneg_right (hnum_bound N) (le_of_lt hdenom_min_pos)
  have h2 : max 1 t ^ g * t ^ N / (C * ‖1 + s‖ ^ N) = (max 1 t ^ g / C) * r ^ N := by
    rw [hr_def]
    rw [div_pow]
    field_simp [hnorm_1s_pos.ne']
  rw [h2] at h1
  convert h1 using 1
  exact Real.norm_of_nonneg (by positivity)


/- Target 4 (priority result): the pointwise paper theorem for the actual
reversed approximant, with the principal complex power and the k = 0
cancellation represented faithfully. -/
theorem tendsto_reversed_ratio_cpow {g k : ℕ} (hg : 0 < g) (hk : k < g)
    {x : ℂ} (hx : x ∈ Complex.slitPlane) :
    Filter.Tendsto
      (fun N : ℕ => reversedRatioComplex g k N x)
      Filter.atTop (nhds (x ^ ((k : ℂ) / (g : ℂ)))) := by
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hg2 : 2 ≤ g := Nat.lt_of_le_of_ne hg (Ne.symm (by omega : g ≠ 1))
    unfold reversedRatioComplex
    simp [hk0]
    have hx_ne : x ≠ 0 := Complex.slitPlane_ne_zero hx
    have hx_pow_ne : ∀ N : ℕ, x ^ ResidueSlices.qIdx g N ≠ 0 := fun N => pow_ne_zero _ hx_ne
    -- The ratio simplifies after applying revAComplex_eq_slice and revBComplex_eq_slice
    have h_eq : (fun N => revAComplex g k N x / revAComplex g 0 N x) =ᶠ[Filter.atTop]
        (fun N => slice g k N x⁻¹ / (slice g 0 N x⁻¹ - epsIdx g N * (x⁻¹) ^ (ResidueSlices.qIdx g N + 1))) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      rw [revAComplex_eq_slice hg (Nat.one_le_iff_ne_zero.mpr hk0) hk hx_ne]
      rw [revBComplex_eq_slice hg hN hx_ne]
      rw [mul_comm, mul_comm (x ^ ResidueSlices.qIdx g N)]
      rw [mul_div_mul_right _ _ (hx_pow_ne N)]
    refine Filter.Tendsto.congr' h_eq.symm ?_
    -- Use tendsto_slice_ratio_cpow for the slice ratio
    have h_slice_ratio := tendsto_slice_ratio_cpow hg hk hx
    -- Use tendsto_endpointCorrection_cpow for the vanishing correction
    have h_endpoint := tendsto_endpointCorrection_cpow hg2 hx
    -- Rewrite the expression as (slice k / slice 0) / (1 - endpoint_cor/slice 0)
    have h_factor : (fun N => slice g k N x⁻¹ / (slice g 0 N x⁻¹ - epsIdx g N * (x⁻¹) ^ (ResidueSlices.qIdx g N + 1))) =ᶠ[Filter.atTop]
        (fun N => (slice g k N x⁻¹ / slice g 0 N x⁻¹) / (1 - epsIdx g N * (x⁻¹) ^ (ResidueSlices.qIdx g N + 1) / slice g 0 N x⁻¹)) := by
      have h_eq' : ∀ᶠ N in Filter.atTop, slice g 0 N x⁻¹ ≠ 0 := by
        have hlim_ne : x ^ ((k : ℂ) / (g : ℂ)) ≠ 0 := by
          have hx' := Complex.slitPlane_ne_zero hx
          rw [Complex.cpow_def_of_ne_zero hx']
          exact Complex.exp_ne_zero _
        have h_ratio_ne : ∀ᶠ N in Filter.atTop, slice g k N x⁻¹ / slice g 0 N x⁻¹ ≠ 0 := by
          exact h_slice_ratio.eventually_ne hlim_ne
        filter_upwards [h_ratio_ne] with N hN
        intro h_denom_zero
        simp [h_denom_zero] at hN
      filter_upwards [h_eq'] with N hN
      field_simp [hN]
    refine Filter.Tendsto.congr' h_factor.symm ?_
    -- Denominator tends to 1 - 0 = 1
    have h_denom : Filter.Tendsto (fun N => 1 - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N x⁻¹) Filter.atTop (nhds 1) := by
      simpa using Filter.Tendsto.const_sub 1 h_endpoint
    -- Use tendsto_div
    have := Filter.Tendsto.div h_slice_ratio h_denom (by norm_num : (1 : ℂ) ≠ 0)
    simpa using this




/- Target 5: compact-uniform strengthening of the already proved forward
slice theorem.  This is precisely uniform convergence on an arbitrary compact
subset of the slit plane. -/
theorem tendstoUniformlyOn_slice_ratio_cpow {g k : ℕ}
    (hg : 0 < g) (hk : k < g) {K : Set ℂ}
    (hK : IsCompact K) (hKslit : K ⊆ Complex.slitPlane) :
    TendstoUniformlyOn
      (fun N x => slice g k N x⁻¹ / slice g 0 N x⁻¹)
      (fun x => x ^ ((k : ℂ) / (g : ℂ)))
      Filter.atTop K := by
  -- Define the complex spectral gap
  let complexSpectralGap (s : ℂ) : ℝ :=
    let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (g : ℂ))
    let channels := (Finset.range g \ {0}).image (fun a => ‖1 + s * ω ^ a‖ / ‖1 + s‖)
    (insert 0 channels).max' ⟨0, Finset.mem_insert_self 0 channels⟩
  -- ω is a primitive g-th root of unity
  let ω := Complex.exp (2 * Real.pi * Complex.I / (g : ℂ))
  have hω : IsPrimitiveRoot ω g := Complex.isPrimitiveRoot_exp g hg.ne'
  -- For x in slit plane, s = (x⁻¹)^(1/g) has |arg s| < π/g and s ≠ 0
  let sFn : ℂ → ℂ := fun x => (x⁻¹) ^ ((g : ℂ)⁻¹)
  have ne_zero_of_slitPlane : ∀ x ∈ Complex.slitPlane, x ≠ 0 := by
    intro x hx
    simp [Complex.slitPlane] at hx
    rcases hx with hx | hx <;> intro rfl <;> simp_all
  have inv_slitPlane : ∀ x ∈ Complex.slitPlane, x⁻¹ ∈ Complex.slitPlane := by
    intro x hx
    simp only [Complex.slitPlane] at hx ⊢
    have hne : x ≠ 0 := ne_zero_of_slitPlane x hx
    have hnormSq_pos : 0 < Complex.normSq x := Complex.normSq_pos.mpr hne
    rcases hx with hx | hx <;> [left;right]
    · simp [Complex.inv_re]; exact div_pos hx hnormSq_pos
    · rw [Complex.inv_im]; exact div_ne_zero (neg_ne_zero.mpr hx) (ne_of_gt hnormSq_pos)
  have hsFn_cont : ContinuousOn sFn K := by
    apply ContinuousOn.cpow
    · exact continuousOn_id.inv₀ fun x hx => ne_zero_of_slitPlane x (hKslit hx)
    · exact continuousOn_const
    · intro x hx
      have h := inv_slitPlane x (hKslit hx)
      simp only [Complex.slitPlane, Set.mem_setOf_eq] at h ⊢
      exact h
  -- The image of K under sFn is compact
  let imageK := sFn '' K
  have himageK_compact : IsCompact imageK := hK.image_of_continuousOn hsFn_cont
  -- All elements of imageK give s ≠ 0 and |arg s| < π/g, so spectral gap < 1 pointwise
  have hs_in_slit : ∀ s ∈ imageK, s ≠ 0 ∧ |s.arg| < Real.pi / (g : ℝ) := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := hs
    have hslit := inv_slitPlane x (hKslit hx)
    have hx_ne : x ≠ 0 := ne_zero_of_slitPlane x (hKslit hx)
    have hs_pow : ((x⁻¹) ^ ((g : ℂ)⁻¹)) ^ g = x⁻¹ := by
      rw [ ← Complex.cpow_nat_mul, mul_comm ] ; norm_num [ hg.ne' ]
    refine ⟨?_, ?_⟩
    · aesop
    · have harg_x : |Complex.arg x| < Real.pi := by
        have hxslit := hKslit hx
        simp only [Complex.slitPlane, Set.mem_setOf_eq] at hxslit
        cases hxslit <;> simp_all +decide [Complex.arg]
        · split_ifs <;> norm_num [ abs_lt ];
          · constructor <;> linarith [ Real.neg_pi_div_two_le_arcsin ( x.im / ‖x‖ ), Real.arcsin_le_pi_div_two ( x.im / ‖x‖ ), Real.pi_pos ];
          · linarith;
          · linarith;
        · split_ifs <;> norm_num [ abs_lt ];
          · constructor <;> linarith [ Real.neg_pi_div_two_le_arcsin ( x.im / ‖x‖ ), Real.arcsin_le_pi_div_two ( x.im / ‖x‖ ), Real.pi_pos ];
          · exact ⟨ by linarith [ Real.neg_pi_div_two_le_arcsin ( -x.im / ‖x‖ ), Real.arcsin_le_pi_div_two ( -x.im / ‖x‖ ), Real.pi_pos ], div_neg_of_neg_of_pos ( neg_neg_of_pos ( lt_of_le_of_ne ‹_› ( Ne.symm ‹_› ) ) ) ( norm_pos_iff.mpr ( show x ≠ 0 from by aesop ) ) ⟩;
          · exact ⟨ div_pos ( neg_pos.mpr ( lt_of_not_ge ‹_› ) ) ( norm_pos_iff.mpr ( by aesop ) ), by linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( -x.im / ‖x‖ ) ] ⟩
      have harg_inv : |Complex.arg (x⁻¹)| < Real.pi := by
        rw [Complex.arg_inv]
        split_ifs <;> simp_all +decide [abs_lt]
      have hs_arg_eq : Complex.arg ((x⁻¹) ^ ((g : ℂ)⁻¹)) = Complex.arg (x⁻¹) / (g : ℝ) := by
        convert Complex.arg_mul_cos_add_sin_mul_I _ _ using 2
        rotate_left
        · exact ‖x⁻¹‖ ^ ((g : ℝ)⁻¹)
        · exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hx_ne)) _
        · constructor <;> nlinarith [abs_lt.mp harg_inv, show (g : ℝ) ≥ 1 by norm_cast, mul_div_cancel₀ (Complex.arg (x⁻¹)) (by positivity : (g : ℝ) ≠ 0)]
        · rw [Complex.cpow_def_of_ne_zero (inv_ne_zero hx_ne)]
          rw [Complex.log] ; ring_nf
          rw [Complex.exp_eq_exp_re_mul_sin_add_cos] ; norm_num ; ring_nf
          rw [Real.rpow_def_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx_ne))] ; norm_num ; ring_nf
      rw [hs_arg_eq, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g)]
      gcongr
  -- The channel ratios are all < 1 for s in imageK
  have hchannel_lt_one : ∀ s ∈ imageK, ∀ a ∈ Finset.range g \ {0}, ‖1 + s * ω ^ a‖ / ‖1 + s‖ < 1 := by
    intro s hs a ha
    have ⟨hs_ne, hs_arg⟩ := hs_in_slit s hs
    have ha' := Finset.mem_sdiff.mp ha
    have ha_lt := Finset.mem_range.mp ha'.1
    rw [div_lt_one]
    · have ha0 := Finset.mem_singleton.not.mp ha'.2
      have heq : ω ^ a = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (g : ℂ)) := by
        rw [← Complex.exp_nat_mul]
        field_simp
      simp only [heq]
      simpa [mul_comm] using norm_one_add_root_mul_lt hg ha0 ha_lt hs_ne hs_arg
    · have hne : (1 + s) ≠ 0 := by
        by_contra h
        have : s = -1 := by linear_combination h
        rw [this] at hs_arg
        simp only [Complex.arg_neg_one, abs_of_nonneg Real.pi_pos.le] at hs_arg
        exact not_le.mpr hs_arg (div_le_self Real.pi_pos.le (by norm_cast))
      exact norm_pos_iff.mpr hne
  -- For nonempty K, get uniform bound ρ < 1
  by_cases hK_nonempty : K.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hK_nonempty
    have himage_nonempty : imageK.Nonempty := ⟨sFn x₀, Set.mem_image_of_mem _ hx₀⟩
    -- Show 1 + s ≠ 0 for s ∈ imageK
    have h1_plus_s_ne_zero : ∀ s ∈ imageK, (1 + s) ≠ 0 := by
      intro s hs
      have ⟨hs_ne, hs_arg⟩ := hs_in_slit s hs
      intro h
      have : s = -1 := by linear_combination h
      rw [this] at hs_arg
      simp only [Complex.arg_neg_one, abs_of_nonneg Real.pi_pos.le] at hs_arg
      exact not_le.mpr hs_arg (div_le_self Real.pi_pos.le (by norm_cast))
    -- Channel ratios are continuous on imageK
    have hchannel_cont : ∀ a < g, a ≠ 0 → ContinuousOn (fun s : ℂ => ‖1 + s * ω ^ a‖ / ‖1 + s‖) imageK := fun a _ _ =>
      ContinuousOn.div (Continuous.norm (continuous_const.add (continuous_id.mul continuous_const))).continuousOn
        (Continuous.norm (continuous_const.add continuous_id)).continuousOn
        (fun s hs => norm_ne_zero_iff.mpr (h1_plus_s_ne_zero s hs))
    -- The spectral gap function is continuous on imageK
    have hcomplexSpectralGap_cont : ContinuousOn (fun s : ℂ => complexSpectralGap s) imageK := by
      refine' ContinuousOn.congr _ _
      exact fun s => (Insert.insert 0 ((Finset.range g \ {0}).image fun a => ‖1 + s * ω ^ a‖ / ‖1 + s‖)).max' ⟨0, Finset.mem_insert_self 0 _⟩
      · intro s hs
        refine' tendsto_order.2 ⟨ _, _ ⟩
        · intro a' ha'
          simp_all +decide [Finset.max']
          rcases ha' with ( ha' | ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ )
          · exact Or.inl ha'
          · refine' Or.inr _
            have h_cont : Filter.Tendsto (fun x : ℂ => ‖1 + x * ω ^ a‖ / ‖1 + x‖) (nhdsWithin s imageK) (nhds (‖1 + s * ω ^ a‖ / ‖1 + s‖)) :=
              Filter.Tendsto.div ( ContinuousAt.continuousWithinAt (by exact ContinuousAt.norm <| ContinuousAt.add continuousAt_const <| ContinuousAt.mul continuousAt_id <| continuousAt_const) )
                ( ContinuousAt.continuousWithinAt (by exact ContinuousAt.norm <| ContinuousAt.add continuousAt_const continuousAt_id) )
                ( norm_ne_zero_iff.mpr (h1_plus_s_ne_zero s hs) )
            filter_upwards [ h_cont.eventually ( lt_mem_nhds ha₃ ) ] with x hx using ⟨ a, ⟨ ha₁, ha₂ ⟩, hx ⟩
        · intro a' ha'
          simp_all +decide [Finset.max']
          -- Each channel function is continuous at s
          have h_cont_at : ∀ x < g, x ≠ 0 → ContinuousAt (fun b : ℂ => ‖1 + b * ω ^ x‖ / ‖1 + b‖) s := fun x hx_lt hx_ne =>
            ContinuousAt.div ( ContinuousAt.norm <| ContinuousAt.add continuousAt_const <| ContinuousAt.mul continuousAt_id <| continuousAt_const )
              ( ContinuousAt.norm <| ContinuousAt.add continuousAt_const continuousAt_id )
              ( norm_ne_zero_iff.mpr <| h1_plus_s_ne_zero s hs )
          -- Get ε for each channel
          have h_exists_eps : ∀ x < g, x ≠ 0 → ∃ ε > 0, ∀ b, dist b s < ε → ‖1 + b * ω ^ x‖ / ‖1 + b‖ < a' := by
            intro x hx_lt hx_ne
            have hchan_at_s : ‖1 + s * ω ^ x‖ / ‖1 + s‖ < a' := ha'.2 _ x hx_lt hx_ne rfl
            exact Metric.mem_nhds_iff.mp ( ContinuousAt.preimage_mem_nhds ( h_cont_at x hx_lt hx_ne ) ( Iio_mem_nhds hchan_at_s ) )
          choose! ε hε₁ hε₂ using h_exists_eps
          -- Choose ε to be the minimum of the ε_x's.
          by_cases h_empty : Finset.filter (fun x => x ≠ 0) (Finset.range g) = ∅
          · simp_all +decide
          · obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ Finset.filter (fun x => x ≠ 0) (Finset.range g), ∀ x ∈ Finset.filter (fun x => x ≠ 0) (Finset.range g), ε x₀ ≤ ε x := by
              exact Finset.exists_min_image _ _ ( Finset.nonempty_of_ne_empty h_empty )
            have hx₀_valid : x₀ < g ∧ x₀ ≠ 0 := by simpa [Finset.mem_filter] using hx₀.1
            have hε₀_pos : ε x₀ > 0 := hε₁ x₀ hx₀_valid.1 hx₀_valid.2
            filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds s hε₀_pos)] with b hb₁ hb₂ a x hx_lt hx_ne hx_eq
            have hdist : dist b s < ε x₀ := hb₂.out
            have hx₀_le : ε x₀ ≤ ε x := hx₀.2 x (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx_lt, hx_ne⟩)
            exact hx_eq ▸ hε₂ x hx_lt hx_ne b (hdist.trans_le hx₀_le)
      · intro s hs
        rfl
    -- Use compactness to find max spectral gap
    obtain ⟨s₀, hs₀⟩ := IsCompact.exists_isMaxOn himageK_compact himage_nonempty hcomplexSpectralGap_cont
    -- The spectral gap is < 1 for each s in imageK
    have hspectral_lt_one : ∀ s ∈ imageK, complexSpectralGap s < 1 := by
      intro s hs
      simp only [complexSpectralGap]
      simp_all +decide [Finset.max']
      exact fun a x hx hx' hx'' => hx''.symm ▸ hchannel_lt_one s hs x hx hx'
    have hρ_lt_one : complexSpectralGap s₀ < 1 := hspectral_lt_one s₀ hs₀.1
    -- We need a complex version of the explicit rate theorem
    -- Define a complex packet principal deviation lemma
    have hpacket_complex : ∀ N : ℕ, ∀ s ∈ imageK,
        ‖(g : ℂ) * s ^ k * slice g k N (s ^ g) - (1 + s) ^ N‖ ≤
          ((g : ℝ) - 1) * complexSpectralGap s ^ N * ‖1 + s‖ ^ N := by
      intro N s hs
      have hω : IsPrimitiveRoot ω g := hω
      -- Use roots_of_unity_filter for complex s
      have hfilter := roots_of_unity_filter (N := N) hg hk hω s
      -- Split the sum: the a=0 term gives (1+s)^N
      have h0 : (0 : ℕ) ∈ Finset.range g := Finset.mem_range.mpr hg
      rw [← Finset.add_sum_erase _ _ h0] at hfilter
      simp only [pow_zero, mul_one] at hfilter
      -- From hfilter: (1+s)^N + ∑_{a≠0} ... = g * s^k * slice k
      -- So: g * s^k * slice k - (1+s)^N = ∑_{a≠0} ...
      have hdiff : (g : ℂ) * s ^ k * slice g k N (s ^ g) - (1 + s) ^ N =
          ∑ a ∈ (Finset.range g).erase 0, ω ^ (a * (g - k)) * (1 + s * ω ^ a) ^ N := by
        linear_combination -hfilter
      rw [hdiff]
      refine le_trans (norm_sum_le _ _) ?_
      -- Bound each term
      have hterm : ∀ a ∈ (Finset.range g).erase 0,
          ‖ω ^ (a * (g - k)) * (1 + s * ω ^ a) ^ N‖ ≤
            complexSpectralGap s ^ N * ‖1 + s‖ ^ N := by
        intro a ha
        obtain ⟨ha0, harange⟩ := Finset.mem_erase.mp ha
        have h1 : ‖ω ^ (a * (g - k))‖ = 1 := by
          rw [norm_pow, hω.norm'_eq_one hg.ne', one_pow]
        rw [norm_mul, h1, one_mul, norm_pow]
        -- Need: ‖1 + s * ω ^ a‖ ≤ complexSpectralGap s * ‖1 + s‖
        have hchan : ‖1 + s * ω ^ a‖ / ‖1 + s‖ ≤ complexSpectralGap s := by
          simp only [complexSpectralGap]
          have hmem : (‖1 + s * ω ^ a‖ / ‖1 + s‖) ∈ Insert.insert 0 ((Finset.range g \ {0}).image fun a => ‖1 + s * ω ^ a‖ / ‖1 + s‖) :=
            Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_sdiff.mpr ⟨harange, by simpa using ha0⟩, rfl⟩)
          exact Finset.le_max' _ _ hmem
        have hpos : 0 < ‖1 + s‖ := norm_pos_iff.mpr (h1_plus_s_ne_zero s hs)
        have hchan' : ‖1 + s * ω ^ a‖ ≤ complexSpectralGap s * ‖1 + s‖ := by
          rwa [div_le_iff₀ hpos] at hchan
        calc ‖1 + s * ω ^ a‖ ^ N ≤ (complexSpectralGap s * ‖1 + s‖) ^ N := pow_le_pow_left₀ (norm_nonneg _) hchan' N
          _ = complexSpectralGap s ^ N * ‖1 + s‖ ^ N := mul_pow (complexSpectralGap s) (‖1 + s‖) N
      refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hg), Finset.card_range, nsmul_eq_mul]
      rw [Nat.cast_sub hg, Nat.cast_one, mul_assoc]
    -- Get uniform spectral gap bound ρ < 1
    have hρ_uniform : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ s ∈ imageK, complexSpectralGap s ≤ ρ := by
      use complexSpectralGap s₀
      have h0_in_set : (0 : ℝ) ∈ Insert.insert 0 ((Finset.range g \ {0}).image fun a => ‖1 + s₀ * ω ^ a‖ / ‖1 + s₀‖) :=
        Finset.mem_insert_self 0 _
      have h_nonneg : 0 ≤ complexSpectralGap s₀ := by
        unfold complexSpectralGap
        simp only
        exact Finset.le_max' _ _ h0_in_set
      exact ⟨h_nonneg, hρ_lt_one, hs₀.2⟩
    -- Extract the bound and define auxiliary quantities
    obtain ⟨ρ, hρ_nonneg, hρ_lt_one, hρ_uniform_bound⟩ := hρ_uniform
    -- Find N₀ such that for N ≥ N₀, (g-1) * ρ^N ≤ 1/2
    have h_lim : Filter.Tendsto (fun N => (g - 1 : ℝ) * ρ ^ N) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one hρ_nonneg hρ_lt_one )
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (h_lim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1/2)))
    -- s^g = x⁻¹ for x ∈ K, so slice on s^g = slice on x⁻¹
    have hs_pow : ∀ x ∈ K, (sFn x) ^ g = x⁻¹ := by
      intro x hx
      rw [← Complex.cpow_nat_mul, mul_comm]; norm_num [hg.ne']
    -- We need a lower bound on ‖1 + s‖ for s ∈ imageK
    have h1_plus_s_bounded_below : ∃ c > 0, ∀ s ∈ imageK, ‖1 + s‖ ≥ c := by
      have hcont : ContinuousOn (fun s : ℂ => ‖1 + s‖) imageK := by
        exact ContinuousOn.norm (ContinuousOn.add continuousOn_const continuousOn_id)
      obtain ⟨s_min, hs_min⟩ := IsCompact.exists_isMinOn himageK_compact himage_nonempty hcont
      exact ⟨‖1 + s_min‖, norm_pos_iff.mpr (h1_plus_s_ne_zero s_min hs_min.1), hs_min.2⟩
    -- We need an upper bound on ‖1 + s‖ for s ∈ imageK
    have h1_plus_s_bounded_above : ∃ C > 0, ∀ s ∈ imageK, ‖1 + s‖ ≤ C := by
      have hcont : ContinuousOn (fun s : ℂ => ‖1 + s‖) imageK := by
        exact ContinuousOn.norm (ContinuousOn.add continuousOn_const continuousOn_id)
      obtain ⟨C, hC⟩ := himageK_compact.bddAbove_image hcont
      exact ⟨max C 1, by positivity, fun s hs => le_trans (hC ⟨s, hs, rfl⟩) (le_max_left _ _)⟩
    -- We need bounds on the slit plane for x^(k/g)
    have htarget_bounded : ∃ B > 0, ∀ x ∈ K, ‖x ^ ((k : ℂ) / (g : ℂ))‖ ≤ B := by
      have hcont : ContinuousOn (fun x : ℂ => x ^ ((k : ℂ) / (g : ℂ))) K := by
        apply ContinuousOn.cpow
        · exact continuousOn_id
        · exact continuousOn_const
        · intro x hx
          exact hKslit hx
      have hcont_norm : ContinuousOn (fun x : ℂ => ‖x ^ ((k : ℂ) / (g : ℂ))‖) K := hcont.norm
      obtain ⟨B, hB⟩ := hK.bddAbove_image hcont_norm
      exact ⟨max B 1, by positivity, fun x hx => le_trans (hB ⟨x, hx, rfl⟩) (le_max_left _ _)⟩
    -- Extract bounds
    obtain ⟨c, hc_pos, hc⟩ := h1_plus_s_bounded_below
    obtain ⟨C, hC_pos, hC⟩ := h1_plus_s_bounded_above
    obtain ⟨B, hB_pos, hB⟩ := htarget_bounded
    -- Derive complex explicit rate from hpacket_complex
    -- First, prove the packet bound for k=0 separately
    have hpacket_complex_0 : ∀ N : ℕ, ∀ s ∈ imageK,
        ‖(g : ℂ) * (1 : ℂ) * slice g 0 N (s ^ g) - (1 + s) ^ N‖ ≤
          ((g : ℝ) - 1) * ρ ^ N * ‖1 + s‖ ^ N := by
      intro N s hs
      -- Use roots_of_unity_filter for k=0
      have hfilter := roots_of_unity_filter (N := N) hg (k := 0) (by linarith) hω s
      have h0 : (0 : ℕ) ∈ Finset.range g := Finset.mem_range.mpr hg
      rw [← Finset.add_sum_erase _ _ h0] at hfilter
      simp only [pow_zero, mul_one] at hfilter
      have hdiff : (g : ℂ) * (1 : ℂ) * slice g 0 N (s ^ g) - (1 + s) ^ N =
          ∑ a ∈ (Finset.range g).erase 0, ω ^ (a * (g - 0)) * (1 + s * ω ^ a) ^ N := by
        linear_combination -hfilter
      rw [hdiff]
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ a ∈ (Finset.range g).erase 0,
          ‖ω ^ (a * (g - 0)) * (1 + s * ω ^ a) ^ N‖ ≤
            ρ ^ N * ‖1 + s‖ ^ N := by
        intro a ha
        obtain ⟨ha0, harange⟩ := Finset.mem_erase.mp ha
        have h1 : ‖ω ^ (a * (g - 0))‖ = 1 := by
          rw [norm_pow, hω.norm'_eq_one hg.ne', one_pow]
        rw [norm_mul, h1, one_mul, norm_pow]
        have hchan : ‖1 + s * ω ^ a‖ / ‖1 + s‖ ≤ complexSpectralGap s := by
          simp only [complexSpectralGap]
          have hmem : (‖1 + s * ω ^ a‖ / ‖1 + s‖) ∈ Insert.insert 0 ((Finset.range g \ {0}).image fun a => ‖1 + s * ω ^ a‖ / ‖1 + s‖) :=
            Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_sdiff.mpr ⟨harange, by simpa using ha0⟩, rfl⟩)
          exact Finset.le_max' _ _ hmem
        have hpos : 0 < ‖1 + s‖ := norm_pos_iff.mpr (h1_plus_s_ne_zero s hs)
        have hchan' : ‖1 + s * ω ^ a‖ ≤ complexSpectralGap s * ‖1 + s‖ := by
          rwa [div_le_iff₀ hpos] at hchan
        have hrho_bound : complexSpectralGap s ≤ ρ := hρ_uniform_bound s hs
        have hsg_nonneg : 0 ≤ complexSpectralGap s := by
          simp only [complexSpectralGap]
          exact Finset.le_max' _ _ (Finset.mem_insert_self 0 _)
        calc ‖1 + s * ω ^ a‖ ^ N ≤ (complexSpectralGap s * ‖1 + s‖) ^ N := pow_le_pow_left₀ (norm_nonneg _) hchan' N
          _ ≤ (ρ * ‖1 + s‖) ^ N := by gcongr
          _ = ρ ^ N * ‖1 + s‖ ^ N := mul_pow ρ ‖1 + s‖ N
      refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hg), Finset.card_range, nsmul_eq_mul]
      rw [Nat.cast_sub hg, Nat.cast_one, mul_assoc]
    have hratio_explicit : ∀ N ≥ N₀, ∀ s ∈ imageK, s ≠ 0 →
        ‖slice g k N (s ^ g) / slice g 0 N (s ^ g) - s ^ (-(k : ℤ))‖ ≤
          4 * ((g : ℝ) - 1) * ρ ^ N / ‖s‖ ^ k := by
      intro N hN s hs hs_ne
      have hpack_k := hpacket_complex N s hs
      have hpack0 := hpacket_complex_0 N s hs
      -- Define the packet deviations
      set A : ℂ := (g : ℂ) * s ^ k * slice g k N (s ^ g) with hAdef
      set B : ℂ := (g : ℂ) * slice g 0 N (s ^ g) with hBdef
      set P : ℂ := (1 + s) ^ N with hPdef
      -- From packet bounds: ‖A - P‖ ≤ (g-1) * complexSpectralGap s ^ N * ‖1+s‖^N
      --                    ‖B - P‖ ≤ (g-1) * ρ ^ N * ‖1+s‖^N
      have hA_bound : ‖A - P‖ ≤ (g - 1) * complexSpectralGap s ^ N * ‖1 + s‖ ^ N := hpack_k
      have hpack0' : ‖B - P‖ ≤ (g - 1) * ρ ^ N * ‖1 + s‖ ^ N := by simpa [mul_one] using hpack0
      -- Derive that slice g 0 N (s ^ g) ≠ 0 from the packet bound
      have h1_plus_s_norm : ‖1 + s‖ > 0 := norm_pos_iff.mpr (h1_plus_s_ne_zero s hs)
      have hP_norm : ‖P‖ = ‖1 + s‖ ^ N := by simp [hPdef, norm_pow]
      have hB_bound : ‖B‖ ≥ ‖P‖ - ‖P - B‖ := by
        have := norm_sub_norm_le P B
        linarith
      have hslice_ne_zero : slice g 0 N (s ^ g) ≠ 0 := by
        have hg0_N : (g - 1 : ℝ) * ρ ^ N ≤ 1 / 2 := hN₀ N hN
        have hB_bound' : ‖B‖ ≥ ‖1 + s‖ ^ N - (g - 1) * ρ ^ N * ‖1 + s‖ ^ N := by
          have h1 : ‖B‖ ≥ ‖P‖ - ‖P - B‖ := by linarith [norm_sub_norm_le P B]
          have hPB' : ‖P - B‖ ≤ (g - 1) * ρ ^ N * ‖1 + s‖ ^ N := by simpa [norm_sub_rev] using hpack0'
          linarith [h1, hP_norm, hPB']
        intro hzero
        simp [hBdef, hzero] at hB_bound'
        -- Now (g-1) * ρ^N ≤ 1/2, so ‖1+s‖^N - (g-1)*ρ^N*‖1+s‖^N ≥ ‖1+s‖^N / 2 > 0
        have h1s_pos : 0 < ‖1 + s‖ ^ N := pow_pos h1_plus_s_norm N
        -- hB_bound' says ‖1+s‖^N ≤ (g-1)*ρ^N * ‖1+s‖^N
        -- But hg0_N says (g-1)*ρ^N ≤ 1/2, so RHS ≤ ‖1+s‖^N / 2 < ‖1+s‖^N
        have : (g - 1 : ℝ) * ρ ^ N * ‖1 + s‖ ^ N ≤ (1 / 2) * ‖1 + s‖ ^ N := by
          apply mul_le_mul_of_nonneg_right hg0_N (le_of_lt h1s_pos)
        linarith
      -- Key: A - B = g * (s^k * slice_k - slice_0)
      -- And slice_k / slice_0 - s^(-k) = (A - B) / (g * s^k * slice_0)
      have hkey : slice g k N (s ^ g) / slice g 0 N (s ^ g) - s ^ (-(k : ℤ)) =
          (A - B) / ((g : ℂ) * s ^ k * slice g 0 N (s ^ g)) := by
        simp [hAdef, hBdef]
        field_simp [hg.ne', hs_ne, hslice_ne_zero]
      rw [hkey]
      -- Bound the numerator: ‖A - B‖ ≤ ‖A - P‖ + ‖P - B‖ ≤ (g-1)*(complexSpectralGap s)^N * ‖1+s‖^N + (g-1)*ρ^N * ‖1+s‖^N
      have hAB_bound : ‖A - B‖ ≤ 2 * (g - 1) * ρ ^ N * ‖1 + s‖ ^ N := by
        have hP_minus_B : ‖P - B‖ = ‖B - P‖ := (norm_sub_rev B P).symm
        calc ‖A - B‖ = ‖(A - P) + (P - B)‖ := by ring_nf
          _ ≤ ‖A - P‖ + ‖P - B‖ := norm_add_le _ _
          _ = ‖A - P‖ + ‖B - P‖ := by rw [hP_minus_B]
          _ ≤ (g - 1) * complexSpectralGap s ^ N * ‖1 + s‖ ^ N + (g - 1) * ρ ^ N * ‖1 + s‖ ^ N := add_le_add hA_bound hpack0'
          _ ≤ (g - 1) * ρ ^ N * ‖1 + s‖ ^ N + (g - 1) * ρ ^ N * ‖1 + s‖ ^ N := by
            have hsGap_nonneg : 0 ≤ complexSpectralGap s := by
              simp only [complexSpectralGap]
              exact Finset.le_max' _ _ (Finset.mem_insert_self 0 _)
            have hg1_nonneg : 0 ≤ (g : ℝ) - 1 := sub_nonneg_of_le (by norm_cast)
            gcongr
            all_goals first | exact hsGap_nonneg | exact hρ_uniform_bound s hs
          _ = 2 * (g - 1) * ρ ^ N * ‖1 + s‖ ^ N := by ring
      -- Bound the denominator from below
      -- Need: ‖g * s^k * slice g 0 N (s^g)‖ ≥ something
      have hPB : ‖P - B‖ ≤ (g - 1) * ρ ^ N * ‖1 + s‖ ^ N := by
        simpa [norm_sub_rev] using hpack0'
      have hPnorm : ‖P‖ = ‖1 + s‖ ^ N := by simp [hPdef, norm_pow]
      have hdenom_bound : ‖(g : ℂ) * s ^ k * slice g 0 N (s ^ g)‖ ≥
          ‖s‖ ^ k * (‖1 + s‖ ^ N - (g - 1) * ρ ^ N * ‖1 + s‖ ^ N) := by
        have hB_eq : (g : ℂ) * s ^ k * slice g 0 N (s ^ g) = B * s ^ k := by simp [hBdef]; ring
        rw [hB_eq, norm_mul]
        rw [norm_pow]
        have hB_bound : ‖B‖ ≥ ‖1 + s‖ ^ N - (g - 1) * ρ ^ N * ‖1 + s‖ ^ N := by
          have h1 : ‖B‖ ≥ ‖P‖ - ‖P - B‖ := by linarith [norm_sub_norm_le P B]
          linarith [h1, hPnorm, hPB]
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_left hB_bound
        exact pow_nonneg (norm_nonneg s) k
      -- Combine bounds to get the result
      have hg_factor : (g : ℝ) ≥ 1 := by norm_cast
      have h1s_factor : ‖1 + s‖ ^ N > 0 := pow_pos h1_plus_s_norm N
      have hg0 : (g - 1 : ℝ) * ρ ^ N ≤ 1 / 2 := hN₀ N hN
      -- The denominator bound simplifies
      have hdenom_bound' : ‖(g : ℂ) * s ^ k * slice g 0 N (s ^ g)‖ ≥
          ‖s‖ ^ k * ‖1 + s‖ ^ N / 2 := by
        have hsimp : ‖1 + s‖ ^ N - (g - 1) * ρ ^ N * ‖1 + s‖ ^ N ≥ ‖1 + s‖ ^ N / 2 := by
          have h1s_pos : 0 < ‖1 + s‖ ^ N := pow_pos h1_plus_s_norm N
          nlinarith [h1s_pos, hg0]
        calc ‖(g : ℂ) * s ^ k * slice g 0 N (s ^ g)‖ ≥ ‖s‖ ^ k * (‖1 + s‖ ^ N - (g - 1) * ρ ^ N * ‖1 + s‖ ^ N) := hdenom_bound
          _ ≥ ‖s‖ ^ k * (‖1 + s‖ ^ N / 2) := by gcongr
          _ = ‖s‖ ^ k * ‖1 + s‖ ^ N / 2 := by ring
      -- numerator / denominator ≤ (2 * (g-1) * ρ^N * ‖1+s‖^N) / (‖s‖^k * ‖1+s‖^N / 2) = 4 * (g-1) * ρ^N / ‖s‖^k
      have hpos_s_k : 0 < ‖s‖ ^ k := pow_pos (norm_pos_iff.mpr hs_ne) k
      have hpos_s_k' : 0 < ‖s ^ k‖ := by rw [norm_pow]; exact pow_pos (norm_pos_iff.mpr hs_ne) k
      have hnum_denom : ‖A - B‖ / ‖(g : ℂ) * s ^ k * slice g 0 N (s ^ g)‖ ≤
          4 * ((g : ℝ) - 1) * ρ ^ N / ‖s‖ ^ k := by
        have hpos_denom : 0 < ‖(g : ℂ) * s ^ k * slice g 0 N (s ^ g)‖ := by
          rw [norm_mul, norm_mul]
          apply mul_pos (mul_pos _ _) _
          · exact_mod_cast hg
          · exact hpos_s_k'
          · exact norm_pos_iff.mpr hslice_ne_zero
        rw [div_le_div_iff₀ hpos_denom hpos_s_k]
        have hg1_nonneg : (0 : ℝ) ≤ g - 1 := sub_nonneg_of_le (by norm_cast)
        have h_factor_nonneg : 0 ≤ 2 * (g - 1) * ρ ^ N := by positivity
        have h_ineq : ‖s‖ ^ k * ‖1 + s‖ ^ N ≤ 2 * ‖(g : ℂ) * s ^ k * slice g 0 N (s ^ g)‖ := by
          have := hdenom_bound'
          linarith
        calc ‖A - B‖ * ‖s‖ ^ k
            ≤ 2 * (g - 1) * ρ ^ N * ‖1 + s‖ ^ N * ‖s‖ ^ k := by
              apply mul_le_mul_of_nonneg_right hAB_bound; exact pow_nonneg (norm_nonneg s) k
          _ = 2 * (g - 1) * ρ ^ N * (‖s‖ ^ k * ‖1 + s‖ ^ N) := by ring
          _ ≤ 2 * (g - 1) * ρ ^ N * (2 * ‖(g : ℂ) * s ^ k * slice g 0 N (s ^ g)‖) := by
              apply mul_le_mul_of_nonneg_left h_ineq h_factor_nonneg
          _ = 4 * (g - 1) * ρ ^ N * ‖(g : ℂ) * s ^ k * slice g 0 N (s ^ g)‖ := by ring
      calc ‖(A - B) / ((g : ℂ) * s ^ k * slice g 0 N (s ^ g))‖ = ‖A - B‖ / ‖(g : ℂ) * s ^ k * slice g 0 N (s ^ g)‖ := norm_div _ _
        _ ≤ 4 * ((g : ℝ) - 1) * ρ ^ N / ‖s‖ ^ k := hnum_denom
    -- Get lower bound for ‖s‖ on imageK
    have hs_bounded_below : ∃ m > 0, ∀ s ∈ imageK, ‖s‖ ≥ m := by
      have hcont : ContinuousOn (fun s : ℂ => ‖s‖) imageK := continuousOn_id.norm
      obtain ⟨s_min, hs_min⟩ := IsCompact.exists_isMinOn himageK_compact himage_nonempty hcont
      exact ⟨‖s_min‖, norm_pos_iff.mpr (hs_in_slit s_min hs_min.1 |>.1), hs_min.2⟩
    obtain ⟨m, hm_pos, hm⟩ := hs_bounded_below
    -- Simplify the bound: ‖1+s‖^N / c^N ≥ 1, but we can just use ≤ (C/c)^N
    -- Key: 4*(g-1)*ρ^N*‖1+s‖^N/(c^N*‖s^k‖) ≤ 4*(g-1)*ρ^N*C^N/(c^N*m^k)
    -- = 4*(g-1)/m^k * (ρ*C/c)^N
    -- For this to work, need a refined argument or different bound structure
    -- Use: the bound for each s is ≤ 4*(g-1)*ρ^N*‖1+s‖^N/(c^N*m^k)
    -- and ‖1+s‖^N ≤ C^N, so overall ≤ 4*(g-1)*C^N*ρ^N/(c^N*m^k) = (4*(g-1)/m^k)*(ρ*C/c)^N
    -- Get lower bound for ‖s‖ on imageK
    have hs_bounded_below : ∃ m > 0, ∀ s ∈ imageK, ‖s‖ ≥ m := by
      have hcont : ContinuousOn (fun s : ℂ => ‖s‖) imageK := continuousOn_id.norm
      obtain ⟨s_min, hs_min⟩ := IsCompact.exists_isMinOn himageK_compact himage_nonempty hcont
      exact ⟨‖s_min‖, norm_pos_iff.mpr (hs_in_slit s_min hs_min.1 |>.1), hs_min.2⟩
    obtain ⟨m, hm_pos, hm⟩ := hs_bounded_below
    -- The uniform bound: for s ∈ imageK, ‖s‖^k ≥ m^k
    -- So: 4*(g-1)*ρ^N / ‖s‖^k ≤ 4*(g-1)*ρ^N / m^k
    -- This tends to 0 as N → ∞ since ρ < 1
    have hbound_tends_zero : Filter.Tendsto (fun N => 4 * ((g : ℝ) - 1) * ρ ^ N / m ^ k) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun N => 4 * ((g : ℝ) - 1) * ρ ^ N) Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hρ_nonneg hρ_lt_one)
      simpa using h1.div_const (m ^ k)
    -- Conclude TendstoUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hbound_tends_zero.eventually (Metric.ball_mem_nhds _ hε))
    filter_upwards [Filter.eventually_ge_atTop N₀, Filter.eventually_ge_atTop N₁] with N hN₀' hN₁' x hx
    have hsx : sFn x ∈ imageK := ⟨x, hx, rfl⟩
    have hsx_ne : sFn x ≠ 0 := (hs_in_slit (sFn x) hsx).1
    have hbound := hratio_explicit N hN₀' (sFn x) hsx hsx_ne
    have hm_k_pos : 0 < m ^ k := pow_pos hm_pos k
    have hg1_nonneg : (0 : ℝ) ≤ (g : ℝ) - 1 := sub_nonneg_of_le (Nat.one_le_cast.mpr hg)
    have hnum_nonneg : (0 : ℝ) ≤ 4 * ((g : ℝ) - 1) * ρ ^ N := mul_nonneg (mul_nonneg (by norm_num) hg1_nonneg) (pow_nonneg hρ_nonneg N)
    have hbound' : 4 * ((g : ℝ) - 1) * ρ ^ N / m ^ k < ε := by
      have := hN₁ N hN₁'
      simp only [dist_zero_right] at this
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum_nonneg (pow_nonneg (le_of_lt hm_pos) k))] at this
      exact this
    -- Key equalities: x^(k/g) = (sFn x)^(-k) and x⁻¹ = (sFn x)^g
    have hx_pow_eq : x ^ ((k : ℂ) / (g : ℂ)) = (sFn x) ^ (-(k : ℤ)) := by
      have hxn : x ≠ 0 := ne_zero_of_slitPlane x (hKslit hx)
      have hxslit : x ∈ Complex.slitPlane := hKslit hx
      simp only [sFn]
      -- Goal: x ^ (k/g) = ((x⁻¹) ^ (1/g)) ^ (-k : ℤ)
      -- The ℤ power is actually zpow
      rw [← Complex.cpow_intCast]
      -- Now goal: x ^ (k/g) = ((x⁻¹) ^ (1/g)) ^ (-k : ℂ)
      have hxinv_slit : x⁻¹ ∈ Complex.slitPlane := inv_slitPlane x hxslit
      rw [← Complex.cpow_mul]
      simp only [inv_mul_eq_div]
      -- Goal: x ^ (k/g) = (x⁻¹) ^ ((-k)/g)
      rw [Complex.inv_cpow]
      · -- Main goal: x ^ (k/g) = (x ^ (-k/g))⁻¹
        rw [← Complex.cpow_neg]
        congr 1
        have hg_ne : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith)
        field_simp
        simp
      · -- hx: x.arg ≠ Real.pi
        exact (Complex.mem_slitPlane_iff_arg.mp hxslit).1
      · -- h₁: -π < (Complex.log x⁻¹ * g⁻¹).im
        have hg_ne : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith)
        have hg_pos : (0 : ℝ) < g := by positivity
        have hg_one : (1 : ℝ) ≤ g := by norm_cast
        have hg_inv_pos : (0 : ℝ) < (g : ℝ)⁻¹ := by positivity
        have hg_inv_le_one : (g : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hg_one
        rw [Complex.mul_im]
        have hg_inv_re : ((g : ℂ)⁻¹).re = (g : ℝ)⁻¹ := by simp [Complex.inv_re]
        have hg_inv_im : ((g : ℂ)⁻¹).im = 0 := by simp [Complex.inv_im]
        rw [hg_inv_re, hg_inv_im]
        simp
        rw [Complex.log_im]
        have hxinvarg := Complex.mem_slitPlane_iff_arg.mp hxinv_slit
        have h_arg_bound := Complex.neg_pi_lt_arg (x⁻¹)
        have h1 : -Real.pi * (g : ℝ)⁻¹ < x⁻¹.arg * (g : ℝ)⁻¹ := mul_lt_mul_of_pos_right h_arg_bound hg_inv_pos
        have h2 : -Real.pi ≤ -Real.pi * (g : ℝ)⁻¹ := by nlinarith [Real.pi_pos]
        linarith
      · -- h₂: (Complex.log x⁻¹ * g⁻¹).im ≤ π
        have hg_ne : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith)
        have hg_pos : (0 : ℝ) < g := by positivity
        have hg_one : (1 : ℝ) ≤ g := by norm_cast
        have hg_inv_pos : (0 : ℝ) < (g : ℝ)⁻¹ := by positivity
        have hg_inv_le_one : (g : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hg_one
        rw [Complex.mul_im]
        have hg_inv_re : ((g : ℂ)⁻¹).re = (g : ℝ)⁻¹ := by simp [Complex.inv_re]
        have hg_inv_im : ((g : ℂ)⁻¹).im = 0 := by simp [Complex.inv_im]
        rw [hg_inv_re, hg_inv_im]
        simp
        rw [Complex.log_im]
        have hxinvarg := Complex.mem_slitPlane_iff_arg.mp hxinv_slit
        have h_arg_bound := Complex.arg_le_pi (x⁻¹)
        have h1 : x⁻¹.arg * (g : ℝ)⁻¹ ≤ Real.pi * (g : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h_arg_bound (le_of_lt hg_inv_pos)
        have h2 : Real.pi * (g : ℝ)⁻¹ ≤ Real.pi := by
          exact mul_le_of_le_one_right Real.pi_pos.le hg_inv_le_one
        linarith
    have hx_inv_eq : x⁻¹ = (sFn x) ^ g := (hs_pow x hx).symm
    calc dist (x ^ ((k : ℂ) / (g : ℂ))) (slice g k N x⁻¹ / slice g 0 N x⁻¹)
        = dist ((sFn x) ^ (-(k : ℤ))) (slice g k N ((sFn x) ^ g) / slice g 0 N ((sFn x) ^ g)) := by
          rw [hx_pow_eq, hx_inv_eq]
      _ = ‖(sFn x) ^ (-(k : ℤ)) - slice g k N ((sFn x) ^ g) / slice g 0 N ((sFn x) ^ g)‖ := by simp [dist_eq_norm]
      _ = ‖slice g k N ((sFn x) ^ g) / slice g 0 N ((sFn x) ^ g) - (sFn x) ^ (-(k : ℤ))‖ := by rw [← norm_neg, neg_sub]
      _ ≤ 4 * ((g : ℝ) - 1) * ρ ^ N / ‖sFn x‖ ^ k := hbound
      _ ≤ 4 * ((g : ℝ) - 1) * ρ ^ N / m ^ k := by
          apply div_le_div_of_nonneg_left hnum_nonneg (pow_pos hm_pos k)
          exact pow_le_pow_left₀ (le_of_lt hm_pos) (hm (sFn x) hsx) k
      _ < ε := hbound'
  · rw [ Metric.tendstoUniformlyOn_iff ];
    exact fun ε hε => Filter.Eventually.of_forall fun N x hx => False.elim <| hK_nonempty ⟨x, hx⟩

/- Targets 6–7 are preserved below but disabled because their compact-uniform endpoint proof remains open.
Targets 1–5 are fully proved.

/- Target 6: compact-uniform endpoint suppression.  Again g ≥ 2 is required
and is available in the positive-k branch of the final theorem. -/
theorem tendstoUniformlyOn_endpointCorrection_cpow {g : ℕ} (hg : 2 ≤ g)
    {K : Set ℂ} (hK : IsCompact K) (hKslit : K ⊆ Complex.slitPlane) :
    TendstoUniformlyOn
      (fun N x =>
        (epsIdx g N : ℂ) * (x⁻¹) ^ (qIdx g N + 1) /
          slice g 0 N x⁻¹)
      (fun _ => 0)
      Filter.atTop K := by
  proof_placeholder

/- Target 7 (full paper statement): local uniformity of the actual reversed
approximants on every compact subset of ℂ ∖ (−∞,0]. -/
theorem tendstoUniformlyOn_reversed_ratio_cpow {g k : ℕ}
    (hg : 0 < g) (hk : k < g) {K : Set ℂ}
    (hK : IsCompact K) (hKslit : K ⊆ Complex.slitPlane) :
    TendstoUniformlyOn
      (fun N x => reversedRatioComplex g k N x)
      (fun x => x ^ ((k : ℂ) / (g : ℂ)))
      Filter.atTop K := by
  by_cases hk0 : k = 0
  · simp_all +decide [ reversedRatioComplex ]
    rw [ Metric.tendstoUniformlyOn_iff ]
    intro ε hε
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN x hx
    simp [hε]
  · -- Use uniform convergence of slice ratio and endpoint correction
    -- Apply the division of uniformly convergent functions
    have h_slice_conv := tendstoUniformlyOn_slice_ratio_cpow hg hk hK hKslit
    have hk_pos : 1 ≤ k := Nat.pos_of_ne_zero hk0
    have hg2 : 2 ≤ g := Nat.lt_of_le_of_lt hk_pos hk
    have h_endpt_conv := tendstoUniformlyOn_endpointCorrection_cpow hg2 hK hKslit
    -- We need to show that (slice ratio) / (1 - endpoint) → x^(k/g) uniformly
    -- Since endpoint → 0 uniformly, 1 - endpoint → 1 uniformly and is eventually bounded away from 0
    rw [Metric.tendstoUniformlyOn_iff] at h_slice_conv h_endpt_conv ⊢
    intro ε hε
    -- Get uniform bounds from compactness
    have hx_ne_zero : ∀ x ∈ K, x ≠ 0 := by
      intro x hx
      have := hKslit hx
      simp [Complex.slitPlane] at this
      rcases this with h | h
      · exact fun h' => by simp [Complex.ext_iff] at h'; linarith
      · exact fun h' => by simp [Complex.ext_iff] at h'; exact h h'.2
    have h_cont_pow : ContinuousOn (fun x : ℂ => x ^ ((k : ℂ) / (g : ℂ))) K := by
      intro x hx
      have hx_slit := hKslit hx
      simp [Complex.slitPlane] at hx_slit
      rcases hx_slit with h | h
      · exact (continuousAt_cpow_const (Or.inl h)).continuousWithinAt
      · exact (continuousAt_cpow_const (Or.inr h)).continuousWithinAt
    obtain ⟨B, hB_pos, hB⟩ : ∃ B > 0, ∀ x ∈ K, ‖x ^ ((k : ℂ) / (g : ℂ))‖ ≤ B := by
      obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn hK h_cont_pow
      exact ⟨max B 1, by positivity, fun x hx => le_trans (hB x hx) (le_max_left _ _)⟩
    -- Choose δ for endpoint convergence: need B * δ < ε / 4
    -- Also need δ ≤ 1/2 to ensure |1 - endpoint| ≥ 1/2
    set δ := min (ε / (8 * (B + 1))) (1 / 2) with hδ_def
    have hδ_pos : δ > 0 := by positivity
    have hBδ_lt : B * δ < ε / 4 := by
      calc B * δ ≤ B * (ε / (8 * (B + 1))) := by
            apply mul_le_mul_of_nonneg_left (min_le_left _ _) (le_of_lt hB_pos)
        _ = ε * B / (8 * (B + 1)) := by ring
        _ < ε / 4 := by
            rw [div_lt_iff₀ (by positivity : (0:ℝ) < 8 * (B + 1))]
            ring_nf
            nlinarith
    -- Get N₁ from endpoint convergence with bound δ
    have h_endpt_eventually := h_endpt_conv δ hδ_pos
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h_endpt_eventually
    -- After this, ‖endpoint‖ < δ ≤ 1/2, so |1 - endpoint| ≥ 1/2
    have h_denom_bound : ∀ N ≥ N₁, ∀ x ∈ K, ‖(1 : ℂ) - (epsIdx g N : ℂ) * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N x⁻¹‖ ≥ 1 / 2 := by
      intro N hN x hx
      have h_eps := hN₁ N hN x hx
      rw [dist_zero_left] at h_eps
      by_contra h_contra
      push_neg at h_contra
      have h_eps_norm : ‖(epsIdx g N : ℂ) * x⁻¹ ^ (qIdx g N + 1) / slice g 0 N x⁻¹‖ < 1 / 2 := by
        calc ‖(epsIdx g N : ℂ) * x⁻¹ ^ (qIdx g N + 1) / slice g 0 N x⁻¹‖ < δ := h_eps
          _ ≤ 1 / 2 := min_le_right _ _
      have h_tri := norm_add_le (1 - (epsIdx g N : ℂ) * x⁻¹ ^ (qIdx g N + 1) / slice g 0 N x⁻¹) ((epsIdx g N : ℂ) * x⁻¹ ^ (qIdx g N + 1) / slice g 0 N x⁻¹)
      simp only [sub_add_cancel] at h_tri
      have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
      rw [h1] at h_tri
      linarith
    -- Get uniform lower bound on ‖x^(k/g)‖ from compactness
    have hx_pow_ne_zero : ∀ x ∈ K, x ^ ((k : ℂ) / (g : ℂ)) ≠ 0 := by
      intro x hx
      have hx' := hx_ne_zero x hx
      rw [Complex.cpow_def_of_ne_zero hx']
      exact Complex.exp_ne_zero _
    -- Choose ε' for slice convergence
    have h_cont_norm_pow : ContinuousOn (fun x : ℂ => ‖x ^ ((k : ℂ) / (g : ℂ))‖) K := by
      exact continuous_norm.comp_continuousOn h_cont_pow
    obtain ⟨m, hm_pos, hm⟩ : ∃ m > 0, ∀ x ∈ K, m ≤ ‖x ^ ((k : ℂ) / (g : ℂ))‖ := by
      by_cases hK_empty : K = ∅
      · use 1
        simp_all
      · have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
        obtain ⟨x₀, hx₀, hm⟩ := hK.exists_isMinOn hK_nonempty h_cont_norm_pow
        use ‖x₀ ^ ((k : ℂ) / (g : ℂ))‖
        constructor
        · exact norm_pos_iff.mpr (hx_pow_ne_zero x₀ hx₀)
        · intro x hx
          exact hm hx
    set ε' := min (ε / (4 * (B + 1))) (m / 2) with hε'_def
    have hε'_pos : ε' > 0 := by positivity
    have h_slice_eventually := h_slice_conv ε' hε'_pos
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp h_slice_eventually
    -- Use N = max N₁ N₂ + 1 to ensure N ≥ 1
    rw [Filter.eventually_atTop]
    use max N₁ N₂ + 1
    intro N hN x hx
    have hN_ge : max N₁ N₂ + 1 ≤ N := hN
    have hN₁' : N₁ ≤ N := by omega
    have hN₂' : N₂ ≤ N := by omega
    have h_eps := hN₁ N hN₁' x hx
    have h_rat := hN₂ N hN₂' x hx
    rw [dist_zero_left] at h_eps
    simp only [dist_eq_norm] at h_rat
    -- Key: reversedRatioComplex g k N x = (slice ratio) / (1 - endpoint)
    have hx_ne := hx_ne_zero x hx
    have h_slice_k := @revAComplex_eq_slice g k N hg (Nat.pos_of_ne_zero hk0) hk x hx_ne
    have hN_ge_1 : 1 ≤ N := by omega
    have h_slice_0 := @revBComplex_eq_slice g N hg hN_ge_1 x hx_ne
    -- Now compute reversedRatioComplex
    rw [reversedRatioComplex]
    simp only [hk0, ↓reduceIte]
    rw [h_slice_k, h_slice_0]
    have hx_pow_N_ne : x ^ qIdx g N ≠ 0 := pow_ne_zero _ hx_ne
    rw [mul_div_mul_left _ _ hx_pow_N_ne]
    -- Set up notation
    set s_k := slice g k N x⁻¹ with hs_k
    set s_0 := slice g 0 N x⁻¹ with hs_0
    set e := (epsIdx g N : ℂ) * x⁻¹ ^ (qIdx g N + 1) with he_def
    set endpt := e / s_0 with h_endpt_def
    -- We need s_0 ≠ 0 first
    have hs_0_ne_zero : s_0 ≠ 0 := by
      intro h
      rw [h] at h_rat
      simp at h_rat
      have h_lb := hm x hx
      have h_eps' : ε' ≤ m / 2 := min_le_right _ _
      linarith
    -- Denominator: s_0 - e = s_0 * (1 - endpt)
    have h_denom_eq : s_0 - e = s_0 * (1 - endpt) := by
      rw [h_endpt_def]
      field_simp [hs_0_ne_zero]
    rw [h_denom_eq]
    -- s_k / (s_0 * (1 - endpt)) = (s_k / s_0) / (1 - endpt)
    have h_ratio_eq : s_k / (s_0 * (1 - endpt)) = (s_k / s_0) / (1 - endpt) := by field_simp
    rw [h_ratio_eq]
    -- Now goal: dist (x^(k/g)) ((s_k / s_0) / (1 - endpt)) < ε
    have h_denom_bound : ‖1 - endpt‖ ≥ 1 / 2 := h_denom_bound N hN₁' x hx
    -- Key inequality: |x^(k/g) - s_k/(1-endpt)| = |(x^(k/g)*(1-endpt) - s_k) / (1-endpt)|
    --                                          = |((x^(k/g) - s_k) - x^(k/g)*endpt) / (1-endpt)|
    --                                          ≤ (|x^(k/g) - s_k| + |x^(k/g)|*|endpt|) / |1-endpt|
    have h_endpt_bound : ‖endpt‖ < δ := h_eps
    have h_B_endpt_lt : B * ‖endpt‖ < ε / 4 := by
      calc B * ‖endpt‖ < B * δ := by
            apply mul_lt_mul_of_pos_left h_endpt_bound hB_pos
        _ < ε / 4 := hBδ_lt
    have h_dist_eq : ‖x ^ ((k : ℂ) / (g : ℂ)) - s_k / s_0 / (1 - endpt)‖ =
        ‖((x ^ ((k : ℂ) / (g : ℂ)) - s_k / s_0) - x ^ ((k : ℂ) / (g : ℂ)) * endpt) / (1 - endpt)‖ := by
      have h1_sub_endpt_ne : (1 : ℂ) - endpt ≠ 0 := by
        intro h
        have : ‖1 - endpt‖ = 0 := by rw [h]; norm_num
        linarith
      field_simp [h1_sub_endpt_ne]
      ring_nf
    rw [dist_eq_norm, h_dist_eq]
    rw [norm_div]
    have h_num_bound : ‖(x ^ ((k : ℂ) / (g : ℂ)) - s_k / s_0) - x ^ ((k : ℂ) / (g : ℂ)) * endpt‖ ≤
        ‖x ^ ((k : ℂ) / (g : ℂ)) - s_k / s_0‖ + ‖x ^ ((k : ℂ) / (g : ℂ))‖ * ‖endpt‖ := by
      calc ‖(x ^ ((k : ℂ) / (g : ℂ)) - s_k / s_0) - x ^ ((k : ℂ) / (g : ℂ)) * endpt‖
          ≤ ‖x ^ ((k : ℂ) / (g : ℂ)) - s_k / s_0‖ + ‖x ^ ((k : ℂ) / (g : ℂ)) * endpt‖ := norm_sub_le _ _
        _ = ‖x ^ ((k : ℂ) / (g : ℂ)) - s_k / s_0‖ + ‖x ^ ((k : ℂ) / (g : ℂ))‖ * ‖endpt‖ := by rw [norm_mul]
    have h_inv_denom : ‖(1 - endpt)‖⁻¹ ≤ 2 := by
      have h1 : (1/2 : ℝ) ≤ ‖1 - endpt‖ := h_denom_bound
      have h2 : (0 : ℝ) < (1/2 : ℝ) := by norm_num
      have h3 : (‖1 - endpt‖ : ℝ)⁻¹ ≤ (1/2)⁻¹ := inv_anti₀ h2 h1
      norm_num at h3 ⊢; exact h3
    have h_num_lt : ‖x ^ ((k : ℂ) / (g : ℂ))‖ * ‖endpt‖ < B * δ := by
      calc ‖x ^ ((k : ℂ) / (g : ℂ))‖ * ‖endpt‖ ≤ B * ‖endpt‖ := by
            apply mul_le_mul_of_nonneg_right (hB x hx) (norm_nonneg _)
        _ < B * δ := mul_lt_mul_of_pos_left h_eps hB_pos
    have h_sum_lt : ‖x ^ ((k : ℂ) / (g : ℂ)) - s_k / s_0‖ + ‖x ^ ((k : ℂ) / (g : ℂ))‖ * ‖endpt‖ < ε' + B * δ := add_lt_add h_rat h_num_lt
    have h_pos_num : 0 < ε' + B * δ := add_pos hε'_pos (mul_pos hB_pos hδ_pos)
    have h_num_le_denom_bound : ‖x ^ ((k : ℂ) / (g : ℂ)) - s_k / s_0‖ + ‖x ^ ((k : ℂ) / (g : ℂ))‖ * ‖endpt‖ ≤ ε' + B * δ := le_of_lt h_sum_lt
    have h_UB : (ε' + B * δ) * 2 < ε := by
          have h1 : ε' ≤ ε / (4 * (B + 1)) := min_le_left _ _
          have h2 : δ ≤ ε / (8 * (B + 1)) := min_le_left _ _
          have h1' : ε' * (4 * (B + 1)) ≤ ε := by
            have h4B_pos : (0 : ℝ) < 4 * (B + 1) := by positivity
            rwa [le_div_iff₀ h4B_pos] at h1
          have h2' : δ * (8 * (B + 1)) ≤ ε := by
            have h8B_pos : (0 : ℝ) < 8 * (B + 1) := by positivity
            rwa [le_div_iff₀ h8B_pos] at h2
          nlinarith [hB_pos, hε]
    calc ‖(x ^ ((k : ℂ) / (g : ℂ)) - s_k / s_0) - x ^ ((k : ℂ) / (g : ℂ)) * endpt‖ / ‖1 - endpt‖
        ≤ (‖x ^ ((k : ℂ) / (g : ℂ)) - s_k / s_0‖ + ‖x ^ ((k : ℂ) / (g : ℂ))‖ * ‖endpt‖) / ‖1 - endpt‖ := by
          gcongr
      _ ≤ (ε' + B * δ) / ‖1 - endpt‖ := by exact div_le_div_of_nonneg_right h_num_le_denom_bound (by positivity)
      _ ≤ (ε' + B * δ) * 2 := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left h_inv_denom (le_of_lt h_pos_num)
      _ < ε := h_UB


-/

end ResidueSlices
