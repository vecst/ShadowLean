/-
Axiom audit for all principal theorems.  Run with:
  lake env lean audit/AxiomAudit.lean
Every line must report exactly [propext, Classical.choice, Quot.sound].
-/
import RequestProject.Main

-- ResidueSlices core
#print axioms ResidueSlices.packet_decomposition
#print axioms ResidueSlices.one_le_slice_zero
#print axioms ResidueSlices.square_ratio_error
#print axioms ResidueSlices.tendsto_square_ratio

-- General-g convergence
#print axioms ResidueSlices.roots_of_unity_filter
#print axioms ResidueSlices.tendsto_general_slice_ratio

-- Quantitative rate
#print axioms ResidueSlices.spectralGap_mem_unitInterval
#print axioms ResidueSlices.general_slice_ratio_spectral_rate
#print axioms ResidueSlices.general_slice_ratio_spectral_rate_exp

-- Explicit rate
#print axioms ResidueSlices.packet_principal_deviation
#print axioms ResidueSlices.general_slice_ratio_explicit_rate
#print axioms ResidueSlices.general_slice_ratio_explicit_rate_exp

-- rpow corollaries
#print axioms ResidueSlices.slice_zero_pos
#print axioms ResidueSlices.slice_zero_ne_zero
#print axioms ResidueSlices.tendsto_slice_ratio_rpow
#print axioms ResidueSlices.slice_ratio_explicit_rate_rpow

-- Head–tail and certified ζ
#print axioms ResidueSlices.head_tail_identity
#print axioms ResidueSlices.partial_sum_decomposition
#print axioms ResidueSlices.zeta_certified_bounds

-- Diagonal suppression and uniform diagonal estimate
#print axioms ResidueSlices.diagGap_pos
#print axioms ResidueSlices.re_pow_le_cos
#print axioms ResidueSlices.channelRatio_diagonal_bound
#print axioms ResidueSlices.spectralGap_diagonal_bound
#print axioms ResidueSlices.diagonal_slice_ratio_bound
#print axioms ResidueSlices.diagonal_threshold_eventually

-- Reversed approximants (corrected endpoint treatment)
#print axioms ResidueSlices.revA_eq_slice
#print axioms ResidueSlices.revB_eq_slice
#print axioms ResidueSlices.revA_pos
#print axioms ResidueSlices.tendsto_reversed_ratio

-- Spin factor / cross-norm
#print axioms SpinFactor.mul_comm
#print axioms SpinFactor.mul_conj
#print axioms SpinFactor.cross_norm_identity
#print axioms SpinFactor.signed_mul_conj
#print axioms SpinFactor.associator_eq
#print axioms SpinFactor.mul_self_assoc
#print axioms SpinFactor.jordan_identity
