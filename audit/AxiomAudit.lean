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

-- Rational-exponent diagonal zeta
#print axioms ResidueSlices.tendsto_tailTerm
#print axioms ResidueSlices.tendsto_mixedKernel
#print axioms ResidueSlices.tendsto_diagZeta
#print axioms ResidueSlices.diagZeta_error_bound
#print axioms ResidueSlices.real_rpow_tsum_tail_bound
#print axioms ResidueSlices.headTerm_uniform_bound
#print axioms ResidueSlices.mixedKernel_diagonal_error

-- Compact-uniform convergence
#print axioms ResidueSlices.exists_uniform_spectralGap
#print axioms ResidueSlices.tendstoUniformlyOn_slice_ratio
#print axioms ResidueSlices.tendstoUniformlyOn_tailTerm
#print axioms ResidueSlices.tendstoUniformlyOn_mixedKernel
#print axioms ResidueSlices.tendstoUniformlyOn_reversed_ratio

-- Reversed-approximant combined rate
#print axioms ResidueSlices.combinedRate_mem_unitInterval
#print axioms ResidueSlices.endpointCorrection_geometric_bound
#print axioms ResidueSlices.reversed_ratio_geometric_bound
#print axioms ResidueSlices.reversed_ratio_isBigO

-- Slit-plane (principal-branch complex) convergence
#print axioms ResidueSlices.norm_one_add_root_mul_lt
#print axioms ResidueSlices.tendsto_slice_ratio_cpow

-- Reversed approximant over the slit plane (Targets 1-5; 6-7 disabled/open)
#print axioms ResidueSlices.revAComplex_eq_slice
#print axioms ResidueSlices.revBComplex_eq_slice
#print axioms ResidueSlices.tendsto_endpointCorrection_cpow
#print axioms ResidueSlices.tendsto_reversed_ratio_cpow
#print axioms ResidueSlices.tendstoUniformlyOn_slice_ratio_cpow

-- Residual certificate interface (generator-agnostic)
#print axioms ResidualCertificate.residual_order_lower
#print axioms ResidualCertificate.residual_order_upper
#print axioms ResidualCertificate.residual_bracket
#print axioms ResidualCertificate.residual_pair_intersection
#print axioms ResidualCertificate.residual_finset_intersection
#print axioms ResidualCertificate.sqrt_ten_certificate
#print axioms ResidualCertificate.pow_residual_relative_bound
#print axioms ResidualCertificate.fractional_residual_relative_bound
#print axioms ResidualCertificate.residual_positive_enclosure
#print axioms ResidualCertificate.residual_negative_enclosure
#print axioms ResidualCertificate.sqrt_ten_bracket_via_interface

-- Spin factor / cross-norm
#print axioms SpinFactor.mul_comm
#print axioms SpinFactor.mul_conj
#print axioms SpinFactor.cross_norm_identity
#print axioms SpinFactor.signed_mul_conj
#print axioms SpinFactor.associator_eq
#print axioms SpinFactor.mul_self_assoc
#print axioms SpinFactor.jordan_identity
