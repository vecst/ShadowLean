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
#print axioms ResidueSlices.tendstoUniformlyOn_endpointCorrection_cpow
#print axioms ResidueSlices.tendstoUniformlyOn_reversed_ratio_cpow

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

-- Packet derivative jet (Fourier core; Targets 7-9 Stirling moments deferred)
#print axioms ResidueSlices.forwardDiff_binomial_symbol
#print axioms ResidueSlices.forwardDiffSymbol_eq_pow
#print axioms ResidueSlices.forwardDiffPacket_eq_dft_sum
#print axioms ResidueSlices.forwardDiffSymbol_zero
#print axioms ResidueSlices.forwardDiffPacket_eq_dft_sum_erase_zero
#print axioms ResidueSlices.forwardDiffPacket_movingPacketMass

-- Packet high-pass (moving-packet Fourier identity + total-variation bound)
#print axioms ResidueSlices.dft_movingPacketMass
#print axioms ResidueSlices.movingPacketMass_add_one_sub
#print axioms ResidueSlices.stdAddChar_sub_one_mul_dft
#print axioms ResidueSlices.dft_norm_mul_le_cyclicVariation
#print axioms ResidueSlices.movingPacket_dft_highpass_bound

-- IFFT preparation (exact finite-g spectral reconstruction)
#print axioms ResidueSlices.preparedScaledPacket_formula
#print axioms ResidueSlices.positiveDFT_preparedScaledPacket
#print axioms ResidueSlices.packetSpectrum_preparedPacket
#print axioms ResidueSlices.preparedPacket_no_spectral_leakage
#print axioms ResidueSlices.preparedPacket_conj_eq_self
#print axioms ResidueSlices.preparedPacket_pos_of_dominant_zero

-- Dual-slice logarithm (powers -> log via two-stage limit)
#print axioms ResidueSlices.tendsto_binomialLog_row
#print axioms ResidueSlices.logSurrogate_eq_tanh
#print axioms ResidueSlices.tendsto_logSurrogate
#print axioms ResidueSlices.binomialLog_iterated_converges_to_log
#print axioms ResidueSlices.tendstoUniformlyOn_binomialLog_row

-- Metallic-cutoff recurrence (Targets 1-4 proved; 5-8 open)
#print axioms MetallicCutoff.state_neg_one_even
#print axioms MetallicCutoff.state_neg_one_odd
#print axioms MetallicCutoff.silver_identities
#print axioms MetallicCutoff.ratio_three_closed_form
#print axioms MetallicCutoff.even_pole_residue

-- Spin factor / cross-norm
#print axioms SpinFactor.mul_comm
#print axioms SpinFactor.mul_conj
#print axioms SpinFactor.cross_norm_identity
#print axioms SpinFactor.signed_mul_conj
#print axioms SpinFactor.associator_eq
#print axioms SpinFactor.mul_self_assoc
#print axioms SpinFactor.jordan_identity
