import T1PrimitiveErrorScales
import T1VKWeight
import T1VKWeightGrowth
import T1ReciprocalZeta
import T1ZetaFractionalMellin
import T1ZetaFractionalBound
import T1ZetaFractionalFormula
import T1ZetaGrowth
import T1DiskAnalyticLog
import T1DiskReciprocalBound
import T1ZetaStripDisk
import T1ReciprocalZetaStripBound
import T1QRHStrip
import T1VKHeightWidth
import T1RieszMellinKernel
import T1VerticalPower
import T1RieszDenominator
import T1RieszKernelInversion
import T1VKRegion
import T1VKDiskGeometry
import T1ReciprocalZetaRightBound
import T1VKReciprocalCenter
import T1VKReciprocalBound
import T1MobiusFinite
import T1MertensFinite
import T1RieszMertensSum
import T1RieszLineTerm
import T1RieszMertensInversion
import T1VerticalContourShift
import T1RieszStripIntegrand
import T1VKAnalyticRegion
import T1FiniteContourShift
import T1VerticalTail
import T1RieszMertensContour
import T1VKFiniteRieszContour
import T1VKHeightSchedule
import T1VKContourScales
import T1VKRieszGrowth
import T1RieszDifferenceKernel
import T1RieszDifferenceSum
import T1RieszDifferenceError
import T1VKDesmoothing
import T1LogarithmicHeadSum
import T1GeometricPrimitiveCount
import T1IntegerDivisibility

#print axioms Markov.t1_primitiveConditionalScale_pos
#print axioms Markov.t1_primitiveUnconditionalScale_pos
#print axioms Markov.t1_power_saving_isLittleO_primitiveConditional
#print axioms Markov.t1_vkWeight
#print axioms Markov.t1_vkWeight_pos
#print axioms Markov.t1_vkWeight_as_rpow
#print axioms Markov.t1_vkWeight_monotone
#print axioms Markov.t1_vkWeight_tendsto
#print axioms Markov.t1_vkWeight_isLittleO_log
#print axioms Markov.t1_vkWeight_half_log
#print axioms Markov.t1_poleRemovedZeta
#print axioms Markov.t1_poleRemovedZeta_differentiable
#print axioms Markov.t1_reciprocalZeta
#print axioms Markov.t1_reciprocalZeta_one
#print axioms Markov.t1_reciprocalZeta_of_ne_one
#print axioms Markov.t1_poleRemovedZeta_ne_zero
#print axioms Markov.t1_reciprocalZeta_holomorphic_of_QRH
#print axioms Markov.t1_reciprocalZeta_eq_moebius_LSeries
#print axioms Markov.t1_fractionalTail
#print axioms Markov.t1_fractionalTail_norm_le
#print axioms Markov.t1_fractionalTail_measurable
#print axioms Markov.t1_fractionalTail_locallyIntegrable
#print axioms Markov.t1_fractionalTail_atTop
#print axioms Markov.t1_fractionalTail_atZero
#print axioms Markov.t1_zetaFractionalMellin
#print axioms Markov.t1_zetaFractionalMellin_differentiableAt
#print axioms Markov.t1_zetaFractionalMellin_integral
#print axioms Markov.t1_zetaFractionalMellin_norm_le
#print axioms Markov.t1_zetaFractional_integrable
#print axioms Markov.t1_zeta_fractional_formula_right
#print axioms Markov.t1_poleRemovedZeta_fractional_formula
#print axioms Markov.t1_poleRemovedZeta_norm_le
#print axioms Markov.t1_reciprocalZeta_line_two_bounded
#print axioms Markov.t1_poleRemovedZeta_reciprocal_line_two_bounded
#print axioms Markov.t1_disk_normalized_log
#print axioms Markov.t1_disk_reciprocal_bound
#print axioms Markov.t1_zetaDiskCenter
#print axioms Markov.t1_zetaDiskCenter_re
#print axioms Markov.t1_zetaDiskCenter_im
#print axioms Markov.t1_zetaDiskCenter_norm
#print axioms Markov.t1_zetaDiskCenter_distance
#print axioms Markov.t1_zetaDisk_realPart
#print axioms Markov.t1_zetaDisk_norm
#print axioms Markov.t1_reciprocalZeta_fixed_strip
#print axioms Markov.t1_QRH_reciprocalZeta_strip
#print axioms Markov.t1_vkHeightBase
#print axioms Markov.t1_vkHeightLog
#print axioms Markov.t1_vkHeightDenom
#print axioms Markov.t1_vkHeightWidth
#print axioms Markov.t1_vkHeightLog_ge
#print axioms Markov.t1_vkHeightDoubleLog_ge
#print axioms Markov.t1_vkHeightDenom_ge_one
#print axioms Markov.t1_vkHeightWidth_pos
#print axioms Markov.t1_vkHeightWidth_le
#print axioms Markov.t1_vkHeightWidth_antitone_abs
#print axioms Markov.t1_vkHeightDenom_le_log
#print axioms Markov.t1_vkHeightDenom_le_linear
#print axioms Markov.t1_vkHeightWidth_abs
#print axioms Markov.t1_rieszKernel
#print axioms Markov.t1_rieszDenom
#print axioms Markov.t1_rieszKernel_continuous
#print axioms Markov.t1_rieszKernel_hasMellin
#print axioms Markov.t1_verticalPower_integrable
#print axioms Markov.t1_rieszDenom_ne_zero
#print axioms Markov.t1_rieszDenom_differentiable
#print axioms Markov.t1_rieszDenom_inv_norm_le
#print axioms Markov.t1_rieszDenom_inv_verticalIntegrable
#print axioms Markov.t1_verticalPoint
#print axioms Markov.t1_verticalPoint_re
#print axioms Markov.t1_verticalPoint_im
#print axioms Markov.t1_verticalPoint_continuous
#print axioms Markov.t1_rieszKernel_inversion
#print axioms Markov.t1_VKZeroFreeRegion
#print axioms Markov.t1_poleRemovedZeta_ne_zero_of_one_le_re
#print axioms Markov.t1_verticalPoint_distance
#print axioms Markov.t1_poleRemovedZeta_compact_height
#print axioms Markov.t1_VKZeroFreeRegion_global
#print axioms Markov.t1_vkDiskWidth
#print axioms Markov.t1_vkDiskCenter
#print axioms Markov.t1_vkContourLeft
#print axioms Markov.t1_vkDiskWidth_pos
#print axioms Markov.t1_vkDiskWidth_le
#print axioms Markov.t1_vkDiskWidth_inv_le
#print axioms Markov.t1_vkContourLeft_bounds
#print axioms Markov.t1_vkContourLeft_mono
#print axioms Markov.t1_vkDisk_inside_region
#print axioms Markov.t1_vkDisk_norm_le
#print axioms Markov.t1_vkDisk_evaluation
#print axioms Markov.t1_LSeries_one_real_term_eq_norm
#print axioms Markov.t1_reciprocalZeta_norm_le_real_zeta
#print axioms Markov.t1_reciprocalZeta_norm_le_right
#print axioms Markov.t1_vkInverseWidthConstant
#print axioms Markov.t1_vkInverseWidthConstant_pos
#print axioms Markov.t1_vkReciprocalZeta_right
#print axioms Markov.t1_vkPoleRemovedZeta_inverse_center
#print axioms Markov.t1_vkReciprocalZeta_near_line
#print axioms Markov.t1_vkReciprocalZeta_moving_region
#print axioms Markov.t1_moebius_divisor_sum
#print axioms Markov.t1_primitive_indicator_moebius
#print axioms Markov.t1_finite_primitive_count_moebius
#print axioms Markov.t1_gcdCutoff
#print axioms Markov.t1_gcd_le_cutoff
#print axioms Markov.t1_gcd_divisors_as_filter
#print axioms Markov.t1_finite_primitive_count_divisor_fibers
#print axioms Markov.t1_mertensNat
#print axioms Markov.t1_mertens
#print axioms Markov.t1_mertensNat_zero
#print axioms Markov.t1_mertens_interval
#print axioms Markov.t1_mertens_threshold_interval
#print axioms Markov.t1_finite_hyperbola_interchange
#print axioms Markov.t1_rieszMertens
#print axioms Markov.t1_moebiusKernelTerm
#print axioms Markov.t1_moebiusKernelTerm_vanishes
#print axioms Markov.t1_rieszMertens_eq_tsum
#print axioms Markov.t1_rieszLineTerm
#print axioms Markov.t1_rieszLineTerm_norm
#print axioms Markov.t1_rieszLineTerm_integrable
#print axioms Markov.t1_rieszLineTerm_integral
#print axioms Markov.t1_rieszIntegrand
#print axioms Markov.t1_rieszLineTerm_summable_integral_norm
#print axioms Markov.t1_rieszLineTerm_tsum
#print axioms Markov.t1_rieszMertens_integral_line_two
#print axioms Markov.t1_horizontal_integral_tendsto_zero
#print axioms Markov.t1_vertical_integral_shift
#print axioms Markov.t1_rieszIntegrand_differentiableOn
#print axioms Markov.t1_rieszIntegrand_norm_le
#print axioms Markov.t1_rieszIntegrand_verticalIntegrable
#print axioms Markov.t1_vkRieszOrder
#print axioms Markov.t1_vk_reciprocalZeta_differentiableAt
#print axioms Markov.t1_vkRieszIntegrand_differentiableAt
#print axioms Markov.t1_vkRieszIntegrand_norm
#print axioms Markov.t1_vkRieszIntegrand_right_strip
#print axioms Markov.t1_verticalTrunc
#print axioms Markov.t1_verticalTrunc_rect_bound
#print axioms Markov.t1_verticalTrunc_integrable_majorant
#print axioms Markov.t1_Ioi_norm_integral_le_fourth_tail
#print axioms Markov.t1_Iio_norm_integral_le_fourth_tail
#print axioms Markov.t1_vertical_truncation_error
#print axioms Markov.t1_rieszIntegrand_shift
#print axioms Markov.t1_rieszMertens_integral_on_strip
#print axioms Markov.t1_vkRiesz_integral_finite_bound
#print axioms Markov.t1_vkContourHeight
#print axioms Markov.t1_vkWeight_height_exponents
#print axioms Markov.t1_vkContourHeight_eventually_admissible
#print axioms Markov.t1_vkContourRight
#print axioms Markov.t1_vkContourRight_bounds
#print axioms Markov.t1_vkContourRight_power
#print axioms Markov.t1_vkContourHeight_negThree
#print axioms Markov.t1_vkContourLeft_power
#print axioms Markov.t1_vkContour_eventual_scales
#print axioms Markov.t1_vkRieszMertens_eventual_bound
#print axioms Markov.t1_differenceWeight
#print axioms Markov.t1_rieszDifference
#print axioms Markov.t1_rieszDifferenceKernel
#print axioms Markov.t1_differenceWeight_abs
#print axioms Markov.t1_difference_polynomial_moment
#print axioms Markov.t1_rieszDifferenceKernel_eq_pow
#print axioms Markov.t1_rieszMertens_extend_sum
#print axioms Markov.t1_rieszDifference_eq_sum
#print axioms Markov.t1_rieszDifference_split
#print axioms Markov.t1_differenceWeightNorm
#print axioms Markov.t1_differenceBoundaryConstant
#print axioms Markov.t1_differenceWeightNorm_nonneg
#print axioms Markov.t1_differenceBoundaryConstant_nonneg
#print axioms Markov.t1_rieszDifferenceKernel_boundary_bound
#print axioms Markov.t1_differenceBoundary_card_le
#print axioms Markov.t1_rieszDifference_error
#print axioms Markov.t1_rieszDifference_vk_bound
#print axioms Markov.t1_mertens_le_difference_div_add_error
#print axioms Markov.t1_vkDesmoothingStep
#print axioms Markov.t1_vkDesmoothingStep_eventual_bounds
#print axioms Markov.t1_vkDesmoothingStep_power
#print axioms Markov.t1_headLog
#print axioms Markov.t1_headWeight
#print axioms Markov.t1_headLog_pos_on
#print axioms Markov.t1_headWeight_continuousOn
#print axioms Markov.t1_headWeight_antiderivative
#print axioms Markov.t1_headWeight_cell_bound
#print axioms Markov.t1_logarithmic_head_weight_sum
#print axioms Markov.t1_geometricNonzeroCoordinates
#print axioms Markov.t1_geometricPrimitiveCoordinates
#print axioms Markov.t1_geometricPrimitiveCount
#print axioms Markov.t1_geometricNonzeroCoordinates_finite
#print axioms Markov.t1_geometricPrimitiveCoordinates_finite
#print axioms Markov.t1_geometricNonzeroFinset
#print axioms Markov.t1_mem_geometricNonzeroFinset
#print axioms Markov.t1_primitive_finset_actual
#print axioms Markov.t1_geometricPrimitiveCount_eq_filter_card
#print axioms Markov.t1_geometricPrimitiveCount_moebius_fibers
#print axioms Markov.t1_dvd_integer_gcd_iff
#print axioms Markov.t1_integer_gcd_dvd_iff_nsmul
#print axioms Markov.t1_integer_nsmul_injective
#print axioms Markov.t1_integer_nsmul_ne_zero
