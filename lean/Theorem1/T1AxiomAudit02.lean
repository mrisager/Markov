import T1GeometricMobius
import T1UniformLatticeError
import T1SmallDivisorHead
import T1GeometricThreshold
import T1GeometricHyperbola
import T1MertensEnvelope
import T1GeometricCountingBounds
import T1GeometricTailBound
import T1GeometricPartialCutoff
import T1MertensSquareAbel
import T1MertensSquareFiniteBound
import T1MoebiusSquareCoefficient
import T1MoebiusSquareTail
import T1GeometricCutoff
import T1RealCutoffSelection
import T1VKCutoffSelection
import T1VKScaleAlgebra
import T1MertensVKEnvelope
import T1VKCutoffTerms
import T1AmbientConjugation
import T1LatticeRotationCoordinates
import T1ReflectionAlgebra
import T1LatticeTurns
import T1BoundaryOrbits
import T1AmbientAxisSimplicity
import T1GeometricRotation
import T1GeometricReflection
import T1GeometricDihedral
import T1FareyWords
import T1FareyTraceOrder
import T1FrickeNumbers
import T1MarkovDescent
import T1MarkovGeneration
import T1MarkovChildren
import T1FareyTraceTriples
import T1LengthVariable
import T1FareyGeometricLength
import T1GeometricBoundaryOrbits
import T1MarkovTreeParent
import T1MarkovWords
import T1FareyMarkovWordMap
import T1FareyWordCoverage
import T1FareyWordUnique
import T1SectorMarkovEquiv
import T1MarkovExceptionalCount

#print axioms Markov.t1_mem_coordinate_norm_iff
#print axioms Markov.t1_euclidean_direction_nsmul
#print axioms Markov.t1_intrinsic_norm_nsmul
#print axioms Markov.t1_geometric_zero_mem
#print axioms Markov.t1_geometricNonzero_card
#print axioms Markov.t1_geometricLatticeCount_pos
#print axioms Markov.t1_geometric_divisor_fiber_image
#print axioms Markov.t1_geometric_divisor_fiber_card
#print axioms Markov.t1_geometricPrimitiveCount_moebius_scaled
#print axioms Markov.t1_geometricPrimitiveCount_moebius_full
#print axioms Markov.t1_latticeErrorScale
#print axioms Markov.t1_nonzeroLatticeError
#print axioms Markov.t1_latticeErrorScale_pos
#print axioms Markov.t1_one_isBigO_latticeErrorScale
#print axioms Markov.t1_nonzeroLatticeError_isBigO
#print axioms Markov.t1_uniform_nonzero_lattice_error
#print axioms Markov.t1_headWeight_eq_kernel
#print axioms Markov.t1_errorScale_at_div
#print axioms Markov.t1_geometricMobiusHead
#print axioms Markov.t1_moebiusSquarePartial
#print axioms Markov.t1_geometric_head_error_identity
#print axioms Markov.t1_geometric_small_divisor_bound
#print axioms Markov.t1_geometricLength
#print axioms Markov.t1_geometricLength_pos
#print axioms Markov.t1_geometricThreshold
#print axioms Markov.t1_geometricThreshold_iff
#print axioms Markov.t1_geometricThreshold_le_cutoff
#print axioms Markov.t1_geometric_threshold_fiber
#print axioms Markov.t1_geometric_small_radius_empty
#print axioms Markov.t1_geometric_mobius_tail_hyperbola
#print axioms Markov.t1_mertensNat_abs_le
#print axioms Markov.t1_mertensNat_real_abs_le
#print axioms Markov.t1_mertensRatio
#print axioms Markov.t1_mertensRatio_nonneg
#print axioms Markov.t1_mertensRatio_le_one
#print axioms Markov.t1_mertensEnvelope
#print axioms Markov.t1_mertensEnvelope_bddAbove
#print axioms Markov.t1_mertensEnvelope_nonneg
#print axioms Markov.t1_mertensEnvelope_le_one
#print axioms Markov.t1_mertensEnvelope_dominates
#print axioms Markov.t1_mertensEnvelope_antitone
#print axioms Markov.t1_mertensEnvelope_le_of_uniform_bound
#print axioms Markov.t1_geometricComparisonConstant
#print axioms Markov.t1_geometricComparisonConstant_pos
#print axioms Markov.t1_geometricComparisonConstant_ge_one
#print axioms Markov.t1_geometricLength_traceNorm
#print axioms Markov.t1_euclidean_le_geometricLength
#print axioms Markov.t1_geometricMinimumLength
#print axioms Markov.t1_geometricMinimumLength_pos
#print axioms Markov.t1_geometricLength_lower
#print axioms Markov.t1_geometricCountingConstant
#print axioms Markov.t1_geometricCountingConstant_nonneg
#print axioms Markov.t1_finite_geometric_count_le
#print axioms Markov.t1_geometricNonzeroFinset_length_bounds
#print axioms Markov.t1_geometricNonzeroFinset_empty_of_small
#print axioms Markov.t1_geometricNonzeroFinset_card_le
#print axioms Markov.t1_geometricReciprocalConstant
#print axioms Markov.t1_geometricReciprocalConstant_nonneg
#print axioms Markov.t1_geometric_reciprocal_sum_le
#print axioms Markov.t1_geometricMobiusTail
#print axioms Markov.t1_geometric_tail_envelope_sum
#print axioms Markov.t1_geometricTailConstant
#print axioms Markov.t1_geometricTailConstant_pos
#print axioms Markov.t1_geometric_mobius_tail_bound
#print axioms Markov.t1_geometric_primitive_head_tail
#print axioms Markov.t1_geometric_cutoff_admissible
#print axioms Markov.t1_geometric_partial_cutoff_bound
#print axioms Markov.t1_mertensNat_succ
#print axioms Markov.t1_moebius_square_abel
#print axioms Markov.t1_square_abel_kernel_nonneg
#print axioms Markov.t1_square_abel_kernel_bound
#print axioms Markov.t1_reciprocal_interval_telescope
#print axioms Markov.t1_mertens_square_kernel_sum_bound
#print axioms Markov.t1_moebius_square_finite_tail_bound
#print axioms Markov.t1_moebiusSquareTerm
#print axioms Markov.t1_moebiusSquareTerm_complex
#print axioms Markov.t1_moebiusSquareTerm_summable
#print axioms Markov.t1_moebiusSquareTerm_tsum
#print axioms Markov.t1_moebiusSquarePartial_eq_range
#print axioms Markov.t1_moebiusSquarePartial_tendsto
#print axioms Markov.t1_moebiusSquarePartial_interval
#print axioms Markov.t1_moebiusSquarePartial_tail_bound
#print axioms Markov.t1_geometric_primitive_cutoff_bound
#print axioms Markov.t1_realCutoff
#print axioms Markov.t1_realCutoff_bounds
#print axioms Markov.t1_realCutoff_radius
#print axioms Markov.t1_realCutoff_ratio
#print axioms Markov.t1_vkY
#print axioms Markov.t1_vkY_tendsto
#print axioms Markov.t1_vkY_eventually_le_quarterPower
#print axioms Markov.t1_vkCutoff_eventually_admissible
#print axioms Markov.t1_primitiveUnconditionalScale_vkWeight
#print axioms Markov.t1_vk_tail_isLittleO
#print axioms Markov.t1_MertensVKBound
#print axioms Markov.t1_mertens_vk_implies_envelope
#print axioms Markov.t1_vkCutoff_head
#print axioms Markov.t1_vkCutoff_tail
#print axioms Markov.t1_ambientConjugation
#print axioms Markov.t1_ambientConjugation_val
#print axioms Markov.t1_ambient_quotient_eq_iff
#print axioms Markov.t1_ambientConjugation_trace
#print axioms Markov.t1_ambientConjugation_period
#print axioms Markov.t1_ambientConjugation_axis
#print axioms Markov.t1_latticeRotation
#print axioms Markov.t1_latticeRotationHom
#print axioms Markov.t1_latticeRotation_coprime
#print axioms Markov.t1_ambient_T_basis_zero
#print axioms Markov.t1_ambient_T_basis_one
#print axioms Markov.t1_ambient_T_marked_coordinates
#print axioms Markov.t1_latticeSwap
#print axioms Markov.t1_reflectMatrix
#print axioms Markov.t1_latticeSwap_add
#print axioms Markov.t1_reflectMatrix_mul
#print axioms Markov.t1_reflectMatrix_trace
#print axioms Markov.t1_reflectMatrix_adjugate
#print axioms Markov.t1_reflectedQuadrant
#print axioms Markov.t1_reflectedQuadrant_directions
#print axioms Markov.t1_reflectedQuadrant_matrices
#print axioms Markov.t1_seededFarey_reflection
#print axioms Markov.t1_quadrantSeededFarey_reflection
#print axioms Markov.t1_quadrantWordTrace_reflection
#print axioms Markov.t1_latticeTurn
#print axioms Markov.t1_dihedralAction
#print axioms Markov.t1_latticeRotation_coprime_iff
#print axioms Markov.t1_latticeRotation_iterate_coprime_iff
#print axioms Markov.t1_latticeTurn_eq_iterate
#print axioms Markov.t1_latticeTurn_coprime_iff
#print axioms Markov.t1_dihedralAction_coprime_iff
#print axioms Markov.t1_oppositeTurn
#print axioms Markov.t1_latticeTurn_opposite
#print axioms Markov.t1_dihedralAction_opposite
#print axioms Markov.t1_shortOrbit
#print axioms Markov.t1_middleOrbit
#print axioms Markov.t1_shortOrbit_card
#print axioms Markov.t1_middleOrbit_card
#print axioms Markov.t1_boundaryOrbits_disjoint
#print axioms Markov.t1_shortOrbit_eq_turn_image
#print axioms Markov.t1_middleOrbit_eq_turn_image
#print axioms Markov.t1_shortOrbit_neg_iff
#print axioms Markov.t1_middleOrbit_neg_iff
#print axioms Markov.t1_positive_coprime_multiple_self
#print axioms Markov.t1_ambientConjugation_projected_axis_injective
#print axioms Markov.t1_ambientConjugation_period_eq_primitive_norm
#print axioms Markov.t1_geometricLength_rotation
#print axioms Markov.t1_primitive_exists_quadrantWordTrace
#print axioms Markov.t1_quadrantWordTrace_geometricLength
#print axioms Markov.t1_geometricLength_swap
#print axioms Markov.t1_geometricLength_rotation_iterate
#print axioms Markov.t1_geometricLength_turn
#print axioms Markov.t1_geometricLength_dihedralAction
#print axioms Markov.t1_fareyWordDirections
#print axioms Markov.t1_fareyWordMatrices
#print axioms Markov.t1_fareyWordDirection
#print axioms Markov.t1_fareyWord_holonomy
#print axioms Markov.t1_fareyWord_seeded
#print axioms Markov.t1_fareyWord_cone
#print axioms Markov.t1_fareyWordDirection_primitive
#print axioms Markov.t1_fareyWordDirection_strict
#print axioms Markov.t1_seededFarey_exists_word
#print axioms Markov.t1_fareyWord_seed_traces
#print axioms Markov.t1_fareyWord_trace_order
#print axioms Markov.t1_traceNumber
#print axioms Markov.t1_traceNumber_spec
#print axioms Markov.t1_positiveFricke_numbers
#print axioms Markov.t1_traceNumber_left_move
#print axioms Markov.t1_traceNumber_right_move
#print axioms Markov.t1_ordered_markov_largest_lt
#print axioms Markov.t1_vieta_complement_product
#print axioms Markov.t1_vieta_complement_pos
#print axioms Markov.t1_vieta_complement_equation
#print axioms Markov.t1_vieta_strict_descent
#print axioms Markov.t1_markov_exceptional
#print axioms Markov.t1_markov_sorted_parent
#print axioms Markov.t1_vietaLeft
#print axioms Markov.t1_vietaRight
#print axioms Markov.t1_vietaSuccessor
#print axioms Markov.t1_markovGenerated
#print axioms Markov.t1_all_ordered_markov_generated
#print axioms Markov.t1_ordered_markov_left_child
#print axioms Markov.t1_ordered_markov_right_child
#print axioms Markov.t1_vietaSuccessor_preserves_ordered
#print axioms Markov.t1_markovGenerated_ordered
#print axioms Markov.t1_markovGenerated_iff_ordered
#print axioms Markov.t1_fareyWordTriple
#print axioms Markov.t1_fareyWord_number_order
#print axioms Markov.t1_fareyWordTriple_ordered
#print axioms Markov.t1_fareyWordTriple_strict
#print axioms Markov.t1_fareyWordTriple_nil
#print axioms Markov.t1_fareyWordTriple_left
#print axioms Markov.t1_fareyWordTriple_right
#print axioms Markov.t1_markovLength
#print axioms Markov.t1_arcosh_log_gap
#print axioms Markov.t1_arcosh_square_log_gap
#print axioms Markov.t1_markovLength_square_error
#print axioms Markov.t1_markovLength_square_error_isBigO_one
#print axioms Markov.t1_fareyWord_coordinateSeeded
#print axioms Markov.t1_fareyWord_geometric_length
#print axioms Markov.t1_markovLength_le_iff
#print axioms Markov.t1_fareyWord_geometric_cutoff_iff
#print axioms Markov.t1_geometricLength_short_seed
#print axioms Markov.t1_geometricLength_middle_seed
#print axioms Markov.t1_shortOrbit_primitive_length
#print axioms Markov.t1_middleOrbit_primitive_length
#print axioms Markov.t1_markovLength_pos
#print axioms Markov.t1_boundaryOrbits_length_le
#print axioms Markov.t1_vietaParent
#print axioms Markov.t1_vietaParent_left
#print axioms Markov.t1_vietaParent_right
#print axioms Markov.t1_vietaSuccessor_parent
#print axioms Markov.t1_vietaSuccessor_unique_parent
#print axioms Markov.t1_vietaChildren_distinct
#print axioms Markov.t1_markovWord
#print axioms Markov.t1_markovWord_ordered
#print axioms Markov.t1_markovWord_strict
#print axioms Markov.t1_markovWord_height_ge
#print axioms Markov.t1_markovWord_parent_cons
#print axioms Markov.t1_markovWord_cons_ne_nil
#print axioms Markov.t1_markovWord_injective
#print axioms Markov.t1_markovGenerated_exception_or_word
#print axioms Markov.t1_ordered_markov_exception_or_word
#print axioms Markov.t1_fareyBranch
#print axioms Markov.t1_fareyBranch_involutive
#print axioms Markov.t1_fareyToMarkovWord
#print axioms Markov.t1_fareyToMarkovWord_injective
#print axioms Markov.t1_fareyToMarkovWord_surjective
#print axioms Markov.t1_fareyWordTriple_eq_markovWord
#print axioms Markov.t1_fareyWordTriple_injective
#print axioms Markov.t1_ordered_markov_exception_or_farey_word
#print axioms Markov.t1_strict_sector_coordinate_primitive
#print axioms Markov.t1_strict_sector_exists_farey_word
#print axioms Markov.t1_fareyWordDirections_injective
#print axioms Markov.t1_fareyWordDirection_injective
#print axioms Markov.t1_strict_sector_exists_unique_farey_word
#print axioms Markov.t1_primitiveSector
#print axioms Markov.t1_nonexceptionalMarkovTriples
#print axioms Markov.t1_fareyWordSector
#print axioms Markov.t1_fareyWordSector_bijective
#print axioms Markov.t1_wordSectorEquiv
#print axioms Markov.t1_fareyWordTriple_nonexceptional
#print axioms Markov.t1_fareyWordNonexceptionalTriple
#print axioms Markov.t1_fareyWordNonexceptionalTriple_bijective
#print axioms Markov.t1_wordTripleEquiv
#print axioms Markov.t1_sectorTripleEquiv
#print axioms Markov.t1_sectorTripleEquiv_length
#print axioms Markov.t1_sectorTripleEquiv_cutoff
#print axioms Markov.t1_markovExceptionalFinset
#print axioms Markov.t1_nonexceptionalTriplesUpTo
#print axioms Markov.t1_markovExceptionalFinset_card
#print axioms Markov.t1_markovExceptionalFinset_subset
#print axioms Markov.t1_nonexceptionalTriplesUpTo_eq_sdiff
#print axioms Markov.t1_nonexceptionalTriplesUpTo_count
#print axioms Markov.t1_nonexceptionalTriplesUpTo_real_count
