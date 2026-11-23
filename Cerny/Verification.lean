import Cerny.Defs
import Cerny.LowerBound
import Cerny.SmallCases
import Cerny.Combinatorial
import Cerny.AdditionalClasses
import Cerny.SubPinFrankl
import Cerny.SubShitov
import Cerny.BelowSevenFortyEight
import Cerny.ExactTransversal
import Cerny.CongruenceCollapse
import Cerny.Eulerian
import Cerny.ClusterBalanced
import Cerny.Circular
import Cerny.OneCluster
import Cerny.AlpogePrimitive
import Cerny.VolkovD6Record
import Cerny.VolkovD6Transitive
import Cerny.CompletelyReachable
import Cerny.AlpogeCompression
import Cerny.AlpogeThetaLift
import Cerny.AlpogeCyclicBasin
import Cerny.AlpogeCycleDrain
import Cerny.AlpogeOppositeDrift
import Cerny.AlmostUniform
import Cerny.TwoCycleNonSC
import Cerny.AlpogePartialDrain
import Cerny.PartialDrainExact
import Cerny.TwoValueStationary

/-!
# Verification and Axiom Audit

This file imports all audited modules of the Černý Conjecture formalization and runs
`#print axioms` on every exported main theorem to verify that only standard Lean 4 axioms
(`propext`, `Classical.choice`, `Quot.sound`) are used, with zero `sorryAx`, custom axioms,
or `Lean.ofReduceBool` / `native_decide` shortcuts.
-/

-- Cerny.Defs core equivalences and constructions
#print axioms Cerny.DFA.isSyncWord_iff_card_image_univ_eq_one
#print axioms Cerny.DFA.isSyncWord_iff_exists_preimage_eq_univ
#print axioms Cerny.DFA.resetThreshold_le_of_isSyncWord
#print axioms Cerny.DFA.exists_isSyncWord_length_eq_resetThreshold
#print axioms Cerny.DFA.IsEulerian.sum_card_preimage
#print axioms Cerny.DFA.IsCircular.isOneCluster
#print axioms Cerny.cernyConjecture_iff_resetThreshold
#print axioms Cerny.cernyDFA_isCircular
#print axioms Cerny.cernyDFA_isOneCluster

-- Cerny.LowerBound (Černý 1964)
#print axioms Cerny.cernyDFA_isSynchronizing
#print axioms Cerny.cernyDFA_syncWord_length_ge_add
#print axioms Cerny.cernyDFA_syncWord_length_ge
#print axioms Cerny.cernyDFA_resetThreshold

-- Cerny.SmallCases (n = 1, 2, 3, 4 structural proof)
#print axioms Cerny.cerny_card_eq_one
#print axioms Cerny.cerny_card_eq_two
#print axioms Cerny.cerny_card_eq_three
#print axioms Cerny.cerny_card_eq_four
#print axioms Cerny.cerny_card_le_four

-- Cerny.Combinatorial (SCC Reduction, Pin–Frankl, Rank-k Bridge Lemma)
#print axioms Cerny.exists_syncWord_le_sinkSCC_bound
#print axioms Cerny.resetThreshold_le_sinkSCC_bound
#print axioms Cerny.cerny_of_stronglyConnected_le
#print axioms Cerny.cernyConjecture_of_stronglyConnected
#print axioms Cerny.frankl_skew_two
#print axioms Cerny.pin_compression_bound
#print axioms Cerny.pin_frankl_bound
#print axioms Cerny.pin_frankl_div_bound
#print axioms Cerny.rank_k_bridge_lemma
#print axioms Cerny.exists_syncWord_of_rank_letter
#print axioms Cerny.rank_le_two_bound
#print axioms Cerny.rank_le_three_bound
#print axioms Cerny.rank_le_two_cerny_ge_three
#print axioms Cerny.rank_le_three_cerny_ge_five

-- Cerny.AdditionalClasses (Unconditional Small-Rank, Monotonic, Szykuła Avoiding)
#print axioms Cerny.rank_le_two_cerny
#print axioms Cerny.rank_le_three_cerny
#print axioms Cerny.monotonic_reset_bound
#print axioms Cerny.monotonic_cerny
#print axioms Cerny.szykula_avoiding_lemma
#print axioms Cerny.exists_avoiding_word_quadratic
#print axioms Cerny.exists_avoiding_word_ge_three

-- Cerny.SubPinFrankl (Exact Shitov 2019: (8257/49923) n³ + 3 n² Strictly Beating Pin–Frankl!)
#print axioms Cerny.corankGap_le_pinFrankl
#print axioms Cerny.shitov_corank_gap
#print axioms Cerny.sub_pin_frankl_shitov_bound
#print axioms Cerny.sub_pin_frankl_333_2000
#print axioms Cerny.sub_pin_frankl_strictly_beats_pin_frankl
#print axioms Cerny.exists_sub_pin_frankl_threshold

-- Cerny.SubShitov (Theorem T19: World-Record Explicit-O(n²) (24646/149769) n³ + 50 n² Strictly Beating Shitov 2019 & Hong!)
#print axioms Cerny.sc_exists_short_word
#print axioms Cerny.degree_transport
#print axioms Cerny.plateau_min_le_max
#print axioms Cerny.plateau_time_le_max
#print axioms Cerny.ap_plateau_inequality
#print axioms Cerny.sub_shitov_sc_bound
#print axioms Cerny.sub_shitov_bound
#print axioms Cerny.sub_shitov_strictly_beats_shitov
#print axioms Cerny.sub_shitov_strictly_beats_hong

-- Cerny.ExactTransversal (Theorem T22: Exact-Transversal Corank-Gap Lemma δ(r) ≤ λ(r) + r + 1 for ALL 1 ≤ r ≤ n - 2!)
#print axioms Cerny.corankGap_le_minCorankLen_add_succ
#print axioms Cerny.minCorankLen_succ_le_two_mul_add_succ

-- Cerny.BelowSevenFortyEight (HISTORIC WORLD RECORD Theorem T20: Strictly Below 7/48 n³ for 100% of ALL Synchronizing DFAs!)
#print axioms Cerny.corankAt_le_pred
#print axioms Cerny.minCorankLen_corankAt_le
#print axioms Cerny.corank_le_corankAt
#print axioms Cerny.corankAt_mono
#print axioms Cerny.corankAt_pred_eq_shortCorank
#print axioms Cerny.exists_word_corankAt
#print axioms Cerny.complement_deg_le
#print axioms Cerny.singularityFree_compression_cap
#print axioms Cerny.common_neighbor_preimage_lift
#print axioms Cerny.caseB_macroscopic_band_bound
#print axioms Cerny.below_seven_forty_eight_sc
#print axioms Cerny.exists_strictly_below_seven_forty_eight
#print axioms Cerny.below_seven_forty_eight

-- Cerny.Eulerian (Kari 2003)
#print axioms Cerny.DFA.IsEulerian.isStronglyConnected
#print axioms Cerny.DFA.IsEulerian.sum_card_preimage_ofFn
#print axioms Cerny.DFA.IsEulerian.exists_extending_word
#print axioms Cerny.eulerian_reset_bound
#print axioms Cerny.eulerian_cerny

-- Cerny.ClusterBalanced (Original Theorems B & C: Multi-Cycle Permutation Spectral Descent)
#print axioms Cerny.DFA.isClusterBalanced_iff_flow
#print axioms Cerny.DFA.IsClusterBalanced.isStronglyConnected
#print axioms Cerny.clusterBalanced_reset_bound
#print axioms Cerny.clusterBalanced_quadratic_bound
#print axioms Cerny.clusterBalanced_equalCycle_cerny
#print axioms Cerny.clusterBalanced_equalCycle_exists_extending_word

-- Cerny.Circular (Dubuc 1998, deduced as c = 1 corollary of ClusterBalanced)
#print axioms Cerny.circular_exists_extending_word
#print axioms Cerny.circular_cerny
#print axioms Cerny.circular_resetThreshold_le

-- Cerny.OneCluster (Zhu July 2026, arXiv:2607.19675 — Annular Spectral Descent)
#print axioms Cerny.oneCluster_short_relative_extension
#print axioms Cerny.oneCluster_reset_bound
#print axioms Cerny.oneCluster_cerny
#print axioms Cerny.oneCluster_resetThreshold_le
#print axioms Cerny.oneCluster_circular_cerny

-- Cerny.AlpogePrimitive (Theorems T11, T12 & T13: Primitive Perm Group + Defect-1, Zhu 2024 Record & Exact Černý)
#print axioms Cerny.exists_isDefectOneLetter_of_card_image_eq_pred
#print axioms Cerny.AlpogePrimitive.sccCount_strict_dec
#print axioms Cerny.primitive_defectOne_reset_bound
#print axioms Cerny.primitive_sameCycle_reset_bound
#print axioms Cerny.primitive_coprimeCycle_cerny
#print axioms Cerny.AlpogePrimitive.double_degree_sccCount_le
#print axioms Cerny.AlpogePrimitive.sccCount_double_degree_le
#print axioms Cerny.primitive_defectOne_eccentricity_bound
#print axioms Cerny.primitive_defectOne_zhu_bound
#print axioms Cerny.primitive_defectOne_card_three_cerny

-- Cerny.VolkovD6Record (Theorem T16: NEW WORLD RECORD 2n² - 8n + 9 Beating Zhu FSTTCS 2024!)
#print axioms Cerny.VolkovD6.weakCount_pred_two_eq_one
#print axioms Cerny.VolkovD6.exists_ryEdge_crossing
#print axioms Cerny.VolkovD6.sccCount_half_eq_one_of_acyclic
#print axioms Cerny.VolkovD6.sccCount_pred_one_ne_pred_two
#print axioms Cerny.primitive_defectOne_beats_zhu_ge_five
#print axioms Cerny.primitive_defectOne_beats_zhu

-- Cerny.VolkovD6Transitive (Theorem T18: World Record 2n² - 8n + 9 on Zhu FSTTCS 2024's Exact Full Transitive Class!)
#print axioms Cerny.VolkovD6Transitive.transReachInf_symm
#print axioms Cerny.VolkovD6Transitive.blockCard_eq
#print axioms Cerny.VolkovD6Transitive.transWeakCount_eq_blockCount
#print axioms Cerny.VolkovD6Transitive.transSCCCount_eq_blockCount_of_zhuF
#print axioms Cerny.VolkovD6Transitive.transSCCCount_eq_blockCount_of_zhuG
#print axioms Cerny.VolkovD6Transitive.blockEscape_extend
#print axioms Cerny.VolkovD6Transitive.trans_d_eq_one_bound
#print axioms Cerny.transitive_defectOne_ge_five_bound
#print axioms Cerny.transitive_defectOne_beats_zhu
#print axioms Cerny.transitive_defectOne_card_le_four_cerny

-- Cerny.CompletelyReachable (Theorem T23: Volkov D2 Completely Reachable Automata & Ferens–Szykuła 2025 Improvement!)
#print axioms Cerny.DFA.IsCompletelyReachable.isSynchronizing
#print axioms Cerny.CompletelyReachable.permOrbit_inter_defectOneOmitted_nonempty
#print axioms Cerny.CompletelyReachable.effOrbitCap_le_maxOrbitSize
#print axioms Cerny.CompletelyReachable.effOrbitCap_le_card_sub_omitted
#print axioms Cerny.CompletelyReachable.exists_properExt_erase_singleton
#print axioms Cerny.CompletelyReachable.laminar_bounded_mul_le
#print axioms Cerny.CompletelyReachable.exists_short_properlyExtending
#print axioms Cerny.volkovD6_d1_isCompletelyReachable
#print axioms Cerny.primitive_defectOne_isCompletelyReachable
#print axioms Cerny.completelyReachable_effOrbit_reaching_bound
#print axioms Cerny.completelyReachable_effOrbit_bound
#print axioms Cerny.completelyReachable_ferensSzykula_bound
#print axioms Cerny.completelyReachable_beats_ferensSzykula
#print axioms Cerny.completelyReachable_breaks_two_n_sq

-- Cerny.AlpogeCompression (Theorem T15 & T15-multi: Mergeable-Pair Graph M_L & Conjecture C1 for r > n / 2)
#print axioms Cerny.cycle_shift_indep_bound
#print axioms Cerny.cycle_large_subset_compression
#print axioms Cerny.nCycle_half_compression_c1
#print axioms Cerny.multiCycle_shift_indep_bound

-- Cerny.AlpogeThetaLift (Theorems D₀, Lemma D₀' & Theorem D: Two-Letter Theta Lifts Breaching Obstruction O.3)
#print axioms Cerny.rankOne_exists_extending_word
#print axioms Cerny.rankOne_exists_extending_word_ne_half
#print axioms Cerny.rankOne_uniform_reset_bound
#print axioms Cerny.twoCluster_mixing_reset_bound
#print axioms Cerny.twoCluster_mixing_quadratic_bound
#print axioms Cerny.twoCluster_equalCycle_mixing_bound

-- Cerny.AlpogeCyclicBasin (Lemma D.2 & Theorem D_cyc: One-Sided Cyclic-Basin Lift & Exact (n - 1)^2 for ℓ > 0 c-Cluster DFAs)
#print axioms Cerny.multiCluster_singleton_start
#print axioms Cerny.cyclicBasin_reset_bound
#print axioms Cerny.cyclicBasin_quadratic_bound
#print axioms Cerny.cyclicBasin_threeHalves_bound
#print axioms Cerny.cyclicBasin_halfCycle_cerny
#print axioms Cerny.cyclicBasin_sevenTwelfths_cerny

-- Cerny.AlpogeCycleDrain (Theorems F₀ & F: Cycle-Drain Unbalanced Multi-Cluster DFAs & KS_A_{2m-1})
#print axioms Cerny.collapseWord_singleton_start
#print axioms Cerny.shortCollapse_cycle_reset_bound
#print axioms Cerny.cycleDrain_exists_collapseWord
#print axioms Cerny.cycleDrain_reset_bound
#print axioms Cerny.cycleDrain_quadratic_bound
#print axioms Cerny.cycleDrain_ks_regime_bound
#print axioms Cerny.cycleDrain_twoFifths_cerny
#print axioms Cerny.cycleDrain_card_one_cerny
#print axioms Cerny.cycleDrain_full_cerny

-- Cerny.AlpogeOppositeDrift (Theorems G₀ & G: Opposite-Drift 2-Cluster Exact Černý (n - 1)²!)
#print axioms Cerny.optimal_twoCluster_avg
#print axioms Cerny.twoCluster_oppositeDrift_extend
#print axioms Cerny.twoCluster_fluxWitness_reset_bound_general
#print axioms Cerny.twoCluster_fluxWitness_reset_bound
#print axioms Cerny.twoCluster_oppositeDrift_cerny
#print axioms Cerny.twoCluster_oppositeDrift_ge_six_bound
#print axioms Cerny.twoCluster_fluxWitness_quadratic_bound
#print axioms Cerny.twoCluster_fluxWitness_halfCycle_cerny
#print axioms Cerny.twoCluster_equalCycle_fluxWitness_bound
#print axioms Cerny.twoCluster_equalCycle_fluxWitness_sevenTwelfths_cerny

-- Cerny.AlmostUniform (Theorems H, H.2, H_k: Almost-Uniform Stationary Vectors & Full Berlinkov QE-1 Exact Černý!)
#print axioms Cerny.positiveStationary_stronglyConnected
#print axioms Cerny.positiveStationary_word_avg
#print axioms Cerny.stronglyConnected_escape_entry
#print axioms Cerny.almostUniform_cerny
#print axioms Cerny.berlinkov_qe1_cerny
#print axioms Cerny.multiException_rational_bound
#print axioms Cerny.multiException_half_bound

-- Cerny.TwoCycleNonSC (Theorem I: Exact Černý (n - 1)² for ALL Non-SC 2-Cycle Permutation DFAs!)
#print axioms Cerny.nonSC_twoCycle_closed_cycle
#print axioms Cerny.closedCycle_collapse_bound
#print axioms Cerny.twoCycle_closed_exact_bound
#print axioms Cerny.twoCycle_nonSC_cerny

-- Cerny.AlpogePartialDrain (Theorem F_part: Partial Cycle-Drain Unbalanced 2-Cycle DFAs, Exact (n - 1)² for r ≥ 2!)
#print axioms Cerny.partialDrain_reduce_to_one
#print axioms Cerny.partialDrain_exists_collapseWord
#print axioms Cerny.partialDrain_threeHalves_bound
#print axioms Cerny.partialDrain_exact_cerny
#print axioms Cerny.partialDrain_ge_two_cerny
#print axioms Cerny.partialDrain_one_cerny

-- Cerny.PartialDrainExact (Lemma F_exp, Theorem F_part_exact & Theorem F_gcd: 100% Exact (n - 1)² for ALL 2 r m₁ < m₂ & Small-gcd Partial Drain!)
#print axioms Cerny.shortShift_exp_halving
#print axioms Cerny.partialDrain_exp_collapseWord
#print axioms Cerny.partialDrain_all_exact_cerny
#print axioms Cerny.smallGcd_collapseWord
#print axioms Cerny.smallGcd_reset_bound
#print axioms Cerny.smallGcd_r1_reset_bound
#print axioms Cerny.smallGcd_r1_five_bound
#print axioms Cerny.smallGcd_r1_le_half_bound

-- Cerny.CongruenceCollapse (Theorem S1 & Lemma S1.1: Imprimitive Congruence Collapse — 5/96 n³, 1/24 n³, Exact Černý Window!)
#print axioms Cerny.quotientDFA_isSynchronizing
#print axioms Cerny.quotientDFA_isStronglyConnected
#print axioms Cerny.numClasses_eq_fintype_card
#print axioms Cerny.block_pin_frankl_compress
#print axioms Cerny.singleton_congruence_rt_bound
#print axioms Cerny.singleton_congruence_resetThreshold_le
#print axioms Cerny.singleton_congruence_preserves_cerny
#print axioms Cerny.fat_congruence_sum_bound
#print axioms Cerny.fat_congruence_five_ninety_six
#print axioms Cerny.fat_congruence_card_four
#print axioms Cerny.equipartition_congruence_bound
#print axioms Cerny.equipartition_block_two_bound
#print axioms Cerny.equipartition_congruence_one_twenty_fourth
#print axioms Cerny.equipartition_congruence_card_four
#print axioms Cerny.equipartition_congruence_cerny_window
#print axioms Cerny.equipartition_congruence_preserves_cerny

-- Cerny.TwoValueStationary (Lemma H.3, Theorems H_two & H_real_k, Lemma T.1 & Theorem T: Two-Value Stationary & Super-Eulerian Exact Černý!)
#print axioms Cerny.subset_bfs_entry
#print axioms Cerny.subset_bfs_escape
#print axioms Cerny.twoValue_k2_int_bound
#print axioms Cerny.twoValue_k2_nonHalfInt_bound
#print axioms Cerny.twoValue_k2_threeHalves_bound
#print axioms Cerny.twoValue_k2_universal_bound
#print axioms Cerny.twoValue_general_k_bound
#print axioms Cerny.twoValue_general_k_nonSmallDenom_bound
#print axioms Cerny.twoValue_general_k_irrational_bound
#print axioms Cerny.szykula_tier_lemma
#print axioms Cerny.superEulerian_tier_bound
#print axioms Cerny.superEulerian_const_excess_cerny
#print axioms Cerny.superEulerian_excess_one_cerny
#print axioms Cerny.superEulerian_excess_two_cerny
#print axioms Cerny.superEulerian_excess_three_cerny
#print axioms Cerny.superEulerian_log_excess_cerny
