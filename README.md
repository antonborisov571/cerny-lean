# cerny-lean: Machine-Verified Bounds on Reset Thresholds of Synchronizing Automata

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24463928.svg)](https://doi.org/10.5281/zenodo.24463928)

A self-contained Lean 4 (`v4.36.0` / Mathlib `v4.36.0`) formalization establishing new general and structured upper bounds on the reset threshold $\operatorname{rt}(\mathcal{A})$ of synchronizing deterministic finite automata (DFAs), accompanied by three self-contained LaTeX preprints and a standalone statement-only verification audit.

Every theorem stated in the three preprints is formally verified in Lean 4 with **zero `sorry`**, **zero custom axioms**, **zero `native_decide`**, and **zero `maxHeartbeats` overrides**, using only the standard Lean logical axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Accompanying Preprints

1. **Paper 1 ([`papers/paper1_below_7_48/main.pdf`](papers/paper1_below_7_48/main.pdf), 24 pp.):** *Breaking the $\frac{7}{48} n^3$ Barrier for Synchronizing Automata* — proves the first general asymptotic upper bound strictly below $\frac{7}{48} n^3$ for all synchronizing automata, an explicit-$O(n^2)$ general bound $\frac{24646}{149769} n^3 + 50 n^2$ improving Shitov (2019) and Hong's unrefereed preprint (`hexagon:2611.00172v1`), and the exact transversal corank-gap bound $\delta(r) \le \lambda(r) + r + 1$.
2. **Paper 2 ([`papers/paper2_volkov_d6_d2/main.pdf`](papers/paper2_volkov_d6_d2/main.pdf), 15 pp.):** *Beating $2n^2 - 7n + 7$ for Transitive Defect-1 Automata and Sharpening Bounds for Completely Reachable and Imprimitive Automata* — improves Zhu (FSTTCS 2024) on his full transitive defect-$\le 1$ class to $2n^2 - 8n + 9$, establishes a strict improvement over Ferens–Szykuła (2025) for completely reachable automata via the defect-1 omitted-state set $M_1$, and proves zero-error congruence-collapse bounds for imprimitive automata.
3. **Paper 3 ([`papers/paper3_beyond_one_cluster/main.pdf`](papers/paper3_beyond_one_cluster/main.pdf), 20 pp.):** *Exact $(n-1)^2$ and Quadratic Reset Threshold Bounds Beyond One-Cluster Automata* — proves exact $(n-1)^2$ and quadratic bounds across cluster-balanced, opposite-drift, mixing, cyclic-basin, cycle-drain, partial-drain, non-strongly-connected 2-cycle, almost-uniform, two-value stationary, and super-Eulerian automata, together with an independent formalization of Zhu's July 2026 one-cluster theorem (`arXiv:2607.19675`).

---

## Summary of Verified Results

All bounds below hold for arbitrary finite nonempty state sets $Q$ ($n = |Q|$) and arbitrary (not necessarily finite) input alphabets $\alpha$, unless a specific subclass hypothesis is explicitly stated.

### 1. General Cubic Upper Bounds (Paper 1)

- **Strictly below $\frac{7}{48} n^3$ for all synchronizing automata:** There exist $\delta \in \mathbb{Q}_{>0}$ (equivalently positive integers $p, q$) and $N_0 \in \mathbb{N}$ such that every synchronizing $n$-state DFA with $n \ge N_0$ has a synchronizing word of length at most $(\frac{7}{48} - \delta) n^3$ (`Cerny.exists_strictly_below_seven_forty_eight`, `Cerny.below_seven_forty_eight`). This strictly improves both the classical peer-reviewed record of Shitov (2019, $\frac{8257}{49923} n^3 + O(n^2)$) and the unrefereed November 2026 uniform $\frac{7}{48} n^3 + o(n^3)$ preprint of Hong (`hexagon:2611.00506v1`).
- **Explicit-$O(n^2)$ sub-Shitov bound:** For every synchronizing $n$-state DFA ($n \ge 1$),
  $$149769\,\operatorname{rt}(\mathcal{A}) \le 24646\,n^3 + 7488450\,n^2 \qquad \left(\approx 0.164560\,n^3 + 50\,n^2\right)$$
  (`Cerny.sub_shitov_bound`), strictly beating Shitov (2019) for all $n \ge 59{,}908$ (`Cerny.sub_shitov_strictly_beats_shitov`) and Hong's unrefereed preprint (`hexagon:2611.00172v1`, $\frac{8242}{49923} n^3$) for all $n \ge 93{,}606$ (`Cerny.sub_shitov_strictly_beats_hong`).
- **Exact transversal corank-gap bound:** For every synchronizing $n$-state DFA and every $1 \le r \le n - 2$, the corank gap $\delta(r) = \lambda(r+1) - \lambda(r)$ satisfies $\delta(r) \le \lambda(r) + r + 1$ (`Cerny.corankGap_le_minCorankLen_add_succ`).
- **Formalized general baselines:** Complete formalizations of Pin–Frankl $\frac{n^3 - n}{6}$ (`Cerny.pin_frankl_bound`) and Shitov's $\frac{8257}{49923} n^3 + 3n^2$ (`Cerny.sub_pin_frankl_shitov_bound`).

### 2. Transitive Defect-1, Completely Reachable, and Imprimitive Automata (Paper 2)

- **Beating Zhu (FSTTCS 2024) on his full transitive class:** For every synchronizing $n$-state DFA ($n \ge 4$) whose bijective letters generate a transitive permutation group (primitive or imprimitive) and whose remaining letters all have defect $1$,
  $$\operatorname{rt}(\mathcal{A}) \le 2n^2 - 8n + 9 < 2n^2 - 7n + 7$$
  (`Cerny.transitive_defectOne_beats_zhu`), with exact $(n-1)^2$ for $n \le 4$ (`Cerny.transitive_defectOne_card_le_four_cerny`). For the coprime-cycle primitive subclass, $\operatorname{rt}(\mathcal{A}) \le (n-1)^2$ (`Cerny.primitive_coprimeCycle_cerny`).
- **Completely reachable automata (improving Ferens–Szykuła 2025):** Every transitive defect-1 automaton with strongly connected Rystsov graph (in particular, every primitive defect-1 automaton) is completely reachable (`Cerny.volkovD6_d1_isCompletelyReachable`, `Cerny.primitive_defectOne_isCompletelyReachable`). For every completely reachable automaton with defect-1 omitted-state set $M_1$, every permutation orbit meets $M_1$, giving the effective orbit cap $\ell_{\mathrm{eff}_1} \le \min(\ell_{\mathrm{orb}}, n - |M_1| + 1)$ and
  $$\operatorname{rt}(\mathcal{A}) \le 1 + (n - 2)(\ell_{\mathrm{eff}_1} + n) - n H_{n-2}$$
  (`Cerny.completelyReachable_effOrbit_bound`). This strictly improves Ferens–Szykuła (2025) whenever $|M_1| \ge 2$ and $\ell_{\mathrm{orb}} = n$ (`Cerny.completelyReachable_beats_ferensSzykula`), and breaks $2n^2$ to $(2 - \varepsilon)n^2 - n H_{n-2} + O(n)$ whenever $|M_1| \ge \varepsilon n$ (`Cerny.completelyReachable_breaks_two_n_sq`).
- **Zero-error congruence collapse for imprimitive automata:** Singleton-class congruence reduction preserving $(n-1)^2$ (`Cerny.singleton_congruence_preserves_cerny`), fat-congruence bound $96\,\operatorname{rt}(\mathcal{A}) \le 5n^3$ for $n \ge 5$ (`Cerny.fat_congruence_five_ninety_six`), equipartition bound $24\,\operatorname{rt}(\mathcal{A}) \le n^3$ for $n \ge 6$ (`Cerny.equipartition_congruence_one_twenty_fourth`), and an unconditional exact $(n-1)^2$ window for equipartition congruences with $m \le 2k$ and $k \le 2m^2$ (`Cerny.equipartition_congruence_cerny_window`).
- **Cycle-shift half-rank compression:** On any DFA containing an $n$-cycle letter and a non-injective letter, every subset $R$ of size $r > n/2$ compresses in length at most $2(n - r) + 1 \le n$, satisfying $r \cdot c(\mathcal{A}, R) \le n(n - 1)$ (`Cerny.nCycle_half_compression_c1`).

### 3. Exact $(n-1)^2$ and Quadratic Bounds Beyond One-Cluster Automata (Paper 3)

- **Cluster-balanced permutation automata:** Exact $(n-1)^2$ for all equal-cycle cluster-balanced permutation DFAs (`Cerny.clusterBalanced_equalCycle_cerny`, unifying Dubuc's circular theorem $c = 1$ and Kari's Eulerian/pseudo-Eulerian theorem $c = n$), and $< 2n^2$ for arbitrary cycle lengths (`Cerny.clusterBalanced_reset_bound`, `Cerny.clusterBalanced_quadratic_bound`).
- **Multi-cluster automata with arbitrary trees ($\ell \ge 0$):**
  - *Opposite-drift 2-cluster automata:* Exact $(n-1)^2$ (and $n^2 - 3n + 3$ for $n \ge 6$) for all cycle lengths $(m_1, m_2)$ and arbitrary trees $\ell \ge 0$, without strong connectivity, balance, or mixing (`Cerny.twoCluster_oppositeDrift_cerny`, `Cerny.twoCluster_oppositeDrift_ge_six_bound`).
  - *Mixing 2-cluster and cyclic-basin multi-cluster automata:* $\le 3(n-1)^2$ (general cycles) and $\le 2(n-1)^2$ (equal cycles) under balanced mixing (`Cerny.twoCluster_mixing_quadratic_bound`, `Cerny.twoCluster_equalCycle_mixing_bound`), and exact $(n-1)^2$ for cyclic-basin automata whenever $2m \le n$ or $m_0 \ge 2 \wedge 12m \le 7n$ (`Cerny.cyclicBasin_halfCycle_cerny`, `Cerny.cyclicBasin_sevenTwelfths_cerny`).
  - *Unbalanced cycle-drain, partial-drain, and non-SC 2-cycle automata:* $\le \frac{5n^2 - 6n + 13}{4}$ covering all Kisielewicz–Szykuła $\mathcal{A}_{2m-1}$ automata (`Cerny.cycleDrain_ks_regime_bound`); exact $(n-1)^2$ for all partial-drain 2-cycle DFAs with $r \ge 1$ and $2 r m_1 < m_2$ (`Cerny.partialDrain_all_exact_cerny`); quadratic small-$\gcd$ partial-drain bounds (`Cerny.smallGcd_r1_five_bound`, `Cerny.smallGcd_r1_le_half_bound`); and exact $(n-1)^2$ for all non-strongly-connected synchronizing 2-cycle DFAs (`Cerny.twoCycle_nonSC_cerny`).
- **Stationary-measure automata:**
  - Unified $\mathbb{R}$-proof of exact $(n-1)^2$ for almost-uniform stationary vectors (arbitrary real weights/ratio, matching Goel's unrefereed preprint `hexagon:2611.00635v1`) and unconditional Berlinkov quasi-Eulerian degree-1 automata without strong connectivity (`Cerny.almostUniform_cerny`, `Cerny.berlinkov_qe1_cerny`).
  - First uniform quadratic bound for all 2-exception two-value stationary vectors over $\mathbb{R}_{>0}$: $14\,\operatorname{rt}(\mathcal{A}) < 29(n-1)^2$ unconditionally (`Cerny.twoValue_k2_universal_bound`), with $< 2(n-1)^2$ outside $\frac{1}{2}\mathbb{Z}$, plus polynomial-in-$k$ bounds for general $k$-exception two-value vectors (`Cerny.twoValue_general_k_bound`).
  - Matrix-free proof of Szykuła's tier lemma (`Cerny.szykula_tier_lemma`) yielding exact $(n-1)^2$ for super-Eulerian integer stationary vectors up to constant excess (`Cerny.superEulerian_const_excess_cerny`) and logarithmic excess $J \le n + \lfloor\log_2 n\rfloor - 4$ for $n \ge 32$ (`Cerny.superEulerian_log_excess_cerny`).
- **Independent formalization of Zhu (July 2026) & classical landmarks:** Complete Lean 4 formalization of Zhu's annular spectral descent proof of the Černý conjecture for one-cluster automata (`arXiv:2607.19675`, `Cerny.oneCluster_cerny`), along with Černý's $(n-1)^2$ lower bound (`Cerny/LowerBound.lean`), structural $n \le 4$ (`Cerny/SmallCases.lean`), Eppstein's monotonic bound and rank-$\le 3$ (`Cerny/AdditionalClasses.lean`), Kari's Eulerian theorem (`Cerny/Eulerian.lean`), and Dubuc's circular theorem (`Cerny/Circular.lean`).

---

## What Remains Open

- **The general Černý conjecture** ($\operatorname{rt}(\mathcal{A}) \le (n-1)^2$ for all synchronizing $n$-state DFAs) remains open.
- **Any general subcubic bound** ($\operatorname{rt}(\mathcal{A}) = o(n^3)$, or $O(n^{3-\varepsilon})$ for any $\varepsilon > 0$) remains open.
- **Effective finite-$n$ threshold for `< 7/48 n³`:** `Cerny.below_seven_forty_eight` establishes an explicit positive constant $\delta > 0$ and threshold $N_0$, yielding an asymptotic improvement over $\frac{7}{48} n^3$; for moderate finite $n$, our explicit-$O(n^2)$ bound `Cerny.sub_shitov_bound` ($\frac{24646}{149769} n^3 + 50 n^2$) provides concrete crossovers ($n \ge 59{,}908$ against Shitov 2019).

---

## Methodology: AI-Assisted Discovery and Lean 4 Verification

Mathematical proof discovery, Lean 4 formalization, and LaTeX manuscript drafting in this project were carried out using AI-assisted workflows under human direction.

Crucially, **correctness of the mathematical statements does not depend on trusting any AI system**:
- Every theorem claimed in the accompanying preprints is compiled and type-checked by the Lean `4.36.0` kernel against Mathlib `v4.36.0` with `autoImplicit = false` and `relaxedAutoImplicit = false` (**31 Lean 4 files**, **40,840 total lines**: 28 mathematical modules totaling 39,978 lines, plus `Cerny.lean`, `Cerny/Verification.lean`, and `Cerny/StatementCheck.lean`).
- A global case-sensitive scan across all 31 files confirms **0 `sorry`**, **0 `admit`**, **0 custom `axiom`**, **0 `native_decide`**, **0 `ofReduceBool`**, **0 `unsafe`/`implemented_by`**, and **0 `maxHeartbeats` or `set_option` overrides** in proof or definition code.
- Verification is independently auditable at two layers:
  1. **Kernel replay:** `lake env leanchecker Cerny.StatementCheck` replays the compiled `.olean` environment from scratch without trusting tactic execution (exit `0`).
  2. **Definition & statement audit:** [`Cerny/Defs.lean`](Cerny/Defs.lean) contains the core automata-theoretic definitions (442 lines), [`Cerny/StatementCheck.lean`](Cerny/StatementCheck.lean) (521 lines, **44/44** checks) restates the 5 core theorems directly in raw `List.foldl` terms with zero custom definitions plus all 39 headline theorems across Papers 1–3, and [`Cerny/Verification.lean`](Cerny/Verification.lean) runs `#print axioms` across **220/220** exported declarations (strictly standard axioms only). See [`docs/STATEMENT_AUDIT.md`](docs/STATEMENT_AUDIT.md) and [`docs/verification_report.md`](docs/verification_report.md) for the complete audit reports.

---

## Quick Reproduction

Requires [elan](https://github.com/leanprover/elan) (which automatically installs Lean `v4.36.0` from `lean-toolchain`). From the repository root:

```bash
lake exe cache get && lake build && lake build Cerny.StatementCheck && lake env leanchecker Cerny.StatementCheck
```

*(Run `leanchecker` on `Cerny.StatementCheck` rather than the umbrella module `Cerny` to avoid probing an uncached upstream Mathlib auxiliary `.olean.private` file.)*

To also print the axiom dependencies of all 220 exported declarations:

```bash
lake build Cerny.Verification
```

Expected output: every command exits with status `0` and `0` warnings; all 220 audited declarations depend only on `[propext, Classical.choice, Quot.sound]` (or a subset thereof).

---

## Repository Structure and Module Index

The repository comprises **31 Lean 4 files (40,840 lines)**: **28 mathematical modules (39,978 lines)** plus `Cerny.lean`, `Cerny/Verification.lean`, and `Cerny/StatementCheck.lean`, organized by paper:

### Paper 1 — General Cubic Upper Bounds ([`papers/paper1_below_7_48/main.pdf`](papers/paper1_below_7_48/main.pdf))

| Module | Main Exported Declarations | Result |
| :--- | :--- | :--- |
| [`Cerny/BelowSevenFortyEight.lean`](Cerny/BelowSevenFortyEight.lean) | `exists_strictly_below_seven_forty_eight`, `below_seven_forty_eight` | First general upper bound strictly below $(7/48) n^3$ |
| [`Cerny/SubShitov.lean`](Cerny/SubShitov.lean) | `sub_shitov_bound`, `sub_shitov_strictly_beats_shitov`, `sub_shitov_strictly_beats_hong` | Explicit-$O(n^2)$ bound $\frac{24646}{149769} n^3 + 50 n^2$ |
| [`Cerny/ExactTransversal.lean`](Cerny/ExactTransversal.lean) | `corankGap_le_minCorankLen_add_succ`, `minCorankLen_succ_le_two_mul_add_succ` | Exact corank-gap bound $\delta(r) \le \lambda(r) + r + 1$ |
| [`Cerny/SubPinFrankl.lean`](Cerny/SubPinFrankl.lean) | `sub_pin_frankl_shitov_bound`, `sub_pin_frankl_strictly_beats_pin_frankl` | Formalization of Shitov (2019) $\frac{8257}{49923} n^3 + 3n^2$ |
| [`Cerny/Combinatorial.lean`](Cerny/Combinatorial.lean) | `pin_frankl_bound`, `cernyConjecture_of_stronglyConnected`, `rank_k_bridge_lemma` | SCC reduction, Pin–Frankl $(n^3 - n)/6$, rank-2/3 bridge |

### Paper 2 — Transitive Defect-1, Completely Reachable, and Imprimitive Automata ([`papers/paper2_volkov_d6_d2/main.pdf`](papers/paper2_volkov_d6_d2/main.pdf))

| Module | Main Exported Declarations | Result |
| :--- | :--- | :--- |
| [`Cerny/VolkovD6Transitive.lean`](Cerny/VolkovD6Transitive.lean) | `transitive_defectOne_beats_zhu`, `transitive_defectOne_card_le_four_cerny` | $2n^2 - 8n + 9$ beating Zhu (FSTTCS 2024) on full transitive defect-$\le 1$ class |
| [`Cerny/VolkovD6Record.lean`](Cerny/VolkovD6Record.lean) | `primitive_defectOne_beats_zhu`, `sccCount_half_eq_one_of_acyclic` | Combinatorial DAG-shift teleportation for primitive defect-1 DFAs |
| [`Cerny/AlpogePrimitive.lean`](Cerny/AlpogePrimitive.lean) | `primitive_coprimeCycle_cerny`, `primitive_sameCycle_reset_bound`, `primitive_defectOne_zhu_bound` | Exact $(n-1)^2$ coprime-cycle subclass & combinatorial $2n^2 - 7n + 7$ |
| [`Cerny/CompletelyReachable.lean`](Cerny/CompletelyReachable.lean) | `volkovD6_d1_isCompletelyReachable`, `completelyReachable_effOrbit_bound`, `completelyReachable_beats_ferensSzykula`, `completelyReachable_breaks_two_n_sq` | Transitive $d=1$ $\subseteq$ completely reachable; $M_1$-improved Ferens–Szykuła bound |
| [`Cerny/CongruenceCollapse.lean`](Cerny/CongruenceCollapse.lean) | `singleton_congruence_preserves_cerny`, `fat_congruence_five_ninety_six`, `equipartition_congruence_one_twenty_fourth`, `equipartition_congruence_cerny_window` | Zero-error congruence collapse ($5/96 n^3$, $n^3/24$, exact $(n-1)^2$ window) |
| [`Cerny/AlpogeCompression.lean`](Cerny/AlpogeCompression.lean) | `cycle_shift_indep_bound`, `nCycle_half_compression_c1`, `multiCycle_shift_indep_bound` | Cycle-shift large-subset compression for $r > n/2$ |

### Paper 3 — Exact $(n-1)^2$ and Quadratic Bounds Beyond One-Cluster ([`papers/paper3_beyond_one_cluster/main.pdf`](papers/paper3_beyond_one_cluster/main.pdf))

| Module | Main Exported Declarations | Result |
| :--- | :--- | :--- |
| [`Cerny/ClusterBalanced.lean`](Cerny/ClusterBalanced.lean) | `clusterBalanced_equalCycle_cerny`, `clusterBalanced_reset_bound`, `clusterBalanced_quadratic_bound` | Exact $(n-1)^2$ (equal cycles) and $< 2n^2$ (arbitrary cycles) for cluster-balanced DFAs |
| [`Cerny/AlpogeOppositeDrift.lean`](Cerny/AlpogeOppositeDrift.lean) | `twoCluster_oppositeDrift_cerny`, `twoCluster_oppositeDrift_ge_six_bound`, `twoCluster_fluxWitness_halfCycle_cerny` | Exact $(n-1)^2$ for all opposite-drift 2-cluster DFAs ($\ell \ge 0$) |
| [`Cerny/AlpogeThetaLift.lean`](Cerny/AlpogeThetaLift.lean) | `twoCluster_mixing_quadratic_bound`, `twoCluster_equalCycle_mixing_bound` | $\le 3(n-1)^2$ and $\le 2(n-1)^2$ for mixing 2-cluster DFAs ($\ell \ge 0$) |
| [`Cerny/AlpogeCyclicBasin.lean`](Cerny/AlpogeCyclicBasin.lean) | `cyclicBasin_threeHalves_bound`, `cyclicBasin_halfCycle_cerny`, `cyclicBasin_sevenTwelfths_cerny` | Cyclic-basin multi-cluster DFAs ($\ell \ge 0$) |
| [`Cerny/AlpogeCycleDrain.lean`](Cerny/AlpogeCycleDrain.lean) | `cycleDrain_ks_regime_bound`, `cycleDrain_twoFifths_cerny`, `cycleDrain_quadratic_bound` | Cycle-drain DFAs, solving all Kisielewicz–Szykuła $\mathcal{A}_{2m-1}$ to $\frac{5n^2 - 6n + 13}{4}$ |
| [`Cerny/AlpogePartialDrain.lean`](Cerny/AlpogePartialDrain.lean) | `partialDrain_threeHalves_bound`, `partialDrain_exact_cerny` | Partial cycle-drain 2-cycle DFAs ($2 r m_1 < m_2$) |
| [`Cerny/PartialDrainExact.lean`](Cerny/PartialDrainExact.lean) | `partialDrain_all_exact_cerny`, `smallGcd_r1_five_bound`, `smallGcd_r1_le_half_bound` | Exponential halving closing all $2 r m_1 < m_2$ to exact $(n-1)^2$ + small-$\gcd$ bounds |
| [`Cerny/TwoCycleNonSC.lean`](Cerny/TwoCycleNonSC.lean) | `twoCycle_nonSC_cerny` | Exact $(n-1)^2$ for all non-SC synchronizing 2-cycle DFAs |
| [`Cerny/AlmostUniform.lean`](Cerny/AlmostUniform.lean) | `almostUniform_cerny`, `berlinkov_qe1_cerny`, `multiException_half_bound` | Unified $\mathbb{R}$-proof of exact $(n-1)^2$ for almost-uniform & Berlinkov QE-1 DFAs |
| [`Cerny/TwoValueStationary.lean`](Cerny/TwoValueStationary.lean) | `twoValue_k2_universal_bound`, `twoValue_general_k_bound`, `szykula_tier_lemma`, `superEulerian_const_excess_cerny`, `superEulerian_log_excess_cerny` | Two-value stationary bounds ($14\,\operatorname{rt} < 29(n-1)^2$) & super-Eulerian exact $(n-1)^2$ |
| [`Cerny/OneCluster.lean`](Cerny/OneCluster.lean) | `oneCluster_cerny`, `oneCluster_reset_bound`, `oneCluster_short_relative_extension` | Independent formalization of Zhu (July 2026, `arXiv:2607.19675`) |

### Foundations and Verification Harnesses

| Module / File | Main Exported Declarations / Role |
| :--- | :--- |
| [`Cerny/Defs.lean`](Cerny/Defs.lean) | Core definitions (`DFA`, `eval`, `IsSyncWord`, `IsSynchronizing`, `resetThreshold`, `CernyConjecture`, `cernyDFA`) |
| [`Cerny/LowerBound.lean`](Cerny/LowerBound.lean) | Černý's Theorem (1964): exact $\operatorname{rt}(\mathcal{C}_n) = (n-1)^2$ (`cernyDFA_resetThreshold`) |
| [`Cerny/SmallCases.lean`](Cerny/SmallCases.lean) | Structural Černý conjecture for $n \in \{1, 2, 3, 4\}$ (`cerny_card_le_four`) |
| [`Cerny/AdditionalClasses.lean`](Cerny/AdditionalClasses.lean) | Monotonic automata (`monotonic_reset_bound`), rank $\le 2, 3$, Szykuła avoiding-subset lemma |
| [`Cerny/Eulerian.lean`](Cerny/Eulerian.lean) | Kari's Theorem (2003): `eulerian_cerny`, `eulerian_reset_bound` |
| [`Cerny/Circular.lean`](Cerny/Circular.lean) | Dubuc's Theorem (1998): `circular_cerny` |
| [`Cerny/StatementCheck.lean`](Cerny/StatementCheck.lean) | Standalone statement-only comparator restating flagship theorems in raw terms |
| [`Cerny/Verification.lean`](Cerny/Verification.lean) | Full `#print axioms` harness across all exported declarations |
| [`docs/STATEMENT_AUDIT.md`](docs/STATEMENT_AUDIT.md) | Independent statement-fidelity & kernel-replay audit report |
| [`docs/verification_report.md`](docs/verification_report.md) | Full build, axiom-transcript, and mathematical audit ledger |

---

## Author, Citation & License

**Author:** Anton Borisov ([ORCID 0009-0004-4709-6705](https://orcid.org/0009-0004-4709-6705), `@antonborisov571`).  
**Permanent Archive (Zenodo):** [doi:10.5281/zenodo.24463928](https://doi.org/10.5281/zenodo.24463928) (concept DOI for all versions: [doi:10.5281/zenodo.24463927](https://doi.org/10.5281/zenodo.24463927)).  
Licensed under the [Apache License 2.0](LICENSE). Citation metadata is provided in [`CITATION.cff`](CITATION.cff).
