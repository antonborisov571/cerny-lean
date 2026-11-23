import Cerny

/-!
# Publication-Grade Statement-Only Comparator (`Cerny.StatementCheck`)

This standalone audit module is designed for independent human and machine verification
(including standalone kernel replay via `lake env leanchecker Cerny.StatementCheck`).

1. **Section 0 (Zero-Custom-Definition Raw Statements):**
   Restates flagship general and classical results using **zero** custom `Cerny` definitions —
   only a raw transition function `step : Q → α → Q`, `List.foldl`, `List.length`, and
   `Fintype.card Q`.
2. **Section 1 (Paper 1 — Breaking `(7/48) n³`, Explicit Sub-Shitov & Exact Transversal):**
   Exact type-ascription checks of all 7 headline theorems in Paper 1.
3. **Section 2 (Paper 2 — Full-Transitive Volkov D6, Completely Reachable D2 & Imprimitive Collapse):**
   Exact type-ascription checks of all 11 headline theorems in Paper 2.
4. **Section 3 (Paper 3 — Exact `(n-1)²` & Quadratic Bounds Beyond One-Cluster + Classical Foundations):**
   Exact type-ascription checks of all 21 headline theorems in Paper 3.
5. **Section 4 (`#print axioms` Audit):**
   Runs `#print axioms` on every single `check_*` declaration to confirm that ONLY standard
   Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`) are used, with zero `sorryAx`,
   zero custom axioms, and zero `Lean.ofReduceBool` / `native_decide` shortcuts.
-/

namespace Cerny.StatementCheck

universe u v

/-! ## Section 0: Zero-Custom-Definition Raw Statements (`List.foldl` Only!) -/

/-- **Completely raw (zero custom definitions!) statement of Theorem T20 (`ℚ` form)**:
There exist universal constants `δ : ℚ` (`0 < δ`) and `N₀ : ℕ` such that for EVERY finite nonempty
state set `Q` of size `|Q| ≥ N₀`, EVERY alphabet `α`, and EVERY transition map `step : Q → α → Q`
admitting a synchronizing word (`∃ w q₀, ∀ q, w.foldl step q = q₀`), there exists a synchronizing
word `w` of length at most `(7 / 48 - δ) * |Q| ^ 3`. -/
theorem check_raw_below_7_48 :
    ∃ δ : ℚ, 0 < δ ∧ ∃ N₀ : ℕ,
      ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (step : Q → α → Q),
        N₀ ≤ Fintype.card Q →
        (∃ w : List α, ∃ q₀ : Q, ∀ q : Q, w.foldl step q = q₀) →
        ∃ w : List α, (∃ q₀ : Q, ∀ q : Q, w.foldl step q = q₀) ∧
          (w.length : ℚ) ≤ (7 / 48 - δ) * (Fintype.card Q : ℚ) ^ 3 := by
  obtain ⟨δ, hδ, N₀, h⟩ := Cerny.exists_strictly_below_seven_forty_eight.{u, v}
  exact ⟨δ, hδ, N₀, fun step hn hSync => h ⟨step⟩ hn hSync⟩

/-- **Completely raw (zero custom definitions!) statement of Theorem T20 (`ℕ` form)**:
`∃ p q > 0, ∃ N₀, ∀ step, ... → 48 * q * w.length ≤ (7 * q - p) * |Q| ^ 3`. -/
theorem check_raw_below_7_48_nat :
    ∃ (p q : ℕ), 0 < p ∧ 0 < q ∧ ∃ N₀ : ℕ,
      ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (step : Q → α → Q),
        (∃ w : List α, ∃ q₀ : Q, ∀ q : Q, w.foldl step q = q₀) →
        N₀ ≤ Fintype.card Q →
        ∃ w : List α, (∃ q₀ : Q, ∀ q : Q, w.foldl step q = q₀) ∧
          48 * q * w.length ≤ (7 * q - p) * (Fintype.card Q) ^ 3 := by
  obtain ⟨p, q, hp, hq, N₀, h⟩ := Cerny.below_seven_forty_eight.{u, v}
  exact ⟨p, q, hp, hq, N₀, fun step hSync hn => h ⟨step⟩ hSync hn⟩

/-- **Completely raw (zero custom definitions!) statement of Theorem T19 (Explicit-`O(n²)` Sub-Shitov)**:
For EVERY synchronizing DFA on `n ≥ 1` states, `149769 * |w| ≤ 24646 * n³ + 7488450 * n²`. -/
theorem check_raw_sub_shitov :
    ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (step : Q → α → Q),
      (∃ w : List α, ∃ q₀ : Q, ∀ q : Q, w.foldl step q = q₀) →
      ∃ w : List α, (∃ q₀ : Q, ∀ q : Q, w.foldl step q = q₀) ∧
        149769 * w.length ≤ 24646 * (Fintype.card Q) ^ 3 + 7488450 * (Fintype.card Q) ^ 2 :=
  fun step hSync => Cerny.sub_shitov_bound ⟨step⟩ hSync

/-- **Completely raw (zero custom definitions!) statement of Zhu's July 2026 One-Cluster Černý Theorem**:
Every synchronizing DFA having a letter `a` with a unique cycle `C` (nonempty, `a`-invariant,
`a`-transitive, eventually absorbing every state) admits a synchronizing word of length `≤ (|Q| - 1)²`. -/
theorem check_raw_oneCluster_cerny :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] (step : Q → α → Q),
      (∃ a : α, ∃ C : Set Q,
        C.Nonempty ∧
        (∀ q ∈ C, step q a ∈ C) ∧
        (∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => step x a)^[k] p = q) ∧
        (∀ q : Q, ∃ k : ℕ, (fun x => step x a)^[k] q ∈ C)) →
      (∃ w : List α, ∃ q₀ : Q, ∀ q : Q, w.foldl step q = q₀) →
      ∃ w : List α, (∃ q₀ : Q, ∀ q : Q, w.foldl step q = q₀) ∧
        w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  fun step hOC hSync => Cerny.oneCluster_cerny ⟨step⟩ hOC hSync

/-- **Completely raw (zero custom definitions!) statement of `n ≤ 4` Structural Černý**:
Every synchronizing DFA on `1 ≤ |Q| ≤ 4` states admits a synchronizing word of length `≤ (|Q| - 1)²`. -/
theorem check_raw_cerny_card_le_four :
    ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (step : Q → α → Q),
      Fintype.card Q ≤ 4 →
      (∃ w : List α, ∃ q₀ : Q, ∀ q : Q, w.foldl step q = q₀) →
      ∃ w : List α, (∃ q₀ : Q, ∀ q : Q, w.foldl step q = q₀) ∧
        w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  fun step h4 hSync => Cerny.cerny_card_le_four ⟨step⟩ h4 hSync

/-! ## Section 1: Paper 1 — Breaking `(7/48) n³`, Explicit Sub-Shitov & Exact Transversal (7 Theorems) -/

theorem check_p1_exists_strictly_below_seven_forty_eight :
    ∃ δ : ℚ, 0 < δ ∧ ∃ N₀ : ℕ,
      ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : Cerny.DFA Q α),
        N₀ ≤ Fintype.card Q → A.IsSynchronizing →
        ∃ w : List α, A.IsSyncWord w ∧
          (w.length : ℚ) ≤ (7 / 48 - δ) * (Fintype.card Q : ℚ) ^ 3 :=
  Cerny.exists_strictly_below_seven_forty_eight.{u, v}

theorem check_p1_below_seven_forty_eight :
    ∃ (p q : ℕ), 0 < p ∧ 0 < q ∧ ∃ N₀ : ℕ,
      ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : Cerny.DFA Q α),
        A.IsSynchronizing → N₀ ≤ Fintype.card Q →
        ∃ w : List α, A.IsSyncWord w ∧
          48 * q * w.length ≤ (7 * q - p) * (Fintype.card Q) ^ 3 :=
  Cerny.below_seven_forty_eight.{u, v}

theorem check_p1_sub_shitov_bound :
    ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : Cerny.DFA Q α),
      A.IsSynchronizing →
      ∃ w : List α, A.IsSyncWord w ∧
        149769 * w.length ≤ 24646 * (Fintype.card Q) ^ 3 + 7488450 * (Fintype.card Q) ^ 2 :=
  @Cerny.sub_shitov_bound.{u, v}

theorem check_p1_sub_shitov_strictly_beats_shitov :
    ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : Cerny.DFA Q α),
      A.IsSynchronizing → 59908 ≤ Fintype.card Q →
      ∃ w : List α, A.IsSyncWord w ∧ 49923 * w.length < 8257 * (Fintype.card Q) ^ 3 :=
  @Cerny.sub_shitov_strictly_beats_shitov.{u, v}

theorem check_p1_sub_shitov_strictly_beats_hong :
    ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : Cerny.DFA Q α),
      A.IsSynchronizing → 93606 ≤ Fintype.card Q →
      ∃ w : List α, A.IsSyncWord w ∧ 49923 * w.length < 8242 * (Fintype.card Q) ^ 3 :=
  @Cerny.sub_shitov_strictly_beats_hong.{u, v}

theorem check_p1_sub_pin_frankl_shitov_bound :
    ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : Cerny.DFA Q α),
      A.IsSynchronizing →
      ∃ w : List α, A.IsSyncWord w ∧
        49923 * w.length ≤ 8257 * (Fintype.card Q) ^ 3 + 149769 * (Fintype.card Q) ^ 2 :=
  @Cerny.sub_pin_frankl_shitov_bound.{u, v}

theorem check_p1_corankGap_le_minCorankLen_add_succ :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α) (hSync : A.IsSynchronizing) {r : ℕ},
      1 ≤ r → r + 2 ≤ Fintype.card Q →
      Cerny.corankGap A hSync r ≤ Cerny.minCorankLen A hSync r + r + 1 :=
  @Cerny.corankGap_le_minCorankLen_add_succ.{u, v}

/-! ## Section 2: Paper 2 — Volkov D6, Completely Reachable D2 & Imprimitive Collapse (11 Theorems) -/

theorem check_p2_transitive_defectOne_beats_zhu :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [Nonempty Q] [DecidableEq Q]
      (A : Cerny.DFA Q α) (S₀ S₁ : Set α),
      4 ≤ Fintype.card Q → A.IsSynchronizing → Cerny.IsTransitiveDefectLeOne A S₀ S₁ →
      ∃ w : List α, A.IsSyncWord w ∧
        w.length ≤ 2 * (Fintype.card Q) ^ 2 - 8 * Fintype.card Q + 9 ∧
        w.length < 2 * (Fintype.card Q) ^ 2 - 7 * Fintype.card Q + 7 :=
  @Cerny.transitive_defectOne_beats_zhu.{u, v}

theorem check_p2_primitive_defectOne_beats_zhu :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [Nonempty Q] [DecidableEq Q]
      (A : Cerny.DFA Q α) (S : Set α) (a : α),
      4 ≤ Fintype.card Q → A.IsPrimitivePermSet S →
      (A.image Finset.univ [a]).card + 1 = Fintype.card Q →
      ∃ w : List α, A.IsSyncWord w ∧
        w.length ≤ 2 * (Fintype.card Q) ^ 2 - 8 * Fintype.card Q + 9 :=
  @Cerny.primitive_defectOne_beats_zhu.{u, v}

theorem check_p2_primitive_coprimeCycle_cerny :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [Nonempty Q] [DecidableEq Q]
      (A : Cerny.DFA Q α) (S : Set α) (a b : α) (z₀ m₀ : Q) (r d : ℕ),
      A.IsPrimitivePermSet S → A.IsDefectOneLetter a z₀ m₀ → b ∈ S →
      2 ≤ r → 1 ≤ d → d < r → Nat.Coprime d r →
      (fun x => A.step x b)^[r] z₀ = z₀ →
      (∀ k : ℕ, 0 < k → k < r → (fun x => A.step x b)^[k] z₀ ≠ z₀) →
      (fun x => A.step x b)^[d] z₀ = m₀ →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.primitive_coprimeCycle_cerny.{u, v}

theorem check_p2_completelyReachable_effOrbit_bound :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q] (A : Cerny.DFA Q α),
      A.IsCompletelyReachable → 2 ≤ Fintype.card Q →
      ∃ w : List α, A.IsSyncWord w ∧
        (w.length : ℚ) ≤
          1 + ((Fintype.card Q - 2 : ℕ) : ℚ) * ((Cerny.effOrbitCap A : ℚ) + (Fintype.card Q : ℚ)) -
            (Fintype.card Q : ℚ) * Cerny.harmonicRat (Fintype.card Q - 2) :=
  @Cerny.completelyReachable_effOrbit_bound.{u, v}

theorem check_p2_completelyReachable_beats_ferensSzykula :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q] (A : Cerny.DFA Q α),
      A.IsCompletelyReachable → 3 ≤ Fintype.card Q →
      Cerny.maxOrbitSize A = Fintype.card Q → 2 ≤ (Cerny.defectOneOmitted A).card →
      ∃ w : List α, A.IsSyncWord w ∧
        (w.length : ℚ) ≤
          1 + ((Fintype.card Q - 2 : ℕ) : ℚ) * ((Cerny.maxOrbitSize A : ℚ) + (Fintype.card Q : ℚ)) -
            (Fintype.card Q : ℚ) * Cerny.harmonicRat (Fintype.card Q - 2) -
            (((Cerny.defectOneOmitted A).card - 1 : ℕ) : ℚ) * ((Fintype.card Q - 2 : ℕ) : ℚ) ∧
        (w.length : ℚ) <
          1 + ((Fintype.card Q - 2 : ℕ) : ℚ) * ((Cerny.maxOrbitSize A : ℚ) + (Fintype.card Q : ℚ)) -
            (Fintype.card Q : ℚ) * Cerny.harmonicRat (Fintype.card Q - 2) :=
  @Cerny.completelyReachable_beats_ferensSzykula.{u, v}

theorem check_p2_completelyReachable_breaks_two_n_sq :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q] (A : Cerny.DFA Q α),
      A.IsCompletelyReachable → 2 ≤ Fintype.card Q →
      ∀ (ε : ℚ), ε * (Fintype.card Q : ℚ) ≤ ((Cerny.defectOneOmitted A).card : ℚ) →
      ∃ w : List α, A.IsSyncWord w ∧
        (w.length : ℚ) ≤
          1 + ((Fintype.card Q - 2 : ℕ) : ℚ) * ((2 - ε) * (Fintype.card Q : ℚ) + 1) -
            (Fintype.card Q : ℚ) * Cerny.harmonicRat (Fintype.card Q - 2) :=
  @Cerny.completelyReachable_breaks_two_n_sq.{u, v}

theorem check_p2_volkovD6_d1_isCompletelyReachable :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [Nonempty Q] [DecidableEq Q]
      (A : Cerny.DFA Q α) (S₀ S₁ : Set α),
      Cerny.IsTransitiveDefectLeOne A S₀ S₁ →
      Cerny.VolkovD6Transitive.blockCount A S₀ S₁ = 1 →
      A.IsCompletelyReachable :=
  @Cerny.volkovD6_d1_isCompletelyReachable.{u, v}

theorem check_p2_fat_congruence_five_ninety_six :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [Nonempty Q] (A : Cerny.DFA Q α),
      A.IsStronglyConnected → A.IsSynchronizing →
      ∀ (s : Setoid Q), A.IsCongruence s.r →
      2 ≤ Cerny.numClasses s →
      (∀ c : Quotient s, 2 ≤ (Cerny.congruenceClass s c).card) →
      5 ≤ Fintype.card Q →
      ∃ w : List α, A.IsSyncWord w ∧ 96 * w.length ≤ 5 * (Fintype.card Q) ^ 3 :=
  @Cerny.fat_congruence_five_ninety_six.{u, v}

theorem check_p2_equipartition_congruence_one_twenty_fourth :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [Nonempty Q] (A : Cerny.DFA Q α),
      A.IsSynchronizing →
      ∀ (s : Setoid Q), A.IsCongruence s.r →
      ∀ (m : ℕ), 2 ≤ m → 2 ≤ Cerny.numClasses s →
      (∀ c : Quotient s, (Cerny.congruenceClass s c).card = m) →
      6 ≤ Fintype.card Q →
      ∃ w : List α, A.IsSyncWord w ∧ 24 * w.length ≤ (Fintype.card Q) ^ 3 :=
  @Cerny.equipartition_congruence_one_twenty_fourth.{u, v}

theorem check_p2_equipartition_congruence_cerny_window :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [Nonempty Q] (A : Cerny.DFA Q α),
      A.IsSynchronizing →
      ∀ (s : Setoid Q), A.IsCongruence s.r →
      ∀ (m : ℕ), 2 ≤ m → 2 ≤ Cerny.numClasses s →
      (∀ c : Quotient s, (Cerny.congruenceClass s c).card = m) →
      m ≤ 2 * Cerny.numClasses s → Cerny.numClasses s ≤ 2 * m ^ 2 →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.equipartition_congruence_cerny_window.{u, v}

theorem check_p2_nCycle_half_compression_c1 :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α) (b a : α) (hn : 2 ≤ Fintype.card Q)
      (c : Fin (Fintype.card Q) ≃ Q),
      (∀ j : Fin (Fintype.card Q),
        A.step (c j) b = c ⟨(j.val + 1) % Fintype.card Q, Nat.mod_lt _ (by omega)⟩) →
      ¬ Function.Injective (fun q => A.step q a) →
      ∀ (R : Finset Q), Fintype.card Q < 2 * R.card →
      ∃ w : List α,
        w.length ≤ 2 * (Fintype.card Q - R.card) + 1 ∧
        w.length ≤ Fintype.card Q ∧
        R.card * w.length ≤ Fintype.card Q * (Fintype.card Q - 1) ∧
        (A.image R w).card < R.card :=
  @Cerny.nCycle_half_compression_c1.{u, v}

/-! ## Section 3: Paper 3 — Exact `(n-1)²` & Quadratic Bounds Beyond One-Cluster (21 Theorems) -/

theorem check_p3_clusterBalanced_equalCycle_cerny :
    ∀ {Q : Type u} [Fintype Q] [Nonempty Q] [DecidableEq Q]
      {α : Type v} [Fintype α] [DecidableEq α]
      (A : Cerny.DFA Q α) (a : α) (m : ℕ),
      A.IsClusterBalanced a → A.IsEqualCyclePerm a m → A.IsSynchronizing →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.clusterBalanced_equalCycle_cerny.{u, v}

theorem check_p3_clusterBalanced_quadratic_bound :
    ∀ {Q : Type u} [Fintype Q] [Nonempty Q] [DecidableEq Q]
      {α : Type v} [Fintype α] [DecidableEq α]
      (A : Cerny.DFA Q α) (a : α),
      A.IsClusterBalanced a → A.IsSynchronizing →
      ∃ w : List α, A.IsSyncWord w ∧
        w.length ≤ 2 * (Fintype.card Q - 1) ^ 2 ∧
        w.length < 2 * (Fintype.card Q) ^ 2 :=
  @Cerny.clusterBalanced_quadratic_bound.{u, v}

theorem check_p3_twoCluster_oppositeDrift_cerny :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α), A.IsSynchronizing →
      ∀ (D : Cerny.TwoClusterData A) (b_pos b_neg : α),
      (D.C₁.filter (fun q => A.step q b_pos ∈ D.B₂)).card <
        (D.C₂.filter (fun q => A.step q b_pos ∈ D.B₁)).card →
      (D.C₂.filter (fun q => A.step q b_neg ∈ D.B₁)).card <
        (D.C₁.filter (fun q => A.step q b_neg ∈ D.B₂)).card →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.twoCluster_oppositeDrift_cerny.{u, v}

theorem check_p3_twoCluster_fluxWitness_quadratic_bound :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α), A.IsSynchronizing →
      ∀ (D : Cerny.TwoClusterData A) (u_pos u_neg : List α) (L₀ : ℕ),
      L₀ ≤ Fintype.card Q - 1 → u_pos.length ≤ L₀ → u_neg.length ≤ L₀ →
      D.flux12 u_pos < D.flux21 u_pos → D.flux21 u_neg < D.flux12 u_neg →
      ∃ w : List α, A.IsSyncWord w ∧
        w.length ≤ 2 * (Fintype.card Q) ^ 2 + 7 - 7 * Fintype.card Q ∧
        w.length < 2 * (Fintype.card Q - 1) ^ 2 :=
  @Cerny.twoCluster_fluxWitness_quadratic_bound.{u, v}

theorem check_p3_twoCluster_mixing_quadratic_bound :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α) (D : Cerny.TwoClusterData A), A.IsSynchronizing →
      ∀ (b : α),
      (D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card =
        (D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card →
      ((D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card : ℚ) / (D.C₁.card : ℚ) +
        ((D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card : ℚ) / (D.C₂.card : ℚ) ≥ 1 →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ 3 * (Fintype.card Q - 1) ^ 2 :=
  @Cerny.twoCluster_mixing_quadratic_bound.{u, v}

theorem check_p3_cyclicBasin_halfCycle_cerny :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α) (a b : α), A.IsSynchronizing →
      ∀ (D : Cerny.CyclicBasinData A a b),
      2 * (D.c * D.m₀) ≤ Fintype.card Q →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.cyclicBasin_halfCycle_cerny.{u, v}

theorem check_p3_cyclicBasin_sevenTwelfths_cerny :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α) (a b : α), A.IsSynchronizing →
      ∀ (D : Cerny.CyclicBasinData A a b),
      2 ≤ D.m₀ → 12 * (D.c * D.m₀) ≤ 7 * Fintype.card Q →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.cyclicBasin_sevenTwelfths_cerny.{u, v}

theorem check_p3_cycleDrain_ks_regime_bound :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α), A.IsSynchronizing →
      ∀ (a b : α) (C₁ : Finset Q),
      2 ≤ C₁.card → C₁.card < Fintype.card Q → 2 * C₁.card ≤ Fintype.card Q + 1 →
      (∀ q ∈ C₁, A.step q a ∈ C₁) →
      (∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) →
      (∀ q, q ∉ C₁ → A.step q a ∉ C₁) →
      ∀ (u₀ : Q), u₀ ∈ C₁ → (∀ q : Q, q ≠ u₀ → A.step q b ∈ C₁) →
      ∃ w : List α, A.IsSyncWord w ∧
        4 * w.length ≤ 5 * (Fintype.card Q) ^ 2 - 6 * Fintype.card Q + 13 ∧
        w.length ≤ (5 * (Fintype.card Q) ^ 2 - 6 * Fintype.card Q + 13) / 4 :=
  @Cerny.cycleDrain_ks_regime_bound.{u, v}

theorem check_p3_partialDrain_all_exact_cerny :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α), A.IsSynchronizing →
      ∀ (a b : α) (C₁ C₂ : Finset Q),
      2 ≤ C₁.card → 2 ≤ C₂.card → Disjoint C₁ C₂ → C₁ ∪ C₂ = Finset.univ →
      (∀ q ∈ C₁, A.step q a ∈ C₁) →
      (∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) →
      (∀ q ∈ C₂, A.step q a ∈ C₂) →
      (∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) →
      (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1 →
      1 ≤ (C₂.filter (fun x => A.step x b ∈ C₂)).card →
      2 * (C₂.filter (fun x => A.step x b ∈ C₂)).card * C₁.card < C₂.card →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.partialDrain_all_exact_cerny.{u, v}

theorem check_p3_smallGcd_r1_five_bound :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α), A.IsSynchronizing →
      ∀ (a b : α) (C₁ C₂ : Finset Q),
      2 ≤ C₁.card → Disjoint C₁ C₂ → C₁ ∪ C₂ = Finset.univ →
      (∀ q ∈ C₁, A.step q a ∈ C₁) →
      (∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) →
      (∀ q ∈ C₂, A.step q a ∈ C₂) →
      (∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) →
      (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1 →
      (C₂.filter (fun x => A.step x b ∈ C₂)).card = 1 →
      2 * Nat.gcd C₁.card C₂.card < C₂.card →
      ∃ w : List α, A.IsSyncWord w ∧
        w.length ≤ 5 * (Fintype.card Q) ^ 2 + 35 - 26 * Fintype.card Q ∧
        w.length < 5 * (Fintype.card Q - 1) ^ 2 :=
  @Cerny.smallGcd_r1_five_bound.{u, v}

theorem check_p3_twoCycle_nonSC_cerny :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α), A.IsSynchronizing → ¬ A.IsStronglyConnected →
      ∀ (a : α) (C₁ C₂ : Finset Q),
      C₁.Nonempty → C₂.Nonempty → Disjoint C₁ C₂ → C₁ ∪ C₂ = Finset.univ →
      (∀ q ∈ C₁, A.step q a ∈ C₁) →
      (∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) →
      (∀ q ∈ C₂, A.step q a ∈ C₂) →
      (∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.twoCycle_nonSC_cerny.{u, v}

theorem check_p3_almostUniform_cerny :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [Fintype α] [DecidableEq Q]
      (A : Cerny.DFA Q α), A.IsSynchronizing →
      ∀ (P : Cerny.PositiveStationary A) (x₀ : Q) (c : ℝ),
      (∀ q : Q, q ≠ x₀ → P.π q = c) →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.almostUniform_cerny.{u, v}

theorem check_p3_berlinkov_qe1_cerny :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [Fintype α] [DecidableEq Q]
      (A : Cerny.DFA Q α), A.IsSynchronizing →
      ∀ (x₀ s : Q), x₀ ≠ s → ∀ (β : α → ℝ),
      (∀ a : α, 0 < β a) → (∑ a : α, β a) = 1 →
      (∀ a : α, A.step x₀ a = x₀ ∨ A.step x₀ a = s) →
      (∀ q : Q, q ≠ x₀ → q ≠ s → (∑ p : Q, ∑ a : α, if A.step p a = q then β a else 0) = 1) →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.berlinkov_qe1_cerny.{u, v}

theorem check_p3_twoValue_k2_universal_bound :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [Fintype α] [DecidableEq Q]
      (A : Cerny.DFA Q α), A.IsSynchronizing →
      ∀ (P : Cerny.PositiveStationary A) (X : Finset Q),
      X.card = 2 → 3 ≤ Fintype.card Q →
      ∀ (α₀ : ℝ), 0 < α₀ →
      (∀ q : Q, P.π q = if q ∈ X then α₀ else 1) →
      ∃ w : List α, A.IsSyncWord w ∧ 14 * w.length < 29 * (Fintype.card Q - 1) ^ 2 :=
  @Cerny.twoValue_k2_universal_bound.{u, v}

theorem check_p3_superEulerian_log_excess_cerny :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [Fintype α] [DecidableEq Q]
      (A : Cerny.DFA Q α), A.IsSynchronizing →
      ∀ (P : Cerny.PositiveStationary A) (w_int : Q → ℕ),
      (∀ q : Q, 1 ≤ w_int q) →
      (∀ q : Q, P.π q = (w_int q : ℝ)) →
      32 ≤ Fintype.card Q →
      (∑ q : Q, w_int q) - Finset.univ.sup w_int ≤ Fintype.card Q + Nat.log 2 (Fintype.card Q) - 4 →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.superEulerian_log_excess_cerny.{u, v}

theorem check_p3_oneCluster_cerny :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] (A : Cerny.DFA Q α),
      A.IsOneCluster → A.IsSynchronizing →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.oneCluster_cerny.{u, v}

theorem check_p3_oneCluster_reset_bound :
    ∀ {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
      (A : Cerny.DFA Q α), A.IsSynchronizing →
      ∀ (a : α) (C : Finset Q) (ℓ : ℕ), C.Nonempty →
      (∀ q ∈ C, A.step q a ∈ C) →
      (∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) →
      (∀ q : Q, (fun x => A.step x a)^[ℓ] q ∈ C) →
      ∃ w : List α, A.IsSyncWord w ∧
        w.length ≤ (C.card - 1) * (Fintype.card Q - 1) + C.card * ℓ :=
  @Cerny.oneCluster_reset_bound.{u, v}

theorem check_p3_eulerian_cerny :
    ∀ {Q : Type u} [Fintype Q] [Nonempty Q] [DecidableEq Q]
      {α : Type v} [Fintype α] (A : Cerny.DFA Q α),
      A.IsEulerian → A.IsSynchronizing →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.eulerian_cerny.{u, v}

theorem check_p3_circular_cerny :
    ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : Cerny.DFA Q α),
      A.IsCircular → A.IsSynchronizing →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.circular_cerny.{u, v}

theorem check_p3_cernyDFA_resetThreshold :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      (Cerny.cernyDFA n hn).resetThreshold (Cerny.cernyDFA_isSynchronizing n hn) = (n - 1) ^ 2 :=
  Cerny.cernyDFA_resetThreshold

theorem check_p3_cerny_card_le_four :
    ∀ {α : Type v} {Q : Type u} [Fintype Q] [Nonempty Q] (A : Cerny.DFA Q α),
      Fintype.card Q ≤ 4 → A.IsSynchronizing →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  @Cerny.cerny_card_le_four.{v, u}

end Cerny.StatementCheck

/-! ## Section 4: Complete `#print axioms` Audit on All 44 Comparator Declarations -/

-- Section 0: Zero-Custom-Definition Raw Statements (5)
#print axioms Cerny.StatementCheck.check_raw_below_7_48
#print axioms Cerny.StatementCheck.check_raw_below_7_48_nat
#print axioms Cerny.StatementCheck.check_raw_sub_shitov
#print axioms Cerny.StatementCheck.check_raw_oneCluster_cerny
#print axioms Cerny.StatementCheck.check_raw_cerny_card_le_four

-- Section 1: Paper 1 (7)
#print axioms Cerny.StatementCheck.check_p1_exists_strictly_below_seven_forty_eight
#print axioms Cerny.StatementCheck.check_p1_below_seven_forty_eight
#print axioms Cerny.StatementCheck.check_p1_sub_shitov_bound
#print axioms Cerny.StatementCheck.check_p1_sub_shitov_strictly_beats_shitov
#print axioms Cerny.StatementCheck.check_p1_sub_shitov_strictly_beats_hong
#print axioms Cerny.StatementCheck.check_p1_sub_pin_frankl_shitov_bound
#print axioms Cerny.StatementCheck.check_p1_corankGap_le_minCorankLen_add_succ

-- Section 2: Paper 2 (11)
#print axioms Cerny.StatementCheck.check_p2_transitive_defectOne_beats_zhu
#print axioms Cerny.StatementCheck.check_p2_primitive_defectOne_beats_zhu
#print axioms Cerny.StatementCheck.check_p2_primitive_coprimeCycle_cerny
#print axioms Cerny.StatementCheck.check_p2_completelyReachable_effOrbit_bound
#print axioms Cerny.StatementCheck.check_p2_completelyReachable_beats_ferensSzykula
#print axioms Cerny.StatementCheck.check_p2_completelyReachable_breaks_two_n_sq
#print axioms Cerny.StatementCheck.check_p2_volkovD6_d1_isCompletelyReachable
#print axioms Cerny.StatementCheck.check_p2_fat_congruence_five_ninety_six
#print axioms Cerny.StatementCheck.check_p2_equipartition_congruence_one_twenty_fourth
#print axioms Cerny.StatementCheck.check_p2_equipartition_congruence_cerny_window
#print axioms Cerny.StatementCheck.check_p2_nCycle_half_compression_c1

-- Section 3: Paper 3 (21)
#print axioms Cerny.StatementCheck.check_p3_clusterBalanced_equalCycle_cerny
#print axioms Cerny.StatementCheck.check_p3_clusterBalanced_quadratic_bound
#print axioms Cerny.StatementCheck.check_p3_twoCluster_oppositeDrift_cerny
#print axioms Cerny.StatementCheck.check_p3_twoCluster_fluxWitness_quadratic_bound
#print axioms Cerny.StatementCheck.check_p3_twoCluster_mixing_quadratic_bound
#print axioms Cerny.StatementCheck.check_p3_cyclicBasin_halfCycle_cerny
#print axioms Cerny.StatementCheck.check_p3_cyclicBasin_sevenTwelfths_cerny
#print axioms Cerny.StatementCheck.check_p3_cycleDrain_ks_regime_bound
#print axioms Cerny.StatementCheck.check_p3_partialDrain_all_exact_cerny
#print axioms Cerny.StatementCheck.check_p3_smallGcd_r1_five_bound
#print axioms Cerny.StatementCheck.check_p3_twoCycle_nonSC_cerny
#print axioms Cerny.StatementCheck.check_p3_almostUniform_cerny
#print axioms Cerny.StatementCheck.check_p3_berlinkov_qe1_cerny
#print axioms Cerny.StatementCheck.check_p3_twoValue_k2_universal_bound
#print axioms Cerny.StatementCheck.check_p3_superEulerian_log_excess_cerny
#print axioms Cerny.StatementCheck.check_p3_oneCluster_cerny
#print axioms Cerny.StatementCheck.check_p3_oneCluster_reset_bound
#print axioms Cerny.StatementCheck.check_p3_eulerian_cerny
#print axioms Cerny.StatementCheck.check_p3_circular_cerny
#print axioms Cerny.StatementCheck.check_p3_cernyDFA_resetThreshold
#print axioms Cerny.StatementCheck.check_p3_cerny_card_le_four
