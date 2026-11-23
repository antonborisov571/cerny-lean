import Cerny.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Alpöge-Method Mergeable-Pair Graph Compression Bounds (Theorem T15 & T15-multi)

This file formalizes our zero-linear-algebra cycle-shift independence bound on the mergeable-pair
graph `M_L` (**Theorem T15** and its multi-cycle extension **T15-multi**), requiring **NO strong
connectivity** and **NO synchronization** assumption:

* `Cerny.cycle_shift_indep_bound`: Whenever a letter `b` acts as an `m`-cycle `c : Fin m ↪ Q`
  (`m ≥ 2`) and a letter `a` merges two distinct states of that cycle, every subset `R ⊆ Q`
  that cannot be compressed by any word of length `≤ L` (`1 ≤ L ≤ m`) satisfies
  `2 * |R ∩ C| + L ≤ 2 * m` (equivalently `|R ∩ C| ≤ m - ⌈L / 2⌉`).
* `Cerny.cycle_large_subset_compression`: Every subset `R ⊆ Q` with `2 * (n - |R|) + 1 ≤ m`
  compresses in length `≤ 2 * (n - |R|) + 1`.
* `Cerny.nCycle_half_compression_c1`: For **any** `n`-cycle letter `b` (`n ≥ 2`) and **any**
  non-bijective letter `a` (arbitrary extra letters in `α`), every subset `R` of size `r > n / 2`
  compresses in length `≤ 2 * (n - r) + 1 ≤ n`, strictly proving **Conjecture C1**
  (`r * c(A, R) ≤ n * (n - 1)`) for all `r > n / 2` and matching `𝒞_n` to the exact integer!
* `Cerny.multiCycle_shift_indep_bound`: Multi-cycle extension for `s` pairwise disjoint cycles
  `C_i` of lengths `m_i ≥ 2`: `|R| + ∑ i, ⌈min L (m i) / 2⌉ ≤ n`.
-/

namespace Cerny

universe u v w

namespace AlpogeCompression

private lemma eval_replicate_cycle {Q : Type u} {α : Type v} (A : DFA Q α)
    (b : α) {m : ℕ} (hm0 : 0 < m) (c : Fin m ↪ Q)
    (hcyc : ∀ j : Fin m, A.step (c j) b = c ⟨(j.1 + 1) % m, Nat.mod_lt _ hm0⟩) :
    ∀ (k : ℕ) (j : Fin m),
      A.eval (c j) (List.replicate k b) = c ⟨(j.1 + k) % m, Nat.mod_lt _ hm0⟩ := by
  intro k
  induction k with
  | zero =>
    intro j
    simp only [List.replicate_zero, DFA.eval_nil, add_zero]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt j.2).symm
  | succ k ih =>
    intro j
    rw [List.replicate_succ, DFA.eval_cons, hcyc j, ih]
    congr 1
    apply Fin.ext
    dsimp only
    rw [Nat.mod_add_mod]
    congr 1
    omega

private lemma mod_eq_of_lt_two_mul {a b m : ℕ} (_hm0 : 0 < m)
    (ha : a < 2 * m) (hb : b < 2 * m) (hmod : a % m = b % m) :
    a = b ∨ a + m = b ∨ b + m = a := by
  have hmod_val : ∀ x, x < 2 * m → x % m = x ∨ x % m + m = x := by
    intro x hx
    by_cases hxm : x < m
    · left; exact Nat.mod_eq_of_lt hxm
    · right
      have hsub : x % m = (x - m) % m := Nat.mod_eq_sub_mod (by omega)
      rw [hsub, Nat.mod_eq_of_lt (by omega)]
      omega
  rcases hmod_val a ha with ha' | ha' <;> rcases hmod_val b hb with hb' | hb' <;> omega

end AlpogeCompression

/-- **Theorem T15 (Cycle-Shift Independence Bound — Pure `ℕ`, No SC / No Sync Needed!)**:
If `b` acts as an `m`-cycle `c : Fin m ↪ Q` (`m ≥ 2`), `a` merges two distinct states `c i₀, c i₁`,
`1 ≤ L ≤ m`, and no word of length `≤ L` compresses `R`, then
`2 * |{j : Fin m | c j ∈ R}| + L ≤ 2 * m`. -/
theorem cycle_shift_indep_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (b a : α) {m L : ℕ} (hm : 2 ≤ m) (_hL : 1 ≤ L) (hLm : L ≤ m)
    (c : Fin m ↪ Q)
    (hcyc : ∀ j : Fin m, A.step (c j) b = c ⟨(j.1 + 1) % m, Nat.mod_lt _ (by omega)⟩)
    {i₀ i₁ : Fin m} (hne : i₀ ≠ i₁) (hmerge : A.step (c i₀) a = A.step (c i₁) a)
    (R : Finset Q) (hno : ∀ w : List α, w.length ≤ L → (A.image R w).card = R.card) :
    2 * (Finset.univ.filter (fun j : Fin m => c j ∈ R)).card + L ≤ 2 * m := by
  have hm0 : 0 < m := by omega
  let d : ℕ := (i₁.1 + m - i₀.1) % m
  have hd_lt : d < m := Nat.mod_lt _ hm0
  have hd_pos : 1 ≤ d := by
    by_contra h0
    have hd0 : (i₁.1 + m - i₀.1) % m = m % m := by
      have : d = 0 := by omega
      rw [Nat.mod_self]; exact this
    have hcases := AlpogeCompression.mod_eq_of_lt_two_mul hm0 (by omega) (by omega) hd0
    exact hne (Fin.ext (by omega))
  have hi₀_add_d : (i₀.1 + d) % m = i₁.1 := by
    dsimp only [d]
    rw [Nat.add_mod_mod]
    have hsum : i₀.1 + (i₁.1 + m - i₀.1) = i₁.1 + m := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i₁.2]
  let σ : Fin m → Fin m := fun j => ⟨(j.1 + d) % m, Nat.mod_lt _ hm0⟩
  have hσ_inj : Function.Injective σ := by
    intro j₁ j₂ h
    have hmod : (j₁.1 + d) % m = (j₂.1 + d) % m := congrArg Fin.val h
    have hcases := AlpogeCompression.mod_eq_of_lt_two_mul hm0 (by omega) (by omega) hmod
    exact Fin.ext (by omega)
  have hσ_ne : ∀ j : Fin m, σ j ≠ j := by
    intro j heq
    have hmod : (j.1 + d) % m = j.1 % m := by
      rw [Nat.mod_eq_of_lt j.2]; exact congrArg Fin.val heq
    have hcases := AlpogeCompression.mod_eq_of_lt_two_mul hm0 (by omega) (by omega) hmod
    omega
  let shiftIdx : ℕ → Fin m := fun k => ⟨(i₀.1 + m - k) % m, Nat.mod_lt _ hm0⟩
  let S_L : Finset (Fin m) := (Finset.range L).image shiftIdx
  have hSL_card : S_L.card = L := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro k₁ hk₁ k₂ hk₂ heq
    rw [Finset.mem_coe, Finset.mem_range] at hk₁ hk₂
    have hmod : (i₀.1 + m - k₁) % m = (i₀.1 + m - k₂) % m := congrArg Fin.val heq
    have hcases := AlpogeCompression.mod_eq_of_lt_two_mul hm0 (by omega) (by omega) hmod
    omega
  have hmerge_SL : ∀ j ∈ S_L, ∃ w : List α, w.length ≤ L ∧ A.eval (c j) w = A.eval (c (σ j)) w := by
    intro j hj
    rw [Finset.mem_image] at hj
    rcases hj with ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk
    refine ⟨List.replicate k b ++ [a], by simp; omega, ?_⟩
    rw [DFA.eval_append, DFA.eval_append, DFA.eval_singleton, DFA.eval_singleton]
    rw [AlpogeCompression.eval_replicate_cycle A b hm0 c hcyc k (shiftIdx k)]
    rw [AlpogeCompression.eval_replicate_cycle A b hm0 c hcyc k (σ (shiftIdx k))]
    have hleft : (⟨((shiftIdx k).1 + k) % m, Nat.mod_lt _ hm0⟩ : Fin m) = i₀ := by
      apply Fin.ext
      dsimp only [shiftIdx]
      rw [Nat.mod_add_mod]
      have hsum : i₀.1 + m - k + k = i₀.1 + m := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i₀.2]
    have hright : (⟨((σ (shiftIdx k)).1 + k) % m, Nat.mod_lt _ hm0⟩ : Fin m) = i₁ := by
      apply Fin.ext
      dsimp only [σ, shiftIdx]
      have hleft_val : ((i₀.1 + m - k) % m + k) % m = i₀.1 := congrArg Fin.val hleft
      calc (((i₀.1 + m - k) % m + d) % m + k) % m
          = ((i₀.1 + m - k) % m + d + k) % m := Nat.mod_add_mod _ _ _
        _ = ((i₀.1 + m - k) % m + k + d) % m := by congr 1; omega
        _ = (((i₀.1 + m - k) % m + k) % m + d) % m := (Nat.mod_add_mod _ _ _).symm
        _ = (i₀.1 + d) % m := by rw [hleft_val]
        _ = i₁.1 := hi₀_add_d
    rw [hleft, hright, hmerge]
  let I : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => c j ∈ R)
  let A_set : Finset (Fin m) := I ∩ S_L
  let B_set : Finset (Fin m) := A_set.image σ
  have hB_card : B_set.card = A_set.card := Finset.card_image_of_injective A_set hσ_inj
  have hdisj : Disjoint I B_set := by
    rw [Finset.disjoint_left]
    intro x hxI hxB
    rw [Finset.mem_image] at hxB
    rcases hxB with ⟨j, hjA, rfl⟩
    have hjI : j ∈ I := (Finset.mem_inter.mp hjA).1
    have hjSL : j ∈ S_L := (Finset.mem_inter.mp hjA).2
    have hcj_R : c j ∈ R := (Finset.mem_filter.mp hjI).2
    have hcσj_R : c (σ j) ∈ R := (Finset.mem_filter.mp hxI).2
    have hne_c : c (σ j) ≠ c j := c.injective.ne (hσ_ne j)
    obtain ⟨w, hwlen, hwmerge⟩ := hmerge_SL j hjSL
    have himg_eq : A.image R w = A.image (R.erase (c j)) w := by
      ext y
      simp only [DFA.mem_image, Finset.mem_erase]
      constructor
      · rintro ⟨q, hqR, hqy⟩
        by_cases hqj : q = c j
        · subst hqj
          exact ⟨c (σ j), ⟨hne_c, hcσj_R⟩, hwmerge.symm.trans hqy⟩
        · exact ⟨q, ⟨hqj, hqR⟩, hqy⟩
      · rintro ⟨q, ⟨_, hqR⟩, hqy⟩
        exact ⟨q, hqR, hqy⟩
    have hcard_lt : (A.image R w).card < R.card := by
      rw [himg_eq]
      calc (A.image (R.erase (c j)) w).card
          ≤ (R.erase (c j)).card := A.card_image_le (R.erase (c j)) w
        _ = R.card - 1 := Finset.card_erase_of_mem hcj_R
        _ < R.card := by
            have hpos : 0 < R.card := Finset.card_pos.mpr ⟨c j, hcj_R⟩
            omega
    have heq := hno w hwlen
    omega
  have h1 : I.card + A_set.card ≤ m := by
    calc I.card + A_set.card
        = I.card + B_set.card := by rw [hB_card]
      _ = (I ∪ B_set).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = m := by rw [Finset.card_univ, Fintype.card_fin]
  have hI_split : I.card = A_set.card + (I \ S_L).card := by
    have hpart : A_set ∪ (I \ S_L) = I := by
      ext j
      simp only [A_set, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hd : Disjoint A_set (I \ S_L) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      exact (Finset.mem_sdiff.mp hj2).2 (Finset.mem_inter.mp hj1).2
    calc I.card
        = (A_set ∪ (I \ S_L)).card := by rw [hpart]
      _ = A_set.card + (I \ S_L).card := Finset.card_union_of_disjoint hd
  have h2 : (I \ S_L).card + L ≤ m := by
    have hd : Disjoint (I \ S_L) S_L := Finset.sdiff_disjoint
    calc (I \ S_L).card + L
        = (I \ S_L).card + S_L.card := by rw [hSL_card]
      _ = ((I \ S_L) ∪ S_L).card := (Finset.card_union_of_disjoint hd).symm
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = m := by rw [Finset.card_univ, Fintype.card_fin]
  change 2 * I.card + L ≤ 2 * m
  omega

/-- **Theorem T15 (Linear Large-Subset Compression)**:
Whenever `b` acts as an `m`-cycle (`m ≥ 2`) and `a` merges two states of that cycle, EVERY
subset `R ⊆ Q` with `2 * (n - |R|) + 1 ≤ m` is compressed in length `≤ 2 * (n - |R|) + 1`
(NO strong connectivity and NO synchronization assumed!). -/
theorem cycle_large_subset_compression {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (b a : α) {m : ℕ} (hm : 2 ≤ m)
    (c : Fin m ↪ Q)
    (hcyc : ∀ j : Fin m, A.step (c j) b = c ⟨(j.1 + 1) % m, Nat.mod_lt _ (by omega)⟩)
    {i₀ i₁ : Fin m} (hne : i₀ ≠ i₁) (hmerge : A.step (c i₀) a = A.step (c i₁) a)
    (R : Finset Q) (hR : 2 * (Fintype.card Q - R.card) + 1 ≤ m) :
    ∃ w : List α, w.length ≤ 2 * (Fintype.card Q - R.card) + 1 ∧ (A.image R w).card < R.card := by
  by_contra hno_ex
  push Not at hno_ex
  let L := 2 * (Fintype.card Q - R.card) + 1
  have hno : ∀ w : List α, w.length ≤ L → (A.image R w).card = R.card := fun w hw =>
    le_antisymm (A.card_image_le R w) (hno_ex w hw)
  have hindep := cycle_shift_indep_bound A b a hm (by omega) hR c hcyc hne hmerge R hno
  let C_set : Finset Q := Finset.univ.image c
  have hC_card : C_set.card = m := by
    rw [Finset.card_image_of_injective _ c.injective, Finset.card_univ, Fintype.card_fin]
  have hI_eq : (Finset.univ.filter (fun j : Fin m => c j ∈ R)).card = (R ∩ C_set).card := by
    have himg : (Finset.univ.filter (fun j : Fin m => c j ∈ R)).image c = R ∩ C_set := by
      ext q
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_inter, C_set]
      constructor
      · rintro ⟨j, hjR, rfl⟩; exact ⟨hjR, j, rfl⟩
      · rintro ⟨hqR, j, rfl⟩; exact ⟨j, hqR, rfl⟩
    rw [← himg, Finset.card_image_of_injective _ c.injective]
  have hR_split : R.card = (R ∩ C_set).card + (R \ C_set).card := by
    have hpart : (R ∩ C_set) ∪ (R \ C_set) = R := by
      ext q; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    have hd : Disjoint (R ∩ C_set) (R \ C_set) := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      exact (Finset.mem_sdiff.mp hq2).2 (Finset.mem_inter.mp hq1).2
    calc R.card
        = ((R ∩ C_set) ∪ (R \ C_set)).card := by rw [hpart]
      _ = (R ∩ C_set).card + (R \ C_set).card := Finset.card_union_of_disjoint hd
  have hsdiff_le : (R \ C_set).card + m ≤ Fintype.card Q := by
    have hd : Disjoint (R \ C_set) C_set := Finset.sdiff_disjoint
    calc (R \ C_set).card + m
        = (R \ C_set).card + C_set.card := by rw [hC_card]
      _ = ((R \ C_set) ∪ C_set).card := (Finset.card_union_of_disjoint hd).symm
      _ ≤ (Finset.univ : Finset Q).card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card Q := Finset.card_univ
  have hR_le_n : R.card ≤ Fintype.card Q := Finset.card_le_univ R
  omega

/-- **Theorem T15 Corollary (`n`-Cycle DFAs — Proving Conjecture C1 for ALL `r > n / 2`!)**:
For ANY DFA on `n ≥ 2` states with an `n`-cycle letter `b` and ANY non-bijective letter `a`
(no strong connectivity, no synchronization, arbitrary extra letters in `α`), every subset `R`
of size `r > n / 2` compresses in length `≤ 2 * (n - r) + 1 ≤ n`, satisfying Conjecture C1
`r * w.length ≤ n * (n - 1)`! -/
theorem nCycle_half_compression_c1 {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (b a : α) (hn : 2 ≤ Fintype.card Q)
    (c : Fin (Fintype.card Q) ≃ Q)
    (hcyc : ∀ j : Fin (Fintype.card Q),
      A.step (c j) b = c ⟨(j.1 + 1) % Fintype.card Q, Nat.mod_lt _ (by omega)⟩)
    (hnotinj : ¬ Function.Injective (fun q => A.step q a))
    (R : Finset Q) (hR : Fintype.card Q < 2 * R.card) :
    ∃ w : List α,
      w.length ≤ 2 * (Fintype.card Q - R.card) + 1 ∧
      w.length ≤ Fintype.card Q ∧
      R.card * w.length ≤ Fintype.card Q * (Fintype.card Q - 1) ∧
      (A.image R w).card < R.card := by
  simp only [Function.Injective, not_forall] at hnotinj
  rcases hnotinj with ⟨q₀, q₁, hmerge, hne_q⟩
  let i₀ : Fin (Fintype.card Q) := c.symm q₀
  let i₁ : Fin (Fintype.card Q) := c.symm q₁
  have hne : i₀ ≠ i₁ := fun h => hne_q (c.symm.injective h)
  have hmerge' : A.step (c.toEmbedding i₀) a = A.step (c.toEmbedding i₁) a := by
    simp only [Equiv.coe_toEmbedding, i₀, i₁, Equiv.apply_symm_apply]
    exact hmerge
  have hR_le_n : R.card ≤ Fintype.card Q := Finset.card_le_univ R
  have hL_le_n : 2 * (Fintype.card Q - R.card) + 1 ≤ Fintype.card Q := by omega
  obtain ⟨w, hwlen, hwcomp⟩ :=
    cycle_large_subset_compression A b a hn c.toEmbedding hcyc hne hmerge' R hL_le_n
  refine ⟨w, hwlen, le_trans hwlen hL_le_n, ?_, hwcomp⟩
  calc R.card * w.length
      ≤ R.card * (2 * (Fintype.card Q - R.card) + 1) := Nat.mul_le_mul_left R.card hwlen
    _ ≤ Fintype.card Q * (Fintype.card Q - 1) := by
        set n := Fintype.card Q
        set r := R.card
        have h1 : 2 * (n - r) + 1 = 2 * n + 1 - 2 * r := by omega
        by_cases hn4 : 4 ≤ n
        · -- `8 * (n*(n-1) - r*(2*(n-r)+1)) = (4r - (2n+1))^2 + (4n^2 - 12n - 1) > 0`
          zify [hR_le_n, (show 1 ≤ n by omega)]
          nlinarith [sq_nonneg (4 * (r : ℤ) - (2 * (n : ℤ) + 1))]
        · -- `n = 2` or `n = 3`
          rcases (show n = 2 ∨ n = 3 by omega) with hn2 | hn3
          · have hr : r = 2 := by omega
            rw [hn2, hr]
          · rcases (show r = 2 ∨ r = 3 by omega) with hr2 | hr3
            · rw [hn3, hr2]
            · rw [hn3, hr3]; decide

/-- **Theorem T15-multi (Multi-Cycle Independence Bound)**:
If `b` has pairwise disjoint cycles `c i : Fin (m i) ↪ Q` (`m i ≥ 2`) and for each `i` some
letter `a i` merges two distinct states of cycle `i`, then for every `L ≥ 1` and every `R ⊆ Q`
uncompressed up to length `L`,
`R.card + ∑ i, (min L (m i) + 1) / 2 ≤ Fintype.card Q`. -/
theorem multiCycle_shift_indep_bound {Q : Type u} {α : Type v} {ι : Type w}
    [Fintype Q] [DecidableEq Q] [Fintype ι] (A : DFA Q α)
    (b : α) (a : ι → α) (m : ι → ℕ) (hm : ∀ i, 2 ≤ m i)
    (c : ∀ i, Fin (m i) ↪ Q)
    (hdisj : ∀ i j, i ≠ j → ∀ (x : Fin (m i)) (y : Fin (m j)), c i x ≠ c j y)
    (hcyc : ∀ i (j : Fin (m i)),
      A.step (c i j) b = c i ⟨(j.1 + 1) % m i, Nat.mod_lt _ (by have := hm i; omega)⟩)
    (i₀ i₁ : ∀ i, Fin (m i))
    (hne : ∀ i, i₀ i ≠ i₁ i)
    (hmerge : ∀ i, A.step (c i (i₀ i)) (a i) = A.step (c i (i₁ i)) (a i))
    {L : ℕ} (hL : 1 ≤ L)
    (R : Finset Q) (hno : ∀ w : List α, w.length ≤ L → (A.image R w).card = R.card) :
    R.card + ∑ i : ι, (min L (m i) + 1) / 2 ≤ Fintype.card Q := by
  let C_i : ι → Finset Q := fun i => Finset.univ.image (c i)
  have hCi_card : ∀ i, (C_i i).card = m i := fun i => by
    rw [Finset.card_image_of_injective _ (c i).injective, Finset.card_univ, Fintype.card_fin]
  have hCi_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι) : Set ι) C_i := by
    intro i _ j _ hij
    show Disjoint (C_i i) (C_i j)
    rw [Finset.disjoint_left]
    intro q hqi hqj
    rw [Finset.mem_image] at hqi hqj
    rcases hqi with ⟨x, _, rfl⟩
    rcases hqj with ⟨y, _, hy⟩
    exact hdisj i j hij x y hy.symm
  let C_all : Finset Q := Finset.univ.biUnion C_i
  have hCall_card : C_all.card = ∑ i : ι, m i := by
    rw [Finset.card_biUnion hCi_disj]
    exact Finset.sum_congr rfl fun i _ => hCi_card i
  have hper_cycle : ∀ i : ι, (R ∩ C_i i).card + (min L (m i) + 1) / 2 ≤ m i := by
    intro i
    have hLi_pos : 1 ≤ min L (m i) := le_min hL (by have := hm i; omega)
    have hLi_le : min L (m i) ≤ m i := min_le_right L (m i)
    have hno_i : ∀ w : List α, w.length ≤ min L (m i) → (A.image R w).card = R.card :=
      fun w hw => hno w (le_trans hw (min_le_left L (m i)))
    have hind := cycle_shift_indep_bound A b (a i) (hm i) hLi_pos hLi_le (c i) (hcyc i)
      (hne i) (hmerge i) R hno_i
    have hI_eq : (Finset.univ.filter (fun j : Fin (m i) => c i j ∈ R)).card = (R ∩ C_i i).card := by
      have himg : (Finset.univ.filter (fun j : Fin (m i) => c i j ∈ R)).image (c i) = R ∩ C_i i := by
        ext q
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_inter, C_i]
        constructor
        · rintro ⟨j, hjR, rfl⟩; exact ⟨hjR, j, rfl⟩
        · rintro ⟨hqR, j, rfl⟩; exact ⟨j, hqR, rfl⟩
      rw [← himg, Finset.card_image_of_injective _ (c i).injective]
    rw [hI_eq] at hind
    omega
  have hR_inter_eq : R ∩ C_all = Finset.univ.biUnion (fun i => R ∩ C_i i) := by
    ext q
    simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and, C_all]
    constructor
    · rintro ⟨hqR, i, hqi⟩; exact ⟨i, hqR, hqi⟩
    · rintro ⟨i, hqR, hqi⟩; exact ⟨hqR, i, hqi⟩
  have hRCi_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι) : Set ι) (fun i => R ∩ C_i i) := by
    intro i hi j hj hij
    exact (hCi_disj hi hj hij).mono Finset.inter_subset_right Finset.inter_subset_right
  have hR_inter_card : (R ∩ C_all).card = ∑ i : ι, (R ∩ C_i i).card := by
    rw [hR_inter_eq, Finset.card_biUnion hRCi_disj]
  have hR_split : R.card = (R ∩ C_all).card + (R \ C_all).card := by
    have hpart : (R ∩ C_all) ∪ (R \ C_all) = R := by
      ext q; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    have hd : Disjoint (R ∩ C_all) (R \ C_all) := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      exact (Finset.mem_sdiff.mp hq2).2 (Finset.mem_inter.mp hq1).2
    calc R.card
        = ((R ∩ C_all) ∪ (R \ C_all)).card := by rw [hpart]
      _ = (R ∩ C_all).card + (R \ C_all).card := Finset.card_union_of_disjoint hd
  have hsdiff_add : (R \ C_all).card + C_all.card ≤ Fintype.card Q := by
    have hd : Disjoint (R \ C_all) C_all := Finset.sdiff_disjoint
    calc (R \ C_all).card + C_all.card
        = ((R \ C_all) ∪ C_all).card := (Finset.card_union_of_disjoint hd).symm
      _ ≤ (Finset.univ : Finset Q).card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card Q := Finset.card_univ
  have hsum_le : ∑ i : ι, (R ∩ C_i i).card + ∑ i : ι, (min L (m i) + 1) / 2 ≤ ∑ i : ι, m i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hper_cycle i
  rw [hR_split, hR_inter_card]
  rw [hCall_card] at hsdiff_add
  omega

end Cerny
