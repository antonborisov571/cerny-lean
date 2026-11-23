import Cerny.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Combinatorial Upper Bounds & Structural Reductions for the Černý Conjecture

This file proves three foundational combinatorial results for synchronizing DFAs:

1. **Exact SCC Reduction Theorem** (`exists_syncWord_le_sinkSCC_bound`,
   `cerny_of_stronglyConnected_le`, `cernyConjecture_of_stronglyConnected`):
   Every synchronizing DFA on `n` states with sink SCC `C` (`m = n - |C|`) satisfies
   `rt(A) ≤ m * (m + 1) / 2 + rt(A|_C)`. Consequently, proving Černý's conjecture for
   strongly connected synchronizing DFAs (of size `≤ n`) suffices for all synchronizing DFAs.

2. **Pin–Frankl Cubic Upper Bound** (`frankl_skew_two`, `pin_compression_bound`,
   `pin_frankl_bound`, `pin_frankl_div_bound`):
   Proves Frankl's skew Bollobás theorem (`a = 2`) via univariate symmetric polynomials
   over `ℚ` (zero exterior algebra, zero Vandermonde determinants), Pin's compression bound
   `≤ (n - r + 2).choose 2`, and the cubic bound `rt(A) ≤ (n^3 - n) / 6` for all `n ≥ 1`.

3. **Rank-`k` Fiber-Collision Bridge Lemma & Small-Rank Letter Bounds**
   (`rank_k_bridge_lemma`, `exists_syncWord_of_rank_letter`, `rank_le_two_bound`,
   `rank_le_three_bound`, `rank_le_three_cerny_ge_five`):
   For any word `u` of rank `k ≥ 2` and any `k`-subset `S`, there exists `w` of length
   `≤ n - k + 1` with `|S · (w ++ u)| ≤ k - 1`. Iterating yields `rt(A) ≤ (n - r + 3) * 2^(r - 1) - (n + 1)`
   for a letter of rank `r`, giving `rt(A) ≤ n + 1` for rank `≤ 2` and
   `rt(A) ≤ 3 * n - 1 ≤ (n - 1)^2` (for `n ≥ 5`) for rank `≤ 3`.
-/

namespace Cerny

universe u v

/-! ## Part 1: Exact SCC Reduction Theorem -/

section SCCReduction

variable {Q : Type*} {α : Type*}

/-- The canonical sink SCC of a DFA: all states reachable from every state. -/
noncomputable def sinkSCC [Fintype Q] [DecidableEq Q] (A : DFA Q α) : Finset Q := by
  classical
  exact Finset.univ.filter (fun q => ∀ p : Q, ∃ u : List α, A.eval p u = q)

theorem mem_sinkSCC [Fintype Q] [DecidableEq Q] (A : DFA Q α) (q : Q) :
    q ∈ sinkSCC A ↔ ∀ p : Q, ∃ u : List α, A.eval p u = q := by
  classical
  simp [sinkSCC]

theorem sinkSCC_nonempty [Fintype Q] [DecidableEq Q] (A : DFA Q α) (hSync : A.IsSynchronizing) :
    (sinkSCC A).Nonempty := by
  rcases hSync with ⟨w, q₀, hq₀⟩
  refine ⟨q₀, (mem_sinkSCC A q₀).mpr fun p => ⟨w, hq₀ p⟩⟩

theorem sinkSCC_step_mem [Fintype Q] [DecidableEq Q] (A : DFA Q α) {q : Q}
    (hq : q ∈ sinkSCC A) (a : α) : A.step q a ∈ sinkSCC A := by
  rw [mem_sinkSCC] at hq ⊢
  intro p
  obtain ⟨u, hu⟩ := hq p
  exact ⟨u ++ [a], by rw [DFA.eval_append, hu]; rfl⟩

theorem sinkSCC_eval_mem [Fintype Q] [DecidableEq Q] (A : DFA Q α) {q : Q}
    (hq : q ∈ sinkSCC A) (w : List α) : A.eval q w ∈ sinkSCC A := by
  induction w generalizing q with
  | nil => simpa using hq
  | cons a w ih => exact ih (sinkSCC_step_mem A hq a)

/-- The DFA obtained by restricting `A` to its closed sink SCC. -/
noncomputable def restrictSinkSCC [Fintype Q] [DecidableEq Q] (A : DFA Q α) :
    DFA {q // q ∈ sinkSCC A} α where
  step q a := ⟨A.step q.1 a, sinkSCC_step_mem A q.2 a⟩

theorem restrictSinkSCC_eval [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (q : {q // q ∈ sinkSCC A}) (w : List α) :
    ((restrictSinkSCC A).eval q w).1 = A.eval q.1 w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => exact ih ⟨A.step q.1 a, sinkSCC_step_mem A q.2 a⟩

theorem restrictSinkSCC_isStronglyConnected [Fintype Q] [DecidableEq Q] (A : DFA Q α) :
    (restrictSinkSCC A).IsStronglyConnected := by
  intro p q
  obtain ⟨u, hu⟩ := (mem_sinkSCC A q.1).mp q.2 p.1
  refine ⟨u, Subtype.ext ?_⟩
  rw [restrictSinkSCC_eval]
  exact hu

theorem restrictSinkSCC_isSynchronizing [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) : (restrictSinkSCC A).IsSynchronizing := by
  rcases hSync with ⟨w, q₀, hq₀⟩
  have hq₀_mem : q₀ ∈ sinkSCC A := (mem_sinkSCC A q₀).mpr fun p => ⟨w, hq₀ p⟩
  refine ⟨w, ⟨q₀, hq₀_mem⟩, fun p => Subtype.ext ?_⟩
  rw [restrictSinkSCC_eval]
  exact hq₀ p.1

/-- States that can reach `sinkSCC A` in at most `d` steps. -/
noncomputable def sinkLayer [Fintype Q] [DecidableEq Q] (A : DFA Q α) (d : ℕ) : Finset Q := by
  classical
  exact Finset.univ.filter (fun q => ∃ v : List α, v.length ≤ d ∧ A.eval q v ∈ sinkSCC A)

theorem mem_sinkLayer [Fintype Q] [DecidableEq Q] (A : DFA Q α) (d : ℕ) (q : Q) :
    q ∈ sinkLayer A d ↔ ∃ v : List α, v.length ≤ d ∧ A.eval q v ∈ sinkSCC A := by
  classical
  simp [sinkLayer]

theorem sinkLayer_zero [Fintype Q] [DecidableEq Q] (A : DFA Q α) :
    sinkLayer A 0 = sinkSCC A := by
  ext q
  rw [mem_sinkLayer]
  constructor
  · rintro ⟨v, hvlen, hmem⟩
    have hnil : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    simpa [hnil] using hmem
  · intro hq
    exact ⟨[], by simp, by simpa using hq⟩

theorem sinkLayer_mono [Fintype Q] [DecidableEq Q] (A : DFA Q α) {j k : ℕ} (hjk : j ≤ k) :
    sinkLayer A j ⊆ sinkLayer A k := by
  intro q hq
  rw [mem_sinkLayer] at hq ⊢
  rcases hq with ⟨v, hvlen, hmem⟩
  exact ⟨v, le_trans hvlen hjk, hmem⟩

theorem sinkLayer_strict_growth [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (d : ℕ) (hne : sinkLayer A d ≠ Finset.univ) :
    (sinkLayer A d).card + 1 ≤ (sinkLayer A (d + 1)).card := by
  classical
  have hssub : sinkLayer A d ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩
  obtain ⟨p, _, hpNot⟩ := Finset.exists_of_ssubset hssub
  have hex : ∃ k : ℕ, ∃ v : List α, v.length = k ∧ A.eval p v ∈ sinkSCC A := by
    rcases hSync with ⟨w, q₀, hq₀⟩
    exact ⟨w.length, w, rfl, (mem_sinkSCC A (A.eval p w)).mpr fun r => ⟨w, by rw [hq₀ r, hq₀ p]⟩⟩
  obtain ⟨v, hvlen, hvmem⟩ := Nat.find_spec hex
  have hgt : d < v.length := by
    by_contra hle
    push Not at hle
    exact hpNot ((mem_sinkLayer A d p).mpr ⟨v, hle, hvmem⟩)
  let pref := v.take (v.length - (d + 1))
  let suf := v.drop (v.length - (d + 1))
  let q' := A.eval p pref
  have hq'_in : q' ∈ sinkLayer A (d + 1) := by
    rw [mem_sinkLayer]
    refine ⟨suf, by simp only [suf, List.length_drop]; omega, ?_⟩
    dsimp [q', pref, suf]
    rw [← DFA.eval_append, List.take_append_drop]
    exact hvmem
  have hq'_not : q' ∉ sinkLayer A d := by
    intro hmem
    rw [mem_sinkLayer] at hmem
    rcases hmem with ⟨u, hulen, humem⟩
    have hcomb : A.eval p (pref ++ u) ∈ sinkSCC A := by
      rw [DFA.eval_append]
      exact humem
    have hmin := Nat.find_min' hex ⟨pref ++ u, rfl, hcomb⟩
    simp only [List.length_append, pref, List.length_take] at hmin
    omega
  have hsub2 : sinkLayer A d ⊂ sinkLayer A (d + 1) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨sinkLayer_mono A (by omega), fun heq => by
      rw [← heq] at hq'_in
      exact hq'_not hq'_in⟩
  exact Finset.card_lt_card hsub2

theorem sinkLayer_card_ge [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (d : ℕ) (hd : d ≤ Fintype.card Q - (sinkSCC A).card) :
    (sinkSCC A).card + d ≤ (sinkLayer A d).card := by
  induction d with
  | zero =>
    rw [sinkLayer_zero, add_zero]
  | succ d ih =>
    have ih' := ih (by omega)
    by_cases hfull : sinkLayer A d = Finset.univ
    · have hle := Finset.card_le_card (sinkLayer_mono A (by omega : d ≤ d + 1))
      rw [hfull, Finset.card_univ] at hle
      have hsc_le : (sinkSCC A).card ≤ Fintype.card Q := Finset.card_le_univ _
      omega
    · have hgrow := sinkLayer_strict_growth A hSync d hfull
      omega

theorem sink_absorption [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) :
    let m := Fintype.card Q - (sinkSCC A).card
    ∀ t : ℕ, ∀ S : Finset Q, (S \ sinkSCC A).card = t →
      ∃ u : List α, A.image S u ⊆ sinkSCC A ∧ 2 * u.length ≤ t * (2 * m - t + 1) := by
  intro m t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro S ht
    have hsc_le : (sinkSCC A).card ≤ Fintype.card Q := Finset.card_le_univ _
    have ht_le_m : t ≤ m := by
      have hsub : S \ sinkSCC A ⊆ Finset.univ \ sinkSCC A := Finset.sdiff_subset_sdiff (Finset.subset_univ S) subset_rfl
      have hc := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at hc
      omega
    by_cases ht0 : t = 0
    · subst ht0
      have hsub : S ⊆ sinkSCC A := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp ht)
      exact ⟨[], by simpa using hsub, by simp⟩
    · let d := m - t + 1
      have hd_le : d ≤ m := by omega
      have hlayer := sinkLayer_card_ge A hSync d hd_le
      have hinter_ne : ((S \ sinkSCC A) ∩ sinkLayer A d).Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have hdisj : Disjoint (S \ sinkSCC A) (sinkLayer A d) :=
          Finset.disjoint_iff_inter_eq_empty.mpr hemp
        have hunion := Finset.card_le_univ ((S \ sinkSCC A) ∪ sinkLayer A d)
        rw [Finset.card_union_of_disjoint hdisj, ht] at hunion
        omega
      obtain ⟨x, hx_inter⟩ := hinter_ne
      have hx_sdiff : x ∈ S \ sinkSCC A := (Finset.mem_inter.mp hx_inter).1
      have hx_layer : x ∈ sinkLayer A d := (Finset.mem_inter.mp hx_inter).2
      obtain ⟨v, hvlen, hvmem⟩ := (mem_sinkLayer A d x).mp hx_layer
      let S' := A.image S v
      have hS'_sub : S' \ sinkSCC A ⊆ A.image ((S \ sinkSCC A).erase x) v := by
        intro y hy
        rw [Finset.mem_sdiff] at hy
        rcases hy with ⟨hyS', hyNotC⟩
        rw [DFA.mem_image] at hyS' ⊢
        rcases hyS' with ⟨s, hsS, rfl⟩
        refine ⟨s, ?_, rfl⟩
        rw [Finset.mem_erase, Finset.mem_sdiff]
        refine ⟨?_, hsS, ?_⟩
        · intro rfl; exact hyNotC hvmem
        · intro hsC; exact hyNotC (sinkSCC_eval_mem A hsC v)
      let t' := (S' \ sinkSCC A).card
      have ht'_le : t' ≤ t - 1 := by
        calc t' ≤ (A.image ((S \ sinkSCC A).erase x) v).card := Finset.card_le_card hS'_sub
          _ ≤ ((S \ sinkSCC A).erase x).card := A.card_image_le _ v
          _ = t - 1 := by rw [Finset.card_erase_of_mem hx_sdiff, ht]
      obtain ⟨u', hu'sub, hu'len⟩ := ih t' (by omega) S' rfl
      refine ⟨v ++ u', ?_, ?_⟩
      · rw [DFA.image_append]; exact hu'sub
      · rw [List.length_append]
        have hmono : t' * (2 * m - t' + 1) ≤ (t - 1) * (2 * m - (t - 1) + 1) := by
          zify [show t' ≤ 2 * m by omega, show t - 1 ≤ 2 * m by omega, show 1 ≤ t by omega]
          have h1 : (t' : ℤ) ≤ (t : ℤ) - 1 := by omega
          have h2 : (t : ℤ) ≤ (m : ℤ) := by omega
          nlinarith
        have hstep : 2 * d + (t - 1) * (2 * m - (t - 1) + 1) = t * (2 * m - t + 1) := by
          zify [show t ≤ m by omega, show t ≤ 2 * m by omega, show t - 1 ≤ 2 * m by omega,
            show 1 ≤ t by omega]
          dsimp [d]
          zify [show t ≤ m by omega]
          ring
        omega

/-- Quantitative SCC Reduction Theorem (division-free):
`2 * rt(A) ≤ m * (m + 1) + 2 * rt(A|_C)` where `m = n - |C|`. -/
theorem exists_syncWord_le_sinkSCC_bound [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) :
    let m := Fintype.card Q - (sinkSCC A).card
    ∃ w : List α, A.IsSyncWord w ∧
      2 * w.length ≤ m * (m + 1) +
        2 * (restrictSinkSCC A).resetThreshold (restrictSinkSCC_isSynchronizing A hSync) := by
  intro m
  have hm_eq : (Finset.univ \ sinkSCC A).card = m := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  obtain ⟨u, husub, hulen⟩ := sink_absorption A hSync m Finset.univ hm_eq
  obtain ⟨wC, hwC_sync, hwC_len⟩ :=
    (restrictSinkSCC A).exists_isSyncWord_length_eq_resetThreshold
      (restrictSinkSCC_isSynchronizing A hSync)
  rcases hwC_sync with ⟨q₀, hq₀⟩
  refine ⟨u ++ wC, ⟨q₀.1, fun q => ?_⟩, ?_⟩
  · rw [DFA.eval_append]
    have hmem : A.eval q u ∈ sinkSCC A :=
      husub (by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩)
    have h := congrArg Subtype.val (hq₀ ⟨A.eval q u, hmem⟩)
    rw [restrictSinkSCC_eval] at h
    exact h
  · rw [List.length_append, hwC_len]
    have hulen' : 2 * u.length ≤ m * (m + 1) := by
      have heq : 2 * m - m + 1 = m + 1 := by omega
      change 2 * u.length ≤ m * (2 * m - m + 1) at hulen
      rw [heq] at hulen
      exact hulen
    omega

/-- Quantitative SCC Reduction Theorem with exact integer division:
`rt(A) ≤ m * (m + 1) / 2 + rt(A|_C)` where `m = n - |C|`. -/
theorem resetThreshold_le_sinkSCC_bound [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) :
    let m := Fintype.card Q - (sinkSCC A).card
    A.resetThreshold hSync ≤
      m * (m + 1) / 2 +
        (restrictSinkSCC A).resetThreshold (restrictSinkSCC_isSynchronizing A hSync) := by
  intro m
  obtain ⟨w, hw, hlen⟩ := exists_syncWord_le_sinkSCC_bound A hSync
  have hrt := A.resetThreshold_le_of_isSyncWord hSync hw
  have heven : 2 ∣ m * (m + 1) := Nat.even_mul_succ_self m |>.two_dvd
  rcases heven with ⟨k, hk⟩
  have hdiv : m * (m + 1) / 2 = k := by rw [hk]; omega
  change 2 * w.length ≤ m * (m + 1) +
    2 * (restrictSinkSCC A).resetThreshold (restrictSinkSCC_isSynchronizing A hSync) at hlen
  rw [hk] at hlen
  rw [hdiv]
  omega

/-- Local SCC Reduction Theorem: if Černý's conjecture holds for all strongly connected
synchronizing DFAs on at most `Fintype.card Q` states, then it holds for `A`. -/
theorem cerny_of_stronglyConnected_le {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (hSC : ∀ {Q' : Type u} [Fintype Q'] [Nonempty Q'] (A' : DFA Q' α),
      Fintype.card Q' ≤ Fintype.card Q → A'.IsStronglyConnected → A'.IsSynchronizing →
      ∃ w : List α, A'.IsSyncWord w ∧ w.length ≤ (Fintype.card Q' - 1) ^ 2) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  let C := sinkSCC A
  have hC_ne : Nonempty {q // q ∈ C} := by
    obtain ⟨q, hq⟩ := sinkSCC_nonempty A hSync
    exact ⟨⟨q, hq⟩⟩
  have hC_card : Fintype.card {q // q ∈ C} = C.card := Fintype.card_coe C
  have hC_pos : 1 ≤ C.card := Finset.card_pos.mpr (sinkSCC_nonempty A hSync)
  have hC_le : C.card ≤ Fintype.card Q := Finset.card_le_univ C
  obtain ⟨wC, hwC_sync, hwC_len⟩ :=
    hSC (restrictSinkSCC A) (by rw [hC_card]; exact hC_le)
      (restrictSinkSCC_isStronglyConnected A) (restrictSinkSCC_isSynchronizing A hSync)
  have hrtC : (restrictSinkSCC A).resetThreshold (restrictSinkSCC_isSynchronizing A hSync) ≤
      (C.card - 1) ^ 2 := by
    rw [hC_card] at hwC_len
    exact le_trans (DFA.resetThreshold_le_of_isSyncWord _ _ hwC_sync) hwC_len
  obtain ⟨w, hw, hlen⟩ := exists_syncWord_le_sinkSCC_bound A hSync
  refine ⟨w, hw, ?_⟩
  let m := Fintype.card Q - C.card
  let k := C.card
  have hmk : m + k = Fintype.card Q := by omega
  have hlen' : 2 * w.length ≤ m * (m + 1) + 2 * (k - 1) ^ 2 := by
    change 2 * w.length ≤ m * (m + 1) +
      2 * (restrictSinkSCC A).resetThreshold (restrictSinkSCC_isSynchronizing A hSync) at hlen
    change (restrictSinkSCC A).resetThreshold (restrictSinkSCC_isSynchronizing A hSync) ≤
      (k - 1) ^ 2 at hrtC
    omega
  have hineq : m * (m + 1) + 2 * (k - 1) ^ 2 ≤ 2 * (Fintype.card Q - 1) ^ 2 := by
    by_cases hm0 : m = 0
    · have hkQ : k = Fintype.card Q := by omega
      rw [hm0, hkQ]
      simp
    · have hm1 : 1 ≤ m := by omega
      have hk1 : 1 ≤ k := hC_pos
      zify [hk1, show 1 ≤ Fintype.card Q by omega]
      have hmk' : (m : ℤ) + (k : ℤ) = (Fintype.card Q : ℤ) := by exact_mod_cast hmk
      have hm1' : (1 : ℤ) ≤ m := by exact_mod_cast hm1
      have hk1' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
      nlinarith
  omega

/-- Global SCC Reduction Theorem: proving Černý's conjecture for strongly connected
synchronizing DFAs suffices to prove `CernyConjecture`. -/
theorem cernyConjecture_of_stronglyConnected
    (hSC : ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : DFA Q α),
      A.IsStronglyConnected → A.IsSynchronizing →
      ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2) :
    CernyConjecture.{u, v} := by
  intro Q _ _ α A hSync
  exact cerny_of_stronglyConnected_le A hSync fun A' _ hA'SC hA'Sync => hSC A' hA'SC hA'Sync

end SCCReduction

/-! ## Part 2: Symmetric-Polynomial Pin–Frankl Cubic Upper Bound -/

section PinFrankl

/-- Ordered pairs `(u, v)` in `Fin (b + 1) × Fin (b + 1)` with `u ≤ v`. -/
private abbrev SymPairIdx (b : ℕ) := { p : Fin (b + 1) × Fin (b + 1) // p.1 ≤ p.2 }

private theorem sum_range_succ_eq_choose (b : ℕ) :
    ∑ v ∈ Finset.range (b + 1), (v + 1) = (b + 2).choose 2 := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [Finset.sum_range_succ, ih]
    have hsucc : (b + 1 + 2).choose 2 = (b + 2).choose 1 + (b + 2).choose 2 := by
      exact Nat.choose_succ_succ (b + 2) 1
    rw [hsucc, Nat.choose_one_right, add_comm]

private theorem card_symPairIdx (b : ℕ) :
    Fintype.card (SymPairIdx b) = (b + 2).choose 2 := by
  let e : SymPairIdx b ≃ Σ v : Fin (b + 1), Fin (v.val + 1) :=
    { toFun := fun ⟨(u, v), huv⟩ => ⟨v, ⟨u.val, Nat.lt_succ_of_le huv⟩⟩
      invFun := fun ⟨v, u⟩ =>
        ⟨(⟨u.val, lt_of_lt_of_le u.isLt (Nat.succ_le_of_lt v.isLt)⟩, v),
          Nat.le_of_lt_succ u.isLt⟩
      left_inv := fun ⟨(u, v), huv⟩ => rfl
      right_inv := fun ⟨v, u⟩ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun v => v + 1) (b + 1)]
  exact sum_range_succ_eq_choose b

private theorem sum_symPairIdx_eq (b : ℕ) (c a d : Fin (b + 1) → ℚ) :
    (∑ p : SymPairIdx b,
      (c p.1.1 * c p.1.2) *
        (if p.1.1 = p.1.2 then a p.1.1 * d p.1.1
         else a p.1.1 * d p.1.2 + a p.1.2 * d p.1.1)) =
    (∑ u : Fin (b + 1), c u * a u) * (∑ v : Fin (b + 1), c v * d v) := by
  let S_le : Finset (Fin (b + 1) × Fin (b + 1)) := Finset.univ.filter (fun p => p.1 ≤ p.2)
  let S_eq : Finset (Fin (b + 1) × Fin (b + 1)) := Finset.univ.filter (fun p => p.1 = p.2)
  let S_lt : Finset (Fin (b + 1) × Fin (b + 1)) := Finset.univ.filter (fun p => p.1 < p.2)
  let S_gt : Finset (Fin (b + 1) × Fin (b + 1)) := Finset.univ.filter (fun p => p.2 < p.1)
  let F : Fin (b + 1) × Fin (b + 1) → ℚ := fun p =>
    (c p.1 * c p.2) * (if p.1 = p.2 then a p.1 * d p.1 else a p.1 * d p.2 + a p.2 * d p.1)
  have hsub_sum : (∑ p : SymPairIdx b, F p.1) = ∑ p ∈ S_le, F p := by
    exact (Finset.sum_subtype S_le (p := fun p : Fin (b + 1) × Fin (b + 1) => p.1 ≤ p.2)
      (fun p => by simp [S_le]) F).symm
  have hle_union : S_le = S_eq ∪ S_lt := by
    ext p
    simp only [S_le, S_eq, S_lt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact le_iff_eq_or_lt
  have hdisj_eq_lt : Disjoint S_eq S_lt := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [S_eq, S_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    exact ne_of_lt hp2 hp1
  have hswap :
      (∑ p ∈ S_lt, c p.1 * c p.2 * (a p.2 * d p.1)) =
      ∑ p ∈ S_gt, c p.1 * a p.1 * (c p.2 * d p.2) := by
    refine Finset.sum_bij (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [S_lt, S_gt, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact hp
    · intro p₁ _ p₂ _ h
      exact Prod.swap_injective h
    · intro p hp
      refine ⟨p.swap, ?_, Prod.swap_swap p⟩
      simp only [S_lt, S_gt, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact hp
    · intro p _
      simp only [Prod.fst_swap, Prod.snd_swap]
      ring
  have hsum_eq : (∑ p ∈ S_eq, F p) = ∑ p ∈ S_eq, c p.1 * a p.1 * (c p.2 * d p.2) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [S_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [F, hp, ↓reduceIte]
    ring
  have hsum_lt : (∑ p ∈ S_lt, F p) =
      (∑ p ∈ S_lt, c p.1 * a p.1 * (c p.2 * d p.2)) +
      (∑ p ∈ S_gt, c p.1 * a p.1 * (c p.2 * d p.2)) := by
    rw [← hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [S_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hne : p.1 ≠ p.2 := ne_of_lt hp
    simp only [F, hne, ↓reduceIte]
    ring
  have huniv_eq : (Finset.univ : Finset (Fin (b + 1) × Fin (b + 1))) = S_le ∪ S_gt := by
    ext p
    simp only [S_le, S_gt, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    exact le_or_gt p.1 p.2
  have hdisj_le_gt : Disjoint S_le S_gt := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [S_le, S_gt, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    exact not_lt_of_ge hp1 hp2
  calc
    (∑ p : SymPairIdx b, F p.1)
        = ∑ p ∈ S_le, F p := hsub_sum
    _ = (∑ p ∈ S_eq, F p) + (∑ p ∈ S_lt, F p) := by
        rw [hle_union, Finset.sum_union hdisj_eq_lt]
    _ = ((∑ p ∈ S_eq, c p.1 * a p.1 * (c p.2 * d p.2)) +
          (∑ p ∈ S_lt, c p.1 * a p.1 * (c p.2 * d p.2))) +
        (∑ p ∈ S_gt, c p.1 * a p.1 * (c p.2 * d p.2)) := by
        rw [hsum_eq, hsum_lt, add_assoc]
    _ = (∑ p ∈ S_le, c p.1 * a p.1 * (c p.2 * d p.2)) +
        (∑ p ∈ S_gt, c p.1 * a p.1 * (c p.2 * d p.2)) := by
        rw [hle_union, Finset.sum_union hdisj_eq_lt]
    _ = ∑ p : Fin (b + 1) × Fin (b + 1), c p.1 * a p.1 * (c p.2 * d p.2) := by
        rw [← Finset.sum_union hdisj_le_gt, ← huniv_eq]
    _ = (∑ u : Fin (b + 1), c u * a u) * (∑ v : Fin (b + 1), c v * d v) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- Frankl's Skew Bollobás Theorem (`a = 2`), proved over `ℚ` using symmetric
products of univariate polynomials (zero exterior algebra). -/
theorem frankl_skew_two {Q : Type*} [Fintype Q] [DecidableEq Q]
    (m b : ℕ) (x y : Fin m → Q) (B : Fin m → Finset Q)
    (hB : ∀ i, (B i).card ≤ b)
    (hdisj : ∀ i, x i ∉ B i ∧ y i ∉ B i)
    (hinter : ∀ i j : Fin m, j < i → x i ∈ B j ∨ y i ∈ B j) :
    m ≤ (b + 2).choose 2 := by
  let t : Q → ℚ := fun q => ((Fintype.equivFin Q q).val : ℚ)
  have ht_inj : Function.Injective t := by
    intro q₁ q₂ hq
    dsimp [t] at hq
    have hval : (Fintype.equivFin Q q₁).val = (Fintype.equivFin Q q₂).val := by
      exact_mod_cast hq
    exact (Fintype.equivFin Q).injective (Fin.ext hval)
  let P : Fin m → Polynomial ℚ := fun j =>
    ∏ q ∈ B j, (Polynomial.X - Polynomial.C (t q))
  have hP_deg : ∀ j : Fin m, (P j).natDegree ≤ b := by
    intro j
    calc (P j).natDegree
        ≤ ∑ q ∈ B j, (Polynomial.X - Polynomial.C (t q)).natDegree :=
          Polynomial.natDegree_prod_le (B j) _
      _ = ∑ _q ∈ B j, 1 := Finset.sum_congr rfl fun q _ => Polynomial.natDegree_X_sub_C (t q)
      _ = (B j).card := by simp
      _ ≤ b := hB j
  have hP_eval : ∀ (j : Fin m) (r : ℚ),
      (P j).eval r = ∑ u : Fin (b + 1), (P j).coeff u.val * r ^ u.val := by
    intro j r
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hP_deg j)),
      ← Fin.sum_univ_eq_sum_range]
  have hP_eval_prod : ∀ (j : Fin m) (r : ℚ),
      (P j).eval r = ∏ q ∈ B j, (r - t q) := by
    intro j r
    simp [P, Polynomial.eval_prod]
  let w : Fin m → (SymPairIdx b → ℚ) := fun j p =>
    (P j).coeff p.1.1.val * (P j).coeff p.1.2.val
  let z : Fin m → (SymPairIdx b → ℚ) := fun i p =>
    if p.1.1 = p.1.2 then (t (x i)) ^ p.1.1.val * (t (y i)) ^ p.1.1.val
    else (t (x i)) ^ p.1.1.val * (t (y i)) ^ p.1.2.val +
         (t (x i)) ^ p.1.2.val * (t (y i)) ^ p.1.1.val
  have hdot : ∀ i j : Fin m,
      (∑ p : SymPairIdx b, w j p * z i p) = (P j).eval (t (x i)) * (P j).eval (t (y i)) := by
    intro i j
    rw [hP_eval j (t (x i)), hP_eval j (t (y i))]
    exact sum_symPairIdx_eq b (fun u => (P j).coeff u.val)
      (fun u => (t (x i)) ^ u.val) (fun v => (t (y i)) ^ v.val)
  have hdot_lt : ∀ i j : Fin m, j < i → (∑ p : SymPairIdx b, w j p * z i p) = 0 := by
    intro i j hji
    rw [hdot, hP_eval_prod, hP_eval_prod]
    rcases hinter i j hji with hx | hy
    · have h0 : ∏ q ∈ B j, (t (x i) - t q) = 0 :=
        Finset.prod_eq_zero hx (sub_self _)
      rw [h0, zero_mul]
    · have h0 : ∏ q ∈ B j, (t (y i) - t q) = 0 :=
        Finset.prod_eq_zero hy (sub_self _)
      rw [h0, mul_zero]
  have hdot_diag : ∀ i : Fin m, (∑ p : SymPairIdx b, w i p * z i p) ≠ 0 := by
    intro i
    rw [hdot, hP_eval_prod, hP_eval_prod]
    refine mul_ne_zero ?_ ?_
    · rw [Finset.prod_ne_zero_iff]
      intro q hq hsub
      exact (hdisj i).1 ((ht_inj (sub_eq_zero.mp hsub)) ▸ hq)
    · rw [Finset.prod_ne_zero_iff]
      intro q hq hsub
      exact (hdisj i).2 ((ht_inj (sub_eq_zero.mp hsub)) ▸ hq)
  have hlin : LinearIndependent ℚ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push Not at hne
    let s := Finset.univ.filter (fun j : Fin m => c j ≠ 0)
    have hs_ne : s.Nonempty := by
      rcases hne with ⟨j, hj⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    let i := s.max' hs_ne
    have hi_mem : i ∈ s := Finset.max'_mem s hs_ne
    have hci_ne : c i ≠ 0 := (Finset.mem_filter.mp hi_mem).2
    have hsum0 : (∑ p : SymPairIdx b, (∑ j : Fin m, c j • w j) p * z i p) = 0 := by
      rw [hc]
      simp
    have hswap :
        (∑ p : SymPairIdx b, (∑ j : Fin m, c j • w j) p * z i p) =
        ∑ j : Fin m, c j * (∑ p : SymPairIdx b, w j p * z i p) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hswap] at hsum0
    have hsingle : (∑ j : Fin m, c j * (∑ p : SymPairIdx b, w j p * z i p)) =
        c i * (∑ p : SymPairIdx b, w i p * z i p) := by
      refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => absurd (Finset.mem_univ i) hi)
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · rw [hdot_lt i j hlt, mul_zero]
      · have hcj0 : c j = 0 := by
          by_contra hcj_ne
          have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hcj_ne⟩
          exact not_lt_of_ge (Finset.le_max' s j hjs) hgt
        rw [hcj0, zero_mul]
    rw [hsingle] at hsum0
    exact mul_ne_zero hci_ne (hdot_diag i) hsum0
  have hcard := hlin.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_pi, card_symPairIdx] at hcard
  exact hcard

/-- Pin's Compression Lemma (1983): in a synchronizing `n`-state DFA, every subset `R` of
size `r ≥ 2` is compressed (`|R · w| < r`) by some word `w` of length at most `(n - r + 2).choose 2`. -/
theorem pin_compression_bound {Q α : Type*} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (R : Finset Q) (hR : 2 ≤ R.card) :
    ∃ w : List α, w.length ≤ (Fintype.card Q - R.card + 2).choose 2 ∧
      (A.image R w).card < R.card := by
  classical
  have hex : ∃ k : ℕ, ∃ w : List α, w.length = k ∧ (A.image R w).card < R.card := by
    rcases hSync with ⟨w, q₀, hq₀⟩
    refine ⟨w.length, w, rfl, ?_⟩
    have hsub : A.image R w ⊆ {q₀} := by
      intro q hq
      rw [DFA.mem_image] at hq
      rcases hq with ⟨p, _, rfl⟩
      simp [hq₀ p]
    have hc := Finset.card_le_card hsub
    simp at hc
    omega
  let m := Nat.find hex
  obtain ⟨w, hwlen, hwcomp⟩ := Nat.find_spec hex
  have hmin : ∀ v : List α, (A.image R v).card < R.card → m ≤ v.length := fun v hv =>
    Nat.find_min' hex ⟨v, rfl, hv⟩
  refine ⟨w, ?_, hwcomp⟩
  rw [hwlen]
  -- Pick distinct x₀, y₀ ∈ R merged by w
  have hex_pair : ∃ x₀ ∈ R, ∃ y₀ ∈ R, x₀ ≠ y₀ ∧ A.eval x₀ w = A.eval y₀ w := by
    by_contra hall
    push Not at hall
    have hinj : Set.InjOn (fun q => A.eval q w) R := fun x hx y hy hxy => by
      by_contra hne
      exact hall x hx y hy hne hxy
    have heq := Finset.card_image_of_injOn hinj
    change (A.image R w).card = R.card at heq
    omega
  rcases hex_pair with ⟨x₀, hx₀, y₀, hy₀, hx₀y₀, hmerge⟩
  let x : Fin m → Q := fun k => A.eval x₀ (w.take k.val)
  let y : Fin m → Q := fun k => A.eval y₀ (w.take k.val)
  let Rk : Fin m → Finset Q := fun k => A.image R (w.take k.val)
  let B : Fin m → Finset Q := fun k => Finset.univ \ Rk k
  have hRk_card : ∀ k : Fin m, (Rk k).card = R.card := by
    intro k
    have hle : (Rk k).card ≤ R.card := A.card_image_le R (w.take k.val)
    have hnotlt : ¬ (Rk k).card < R.card := by
      intro hlt
      have hb := hmin (w.take k.val) hlt
      rw [List.length_take] at hb
      omega
    omega
  have hB_card : ∀ k : Fin m, (B k).card ≤ Fintype.card Q - R.card := by
    intro k
    dsimp [B]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hRk_card k]
  have hdisj : ∀ k : Fin m, x k ∉ B k ∧ y k ∉ B k := by
    intro k
    have hx_in : x k ∈ Rk k := by rw [DFA.mem_image]; exact ⟨x₀, hx₀, rfl⟩
    have hy_in : y k ∈ Rk k := by rw [DFA.mem_image]; exact ⟨y₀, hy₀, rfl⟩
    exact ⟨fun h => (Finset.mem_sdiff.mp h).2 hx_in, fun h => (Finset.mem_sdiff.mp h).2 hy_in⟩
  have hxy_ne : ∀ k : Fin m, x k ≠ y k := by
    intro k heq
    have hlt : (Rk k).card < R.card := by
      have himg_eq : Rk k = A.image (R.erase x₀) (w.take k.val) := by
        ext q
        simp only [Rk, DFA.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨p, hp, rfl⟩
          by_cases hpx : p = x₀
          · subst hpx; exact ⟨y₀, ⟨hx₀y₀.symm, hy₀⟩, heq.symm⟩
          · exact ⟨p, ⟨hpx, hp⟩, rfl⟩
        · rintro ⟨p, ⟨_, hp⟩, rfl⟩
          exact ⟨p, hp, rfl⟩
      rw [himg_eq]
      exact lt_of_le_of_lt (A.card_image_le _ _) (Finset.card_erase_lt_of_mem hx₀)
    have := hRk_card k
    omega
  have hinter : ∀ i j : Fin m, j < i → x i ∈ B j ∨ y i ∈ B j := by
    intro i j hji
    by_contra hnot
    push Not at hnot
    have hxi_in : x i ∈ Rk j := by
      by_contra hnotR
      exact hnot.1 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotR⟩)
    have hyi_in : y i ∈ Rk j := by
      by_contra hnotR
      exact hnot.2 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotR⟩)
    have hmerge_drop : A.eval (x i) (w.drop i.val) = A.eval (y i) (w.drop i.val) := by
      dsimp [x, y]
      rw [← DFA.eval_append, ← DFA.eval_append, List.take_append_drop]
      exact hmerge
    let w' := w.take j.val ++ w.drop i.val
    have hcomp' : (A.image R w').card < R.card := by
      dsimp [w']
      rw [DFA.image_append]
      change (A.image (Rk j) (w.drop i.val)).card < R.card
      rw [← hRk_card j]
      have himg_eq : A.image (Rk j) (w.drop i.val) = A.image ((Rk j).erase (x i)) (w.drop i.val) := by
        ext q
        simp only [DFA.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨p, hp, rfl⟩
          by_cases hpx : p = x i
          · subst hpx; exact ⟨y i, ⟨(hxy_ne i).symm, hyi_in⟩, hmerge_drop.symm⟩
          · exact ⟨p, ⟨hpx, hp⟩, rfl⟩
        · rintro ⟨p, ⟨_, hp⟩, rfl⟩
          exact ⟨p, hp, rfl⟩
      rw [himg_eq]
      exact lt_of_le_of_lt (A.card_image_le _ _) (Finset.card_erase_lt_of_mem hxi_in)
    have hb := hmin w' hcomp'
    simp only [w', List.length_append, List.length_take, List.length_drop] at hb
    have hji' : j.val < i.val := hji
    omega
  exact frankl_skew_two m (Fintype.card Q - R.card) x y B hB_card hdisj hinter

private theorem six_mul_sum_choose_two (k : ℕ) :
    6 * (∑ r ∈ Finset.range k, (r + 2).choose 2) = k * (k + 1) * (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hch : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
      rw [Nat.choose_two_right]
      have heven : 2 ∣ (k + 2) * (k + 1) := by
        have := Nat.even_mul_succ_self (k + 1)
        rcases this.two_dvd with ⟨t, ht⟩
        exact ⟨t, by linarith⟩
      rcases heven with ⟨t, ht⟩
      have hsub : k + 2 - 1 = k + 1 := by omega
      rw [hsub, ht]
      omega
    linarith

private theorem pin_frankl_induction {Q α : Type*} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) :
    ∀ r : ℕ, 1 ≤ r → r ≤ Fintype.card Q →
      ∀ R : Finset Q, R.card = r →
        ∃ w : List α, (A.image R w).card = 1 ∧
          w.length ≤ ∑ j ∈ Finset.range (r - 1), (Fintype.card Q - (j + 2) + 2).choose 2 := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr1 hrn R hR
    by_cases h1 : r = 1
    · subst h1
      exact ⟨[], by simpa using hR, by simp⟩
    · have hr2 : 2 ≤ R.card := by omega
      obtain ⟨v, hvlen, hvcomp⟩ := pin_compression_bound A hSync R hr2
      let R' := A.image R v
      have hR'_lt : R'.card < R.card := hvcomp
      have hR'_ne : R'.Nonempty := by
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
        exact ⟨A.eval x v, by rw [DFA.mem_image]; exact ⟨x, hx, rfl⟩⟩
      have hR'_pos : 1 ≤ R'.card := Finset.card_pos.mpr hR'_ne
      obtain ⟨u, hu1, hulen⟩ := ih R'.card (by omega) hR'_pos (by omega) R' rfl
      refine ⟨v ++ u, ?_, ?_⟩
      · rw [DFA.image_append]; exact hu1
      · rw [List.length_append]
        have hsum_le :
            (∑ j ∈ Finset.range (R'.card - 1), (Fintype.card Q - (j + 2) + 2).choose 2) ≤
            (∑ j ∈ Finset.range (r - 2), (Fintype.card Q - (j + 2) + 2).choose 2) :=
          Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
        have hsplit :
            (∑ j ∈ Finset.range (r - 1), (Fintype.card Q - (j + 2) + 2).choose 2) =
            (∑ j ∈ Finset.range (r - 2), (Fintype.card Q - (j + 2) + 2).choose 2) +
            (Fintype.card Q - r + 2).choose 2 := by
          have hr_eq : r - 1 = (r - 2) + 1 := by omega
          have harg : (r - 2) + 2 = r := by omega
          rw [hr_eq, Finset.sum_range_succ, harg]
        rw [hR] at hvlen
        omega

/-- Pin–Frankl Cubic Upper Bound (1982/1983, division-free):
every synchronizing `n`-state DFA (`n ≥ 1`) admits a synchronizing word of length `L`
with `6 * L ≤ n ^ 3 - n`. -/
theorem pin_frankl_bound {Q α : Type*} [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ 6 * w.length ≤ (Fintype.card Q) ^ 3 - Fintype.card Q := by
  classical
  have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos
  obtain ⟨w, hw1, hwlen⟩ := pin_frankl_induction A hSync (Fintype.card Q) hpos le_rfl
    Finset.univ Finset.card_univ
  refine ⟨w, (A.isSyncWord_iff_card_image_univ_eq_one w).mpr hw1, ?_⟩
  let n := Fintype.card Q
  have hreindex :
      (∑ j ∈ Finset.range (n - 1), (n - (j + 2) + 2).choose 2) =
      ∑ r ∈ Finset.range (n - 1), (r + 2).choose 2 := by
    refine Finset.sum_bij (fun j _ => n - 2 - j) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_range] at hj ⊢
      omega
    · intro j₁ hj₁ j₂ hj₂ h
      rw [Finset.mem_range] at hj₁ hj₂
      omega
    · intro r hr
      rw [Finset.mem_range] at hr
      refine ⟨n - 2 - r, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j hj
      rw [Finset.mem_range] at hj
      congr 1
      omega
  have hsum := six_mul_sum_choose_two (n - 1)
  have hn1 : 1 ≤ n := hpos
  have hn3 : n ≤ n ^ 3 := Nat.le_self_pow (by omega) n
  have hmul : (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) = n ^ 3 - n := by
    zify [hn1, hn3]
    ring
  change w.length ≤ ∑ j ∈ Finset.range (n - 1), (n - (j + 2) + 2).choose 2 at hwlen
  rw [hreindex] at hwlen
  have h6 : 6 * w.length ≤ 6 * ∑ r ∈ Finset.range (n - 1), (r + 2).choose 2 :=
    Nat.mul_le_mul_left 6 hwlen
  rw [hsum, hmul] at h6
  exact h6

/-- Pin–Frankl Cubic Upper Bound (1982/1983):
every synchronizing `n`-state DFA (`n ≥ 1`) admits a synchronizing word of length at most
`(n ^ 3 - n) / 6`. -/
theorem pin_frankl_div_bound {Q α : Type*} [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ ((Fintype.card Q) ^ 3 - Fintype.card Q) / 6 := by
  obtain ⟨w, hw, h6⟩ := pin_frankl_bound A hSync
  exact ⟨w, hw, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)⟩

end PinFrankl

/-! ## Part 3: Rank-`k` Fiber-Collision Bridge Lemma & Small-Rank Letter Bounds -/

section SmallRank

variable {Q α : Type*}

/-- Pushforward linear operator of a word `w` on row vectors `Q → ℚ`:
`(pushWord A w x) q = ∑_{p : p · w = q} x p`. -/
private def pushWord [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) :
    (Q → ℚ) →ₗ[ℚ] (Q → ℚ) where
  toFun x q := ∑ p : Q, if A.eval p w = q then x p else 0
  map_add' x y := by
    ext q
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  map_smul' c x := by
    ext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp

private theorem pushWord_nil [Fintype Q] [DecidableEq Q] (A : DFA Q α) (x : Q → ℚ) :
    pushWord A [] x = x := by
  ext q
  simp only [pushWord, LinearMap.coe_mk, AddHom.coe_mk, DFA.eval_nil]
  rw [Finset.sum_eq_single q]
  · simp
  · intro p _ hp; simp [hp]
  · intro h; exact absurd (Finset.mem_univ q) h

private theorem pushWord_append [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w₁ w₂ : List α)
    (x : Q → ℚ) :
    pushWord A (w₁ ++ w₂) x = pushWord A w₂ (pushWord A w₁ x) := by
  ext q
  simp only [pushWord, LinearMap.coe_mk, AddHom.coe_mk]
  calc
    (∑ p : Q, if A.eval p (w₁ ++ w₂) = q then x p else 0)
        = ∑ p : Q, ∑ r : Q, if A.eval p w₁ = r then (if A.eval r w₂ = q then x p else 0) else 0 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          simp [Finset.sum_ite_eq, DFA.eval_append]
    _ = ∑ r : Q, ∑ p : Q, if A.eval p w₁ = r then (if A.eval r w₂ = q then x p else 0) else 0 :=
          Finset.sum_comm
    _ = ∑ r : Q, if A.eval r w₂ = q then (∑ p : Q, if A.eval p w₁ = r then x p else 0) else 0 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          by_cases hr : A.eval r w₂ = q
          · simp [hr]
          · simp [hr]

private theorem pushWord_sum_all [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α)
    (x : Q → ℚ) :
    (∑ q : Q, pushWord A w x q) = ∑ p : Q, x p := by
  simp only [pushWord, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Finset.sum_ite_eq]

private def indVec [DecidableEq Q] (S : Finset Q) : Q → ℚ :=
  fun q => if q ∈ S then 1 else 0

private theorem sum_indVec [Fintype Q] [DecidableEq Q] (S : Finset Q) :
    (∑ q : Q, indVec S q) = (S.card : ℚ) := by
  simp [indVec]

private theorem sum_preimage_pushWord_indVec [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (S : Finset Q) (w u : List α) (y : Q) :
    (∑ q ∈ A.preimage {y} u, pushWord A w (indVec S) q) =
    ((S.filter (fun p => A.eval p (w ++ u) = y)).card : ℚ) := by
  simp only [pushWord, LinearMap.coe_mk, AddHom.coe_mk, indVec]
  rw [Finset.sum_comm]
  calc
    (∑ p : Q, ∑ q ∈ A.preimage {y} u, if A.eval p w = q then (if p ∈ S then (1 : ℚ) else 0) else 0)
        = ∑ p : Q, if A.eval p w ∈ A.preimage {y} u then (if p ∈ S then (1 : ℚ) else 0) else 0 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_ite_eq]
    _ = ∑ p : Q, if p ∈ S ∧ A.eval p (w ++ u) = y then (1 : ℚ) else 0 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [DFA.mem_preimage, Finset.mem_singleton, ← DFA.eval_append]
          by_cases h1 : A.eval p (w ++ u) = y <;> by_cases h2 : p ∈ S <;> simp [h1, h2]
    _ = ((S.filter (fun p => A.eval p (w ++ u) = y)).card : ℚ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_one]
          apply congrArg Nat.cast
          apply congrArg Finset.card
          ext p
          simp

/-- **Rank-`k` Fiber-Collision Bridge Lemma**:
In a synchronizing `n`-state DFA, for any word `u` of rank `k := |Q · u| ≥ 2` and any subset
`S` of size `k`, there exists a word `w` of length `≤ n - k + 1` with `|S · (w ++ u)| ≤ k - 1`. -/
theorem rank_k_bridge_lemma [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (u : List α)
    (hk : 2 ≤ (A.image Finset.univ u).card) (S : Finset Q)
    (hS : S.card = (A.image Finset.univ u).card) :
    ∃ w : List α, w.length ≤ Fintype.card Q - (A.image Finset.univ u).card + 1 ∧
      (A.image S (w ++ u)).card ≤ (A.image Finset.univ u).card - 1 := by
  classical
  let Img := A.image Finset.univ u
  let k := Img.card
  have hk2 : 2 ≤ k := hk
  have hk_ne_zero : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  obtain ⟨y₀, hy₀⟩ := Finset.card_pos.mp (by omega : 0 < Img.card)
  let Img' := Img.erase y₀
  have hImg'_card : Img'.card = k - 1 := Finset.card_erase_of_mem hy₀
  -- Define fiber-balance linear map Φ : (Q → ℚ) →ₗ[ℚ] ({y // y ∈ Img'} → ℚ)
  let Φ : (Q → ℚ) →ₗ[ℚ] ({y // y ∈ Img'} → ℚ) :=
    { toFun := fun x y => (k : ℚ) * (∑ q ∈ A.preimage {y.1} u, x q) - ∑ q : Q, x q
      map_add' := fun x₁ x₂ => by
        ext y
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        ext y
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
        ring }
  -- Prove Φ is surjective by exhibiting a preimage for every standard basis vector
  have hrep : ∀ y ∈ Img, ∃ q : Q, A.eval q u = y := by
    intro y hy
    rw [DFA.mem_image] at hy
    rcases hy with ⟨q, _, hq⟩
    exact ⟨q, hq⟩
  obtain ⟨q₀, hq₀⟩ := hrep y₀ hy₀
  have hΦ_surj : Function.Surjective Φ := by
    intro b
    have hbasis : ∀ y : {y // y ∈ Img'}, ∃ v : Q → ℚ, Φ v = Pi.single y 1 := by
      intro y
      have hy_img : y.1 ∈ Img := Finset.mem_of_mem_erase y.2
      have hy_ne : y.1 ≠ y₀ := (Finset.mem_erase.mp y.2).1
      obtain ⟨qy, hqy⟩ := hrep y.1 hy_img
      let v : Q → ℚ := fun q =>
        (1 / (k : ℚ)) * ((if q = qy then (1 : ℚ) else 0) - (if q = q₀ then (1 : ℚ) else 0))
      refine ⟨v, ?_⟩
      ext y'
      have hsum_v : (∑ q : Q, v q) = 0 := by
        simp only [v, ← Finset.mul_sum, Finset.sum_sub_distrib]
        simp
      have hpre_v : (∑ q ∈ A.preimage {y'.1} u, v q) =
          if y' = y then 1 / (k : ℚ) else 0 := by
        simp only [v, ← Finset.mul_sum, Finset.sum_sub_distrib]
        have hq₀_not : q₀ ∉ A.preimage {y'.1} u := by
          rw [DFA.mem_preimage, Finset.mem_singleton, hq₀]
          exact Ne.symm (Finset.mem_erase.mp y'.2).1
        have hqy_iff : qy ∈ A.preimage {y'.1} u ↔ y' = y := by
          rw [DFA.mem_preimage, Finset.mem_singleton, hqy, Subtype.ext_iff]
          exact eq_comm
        simp only [Finset.sum_ite_eq', hq₀_not, ↓reduceIte, sub_zero]
        by_cases hyy : y' = y
        · subst hyy
          have hmem : qy ∈ A.preimage {y'.1} u := hqy_iff.mpr rfl
          simp only [hmem, ↓reduceIte, mul_one]
        · have hnotmem : qy ∉ A.preimage {y'.1} u := fun h => hyy (hqy_iff.mp h)
          simp only [hnotmem, hyy, ↓reduceIte, mul_zero]
      change (k : ℚ) * (∑ q ∈ A.preimage {y'.1} u, v q) - ∑ q : Q, v q =
        (Pi.single y (1 : ℚ) : {y // y ∈ Img'} → ℚ) y'
      rw [hpre_v, hsum_v, sub_zero]
      by_cases hyy : y' = y
      · subst hyy
        simp [hk_ne_zero]
      · simp [hyy]
    choose basis hbasis using hbasis
    refine ⟨∑ y : {y // y ∈ Img'}, b y • basis y, ?_⟩
    rw [map_sum]
    ext y'
    simp only [map_smul, hbasis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single y']
    · simp
    · intro y _ hyy
      simp [Pi.single_eq_of_ne (Ne.symm hyy)]
    · intro h; exact absurd (Finset.mem_univ y') h
  -- Compute dim (ker Φ) = n - k + 1
  let H : Submodule ℚ (Q → ℚ) := LinearMap.ker Φ
  have hdimH : Module.finrank ℚ H = Fintype.card Q - k + 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    have hrange : LinearMap.range Φ = ⊤ := LinearMap.range_eq_top.mpr hΦ_surj
    rw [hrange, finrank_top, Module.finrank_pi, Module.finrank_pi, Fintype.card_coe, hImg'_card] at hrn
    have hk_le : k ≤ Fintype.card Q := Finset.card_le_univ Img
    change k - 1 + Module.finrank ℚ H = Fintype.card Q at hrn
    omega
  -- Exact collision equivalence: pushWord A w (indVec S) ∉ H ↔ |S · (w ++ u)| ≤ k - 1
  have hnotH_iff : ∀ w : List α,
      pushWord A w (indVec S) ∉ H → (A.image S (w ++ u)).card ≤ k - 1 := by
    intro w hnotH
    have hne0 : Φ (pushWord A w (indVec S)) ≠ 0 := by
      simpa [H, LinearMap.mem_ker] using hnotH
    have hex_y : ∃ y : {y // y ∈ Img'}, Φ (pushWord A w (indVec S)) y ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne0 (funext hall)
    obtain ⟨⟨y, hy'⟩, hy_ne0⟩ := hex_y
    have hval : Φ (pushWord A w (indVec S)) ⟨y, hy'⟩ =
        (k : ℚ) * ((S.filter (fun p => A.eval p (w ++ u) = y)).card : ℚ) - (k : ℚ) := by
      change (k : ℚ) * (∑ q ∈ A.preimage {y} u, pushWord A w (indVec S) q) -
          (∑ q : Q, pushWord A w (indVec S) q) = _
      rw [sum_preimage_pushWord_indVec, pushWord_sum_all, sum_indVec, hS]
    rw [hval] at hy_ne0
    let m_y := (S.filter (fun p => A.eval p (w ++ u) = y)).card
    have hmy_ne1 : m_y ≠ 1 := by
      intro h1
      apply hy_ne0
      change (k : ℚ) * (m_y : ℚ) - (k : ℚ) = 0
      rw [h1]
      ring
    by_cases hmy0 : m_y = 0
    · -- y ∉ A.image S (w ++ u), while A.image S (w ++ u) ⊆ Img
      have hsub : A.image S (w ++ u) ⊆ Img.erase y := by
        intro r hr
        rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · intro rfl
          rw [DFA.mem_image] at hr
          rcases hr with ⟨p, hpS, hp_ev⟩
          have hpos : 0 < m_y := Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hpS, hp_ev⟩⟩
          omega
        · rw [DFA.mem_image] at hr
          rcases hr with ⟨p, _, rfl⟩
          rw [DFA.eval_append]
          exact Finset.mem_image.mpr ⟨A.eval p w, Finset.mem_univ _, rfl⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_of_mem_erase hy')] at hle
      exact hle
    · -- m_y ≥ 2: two distinct states in S map to y under w ++ u
      have hge2 : 2 ≤ m_y := by omega
      have h1lt : 1 < (S.filter (fun p => A.eval p (w ++ u) = y)).card := by omega
      obtain ⟨p₁, hp₁, p₂, hp₂, hp12⟩ := Finset.one_lt_card.mp h1lt
      rw [Finset.mem_filter] at hp₁ hp₂
      have hlt : (A.image S (w ++ u)).card < S.card := by
        have heq : A.image S (w ++ u) = A.image (S.erase p₁) (w ++ u) := by
          ext r
          simp only [DFA.mem_image, Finset.mem_erase]
          constructor
          · rintro ⟨p, hp, rfl⟩
            by_cases hpp : p = p₁
            · subst hpp; exact ⟨p₂, ⟨hp12.symm, hp₂.1⟩, hp₂.2.trans hp₁.2.symm⟩
            · exact ⟨p, ⟨hpp, hp⟩, rfl⟩
          · rintro ⟨p, ⟨_, hp⟩, rfl⟩
            exact ⟨p, hp, rfl⟩
        rw [heq]
        exact lt_of_le_of_lt (A.card_image_le _ _) (Finset.card_erase_lt_of_mem hp₁.1)
      change S.card = k at hS
      omega
  -- Check if w = [] already works
  by_cases h0 : indVec S ∉ H
  · refine ⟨[], by simp, hnotH_iff [] (by rw [pushWord_nil]; exact h0)⟩
  push Not at h0
  -- Otherwise run the ascending subspace chain V d = span {pushWord A w (indVec S) | w.length ≤ d}
  let V : ℕ → Submodule ℚ (Q → ℚ) := fun d =>
    Submodule.span ℚ { v : Q → ℚ | ∃ w : List α, w.length ≤ d ∧ v = pushWord A w (indVec S) }
  have hV_mono : ∀ {i j}, i ≤ j → V i ≤ V j := by
    intro i j hij
    apply Submodule.span_mono
    rintro v ⟨w, hwlen, rfl⟩
    exact ⟨w, le_trans hwlen hij, rfl⟩
  -- Synchronization escapes H
  obtain ⟨z, qz, hqz⟩ := hSync
  have hz_notH : pushWord A z (indVec S) ∉ H := by
    intro hzH
    have h0' : Φ (pushWord A z (indVec S)) = 0 := LinearMap.mem_ker.mp hzH
    -- Under z ++ u, every state maps to A.eval qz u
    have hcount : ∀ y : {y // y ∈ Img'},
        (S.filter (fun p => A.eval p (z ++ u) = y.1)).card = 1 := by
      intro y
      have hhy := congrFun h0' y
      change (k : ℚ) * (∑ q ∈ A.preimage {y.1} u, pushWord A z (indVec S) q) -
          (∑ q : Q, pushWord A z (indVec S) q) = 0 at hhy
      rw [sum_preimage_pushWord_indVec, pushWord_sum_all, sum_indVec, hS] at hhy
      have hmul : (k : ℚ) * ((S.filter (fun p => A.eval p (z ++ u) = y.1)).card : ℚ) = (k : ℚ) * 1 := by
        linarith
      have heq1 : ((S.filter (fun p => A.eval p (z ++ u) = y.1)).card : ℚ) = 1 :=
        mul_left_cancel₀ hk_ne_zero hmul
      exact_mod_cast heq1
    -- All states in S map to A.eval qz u, so filter for y ≠ A.eval qz u is empty, yet k ≥ 2!
    have hconst : ∀ p : Q, A.eval p (z ++ u) = A.eval qz u := fun p => by
      rw [DFA.eval_append, hqz p]
    -- Pick y ∈ Img' with y ≠ A.eval qz u? If k = 2, Img' has 1 element which might equal A.eval qz u!
    -- Instead: since S.card = k ≥ 2, for y = A.eval qz u the filter has card k ≥ 2 ≠ 1!
    obtain ⟨y₁, hy₁⟩ := Finset.card_pos.mp (by omega : 0 < Img'.card)
    have hc1 := hcount ⟨y₁, hy₁⟩
    by_cases heq_target : A.eval qz u = y₁
    · have hfilt_all : S.filter (fun p => A.eval p (z ++ u) = y₁) = S :=
        Finset.filter_true_of_mem fun p _ => (hconst p).trans heq_target
      rw [hfilt_all, hS] at hc1
      omega
    · have hfilt_emp : S.filter (fun p => A.eval p (z ++ u) = y₁) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun p _ h => heq_target ((hconst p).symm.trans h)
      rw [hfilt_emp, Finset.card_empty] at hc1
      omega
  have hex_esc : ∃ d : ℕ, ¬ (V d ≤ H) := by
    refine ⟨z.length, fun hle => hz_notH (hle ?_)⟩
    exact Submodule.subset_span ⟨z, le_rfl, rfl⟩
  let d₀ := Nat.find hex_esc
  have hd₀_not : ¬ (V d₀ ≤ H) := Nat.find_spec hex_esc
  have hd₀_min : ∀ j < d₀, V j ≤ H := fun j hj => by
    by_contra hnot
    exact Nat.find_min hex_esc hj hnot
  have hd₀_pos : 1 ≤ d₀ := by
    by_contra h0'
    have hzd : d₀ = 0 := by omega
    rw [hzd] at hd₀_not
    apply hd₀_not
    rw [Submodule.span_le]
    rintro v ⟨w, hwlen, rfl⟩
    have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil, pushWord_nil]
    exact h0
  -- Strict growth V j < V (j + 1) for all j < d₀
  have hV_strict : ∀ j < d₀, V j < V (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hV_mono (by omega)) fun heq => ?_
    have hclosed : ∀ a : α, ∀ v ∈ V j, pushWord A [a] v ∈ V j := by
      intro a v hv
      have hmap : Submodule.map (pushWord A [a]) (V j) ≤ V (j + 1) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨w, hwlen, rfl⟩
        rw [← pushWord_append]
        exact Submodule.subset_span ⟨w ++ [a], by simp; omega, rfl⟩
      rw [← heq] at hmap
      exact hmap ⟨v, hv, rfl⟩
    have hall_words : ∀ w : List α, pushWord A w (indVec S) ∈ V j := by
      intro w
      induction w using List.reverseRecOn with
      | nil =>
        rw [pushWord_nil]
        exact Submodule.subset_span ⟨[], by simp, (pushWord_nil A _).symm⟩
      | append_singleton w a ih =>
        rw [pushWord_append]
        exact hclosed a _ ih
    exact hz_notH (hd₀_min j hj (hall_words z))
  -- Induct on j to get 1 + j ≤ finrank (V j) for j < d₀
  have hdim_V0 : 1 ≤ Module.finrank ℚ (V 0) := by
    have hmem0 : indVec S ∈ V 0 := Submodule.subset_span ⟨[], le_rfl, (pushWord_nil A _).symm⟩
    have hne0 : indVec S ≠ 0 := by
      obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      intro hzero
      have := congrFun hzero s
      simp [indVec, hs] at this
    have hbot : (⊥ : Submodule ℚ (Q → ℚ)) < V 0 := by
      rw [bot_lt_iff_ne_bot]
      intro hbot'
      rw [hbot', Submodule.mem_bot] at hmem0
      exact hne0 hmem0
    have hlt := Submodule.finrank_lt_finrank_of_lt hbot
    rw [finrank_bot] at hlt
    omega
  have hdim_Vj : ∀ j < d₀, 1 + j ≤ Module.finrank ℚ (V j) := by
    intro j
    induction j with
    | zero => intro _; simpa using hdim_V0
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hlt := Submodule.finrank_lt_finrank_of_lt (hV_strict j (by omega))
      omega
  have hd₀_le : d₀ ≤ Fintype.card Q - k + 1 := by
    have h1 := hdim_Vj (d₀ - 1) (by omega)
    have h2 : Module.finrank ℚ (V (d₀ - 1)) ≤ Module.finrank ℚ H :=
      Submodule.finrank_mono (hd₀_min (d₀ - 1) (by omega))
    omega
  -- Extract a generator of V d₀ outside H
  have hex_gen : ∃ v ∈ { v : Q → ℚ | ∃ w : List α, w.length ≤ d₀ ∧ v = pushWord A w (indVec S) },
      v ∉ H := by
    by_contra hall
    push Not at hall
    exact hd₀_not (Submodule.span_le.mpr hall)
  rcases hex_gen with ⟨_, ⟨w, hwlen, rfl⟩, hw_notH⟩
  exact ⟨w, le_trans hwlen hd₀_le, hnotH_iff w hw_notH⟩

private theorem bridge_monotone_aux (n L : ℕ) :
    ∀ k' k : ℕ, 1 ≤ k' → k' ≤ k → k ≤ n →
      2 ^ (k' - 1) * (L + n - k' + 2) ≤ 2 ^ (k - 1) * (L + n - k + 2) := by
  intro k' k hk' hkk' hkn
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases heq : k' = k + 1
    · subst heq; exact le_rfl
    · have hle : k' ≤ k := by omega
      have ih' := ih hle (by omega)
      have hstep : 2 ^ (k - 1) * (L + n - k + 2) ≤ 2 ^ k * (L + n - (k + 1) + 2) := by
        have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
          have hk1 : 1 ≤ k := by omega
          conv_lhs => rw [← Nat.sub_add_cancel hk1, pow_succ]
        rw [hpow, mul_assoc]
        apply Nat.mul_le_mul_left
        omega
      simpa using le_trans ih' hstep

private theorem exists_syncWord_of_rank_word [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) :
    ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card Q →
      ∀ u : List α, (A.image Finset.univ u).card = k →
        ∃ w : List α, A.IsSyncWord w ∧
          w.length + (Fintype.card Q + 1) ≤ 2 ^ (k - 1) * (u.length + Fintype.card Q - k + 2) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk1 hkn u hu
    by_cases hk_eq1 : k = 1
    · subst hk_eq1
      refine ⟨u, (A.isSyncWord_iff_card_image_univ_eq_one u).mpr hu, ?_⟩
      simp only [Nat.sub_self, pow_zero, one_mul]
      omega
    · have hk2 : 2 ≤ (A.image Finset.univ u).card := by omega
      obtain ⟨v, hvlen, hvcard⟩ :=
        rank_k_bridge_lemma A hSync u hk2 (A.image Finset.univ u) rfl
      let u' := u ++ (v ++ u)
      have hu'_img : A.image Finset.univ u' = A.image (A.image Finset.univ u) (v ++ u) := by
        dsimp [u']
        rw [DFA.image_append]
      let k' := (A.image Finset.univ u').card
      have hk'_le : k' ≤ k - 1 := by
        dsimp [k']
        rw [hu'_img, ← hu]
        exact hvcard
      have hk'_pos : 1 ≤ k' := by
        obtain ⟨q⟩ := hSync.nonempty
        exact Finset.card_pos.mpr ⟨A.eval q u', by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩⟩
      obtain ⟨w, hw, hwlen⟩ := ih k' (by omega) hk'_pos (by omega) u' rfl
      refine ⟨w, hw, ?_⟩
      have hmono := bridge_monotone_aux (Fintype.card Q) u'.length k' (k - 1) hk'_pos hk'_le (by omega)
      have hu'_len : u'.length ≤ 2 * u.length + (Fintype.card Q - k + 1) := by
        simp only [u', List.length_append]
        rw [hu] at hvlen
        omega
      have hstep :
          2 ^ (k - 1 - 1) * (u'.length + Fintype.card Q - (k - 1) + 2) ≤
          2 ^ (k - 1) * (u.length + Fintype.card Q - k + 2) := by
        have hpow : 2 ^ (k - 1) = 2 ^ (k - 1 - 1) * 2 := by
          have : 1 ≤ k - 1 := by omega
          conv_lhs => rw [← Nat.sub_add_cancel this, pow_succ]
        rw [hpow, mul_assoc]
        apply Nat.mul_le_mul_left
        omega
      exact le_trans hwlen (le_trans hmono hstep)

/-- **Small-Rank Letter Theorem**: if a synchronizing `n`-state DFA has a letter `a` of
rank `r = |Q · a|`, then `rt(A) ≤ (n - r + 3) * 2^(r - 1) - (n + 1)`. -/
theorem exists_syncWord_of_rank_letter [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (a : α) :
    let r := (A.image Finset.univ [a]).card
    ∃ w : List α, A.IsSyncWord w ∧
      w.length + (Fintype.card Q + 1) ≤ (Fintype.card Q - r + 3) * 2 ^ (r - 1) := by
  intro r
  obtain ⟨q⟩ := hSync.nonempty
  have hr1 : 1 ≤ r := Finset.card_pos.mpr ⟨A.step q a, by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩⟩
  have hrn : r ≤ Fintype.card Q := Finset.card_le_univ _
  obtain ⟨w, hw, hlen⟩ := exists_syncWord_of_rank_word A hSync r hr1 hrn [a] rfl
  refine ⟨w, hw, ?_⟩
  simp only [List.length_singleton] at hlen
  have heq : 1 + Fintype.card Q - r + 2 = Fintype.card Q - r + 3 := by omega
  rw [heq, mul_comm] at hlen
  exact hlen

/-- **Rank-2 Letter Linear Bound**: if a synchronizing `n`-state DFA has a letter of rank `≤ 2`,
then it admits a synchronizing word of length at most `n + 1`. -/
theorem rank_le_two_bound [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (a : α) (hr : (A.image Finset.univ [a]).card ≤ 2) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ Fintype.card Q + 1 := by
  obtain ⟨q⟩ := hSync.nonempty
  have hn1 : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q⟩
  have hpos : 1 ≤ (A.image Finset.univ [a]).card :=
    Finset.card_pos.mpr ⟨A.step q a, by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩⟩
  obtain ⟨w, hw, hlen⟩ := exists_syncWord_of_rank_letter A hSync a
  refine ⟨w, hw, ?_⟩
  have hcases : (A.image Finset.univ [a]).card = 1 ∨ (A.image Finset.univ [a]).card = 2 := by omega
  rcases hcases with h1 | h2
  · rw [h1] at hlen
    have hp : 2 ^ (1 - 1) = 1 := by decide
    rw [hp] at hlen
    omega
  · rw [h2] at hlen
    have hn2 : 2 ≤ Fintype.card Q := by
      have := Finset.card_le_univ (A.image Finset.univ [a])
      omega
    have hp : 2 ^ (2 - 1) = 2 := by decide
    rw [hp] at hlen
    omega

/-- **Rank-3 Letter Linear Bound**: if a synchronizing `n`-state DFA has a letter of rank `≤ 3`,
then it admits a synchronizing word of length at most `3 * n - 1`. -/
theorem rank_le_three_bound [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (a : α) (hr : (A.image Finset.univ [a]).card ≤ 3) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ 3 * Fintype.card Q - 1 := by
  obtain ⟨q⟩ := hSync.nonempty
  have hn1 : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q⟩
  have hpos : 1 ≤ (A.image Finset.univ [a]).card :=
    Finset.card_pos.mpr ⟨A.step q a, by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩⟩
  obtain ⟨w, hw, hlen⟩ := exists_syncWord_of_rank_letter A hSync a
  refine ⟨w, hw, ?_⟩
  have hcases : (A.image Finset.univ [a]).card = 1 ∨
      (A.image Finset.univ [a]).card = 2 ∨ (A.image Finset.univ [a]).card = 3 := by omega
  rcases hcases with h1 | h2 | h3
  · rw [h1] at hlen
    have hp : 2 ^ (1 - 1) = 1 := by decide
    rw [hp] at hlen
    omega
  · rw [h2] at hlen
    have hn2 : 2 ≤ Fintype.card Q := by
      have := Finset.card_le_univ (A.image Finset.univ [a]); omega
    have hp : 2 ^ (2 - 1) = 2 := by decide
    rw [hp] at hlen
    omega
  · rw [h3] at hlen
    have hn3 : 3 ≤ Fintype.card Q := by
      have := Finset.card_le_univ (A.image Finset.univ [a]); omega
    have hp : 2 ^ (3 - 1) = 4 := by decide
    rw [hp] at hlen
    omega

/-- **Rank-3 Letter Černý Theorem (`n ≥ 5`)**: every synchronizing DFA on `n ≥ 5` states
possessing a letter of rank `≤ 3` satisfies Černý's bound `w.length ≤ (n - 1) ^ 2`. -/
theorem rank_le_three_cerny_ge_five [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hn : 5 ≤ Fintype.card Q)
    (a : α) (hr : (A.image Finset.univ [a]).card ≤ 3) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ := rank_le_three_bound A hSync a hr
  refine ⟨w, hw, le_trans hlen ?_⟩
  zify [show 1 ≤ Fintype.card Q by omega, show 1 ≤ 3 * Fintype.card Q by omega]
  nlinarith

/-- **Rank-2 Letter Černý Theorem (`n ≥ 3`)**: every synchronizing DFA on `n ≥ 3` states
possessing a letter of rank `≤ 2` satisfies Černý's bound `w.length ≤ (n - 1) ^ 2`. -/
theorem rank_le_two_cerny_ge_three [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hn : 3 ≤ Fintype.card Q)
    (a : α) (hr : (A.image Finset.univ [a]).card ≤ 2) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ := rank_le_two_bound A hSync a hr
  refine ⟨w, hw, le_trans hlen ?_⟩
  zify [show 1 ≤ Fintype.card Q by omega]
  nlinarith

end SmallRank

end Cerny
