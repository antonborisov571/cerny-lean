import Cerny.Defs
import Cerny.SmallCases
import Cerny.Combinatorial
import Mathlib.Algebra.Field.Rat
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Additional Verified Subclasses & Combinatorial Theorems for the Černý Conjecture

This file builds cleanly on `Cerny.Defs`, `Cerny.SmallCases`, and `Cerny.Combinatorial` to prove:

1. **Unconditional Rank-2 and Rank-3 Letter Černý Theorems** (`rank_le_two_cerny`,
   `rank_le_three_cerny`): every synchronizing DFA on `n ≥ 1` states possessing a letter of
   rank `≤ 2` or `≤ 3` satisfies Černý's conjecture `w.length ≤ (n - 1) ^ 2` for ALL `n ≥ 1`.

2. **Monotonic Automata Theorem (Ananichev–Volkov 2004 / Eppstein 1990)**
   (`DFA.IsMonotonic`, `monotonic_reset_bound`, `monotonic_cerny`): every synchronizing monotonic
   DFA on `Fin n` (every letter preserves `≤`) admits a synchronizing word of length at most
   `n - 1` (hence `≤ (n - 1) ^ 2`).

3. **Szykuła's Avoiding-Subset Lemma & Universal State Avoidance (Szykuła 2018)**
   (`szykula_avoiding_lemma`, `exists_avoiding_word_quadratic`, `exists_avoiding_word_ge_three`):
   for `∅ ⊂ T ⊆ S` with `T ≠ univ`, if some word avoids `T` from `S`, then a word of length
   `≤ n - |T|` either avoids `T` or strictly compresses `S`; consequently every strongly
   connected synchronizing DFA on `n ≥ 2` states avoids any state `q` in length at most
   `n^2 - 3n + 4` (for `n ≥ 3`, and `n^2 + 4 - 3n` for all `n ≥ 2`).
-/

namespace Cerny

universe u v

/-! ## Part 1: Unconditional Rank-2 and Rank-3 Letter Černý Theorems (`∀ n ≥ 1`) -/

section UnconditionalSmallRank

/-- Unconditional Černý Conjecture for all synchronizing DFAs (`n ≥ 1`) possessing a letter
of rank at most `2`. -/
theorem rank_le_two_cerny {Q : Type u} [Fintype Q] [Nonempty Q] [DecidableEq Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (hRank : ∃ a : α, (A.image Finset.univ [a]).card ≤ 2) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  by_cases hle : Fintype.card Q ≤ 4
  · exact cerny_card_le_four A hle hSync
  · rcases hRank with ⟨a, ha⟩
    exact rank_le_two_cerny_ge_three A hSync (by omega) a ha

/-- Unconditional Černý Conjecture for all synchronizing DFAs (`n ≥ 1`) possessing a letter
of rank at most `3`. -/
theorem rank_le_three_cerny {Q : Type u} [Fintype Q] [Nonempty Q] [DecidableEq Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (hRank : ∃ a : α, (A.image Finset.univ [a]).card ≤ 3) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  by_cases hle : Fintype.card Q ≤ 4
  · exact cerny_card_le_four A hle hSync
  · rcases hRank with ⟨a, ha⟩
    exact rank_le_three_cerny_ge_five A hSync (by omega) a ha

end UnconditionalSmallRank

/-! ## Part 2: Monotonic Automata Theorem (`rt(A) ≤ n - 1`) -/

section Monotonic

/-- A DFA on a preordered state set is monotonic if every letter preserves `≤`. -/
def DFA.IsMonotonic {Q : Type u} [Preorder Q] {α : Type v} (A : DFA Q α) : Prop :=
  ∀ (a : α) (p q : Q), p ≤ q → A.step p a ≤ A.step q a

theorem DFA.IsMonotonic.eval_mono {Q : Type u} [Preorder Q] {α : Type v} {A : DFA Q α}
    (hMono : A.IsMonotonic) (w : List α) {p q : Q} (hpq : p ≤ q) :
    A.eval p w ≤ A.eval q w := by
  induction w generalizing p q with
  | nil => simpa using hpq
  | cons a w ih => exact ih (hMono a p q hpq)

/-- **Monotonic Automata Theorem**: every synchronizing monotonic DFA on `Fin n` admits a
synchronizing word of length at most `n - 1`. -/
theorem monotonic_reset_bound {n : ℕ} {α : Type v} (A : DFA (Fin n) α)
    (hMono : A.IsMonotonic) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ n - 1 := by
  classical
  have hn : 1 ≤ n := by
    obtain ⟨q⟩ := hSync.nonempty
    exact Nat.pos_of_ne_zero (by intro h0; subst h0; exact Fin.elim0 q)
  let M : Finset (Fin n) := Finset.univ.filter (fun q => ∃ w : List α, ∀ p : Fin n, A.eval p w = q)
  have hM_ne : M.Nonempty := by
    rcases hSync with ⟨w, q₀, hq₀⟩
    exact ⟨q₀, Finset.mem_filter.mpr ⟨Finset.mem_univ q₀, ⟨w, hq₀⟩⟩⟩
  let qmin : Fin n := M.min' hM_ne
  have hqmin_mem : qmin ∈ M := Finset.min'_mem M hM_ne
  have hqmin_le : ∀ q ∈ M, qmin ≤ q := fun q hq => Finset.min'_le M q hq
  obtain ⟨w₀, hw₀⟩ := (Finset.mem_filter.mp hqmin_mem).2
  -- Closed upset U = {q | qmin ≤ q}
  have hU_step : ∀ (a : α) (q : Fin n), qmin ≤ q → qmin ≤ A.step q a := by
    intro a q hq
    have hstep_mem : A.step qmin a ∈ M := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨w₀ ++ [a], fun p => ?_⟩⟩
      rw [DFA.eval_append, hw₀ p, DFA.eval_singleton]
    exact le_trans (hqmin_le _ hstep_mem) (hMono a qmin q hq)
  have hU_eval : ∀ (w : List α) (q : Fin n), qmin ≤ q → qmin ≤ A.eval q w := by
    intro w
    induction w with
    | nil => intro q hq; simpa using hq
    | cons a w ih => intro q hq; exact ih (A.step q a) (hU_step a q hq)
  -- Step 1: shortest word u₁ taking 0 into U (length ≤ qmin.val)
  let z0 : Fin n := ⟨0, by omega⟩
  have hex₁ : ∃ k : ℕ, ∃ u : List α, u.length = k ∧ qmin ≤ A.eval z0 u :=
    ⟨w₀.length, w₀, rfl, by rw [hw₀ z0]⟩
  obtain ⟨u₁, hu₁_len, hu₁_mem⟩ := Nat.find_spec hex₁
  have hu₁_min : ∀ u : List α, qmin ≤ A.eval z0 u → u₁.length ≤ u.length := by
    intro u hu
    rw [hu₁_len]
    exact Nat.find_min' hex₁ ⟨u, rfl, hu⟩
  have hu₁_bound : u₁.length ≤ qmin.val := by
    let f : Fin u₁.length → Fin qmin.val := fun i =>
      ⟨(A.eval z0 (u₁.take i.val)).val, by
        by_contra hge
        have hle : qmin ≤ A.eval z0 (u₁.take i.val) := by
          change qmin.val ≤ (A.eval z0 (u₁.take i.val)).val
          omega
        have hmin := hu₁_min (u₁.take i.val) hle
        rw [List.length_take] at hmin
        omega⟩
    have hf_inj : Function.Injective f := by
      intro i j hij
      by_contra hne
      have hcut : ∀ a b : Fin u₁.length, a.val < b.val → f a ≠ f b := by
        intro a b hab hfab
        have hval := congrArg Fin.val hfab
        dsimp [f] at hval
        have hev : A.eval z0 (u₁.take a.val) = A.eval z0 (u₁.take b.val) := Fin.ext hval
        let u' := u₁.take a.val ++ u₁.drop b.val
        have hu'_ev : A.eval z0 u' = A.eval z0 u₁ := by
          dsimp [u']
          rw [DFA.eval_append, hev, ← DFA.eval_append, List.take_append_drop]
        have hmin := hu₁_min u' (by rw [hu'_ev]; exact hu₁_mem)
        simp only [u', List.length_append, List.length_take, List.length_drop] at hmin
        omega
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · exact hcut i j hlt hij
      · exact hcut j i hgt hij.symm
    have hcard := Fintype.card_le_of_injective f hf_inj
    simpa using hcard
  -- Step 2: shortest word u₂ taking x = (n - 1) · u₁ to qmin (length ≤ n - 1 - qmin.val)
  let top : Fin n := ⟨n - 1, by omega⟩
  let x : Fin n := A.eval top u₁
  have hx_ge : qmin ≤ x := le_trans hu₁_mem (hMono.eval_mono u₁ (show z0 ≤ top by
    change (0 : ℕ) ≤ n - 1; omega))
  have hex₂ : ∃ k : ℕ, ∃ u : List α, u.length = k ∧ A.eval x u = qmin :=
    ⟨w₀.length, w₀, rfl, hw₀ x⟩
  obtain ⟨u₂, hu₂_len, hu₂_eq⟩ := Nat.find_spec hex₂
  have hu₂_min : ∀ u : List α, A.eval x u = qmin → u₂.length ≤ u.length := by
    intro u hu
    rw [hu₂_len]
    exact Nat.find_min' hex₂ ⟨u, rfl, hu⟩
  have hu₂_bound : u₂.length ≤ n - 1 - qmin.val := by
    let g : Fin u₂.length → Fin (n - 1 - qmin.val) := fun i =>
      ⟨(A.eval x (u₂.take i.val)).val - (qmin.val + 1), by
        have hge : qmin ≤ A.eval x (u₂.take i.val) := hU_eval (u₂.take i.val) x hx_ge
        have hne : A.eval x (u₂.take i.val) ≠ qmin := by
          intro heq
          have hmin := hu₂_min (u₂.take i.val) heq
          rw [List.length_take] at hmin
          omega
        have hlt_top := (A.eval x (u₂.take i.val)).isLt
        have hval_ne : (A.eval x (u₂.take i.val)).val ≠ qmin.val := fun h => hne (Fin.ext h)
        have hval_ge : qmin.val ≤ (A.eval x (u₂.take i.val)).val := hge
        omega⟩
    have hg_inj : Function.Injective g := by
      intro i j hij
      by_contra hne
      have hcut : ∀ a b : Fin u₂.length, a.val < b.val → g a ≠ g b := by
        intro a b hab hgab
        have hge_a : qmin.val ≤ (A.eval x (u₂.take a.val)).val := hU_eval _ x hx_ge
        have hge_b : qmin.val ≤ (A.eval x (u₂.take b.val)).val := hU_eval _ x hx_ge
        have hne_a : (A.eval x (u₂.take a.val)).val ≠ qmin.val := fun h => by
          have hmin := hu₂_min (u₂.take a.val) (Fin.ext h)
          rw [List.length_take] at hmin
          omega
        have hne_b : (A.eval x (u₂.take b.val)).val ≠ qmin.val := fun h => by
          have hmin := hu₂_min (u₂.take b.val) (Fin.ext h)
          rw [List.length_take] at hmin
          omega
        have hsub_eq := congrArg Fin.val hgab
        dsimp [g] at hsub_eq
        have hev : A.eval x (u₂.take a.val) = A.eval x (u₂.take b.val) := by
          ext
          omega
        let u' := u₂.take a.val ++ u₂.drop b.val
        have hu'_ev : A.eval x u' = qmin := by
          dsimp [u']
          rw [DFA.eval_append, hev, ← DFA.eval_append, List.take_append_drop]
          exact hu₂_eq
        have hmin := hu₂_min u' hu'_ev
        simp only [u', List.length_append, List.length_take, List.length_drop] at hmin
        omega
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · exact hcut i j hlt hij
      · exact hcut j i hgt hij.symm
    have hcard := Fintype.card_le_of_injective g hg_inj
    simpa using hcard
  -- Step 3: combine u₁ ++ u₂
  refine ⟨u₁ ++ u₂, ⟨qmin, fun q => ?_⟩, ?_⟩
  · have hlower : qmin ≤ A.eval q (u₁ ++ u₂) := by
      rw [DFA.eval_append]
      apply hU_eval u₂
      exact le_trans hu₁_mem (hMono.eval_mono u₁ (show z0 ≤ q by change 0 ≤ q.val; omega))
    have hupper : A.eval q (u₁ ++ u₂) ≤ qmin := by
      rw [← hu₂_eq, ← DFA.eval_append]
      exact hMono.eval_mono (u₁ ++ u₂) (show q ≤ top by change q.val ≤ n - 1; have := q.isLt; omega)
    exact le_antisymm hupper hlower
  · rw [List.length_append]
    have hqlt := qmin.isLt
    omega

/-- Černý's Conjecture for all synchronizing monotonic DFAs on `Fin n`. -/
theorem monotonic_cerny {n : ℕ} {α : Type v} (A : DFA (Fin n) α)
    (hMono : A.IsMonotonic) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card (Fin n) - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ := monotonic_reset_bound A hMono hSync
  refine ⟨w, hw, le_trans hlen ?_⟩
  rw [Fintype.card_fin]
  nlinarith

end Monotonic

/-! ## Part 3: Szykuła's Avoiding-Subset Lemma & Universal State Avoidance -/

section Avoiding

variable {Q : Type u} {α : Type v}

private def avoidPush [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) :
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

private theorem avoidPush_nil [Fintype Q] [DecidableEq Q] (A : DFA Q α) (x : Q → ℚ) :
    avoidPush A [] x = x := by
  ext q
  simp only [avoidPush, LinearMap.coe_mk, AddHom.coe_mk, DFA.eval_nil]
  rw [Finset.sum_eq_single q]
  · simp
  · intro p _ hp; simp [hp]
  · intro h; exact absurd (Finset.mem_univ q) h

private theorem avoidPush_append [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w₁ w₂ : List α)
    (x : Q → ℚ) :
    avoidPush A (w₁ ++ w₂) x = avoidPush A w₂ (avoidPush A w₁ x) := by
  ext q
  simp only [avoidPush, LinearMap.coe_mk, AddHom.coe_mk]
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

private theorem avoidPush_sum_all [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α)
    (x : Q → ℚ) :
    (∑ q : Q, avoidPush A w x q) = ∑ p : Q, x p := by
  simp only [avoidPush, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Finset.sum_ite_eq]

private def avoidInd [DecidableEq Q] (S : Finset Q) : Q → ℚ :=
  fun q => if q ∈ S then 1 else 0

private theorem avoidPush_ind_apply [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q)
    (w : List α) (t : Q) :
    avoidPush A w (avoidInd S) t = ((S.filter (fun p => A.eval p w = t)).card : ℚ) := by
  simp only [avoidPush, LinearMap.coe_mk, AddHom.coe_mk, avoidInd]
  trans (∑ p : Q, if p ∈ S ∧ A.eval p w = t then (1 : ℚ) else 0)
  · refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h1 : A.eval p w = t <;> by_cases h2 : p ∈ S <;> simp [h1, h2]
  · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    apply congrArg Nat.cast
    apply congrArg Finset.card
    ext p
    simp

/-- **Szykuła's Avoiding-Subset Lemma (2018, Lemma 2)**:
If `∅ ⊂ T ⊆ S` with `T ≠ univ`, and some word `u` avoids `T` from `S` (`¬ T ⊆ S · u`),
then there exists a word `w` of length `≤ |Q| - |T|` that either avoids `T` from `S`
or strictly compresses `S` (`|S · w| < |S|`). -/
theorem szykula_avoiding_lemma [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (S T : Finset Q) (hTne : T.Nonempty) (hTS : T ⊆ S) (hTun : T ≠ Finset.univ)
    (hAvoid : ∃ u : List α, ¬ (T ⊆ A.image S u)) :
    ∃ w : List α, w.length ≤ Fintype.card Q - T.card ∧
      (¬ (T ⊆ A.image S w) ∨ (A.image S w).card < S.card) := by
  classical
  have hSpos : 1 ≤ S.card := le_trans (Finset.card_pos.mpr hTne) (Finset.card_le_card hTS)
  have hS_ne0 : (S.card : ℚ) ≠ 0 := by exact_mod_cast (show S.card ≠ 0 by omega)
  have hT_lt : T.card < Fintype.card Q := by
    have hssub : T ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hTun⟩
    simpa [Finset.card_univ] using Finset.card_lt_card hssub
  obtain ⟨q₀, _, hq₀_notT⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T, hTun⟩)
  -- Linear map Φ : (Q → ℚ) →ₗ[ℚ] ({t // t ∈ T} → ℚ), (Φ x) t = |S| * x t - ∑ p, x p
  let Φ : (Q → ℚ) →ₗ[ℚ] ({t // t ∈ T} → ℚ) :=
    { toFun := fun x t => (S.card : ℚ) * x t.1 - ∑ p : Q, x p
      map_add' := fun x₁ x₂ => by
        ext t
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        ext t
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
        ring }
  -- Surjectivity of Φ via basis vectors (1/|S|)(e_t - e_{q₀})
  have hΦ_surj : Function.Surjective Φ := by
    intro b
    have hbasis : ∀ t : {t // t ∈ T}, ∃ v : Q → ℚ, Φ v = Pi.single t 1 := by
      intro t
      let v : Q → ℚ := fun q =>
        (1 / (S.card : ℚ)) * ((if q = t.1 then (1 : ℚ) else 0) - (if q = q₀ then (1 : ℚ) else 0))
      refine ⟨v, ?_⟩
      ext t'
      have hsum_v : (∑ p : Q, v p) = 0 := by
        simp only [v, ← Finset.mul_sum, Finset.sum_sub_distrib]
        simp
      have ht'_ne_q₀ : t'.1 ≠ q₀ := fun h => hq₀_notT (h ▸ t'.2)
      change (S.card : ℚ) * v t'.1 - ∑ p : Q, v p = (Pi.single t (1 : ℚ) : {t // t ∈ T} → ℚ) t'
      rw [hsum_v, sub_zero]
      dsimp only [v]
      simp only [ht'_ne_q₀, ↓reduceIte, sub_zero]
      by_cases htt : t' = t
      · subst htt
        simp [hS_ne0]
      · have hval_ne : t'.1 ≠ t.1 := fun h => htt (Subtype.ext h)
        simp [hval_ne, htt]
    choose basis hbasis using hbasis
    refine ⟨∑ t : {t // t ∈ T}, b t • basis t, ?_⟩
    rw [map_sum]
    ext t'
    simp only [map_smul, hbasis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single t']
    · simp
    · intro t _ htt
      simp [Pi.single_eq_of_ne (Ne.symm htt)]
    · intro h; exact absurd (Finset.mem_univ t') h
  let H : Submodule ℚ (Q → ℚ) := LinearMap.ker Φ
  have hdimH : Module.finrank ℚ H = Fintype.card Q - T.card := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    have hrange : LinearMap.range Φ = ⊤ := LinearMap.range_eq_top.mpr hΦ_surj
    rw [hrange, finrank_top, Module.finrank_pi, Module.finrank_pi, Fintype.card_coe] at hrn
    change T.card + Module.finrank ℚ H = Fintype.card Q at hrn
    omega
  -- Escaping H certifies either avoiding T or compressing S
  have hnotH_cert : ∀ w : List α, avoidPush A w (avoidInd S) ∉ H →
      ¬ (T ⊆ A.image S w) ∨ (A.image S w).card < S.card := by
    intro w hnotH
    have hne0 : Φ (avoidPush A w (avoidInd S)) ≠ 0 := by
      simpa [H, LinearMap.mem_ker] using hnotH
    have hex_t : ∃ t : {t // t ∈ T}, Φ (avoidPush A w (avoidInd S)) t ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne0 (funext hall)
    obtain ⟨⟨t, ht⟩, ht_ne0⟩ := hex_t
    have hval : Φ (avoidPush A w (avoidInd S)) ⟨t, ht⟩ =
        (S.card : ℚ) * ((S.filter (fun p => A.eval p w = t)).card : ℚ) - (S.card : ℚ) := by
      change (S.card : ℚ) * avoidPush A w (avoidInd S) t - ∑ p : Q, avoidPush A w (avoidInd S) p = _
      rw [avoidPush_ind_apply, avoidPush_sum_all]
      simp [avoidInd]
    rw [hval] at ht_ne0
    let m_t := (S.filter (fun p => A.eval p w = t)).card
    have hmt_ne1 : m_t ≠ 1 := by
      intro h1
      apply ht_ne0
      change (S.card : ℚ) * (m_t : ℚ) - (S.card : ℚ) = 0
      rw [h1]
      ring
    by_cases hmt0 : m_t = 0
    · left
      intro hsub
      have ht_mem : t ∈ A.image S w := hsub ht
      rw [DFA.mem_image] at ht_mem
      rcases ht_mem with ⟨p, hpS, hp_ev⟩
      have hpos : 0 < m_t := Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hpS, hp_ev⟩⟩
      omega
    · right
      have h1lt : 1 < (S.filter (fun p => A.eval p w = t)).card := by omega
      obtain ⟨p₁, hp₁, p₂, hp₂, hp12⟩ := Finset.one_lt_card.mp h1lt
      rw [Finset.mem_filter] at hp₁ hp₂
      exact card_image_lt_of_merge A w hp₁.1 hp₂.1 hp12 (hp₁.2.trans hp₂.2.symm)
  -- Check w = []
  by_cases h0 : avoidInd S ∉ H
  · exact ⟨[], by simp, hnotH_cert [] (by rw [avoidPush_nil]; exact h0)⟩
  push Not at h0
  -- Witness u escapes H
  obtain ⟨u, hu_not⟩ := hAvoid
  have hu_notH : avoidPush A u (avoidInd S) ∉ H := by
    intro huH
    have h0' : Φ (avoidPush A u (avoidInd S)) = 0 := LinearMap.mem_ker.mp huH
    have hex_t : ∃ t ∈ T, t ∉ A.image S u := by
      by_contra hall
      push Not at hall
      exact hu_not hall
    obtain ⟨t, htT, htNot⟩ := hex_t
    have hht := congrFun h0' ⟨t, htT⟩
    change (S.card : ℚ) * avoidPush A u (avoidInd S) t - ∑ p : Q, avoidPush A u (avoidInd S) p = 0 at hht
    rw [avoidPush_ind_apply, avoidPush_sum_all] at hht
    have hemp : S.filter (fun p => A.eval p u = t) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hpS hpev
      exact htNot (by rw [DFA.mem_image]; exact ⟨p, hpS, hpev⟩)
    rw [hemp, Finset.card_empty] at hht
    simp only [avoidInd, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, add_zero,
      Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_zero, mul_zero, zero_sub,
      neg_eq_zero] at hht
    exact hS_ne0 hht
  -- Ascending chain V d = span {avoidPush A w (avoidInd S) | w.length ≤ d}
  let V : ℕ → Submodule ℚ (Q → ℚ) := fun d =>
    Submodule.span ℚ { v : Q → ℚ | ∃ w : List α, w.length ≤ d ∧ v = avoidPush A w (avoidInd S) }
  have hV_mono : ∀ {i j}, i ≤ j → V i ≤ V j := by
    intro i j hij
    apply Submodule.span_mono
    rintro v ⟨w, hwlen, rfl⟩
    exact ⟨w, le_trans hwlen hij, rfl⟩
  have hex_esc : ∃ d : ℕ, ¬ (V d ≤ H) :=
    ⟨u.length, fun hle => hu_notH (hle (Submodule.subset_span ⟨u, le_rfl, rfl⟩))⟩
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
    rw [hnil, avoidPush_nil]
    exact h0
  have hV_strict : ∀ j < d₀, V j < V (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hV_mono (by omega)) fun heq => ?_
    have hclosed : ∀ a : α, ∀ v ∈ V j, avoidPush A [a] v ∈ V j := by
      intro a v hv
      have hmap : Submodule.map (avoidPush A [a]) (V j) ≤ V (j + 1) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨w, hwlen, rfl⟩
        rw [← avoidPush_append]
        exact Submodule.subset_span ⟨w ++ [a], by simp; omega, rfl⟩
      rw [← heq] at hmap
      exact hmap ⟨v, hv, rfl⟩
    have hall_words : ∀ w : List α, avoidPush A w (avoidInd S) ∈ V j := by
      intro w
      induction w using List.reverseRecOn with
      | nil =>
        rw [avoidPush_nil]
        exact Submodule.subset_span ⟨[], by simp, (avoidPush_nil A _).symm⟩
      | append_singleton w a ih =>
        rw [avoidPush_append]
        exact hclosed a _ ih
    exact hu_notH (hd₀_min j hj (hall_words u))
  have hdim_V0 : 1 ≤ Module.finrank ℚ (V 0) := by
    have hmem0 : avoidInd S ∈ V 0 := Submodule.subset_span ⟨[], le_rfl, (avoidPush_nil A _).symm⟩
    have hne0 : avoidInd S ≠ 0 := by
      obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      intro hzero
      have := congrFun hzero s
      simp [avoidInd, hs] at this
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
  have hd₀_le : d₀ ≤ Fintype.card Q - T.card := by
    have h1 := hdim_Vj (d₀ - 1) (by omega)
    have h2 : Module.finrank ℚ (V (d₀ - 1)) ≤ Module.finrank ℚ H :=
      Submodule.finrank_mono (hd₀_min (d₀ - 1) (by omega))
    omega
  have hex_gen : ∃ v ∈ { v : Q → ℚ | ∃ w : List α, w.length ≤ d₀ ∧ v = avoidPush A w (avoidInd S) },
      v ∉ H := by
    by_contra hall
    push Not at hall
    exact hd₀_not (Submodule.span_le.mpr hall)
  rcases hex_gen with ⟨_, ⟨w, hwlen, rfl⟩, hw_notH⟩
  exact ⟨w, le_trans hwlen hd₀_le, hnotH_cert w hw_notH⟩

private theorem avoid_from_subset_ind [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSC : A.IsStronglyConnected) (hSync : A.IsSynchronizing)
    (hn : 2 ≤ Fintype.card Q) (q : Q) :
    ∀ r : ℕ, 1 ≤ r → ∀ S : Finset Q, S.card = r →
      ∃ w : List α, q ∉ A.image S w ∧ w.length ≤ (r - 1) * (Fintype.card Q - 1) + 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr1 S hS
    by_cases hqS : q ∉ S
    · exact ⟨[], by simpa using hqS, by simp⟩
    push Not at hqS
    have hex_ne : ∃ p : Q, p ≠ q := by
      have hlt : 1 < Fintype.card Q := by omega
      obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card hlt
      by_cases hx : x = q
      · subst hx; exact ⟨y, hxy.symm⟩
      · exact ⟨x, hx⟩
    obtain ⟨p₀, hp₀_ne⟩ := hex_ne
    by_cases hr_eq1 : r = 1
    · subst hr_eq1
      have hSq : S = {q} := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          have hcard1 : S.card = 1 := hS
          rw [Finset.card_eq_one] at hcard1
          rcases hcard1 with ⟨z, hz⟩
          rw [hz, Finset.mem_singleton] at hqS hx
          rw [hx, ← hqS, Finset.mem_singleton]
        · rw [hS]; simp
      have hex_letter : ∃ c : α, A.step q c ≠ q := by
        by_contra hall
        push Not at hall
        have hfix : ∀ v : List α, A.eval q v = q := by
          intro v
          induction v with
          | nil => rfl
          | cons c v ihv => rw [DFA.eval_cons, hall c, ihv]
        obtain ⟨v, hv⟩ := hSC q p₀
        exact hp₀_ne (hv.symm.trans (hfix v))
      obtain ⟨c, hc⟩ := hex_letter
      refine ⟨[c], ?_, by simp⟩
      rw [hSq, DFA.image_singleton, DFA.eval_singleton, Finset.mem_singleton]
      exact Ne.symm hc
    · have hTun : ({q} : Finset Q) ≠ Finset.univ := by
        intro heq
        have hp_mem : p₀ ∈ ({q} : Finset Q) := by rw [heq]; exact Finset.mem_univ p₀
        rw [Finset.mem_singleton] at hp_mem
        exact hp₀_ne hp_mem
      have hAvoid : ∃ u : List α, ¬ (({q} : Finset Q) ⊆ A.image S u) := by
        rcases hSync with ⟨w₀, q₀, hq₀⟩
        obtain ⟨v, hv⟩ := hSC q₀ p₀
        refine ⟨w₀ ++ v, fun hsub => ?_⟩
        have hq_mem : q ∈ A.image S (w₀ ++ v) := hsub (by simp)
        rw [DFA.mem_image] at hq_mem
        rcases hq_mem with ⟨s, _, hs⟩
        rw [DFA.eval_append, hq₀ s, hv] at hs
        exact hp₀_ne hs
      obtain ⟨v, hvlen, hvres⟩ := szykula_avoiding_lemma A S {q} ⟨q, by simp⟩
        (Finset.singleton_subset_iff.mpr hqS) hTun hAvoid
      rw [Finset.card_singleton] at hvlen
      rcases hvres with hnot_sub | hcomp
      · refine ⟨v, fun hq_in => hnot_sub (Finset.singleton_subset_iff.mpr hq_in), ?_⟩
        have hr2 : 2 ≤ r := by omega
        have hmul : 1 * (Fintype.card Q - 1) ≤ (r - 1) * (Fintype.card Q - 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      · let S' := A.image S v
        have hS'_lt : S'.card < r := by rw [← hS]; exact hcomp
        have hS'_pos : 1 ≤ S'.card := Finset.card_pos.mpr
          ⟨A.eval q v, by rw [DFA.mem_image]; exact ⟨q, hqS, rfl⟩⟩
        obtain ⟨u', hu'_not, hu'_len⟩ := ih S'.card hS'_lt hS'_pos S' rfl
        refine ⟨v ++ u', ?_, ?_⟩
        · rw [DFA.image_append]; exact hu'_not
        · rw [List.length_append]
          have hmul : (S'.card - 1) * (Fintype.card Q - 1) ≤ (r - 2) * (Fintype.card Q - 1) :=
            Nat.mul_le_mul_right _ (by omega)
          have hadd : (Fintype.card Q - 1) + (r - 2) * (Fintype.card Q - 1) =
              (r - 1) * (Fintype.card Q - 1) := by
            have hr_eq : r - 1 = (r - 2) + 1 := by omega
            rw [hr_eq, add_mul, one_mul, add_comm]
          omega

/-- **Universal Quadratic State-Avoidance Bound** (division/subtraction-free form for all `n ≥ 2`):
in every strongly connected synchronizing DFA on `n ≥ 2` states, every state `q` is avoided
by some word `w` with `w.length + 3 * n ≤ n ^ 2 + 4`. -/
theorem exists_avoiding_word_quadratic [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSC : A.IsStronglyConnected) (hSync : A.IsSynchronizing)
    (hn : 2 ≤ Fintype.card Q) (q : Q) :
    ∃ w : List α, q ∉ A.image Finset.univ w ∧
      w.length + 3 * Fintype.card Q ≤ (Fintype.card Q) ^ 2 + 4 := by
  obtain ⟨a, hni⟩ := exists_non_injective_letter A hSync hn
  unfold Function.Injective at hni
  push Not at hni
  rcases hni with ⟨x, y, hxy_eq, hxy_ne⟩
  have hlt : (A.image Finset.univ [a]).card < (Finset.univ : Finset Q).card :=
    card_image_lt_of_merge A [a] (Finset.mem_univ x) (Finset.mem_univ y) hxy_ne hxy_eq
  rw [Finset.card_univ] at hlt
  let S₁ := A.image Finset.univ [a]
  have hS₁_lt : S₁.card < Fintype.card Q := hlt
  have hS₁_pos : 1 ≤ S₁.card := Finset.card_pos.mpr
    ⟨A.step x a, by rw [DFA.mem_image]; exact ⟨x, Finset.mem_univ x, rfl⟩⟩
  obtain ⟨v, hv_not, hv_len⟩ := avoid_from_subset_ind A hSC hSync hn q S₁.card hS₁_pos S₁ rfl
  refine ⟨a :: v, ?_, ?_⟩
  · rw [DFA.image_cons]; exact hv_not
  · simp only [List.length_cons]
    have hmul : (S₁.card - 1) * (Fintype.card Q - 1) ≤ (Fintype.card Q - 2) * (Fintype.card Q - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have hid : (Fintype.card Q - 2) * (Fintype.card Q - 1) + 2 + 3 * Fintype.card Q =
        (Fintype.card Q) ^ 2 + 4 := by
      zify [hn, show 1 ≤ Fintype.card Q by omega]
      ring
    omega

/-- **Universal Quadratic State-Avoidance Bound (`n ≥ 3`)**:
in every strongly connected synchronizing DFA on `n ≥ 3` states, every state `q` is avoided
by some word `w` of length at most `n ^ 2 - 3 * n + 4`. -/
theorem exists_avoiding_word_ge_three [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSC : A.IsStronglyConnected) (hSync : A.IsSynchronizing)
    (hn : 3 ≤ Fintype.card Q) (q : Q) :
    ∃ w : List α, q ∉ A.image Finset.univ w ∧
      w.length ≤ (Fintype.card Q) ^ 2 - 3 * Fintype.card Q + 4 := by
  obtain ⟨w, hnot, hlen⟩ := exists_avoiding_word_quadratic A hSC hSync (by omega) q
  refine ⟨w, hnot, ?_⟩
  have h3n : 3 * Fintype.card Q ≤ (Fintype.card Q) ^ 2 := by nlinarith
  omega

end Avoiding

end Cerny
