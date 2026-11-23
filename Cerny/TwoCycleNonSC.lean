import Cerny.Defs
import Cerny.Circular
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

/-!
# Exact Černý Bound `(n - 1)^2` for All Non-Strongly-Connected 2-Cycle DFAs (Theorem I)

This file formalizes **Theorem I** (`docs/round4_two_cluster_dichotomy.md` §2.1 & §3.2):
EVERY non-strongly-connected synchronizing `n`-state DFA possessing a 2-cycle permutation
letter `a` (`Q = C₁ ⊔ C₂`, `|C₁| = m₁ ≥ 1`, `|C₂| = m₂ ≥ 1`, arbitrary alphabet `α`) obeys
the **exact Černý Conjecture**:
`w.length ≤ (m₁ - 1)^2 + m₂^2 - m₂ + 1 ≤ (n - 1)^2` (WLOG with `C₁` closed).

## Main Results
* `Cerny.nonSC_twoCycle_closed_cycle`: Any non-strongly-connected DFA with a 2-cycle
  permutation letter `a` has either `C₁` or `C₂` closed under every letter `g : α`.
* `Cerny.closedCycle_collapse_bound`: Pure `ℕ` uniform shift averaging over `Fin m₂` collapses
  `Q` into the closed cycle `C₁` in length `≤ m₂ ^ 2 - m₂ + 1`.
* `Cerny.twoCycle_closed_exact_bound`: Sharp bound `w.length ≤ (m₁ - 1)^2 + m₂^2 - m₂ + 1`
  combining collapse with Dubuc's Circular Theorem (`Cerny.circular_cerny`).
* `Cerny.twoCycle_nonSC_cerny` (**Theorem I**): Exact Černý Conjecture `w.length ≤ (n - 1)^2`
  for ALL non-strongly-connected synchronizing 2-cycle permutation DFAs!
-/

namespace Cerny

universe u v

namespace TwoCycleNonSC

/-- On a finite invariant transitive cycle `C`, iterating `step · a` for `0 ≤ j < |C|`
gives a bijection `Fin C.card ≃ C`, so `∑ j : Fin C.card, 1_{f^[j] c₀ ∈ S} = (S ∩ C).card`. -/
private lemma cycle_count_in_finset {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a : α) (C : Finset Q) (hC_inv : ∀ q ∈ C, A.step q a ∈ C)
    (hC_trans : ∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    {c₀ : Q} (hc₀ : c₀ ∈ C) (S : Finset Q) :
    (∑ j : Fin C.card, if (fun x => A.step x a)^[j.val] c₀ ∈ S then 1 else 0) = (S ∩ C).card := by
  let f : Q → Q := fun x => A.step x a
  have hiter_mem : ∀ k : ℕ, f^[k] c₀ ∈ C := by
    intro k
    induction k with
    | zero => exact hc₀
    | succ k ih => rw [Function.iterate_succ_apply']; exact hC_inv _ ih
  let fC : C → C := fun x => ⟨f x.1, hC_inv x.1 x.2⟩
  have hfC_iter : ∀ (k : ℕ) (x : C), (fC^[k] x).1 = f^[k] x.1 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply, ih]; rfl
  have hfC_surj : Function.Surjective fC := by
    intro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hC_trans (f y) (hC_inv y hy) y hy
    refine ⟨⟨f^[k] y, ?_⟩, Subtype.ext ?_⟩
    · clear hk
      induction k with
      | zero => exact hy
      | succ k ih => rw [Function.iterate_succ_apply']; exact hC_inv _ ih
    · change f (f^[k] y) = y
      rw [← Function.iterate_succ_apply' f k y, Function.iterate_succ_apply]
      exact hk
  have hfC_inj : Function.Injective fC :=
    (Fintype.bijective_iff_surjective_and_card fC).mpr ⟨hfC_surj, rfl⟩ |>.1
  have hmin : ∀ k : ℕ, 0 < k → k < C.card → f^[k] c₀ ≠ c₀ := by
    intro k hk0 hkc hfix
    have hmul : ∀ t : ℕ, f^[k * t] c₀ = c₀ := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hfix]
    have hmod : ∀ t : ℕ, f^[t] c₀ = f^[t % k] c₀ := by
      intro t
      have hdiv : t = t % k + k * (t / k) := by have := Nat.div_add_mod t k; omega
      conv_lhs => rw [hdiv, Function.iterate_add_apply, hmul]
    have hsub : C ⊆ (Finset.range k).image (fun j => f^[j] c₀) := by
      intro y hy
      obtain ⟨t, rfl⟩ := hC_trans c₀ hc₀ y hy
      rw [Finset.mem_image]
      exact ⟨t % k, Finset.mem_range.mpr (Nat.mod_lt t hk0), (hmod t).symm⟩
    have hle := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_range] at hle
    omega
  let g : Fin C.card → C := fun j => ⟨f^[j.val] c₀, hiter_mem j.val⟩
  have hg_inj : Function.Injective g := by
    intro i j hij
    have hval : f^[i.val] c₀ = f^[j.val] c₀ := congrArg Subtype.val hij
    by_contra hne
    have hstep : ∀ x y : ℕ, x < y → y < C.card → f^[x] c₀ = f^[y] c₀ → False := by
      intro x y hxy hyc heq
      have hsub : fC^[x] ⟨c₀, hc₀⟩ = fC^[y] ⟨c₀, hc₀⟩ :=
        Subtype.ext (by rw [hfC_iter, hfC_iter]; exact heq)
      have hsplit : y = x + (y - x) := by omega
      rw [hsplit, Function.iterate_add_apply] at hsub
      have hfixC : fC^[y - x] ⟨c₀, hc₀⟩ = ⟨c₀, hc₀⟩ := (hfC_inj.iterate x) hsub.symm
      have hfix : f^[y - x] c₀ = c₀ := by
        have := congrArg Subtype.val hfixC; rwa [hfC_iter] at this
      exact hmin (y - x) (by omega) (by omega) hfix
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hstep i.val j.val hlt j.isLt hval
    · exact hstep j.val i.val hgt i.isLt hval.symm
  have hg_bij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_inj, by simp⟩
  let e : Fin C.card ≃ C := Equiv.ofBijective g hg_bij
  have hsum : (∑ j : Fin C.card, if (e j).1 ∈ S then (1 : ℕ) else 0) =
      ∑ x : C, if x.1 ∈ S then (1 : ℕ) else 0 :=
    Fintype.sum_equiv e (fun j => if (e j).1 ∈ S then 1 else 0)
      (fun x => if x.1 ∈ S then 1 else 0) (fun _ => rfl)
  change (∑ j : Fin C.card, if (e j).1 ∈ S then 1 else 0) = (S ∩ C).card
  rw [hsum, Finset.sum_coe_sort C (fun x => if x ∈ S then (1 : ℕ) else 0),
    ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter]
  tauto

/-- On a finite invariant transitive cycle `C`, `step · a` is bijective on `C`. -/
private lemma cycle_bijective {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a : α) (C : Finset Q) (hC_inv : ∀ q ∈ C, A.step q a ∈ C)
    (hC_trans : ∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) :
    Function.Bijective (fun x : {q : Q // q ∈ C} => (⟨A.step x.1 a, hC_inv x.1 x.2⟩ : {q : Q // q ∈ C})) := by
  let f : Q → Q := fun x => A.step x a
  let fC : {q : Q // q ∈ C} → {q : Q // q ∈ C} := fun x => ⟨f x.1, hC_inv x.1 x.2⟩
  have hsurj : Function.Surjective fC := by
    intro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hC_trans (f y) (hC_inv y hy) y hy
    refine ⟨⟨f^[k] y, ?_⟩, Subtype.ext ?_⟩
    · clear hk
      induction k with
      | zero => exact hy
      | succ k ih => rw [Function.iterate_succ_apply']; exact hC_inv _ ih
    · change f (f^[k] y) = y
      rw [← Function.iterate_succ_apply' f k y, Function.iterate_succ_apply]
      exact hk
  exact (Fintype.bijective_iff_surjective_and_card fC).mpr ⟨hsurj, rfl⟩

end TwoCycleNonSC

/-- **Closed-Cycle Dichotomy for Non-SC 2-Cycle DFAs**:
In any non-strongly-connected DFA with a 2-cycle letter `a` (`Q = C₁ ⊔ C₂`),
either `C₁` or `C₂` is closed under every letter `g : α`. -/
theorem nonSC_twoCycle_closed_cycle {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a : α) (C₁ C₂ : Finset Q)
    (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hNotSC : ¬ A.IsStronglyConnected) :
    (∀ q ∈ C₁, ∀ g : α, A.step q g ∈ C₁) ∨ (∀ q ∈ C₂, ∀ g : α, A.step q g ∈ C₂) := by
  classical
  unfold DFA.IsStronglyConnected at hNotSC
  push Not at hNotSC
  rcases hNotSC with ⟨p₀, q₀, hpq⟩
  let R : Finset Q := Finset.univ.filter (fun x => ∃ w : List α, A.eval p₀ w = x)
  have hp₀R : p₀ ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ p₀, [], rfl⟩
  have hq₀R : q₀ ∉ R := fun h => by
    rcases (Finset.mem_filter.mp h).2 with ⟨w, hw⟩
    exact hpq w hw
  have hR_closed : ∀ x ∈ R, ∀ g : α, A.step x g ∈ R := by
    intro x hx g
    rcases (Finset.mem_filter.mp hx).2 with ⟨w, hw⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w ++ [g], by rw [DFA.eval_append, hw]; rfl⟩
  have hR_iter : ∀ x ∈ R, ∀ k : ℕ, (fun y => A.step y a)^[k] x ∈ R := by
    intro x hx k
    induction k with
    | zero => exact hx
    | succ k ih => rw [Function.iterate_succ_apply']; exact hR_closed _ ih a
  have hC₁_sub : ∀ x ∈ R, x ∈ C₁ → C₁ ⊆ R := by
    intro x hxR hxC₁ y hyC₁
    obtain ⟨k, rfl⟩ := hC₁_trans x hxC₁ y hyC₁
    exact hR_iter x hxR k
  have hC₂_sub : ∀ x ∈ R, x ∈ C₂ → C₂ ⊆ R := by
    intro x hxR hxC₂ y hyC₂
    obtain ⟨k, rfl⟩ := hC₂_trans x hxC₂ y hyC₂
    exact hR_iter x hxR k
  have hnot_both : ¬ (C₁ ⊆ R ∧ C₂ ⊆ R) := by
    rintro ⟨h1, h2⟩
    have huniv : Finset.univ ⊆ R := by rw [← hC_union]; exact Finset.union_subset h1 h2
    exact hq₀R (huniv (Finset.mem_univ q₀))
  have hp₀_mem : p₀ ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ p₀
  rcases Finset.mem_union.mp hp₀_mem with hp1 | hp2
  · left
    have h1 : C₁ ⊆ R := hC₁_sub p₀ hp₀R hp1
    have hR_eq : R = C₁ := by
      apply Finset.Subset.antisymm _ h1
      intro x hxR
      have hx_mem : x ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ x
      rcases Finset.mem_union.mp hx_mem with hx1 | hx2
      · exact hx1
      · exact absurd ⟨h1, hC₂_sub x hxR hx2⟩ hnot_both
    intro q hq g
    rw [← hR_eq] at hq ⊢
    exact hR_closed q hq g
  · right
    have h2 : C₂ ⊆ R := hC₂_sub p₀ hp₀R hp2
    have hR_eq : R = C₂ := by
      apply Finset.Subset.antisymm _ h2
      intro x hxR
      have hx_mem : x ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ x
      rcases Finset.mem_union.mp hx_mem with hx1 | hx2
      · exact absurd ⟨hC₁_sub x hxR hx1, h2⟩ hnot_both
      · exact hx2
    intro q hq g
    rw [← hR_eq] at hq ⊢
    exact hR_closed q hq g

/-- **Closed-Cycle Collapse Bound (`≤ m₂ ^ 2 - m₂ + 1`)**:
When `C₁` is closed under all letters in a synchronizing 2-cycle DFA (`Q = C₁ ⊔ C₂`),
uniform shift averaging over `Fin m₂` produces a word `w_col` of length
`≤ C₂.card ^ 2 - C₂.card + 1` mapping all of `Q` into `C₁`. -/
theorem closedCycle_collapse_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (a : α) (C₁ C₂ : Finset Q)
    (hC₁_ne : C₁.Nonempty) (hC₂_ne : C₂.Nonempty)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₁_closed : ∀ q ∈ C₁, ∀ g : α, A.step q g ∈ C₁) :
    ∃ w_col : List α, (∀ q : Q, A.eval q w_col ∈ C₁) ∧
      w_col.length ≤ C₂.card ^ 2 - C₂.card + 1 := by
  have hC₁_eval : ∀ q ∈ C₁, ∀ w : List α, A.eval q w ∈ C₁ := by
    intro q hq w
    induction w generalizing q with
    | nil => exact hq
    | cons g u ih => exact ih (A.step q g) (hC₁_closed q hq g)
  -- Some letter `b` maps at least one state of `C₂` into `C₁`
  have hex_b : ∃ b : α, 1 ≤ (C₂.filter (fun x => A.step x b ∈ C₁)).card := by
    by_contra hall
    push Not at hall
    have hC₂_closed : ∀ q ∈ C₂, ∀ g : α, A.step q g ∈ C₂ := by
      intro q hq g
      have h0 : (C₂.filter (fun x => A.step x g ∈ C₁)).card = 0 := by have := hall g; omega
      have hnot1 : A.step q g ∉ C₁ := by
        intro h1
        have hmem : q ∈ C₂.filter (fun x => A.step x g ∈ C₁) := Finset.mem_filter.mpr ⟨hq, h1⟩
        have hpos := Finset.card_pos.mpr ⟨q, hmem⟩
        omega
      have huniv : A.step q g ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ _
      exact (Finset.mem_union.mp huniv).resolve_left hnot1
    have hC₂_eval : ∀ q ∈ C₂, ∀ w : List α, A.eval q w ∈ C₂ := by
      intro q hq w
      induction w generalizing q with
      | nil => exact hq
      | cons g u ih => exact ih (A.step q g) (hC₂_closed q hq g)
    obtain ⟨p₁, hp₁⟩ := hC₁_ne
    obtain ⟨p₂, hp₂⟩ := hC₂_ne
    rcases hSync with ⟨w_sync, q₀, hq₀⟩
    have h1 : q₀ ∈ C₁ := hq₀ p₁ ▸ hC₁_eval p₁ hp₁ w_sync
    have h2 : q₀ ∈ C₂ := hq₀ p₂ ▸ hC₂_eval p₂ hp₂ w_sync
    exact Finset.disjoint_left.mp hC_disj h1 h2
  obtain ⟨b, hb_pos⟩ := hex_b
  set m₂ := C₂.card
  have hm₂_pos : 0 < m₂ := Finset.card_pos.mpr hC₂_ne
  set k₂₁ := (C₂.filter (fun x => A.step x b ∈ C₁)).card
  -- Single-step uniform shift averaging over `j : Fin m₂`
  have hstep : ∀ S : Finset Q, C₁ ⊆ S → (S ∩ C₂).card < m₂ →
      ∃ w : List α, w.length ≤ m₂ ∧ C₁ ⊆ A.preimage S w ∧
        (S ∩ C₂).card < (A.preimage S w ∩ C₂).card := by
    intro S hC₁S ht_lt
    set t := (S ∩ C₂).card
    let wj : Fin m₂ → List α := fun j => b :: List.replicate j.val a
    have hsum_eq :
        (∑ j : Fin m₂, (A.preimage S (wj j) ∩ C₂).card) = k₂₁ * m₂ + (m₂ - k₂₁) * t := by
      have hcard_j : ∀ j : Fin m₂,
          (A.preimage S (wj j) ∩ C₂).card =
            ∑ x ∈ C₂, if A.eval x (wj j) ∈ S then 1 else 0 := by
        intro j
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        congr 1
        ext x
        simp only [Finset.mem_inter, DFA.mem_preimage, Finset.mem_filter]
        tauto
      simp_rw [hcard_j]
      rw [Finset.sum_comm]
      have hinner : ∀ x ∈ C₂,
          (∑ j : Fin m₂, if A.eval x (wj j) ∈ S then 1 else 0) =
            if A.step x b ∈ C₁ then m₂ else t := by
        intro x _
        have heval : ∀ j : Fin m₂,
            A.eval x (wj j) = (fun y => A.step y a)^[j.val] (A.step x b) := by
          intro j
          simp only [wj, DFA.eval_cons, DFA.eval_replicate]
        simp_rw [heval]
        by_cases hxb : A.step x b ∈ C₁
        · simp only [hxb, ↓reduceIte]
          have hall_in : ∀ j : Fin m₂, (fun y => A.step y a)^[j.val] (A.step x b) ∈ S := by
            intro j
            apply hC₁S
            rw [← DFA.eval_replicate]
            exact hC₁_eval (A.step x b) hxb (List.replicate j.val a)
          simp only [hall_in, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul, mul_one]
        · simp only [hxb, ↓reduceIte]
          have hxb2 : A.step x b ∈ C₂ := by
            have huniv : A.step x b ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ _
            exact (Finset.mem_union.mp huniv).resolve_left hxb
          exact TwoCycleNonSC.cycle_count_in_finset A a C₂ hC₂_inv hC₂_trans hxb2 S
      rw [Finset.sum_congr rfl hinner, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
        smul_eq_mul, smul_eq_mul]
      have hcompl_card : (C₂.filter (fun x => A.step x b ∉ C₁)).card = m₂ - k₂₁ := by
        have htot : (C₂.filter (fun x => A.step x b ∈ C₁)).card +
            (C₂.filter (fun x => A.step x b ∉ C₁)).card = C₂.card := by
          rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
          congr 1; ext x; simp only [Finset.mem_union, Finset.mem_filter]; tauto
        omega
      rw [hcompl_card]
    have hk₂₁_le : k₂₁ ≤ m₂ := Finset.card_filter_le _ _
    have hsum_gt : m₂ * t < ∑ j : Fin m₂, (A.preimage S (wj j) ∩ C₂).card := by
      rw [hsum_eq]
      zify [hk₂₁_le]
      nlinarith
    have hex_j : ∃ j : Fin m₂, t < (A.preimage S (wj j) ∩ C₂).card := by
      by_contra hall
      push Not at hall
      have hle : ∑ j : Fin m₂, (A.preimage S (wj j) ∩ C₂).card ≤ ∑ _j : Fin m₂, t :=
        Finset.sum_le_sum fun j _ => hall j
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
      omega
    obtain ⟨j, hj⟩ := hex_j
    refine ⟨wj j, ?_, ?_, hj⟩
    · simp only [wj, List.length_cons, List.length_replicate]
      have := j.isLt; omega
    · intro q hq
      rw [DFA.mem_preimage]
      exact hC₁S (hC₁_eval q hq (wj j))
  -- Strong induction on `k := m₂ - (S ∩ C₂).card`
  have hind : ∀ k : ℕ, ∀ S : Finset Q, C₁ ⊆ S → m₂ - (S ∩ C₂).card = k →
      ∃ v : List α, A.preimage S v = Finset.univ ∧ v.length ≤ k * m₂ := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro S hC₁S hk
      have ht_le : (S ∩ C₂).card ≤ m₂ := Finset.card_le_card Finset.inter_subset_right
      by_cases hfull : (S ∩ C₂).card = m₂
      · have hC₂S : C₂ ⊆ S := by
          have heq : S ∩ C₂ = C₂ := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
          intro x hx; rw [← heq] at hx; exact (Finset.mem_inter.mp hx).1
        refine ⟨[], ?_, by simp⟩
        ext q
        simp only [DFA.mem_preimage, DFA.eval_nil, Finset.mem_univ, iff_true]
        have hq : q ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ q
        rcases Finset.mem_union.mp hq with h1 | h2
        · exact hC₁S h1
        · exact hC₂S h2
      · obtain ⟨w, hw_len, hw_C₁, hw_gt⟩ := hstep S hC₁S (by omega)
        set S' := A.preimage S w
        have hS'_le : (S' ∩ C₂).card ≤ m₂ := Finset.card_le_card Finset.inter_subset_right
        have hk'_lt : m₂ - (S' ∩ C₂).card < k := by omega
        obtain ⟨v', hv'_full, hv'_len⟩ := ih (m₂ - (S' ∩ C₂).card) hk'_lt S' hw_C₁ rfl
        refine ⟨v' ++ w, ?_, ?_⟩
        · ext q
          simp only [DFA.mem_preimage, DFA.eval_append, Finset.mem_univ, iff_true]
          have hq' : q ∈ A.preimage S' v' := hv'_full ▸ Finset.mem_univ q
          exact (DFA.mem_preimage A S w _).mp ((DFA.mem_preimage A S' v' q).mp hq')
        · rw [List.length_append]
          have h1 : (m₂ - (S' ∩ C₂).card + 1) * m₂ ≤ k * m₂ := Nat.mul_le_mul_right m₂ (by omega)
          nlinarith
  -- Start from `S₁ = A.preimage C₁ [b]`, which contains `C₁` and `≥ 1` state of `C₂`
  let S₁ := A.preimage C₁ [b]
  have hC₁_S₁ : C₁ ⊆ S₁ := fun q hq => by
    rw [DFA.mem_preimage, DFA.eval_singleton]; exact hC₁_closed q hq b
  have hS₁_ge1 : 1 ≤ (S₁ ∩ C₂).card := by
    have heq : S₁ ∩ C₂ = C₂.filter (fun x => A.step x b ∈ C₁) := by
      ext x
      simp only [S₁, Finset.mem_inter, DFA.mem_preimage, DFA.eval_singleton, Finset.mem_filter]
      tauto
    rw [heq]; exact hb_pos
  obtain ⟨v, hv_full, hv_len⟩ := hind (m₂ - (S₁ ∩ C₂).card) S₁ hC₁_S₁ rfl
  refine ⟨v ++ [b], ?_, ?_⟩
  · intro q
    rw [DFA.eval_append]
    have hq : q ∈ A.preimage S₁ v := hv_full ▸ Finset.mem_univ q
    have hq' : A.eval q v ∈ S₁ := (DFA.mem_preimage A S₁ v q).mp hq
    exact (DFA.mem_preimage A C₁ [b] _).mp hq'
  · rw [List.length_append, List.length_singleton]
    have h1 : (m₂ - (S₁ ∩ C₂).card) * m₂ ≤ (m₂ - 1) * m₂ := Nat.mul_le_mul_right m₂ (by omega)
    have h2 : (m₂ - 1) * m₂ = m₂ ^ 2 - m₂ := by
      zify [show 1 ≤ m₂ by omega, show m₂ ≤ m₂ ^ 2 by nlinarith]
      ring
    omega

/-- **Sharp Closed-Cycle Reset Bound (`≤ (m₁ - 1)^2 + m₂^2 - m₂ + 1`)**:
Combining `closedCycle_collapse_bound` with Dubuc's Circular Theorem (`Cerny.circular_cerny`)
on the closed cycle `C₁`. -/
theorem twoCycle_closed_exact_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (a : α) (C₁ C₂ : Finset Q)
    (hC₁_ne : C₁.Nonempty) (hC₂_ne : C₂.Nonempty)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₁_closed : ∀ q ∈ C₁, ∀ g : α, A.step q g ∈ C₁) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ (C₁.card - 1) ^ 2 + (C₂.card ^ 2 - C₂.card + 1) := by
  obtain ⟨w_col, hw_col_in, hw_col_len⟩ :=
    closedCycle_collapse_bound A hSync a C₁ C₂ hC₁_ne hC₂_ne hC_disj hC_union
      hC₂_inv hC₂_trans hC₁_closed
  -- Restrict `A` to `C₁`, which is a nonempty synchronizing circular DFA
  let Q₁ := {q : Q // q ∈ C₁}
  have : Nonempty Q₁ := let ⟨q, hq⟩ := hC₁_ne; ⟨⟨q, hq⟩⟩
  let A₁ : DFA Q₁ α := ⟨fun x g => ⟨A.step x.1 g, hC₁_closed x.1 x.2 g⟩⟩
  have hA₁_eval : ∀ (x : Q₁) (w : List α), (A₁.eval x w).1 = A.eval x.1 w := by
    intro x w
    induction w generalizing x with
    | nil => rfl
    | cons g u ih => exact ih (A₁.step x g)
  have hA₁_iter : ∀ (k : ℕ) (x : Q₁), ((fun y => A₁.step y a)^[k] x).1 =
      (fun y => A.step y a)^[k] x.1 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply, ih]; rfl
  have hA₁_circ : A₁.IsCircular := by
    refine ⟨a, TwoCycleNonSC.cycle_bijective A a C₁ hC₁_inv hC₁_trans, ?_⟩
    intro x y
    obtain ⟨k, hk⟩ := hC₁_trans x.1 x.2 y.1 y.2
    exact ⟨k, Subtype.ext (by rw [hA₁_iter]; exact hk)⟩
  have hA₁_sync : A₁.IsSynchronizing := by
    rcases hSync with ⟨w_sync, q₀, hq₀⟩
    obtain ⟨p₁, hp₁⟩ := hC₁_ne
    have hq₀C₁ : q₀ ∈ C₁ := by
      have h1 := hA₁_eval ⟨p₁, hp₁⟩ w_sync
      rw [hq₀ p₁] at h1
      exact h1 ▸ (A₁.eval ⟨p₁, hp₁⟩ w_sync).2
    refine ⟨w_sync, ⟨q₀, hq₀C₁⟩, fun x => Subtype.ext ?_⟩
    rw [hA₁_eval, hq₀ x.1]
  obtain ⟨w₁, ⟨q₁, hq₁⟩, hw₁_len⟩ := circular_cerny A₁ hA₁_circ hA₁_sync
  rw [Fintype.card_coe] at hw₁_len
  refine ⟨w_col ++ w₁, ⟨q₁.1, fun q => ?_⟩, ?_⟩
  · rw [DFA.eval_append]
    have h1 := hA₁_eval ⟨A.eval q w_col, hw_col_in q⟩ w₁
    rw [hq₁ ⟨A.eval q w_col, hw_col_in q⟩] at h1
    exact h1.symm
  · rw [List.length_append]
    omega

/-- **Theorem I (EXACT Černý Conjecture `(n - 1)^2` for ALL Non-SC 2-Cycle Permutation DFAs)**:
Every non-strongly-connected synchronizing `n`-state DFA possessing a 2-cycle permutation letter
`a` (`Q = C₁ ⊔ C₂`, `|C₁| ≥ 1`, `|C₂| ≥ 1`) satisfies `∃ w, A.IsSyncWord w ∧ w.length ≤ (n - 1)^2`! -/
theorem twoCycle_nonSC_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (hNotSC : ¬ A.IsStronglyConnected)
    (a : α) (C₁ C₂ : Finset Q)
    (hC₁_ne : C₁.Nonempty) (hC₂_ne : C₂.Nonempty)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have hn_eq : Fintype.card Q = C₁.card + C₂.card := by
    rw [← Finset.card_univ, ← hC_union, Finset.card_union_of_disjoint hC_disj]
  have hm₁ : 1 ≤ C₁.card := Finset.card_pos.mpr hC₁_ne
  have hm₂ : 1 ≤ C₂.card := Finset.card_pos.mpr hC₂_ne
  have harith : ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → 1 ≤ m₂ →
      (m₁ - 1) ^ 2 + (m₂ ^ 2 - m₂ + 1) ≤ (m₁ + m₂ - 1) ^ 2 := by
    intro m₁ m₂ h1 h2
    have hsq : m₂ ≤ m₂ ^ 2 := by nlinarith
    have hsum : 1 ≤ m₁ + m₂ := by omega
    zify [h1, h2, hsq, hsum]
    nlinarith
  rcases nonSC_twoCycle_closed_cycle A a C₁ C₂ hC_union hC₁_trans hC₂_trans hNotSC with
      hC₁_cl | hC₂_cl
  · obtain ⟨w, hw_sync, hw_len⟩ :=
      twoCycle_closed_exact_bound A hSync a C₁ C₂ hC₁_ne hC₂_ne hC_disj hC_union
        hC₁_inv hC₁_trans hC₂_inv hC₂_trans hC₁_cl
    exact ⟨w, hw_sync, hw_len.trans (by rw [hn_eq]; exact harith C₁.card C₂.card hm₁ hm₂)⟩
  · have hC_union' : C₂ ∪ C₁ = Finset.univ := by rw [Finset.union_comm, hC_union]
    obtain ⟨w, hw_sync, hw_len⟩ :=
      twoCycle_closed_exact_bound A hSync a C₂ C₁ hC₂_ne hC₁_ne hC_disj.symm hC_union'
        hC₂_inv hC₂_trans hC₁_inv hC₁_trans hC₂_cl
    refine ⟨w, hw_sync, hw_len.trans ?_⟩
    rw [hn_eq, Nat.add_comm C₁.card C₂.card]
    exact harith C₂.card C₁.card hm₂ hm₁

end Cerny
