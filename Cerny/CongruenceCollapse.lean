import Cerny.Combinatorial
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Congruence-Decomposed Pin–Frankl Compression & Imprimitive Cubic Collapse (Theorem S1)

This file formalizes Theorem S1 and Lemma S1.1 for synchronizing DFAs admitting a nontrivial
congruence `~` with `k` classes `B_1, ..., B_k` of sizes `s_1, ..., s_k` (`∑ s_t = n`):

1. **Congruences & Quotient DFA** (`DFA.IsCongruence`, `quotientDFA`, `congruenceClass`,
   `quotClasses`, `numClasses`):
   Equivalence relations preserved by all transitions, quotient DFA `A / ~`, preservation of
   synchronizability and strong connectivity, and shortest-path bound `≤ |Q| - 1` in any
   strongly connected DFA.

2. **Lemma S1.1 — Block-Partitioned Pin–Frankl Compression** (`block_pin_frankl_compress`):
   For any subset `S ⊆ B_j` (`|S| = r ≥ 2`) inside a single congruence class, there exists a word
   `w` compressing `S` (`|S · w| < r`) of length
   `w.length ≤ ∑_{t : s_t ≥ r} (s_t - r + 2).choose 2`,
   proved by partitioning prefix times by congruence class and applying `Cerny.frankl_skew_two`
   on each block.

3. **Theorem S1(a) — Singleton-Class Reduction** (`singleton_congruence_rt_bound`,
   `singleton_congruence_resetThreshold_le`, `singleton_congruence_preserves_cerny`):
   If `A` is strongly connected, synchronizing, and some congruence class has size `1`, then
   `rt(A) ≤ rt(A / ~) + k - 1`. In particular, for any nontrivial congruence (`k < n`),
   `rt(A / ~) ≤ (k - 1)^2` implies `rt(A) ≤ (n - 1)^2`.

4. **Theorem S1(b) — Global Fat-Congruence Zero-Error Cubic Collapse**
   (`fat_congruence_sum_bound`, `fat_congruence_five_ninety_six`, `fat_congruence_card_four`):
   If `A` is strongly connected, synchronizing, with `k ≥ 2` classes all of size `≥ s_min ≥ 2`,
   then
   `rt(A) ≤ rt(A / ~) + (k - 1) + ∑_t ((s_t + 1).choose 3 - (s_t - s_min + 2).choose 3)`.
   Using `Cerny.pin_frankl_bound` on `A / ~` and pure sum-of-squares algebra, this yields
   `96 * rt(A) ≤ 5 * n ^ 3` (zero error term) for every `n ≥ 5`, and `rt(A) ≤ 4` for `n = 4`.

5. **Theorem S1(c) — Equipartition Congruence Collapse (No Strong Connectivity Needed)**
   (`equipartition_congruence_bound`, `equipartition_congruence_one_twenty_fourth`,
   `equipartition_congruence_card_four`, `equipartition_congruence_cerny_window`,
   `equipartition_congruence_preserves_cerny`, `equipartition_block_two_bound`):
   For any synchronizing DFA with `k ≥ 2` congruence classes all of size `m ≥ 2` (`n = k * m`):
   - `6 * rt(A) ≤ 6 * rt(A / ~) + k * (m ^ 3 - m)`;
   - `24 * rt(A) ≤ n ^ 3` for every `n ≥ 6` (zero error term), and `rt(A) ≤ 3` for `n = 4`;
   - **Unconditional exact Černý window**: `m ≤ 2 * k ∧ k ≤ 2 * m ^ 2 → rt(A) ≤ (n - 1) ^ 2`;
   - **Conditional Černý preservation**: `rt(A / ~) ≤ (k - 1) ^ 2 ∧ 2 * m ^ 2 ≤ 9 * n - 10 →
     rt(A) ≤ (n - 1) ^ 2` (and `rt(A) ≤ rt(A / ~) + n / 2` when `m = 2`).
-/

namespace Cerny

/-! ## Part 1: Congruences, Quotient DFA, Classes, and Shortest Paths -/

section CongruenceBasics

variable {Q α : Type*}

/-- A congruence on a DFA `A` is an equivalence relation `r` on `Q` preserved by every input letter. -/
structure DFA.IsCongruence (A : DFA Q α) (r : Q → Q → Prop) : Prop where
  /-- `r` is an equivalence relation on `Q`. -/
  equiv : Equivalence r
  /-- Every transition preserves `r`. -/
  compat : ∀ p q a, r p q → r (A.step p a) (A.step q a)

/-- Promote a congruence relation `r` on `A` to a `Setoid Q`. -/
def DFA.IsCongruence.toSetoid {A : DFA Q α} {r : Q → Q → Prop} (h : A.IsCongruence r) :
    Setoid Q where
  r := r
  iseqv := h.equiv

/-- Construct `A.IsCongruence s.r` from a `Setoid Q` and transition compatibility. -/
theorem DFA.IsCongruence.ofSetoid {A : DFA Q α} (s : Setoid Q)
    (hc : ∀ p q a, s.r p q → s.r (A.step p a) (A.step q a)) : A.IsCongruence s.r :=
  ⟨s.iseqv, hc⟩

/-- The quotient DFA `A / ~` induced by a congruence `s` on `A`. -/
def quotientDFA (A : DFA Q α) (s : Setoid Q)
    (h : ∀ p q a, s.r p q → s.r (A.step p a) (A.step q a)) : DFA (Quotient s) α where
  step c a :=
    Quotient.liftOn c (fun q => Quotient.mk s (A.step q a))
      (fun p q hpq => Quotient.sound (h p q a hpq))

@[simp]
theorem quotientDFA_step_mk (A : DFA Q α) (s : Setoid Q)
    (h : ∀ p q a, s.r p q → s.r (A.step p a) (A.step q a)) (q : Q) (a : α) :
    (quotientDFA A s h).step (Quotient.mk s q) a = Quotient.mk s (A.step q a) :=
  rfl

theorem quotientDFA_eval_mk (A : DFA Q α) (s : Setoid Q)
    (h : ∀ p q a, s.r p q → s.r (A.step p a) (A.step q a)) (q : Q) (w : List α) :
    (quotientDFA A s h).eval (Quotient.mk s q) w = Quotient.mk s (A.eval q w) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => exact ih (A.step q a)

theorem quotientDFA_isSynchronizing (A : DFA Q α) (s : Setoid Q)
    (h : ∀ p q a, s.r p q → s.r (A.step p a) (A.step q a)) (hSync : A.IsSynchronizing) :
    (quotientDFA A s h).IsSynchronizing := by
  rcases hSync with ⟨w, q₀, hq₀⟩
  refine ⟨w, Quotient.mk s q₀, fun c => ?_⟩
  refine Quotient.inductionOn c fun q => ?_
  rw [quotientDFA_eval_mk, hq₀ q]

theorem quotientDFA_isStronglyConnected (A : DFA Q α) (s : Setoid Q)
    (h : ∀ p q a, s.r p q → s.r (A.step p a) (A.step q a)) (hSC : A.IsStronglyConnected) :
    (quotientDFA A s h).IsStronglyConnected := by
  intro c₁ c₂
  refine Quotient.inductionOn₂ c₁ c₂ fun p q => ?_
  obtain ⟨w, hw⟩ := hSC p q
  exact ⟨w, by rw [quotientDFA_eval_mk, hw]⟩

/-- The congruence class of `c : Quotient s` as a `Finset Q`. -/
noncomputable def congruenceClass [Fintype Q] (s : Setoid Q) (c : Quotient s) : Finset Q := by
  classical
  exact Finset.univ.filter (fun q => Quotient.mk s q = c)

theorem mem_congruenceClass [Fintype Q] (s : Setoid Q) (c : Quotient s) (q : Q) :
    q ∈ congruenceClass s c ↔ Quotient.mk s q = c := by
  classical
  simp [congruenceClass]

theorem congruenceClass_nonempty [Fintype Q] (s : Setoid Q) (c : Quotient s) :
    (congruenceClass s c).Nonempty := by
  obtain ⟨q, hq⟩ := Quotient.exists_rep c
  exact ⟨q, (mem_congruenceClass s c q).mpr hq⟩

theorem card_congruenceClass_pos [Fintype Q] (s : Setoid Q) (c : Quotient s) :
    1 ≤ (congruenceClass s c).card :=
  Finset.card_pos.mpr (congruenceClass_nonempty s c)

theorem congruenceClass_disjoint [Fintype Q] (s : Setoid Q) {c₁ c₂ : Quotient s} (hne : c₁ ≠ c₂) :
    Disjoint (congruenceClass s c₁) (congruenceClass s c₂) := by
  rw [Finset.disjoint_left]
  intro q hq₁ hq₂
  rw [mem_congruenceClass] at hq₁ hq₂
  exact hne (hq₁.symm.trans hq₂)

/-- The finite set of all congruence classes in `Quotient s`. -/
noncomputable def quotClasses [Fintype Q] (s : Setoid Q) : Finset (Quotient s) := by
  classical
  exact Finset.univ.image (Quotient.mk s)

theorem mem_quotClasses [Fintype Q] (s : Setoid Q) (c : Quotient s) :
    c ∈ quotClasses s := by
  classical
  simp only [quotClasses, Finset.mem_image, Finset.mem_univ, true_and]
  exact Quotient.exists_rep c

/-- The number of congruence classes of `s`. -/
noncomputable def numClasses [Fintype Q] (s : Setoid Q) : ℕ :=
  (quotClasses s).card

theorem numClasses_eq_fintype_card [Fintype Q] (s : Setoid Q) [Fintype (Quotient s)] :
    numClasses s = Fintype.card (Quotient s) := by
  unfold numClasses
  have huniv : quotClasses s = Finset.univ := by
    ext c
    simp [mem_quotClasses s c]
  rw [huniv, Finset.card_univ]

theorem quotClasses_nonempty [Fintype Q] [Nonempty Q] (s : Setoid Q) :
    (quotClasses s).Nonempty := by
  obtain ⟨q⟩ := ‹Nonempty Q›
  exact ⟨Quotient.mk s q, mem_quotClasses s _⟩

theorem numClasses_pos [Fintype Q] [Nonempty Q] (s : Setoid Q) :
    1 ≤ numClasses s :=
  Finset.card_pos.mpr (quotClasses_nonempty s)

theorem sum_card_congruenceClass [Fintype Q] (s : Setoid Q) :
    ∑ c ∈ quotClasses s, (congruenceClass s c).card = Fintype.card Q := by
  classical
  rw [← Finset.card_biUnion]
  · have huniv : (quotClasses s).biUnion (congruenceClass s) = Finset.univ := by
      ext q
      simp only [Finset.mem_biUnion, mem_congruenceClass, Finset.mem_univ, iff_true]
      exact ⟨Quotient.mk s q, mem_quotClasses s _, rfl⟩
    rw [huniv, Finset.card_univ]
  · intro c₁ _ c₂ _ hne
    exact congruenceClass_disjoint s hne

theorem image_subset_congruenceClass [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (s : Setoid Q) (h : ∀ p q a, s.r p q → s.r (A.step p a) (A.step q a))
    {c : Quotient s} {S : Finset Q} (hS : S ⊆ congruenceClass s c) (w : List α) :
    A.image S w ⊆ congruenceClass s ((quotientDFA A s h).eval c w) := by
  intro q hq
  rw [DFA.mem_image] at hq
  rcases hq with ⟨p, hp, rfl⟩
  rw [mem_congruenceClass]
  have hp_cls : Quotient.mk s p = c := (mem_congruenceClass s c p).mp (hS hp)
  rw [← hp_cls, quotientDFA_eval_mk]

theorem isSyncWord_quotientDFA_image_subset [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (s : Setoid Q) (h : ∀ p q a, s.r p q → s.r (A.step p a) (A.step q a))
    {u : List α} {c₀ : Quotient s}
    (hu : ∀ c : Quotient s, (quotientDFA A s h).eval c u = c₀) :
    A.image Finset.univ u ⊆ congruenceClass s c₀ := by
  intro q hq
  rw [DFA.mem_image] at hq
  rcases hq with ⟨p, _, rfl⟩
  rw [mem_congruenceClass, ← quotientDFA_eval_mk A s h p u]
  exact hu (Quotient.mk s p)

/-- In any strongly connected finite DFA, every state is reachable from every other state by a
word of length at most `Fintype.card Q - 1`. -/
theorem exists_reach_length_le_pred [Fintype Q] (A : DFA Q α) (hSC : A.IsStronglyConnected)
    (p q : Q) : ∃ v : List α, A.eval p v = q ∧ v.length ≤ Fintype.card Q - 1 := by
  classical
  have hex : ∃ k : ℕ, ∃ v : List α, v.length = k ∧ A.eval p v = q := by
    obtain ⟨v, hv⟩ := hSC p q
    exact ⟨v.length, v, rfl, hv⟩
  let m := Nat.find hex
  obtain ⟨v, hvlen, hveval⟩ := Nat.find_spec hex
  have hmin : ∀ u : List α, A.eval p u = q → m ≤ u.length := fun u hu =>
    Nat.find_min' hex ⟨u, rfl, hu⟩
  refine ⟨v, hveval, ?_⟩
  let f : Fin (m + 1) → Q := fun i => A.eval p (v.take i.val)
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hlt : ∀ a b : Fin (m + 1), a < b → f a ≠ f b := by
      intro a b hab heq
      let v' := v.take a.val ++ v.drop b.val
      have hv'eval : A.eval p v' = q := by
        dsimp [v']
        rw [DFA.eval_append]
        change A.eval (f a) (v.drop b.val) = q
        rw [heq]
        dsimp [f]
        rw [← DFA.eval_append, List.take_append_drop]
        exact hveval
      have hb := hmin v' hv'eval
      simp only [v', List.length_append, List.length_take, List.length_drop, hvlen] at hb
      have hab' : a.val < b.val := hab
      omega
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt i j h hij
    · exact hlt j i h hij.symm
  have hcard := Fintype.card_le_of_injective f hf_inj
  rw [Fintype.card_fin] at hcard
  omega

/-- Shortest path in the quotient DFA `A / ~` has length at most `numClasses s - 1`. -/
theorem quotientDFA_exists_reach_length_le [Fintype Q]
    (A : DFA Q α) (hSC : A.IsStronglyConnected)
    (s : Setoid Q) (hcong : A.IsCongruence s.r) (c₁ c₂ : Quotient s) :
    ∃ v : List α, (quotientDFA A s hcong.compat).eval c₁ v = c₂ ∧
      v.length ≤ numClasses s - 1 := by
  classical
  let _ : Fintype (Quotient s) := Fintype.ofSurjective (Quotient.mk s) Quotient.exists_rep
  obtain ⟨v, hveval, hvlen⟩ :=
    exists_reach_length_le_pred (quotientDFA A s hcong.compat)
      (quotientDFA_isStronglyConnected A s hcong.compat hSC) c₁ c₂
  rw [← numClasses_eq_fintype_card s] at hvlen
  exact ⟨v, hveval, hvlen⟩

/-- Pin–Frankl cubic bound applied to the quotient DFA `A / ~`. -/
theorem quotientDFA_pin_frankl_bound [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r) :
    ∃ u : List α, (quotientDFA A s hcong.compat).IsSyncWord u ∧
      6 * u.length ≤ (numClasses s) ^ 3 - numClasses s := by
  classical
  let _ : Fintype (Quotient s) := Fintype.ofSurjective (Quotient.mk s) Quotient.exists_rep
  have _ : Nonempty (Quotient s) :=
    let ⟨q⟩ := ‹Nonempty Q›
    ⟨Quotient.mk s q⟩
  obtain ⟨u, huSync, hulen⟩ :=
    pin_frankl_bound (quotientDFA A s hcong.compat)
      (quotientDFA_isSynchronizing A s hcong.compat hSync)
  rw [← numClasses_eq_fintype_card s] at hulen
  exact ⟨u, huSync, hulen⟩

end CongruenceBasics

/-! ## Part 2: Lemma S1.1 — Block-Partitioned Pin–Frankl Compression -/

section BlockPinFrankl

variable {Q α : Type*}

/-- **Lemma S1.1 (Block-Partitioned Pin–Frankl Compression)**:
In a synchronizing DFA `A` admitting a congruence `s`, any subset `S` of size `r ≥ 2`
contained inside a single congruence class `B_{c₀}` is compressed (`|S · w| < |S|`) by a word `w`
of length at most `∑_{c : |B_c| ≥ r} (|B_c| - r + 2).choose 2`. -/
theorem block_pin_frankl_compress [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (c₀ : Quotient s) (S : Finset Q) (hSsub : S ⊆ congruenceClass s c₀) (hS2 : 2 ≤ S.card) :
    ∃ w : List α, (A.image S w).card < S.card ∧
      w.length ≤ ∑ c ∈ (quotClasses s).filter (fun c => S.card ≤ (congruenceClass s c).card),
        ((congruenceClass s c).card - S.card + 2).choose 2 := by
  classical
  have hex : ∃ k : ℕ, ∃ w : List α, w.length = k ∧ (A.image S w).card < S.card := by
    rcases hSync with ⟨w, q₀, hq₀⟩
    refine ⟨w.length, w, rfl, ?_⟩
    have hsub : A.image S w ⊆ {q₀} := by
      intro q hq
      rw [DFA.mem_image] at hq
      rcases hq with ⟨p, _, rfl⟩
      simp [hq₀ p]
    have hc := Finset.card_le_card hsub
    simp at hc
    omega
  let m := Nat.find hex
  obtain ⟨w, hwlen, hwcomp⟩ := Nat.find_spec hex
  have hmin : ∀ v : List α, (A.image S v).card < S.card → m ≤ v.length := fun v hv =>
    Nat.find_min' hex ⟨v, rfl, hv⟩
  refine ⟨w, hwcomp, ?_⟩
  rw [hwlen]
  -- Pick distinct x₀, y₀ ∈ S merged by w
  have hex_pair : ∃ x₀ ∈ S, ∃ y₀ ∈ S, x₀ ≠ y₀ ∧ A.eval x₀ w = A.eval y₀ w := by
    by_contra hall
    push Not at hall
    have hinj : Set.InjOn (fun q => A.eval q w) S := fun x hx y hy hxy => by
      by_contra hne
      exact hall x hx y hy hne hxy
    have heq := Finset.card_image_of_injOn hinj
    change (A.image S w).card = S.card at heq
    omega
  rcases hex_pair with ⟨x₀, hx₀, y₀, hy₀, hx₀y₀, hmerge⟩
  let x : Fin m → Q := fun k => A.eval x₀ (w.take k.val)
  let y : Fin m → Q := fun k => A.eval y₀ (w.take k.val)
  let Sk : Fin m → Finset Q := fun k => A.image S (w.take k.val)
  let cls : Fin m → Quotient s := fun k => (quotientDFA A s hcong.compat).eval c₀ (w.take k.val)
  have hSk_card : ∀ k : Fin m, (Sk k).card = S.card := by
    intro k
    have hle : (Sk k).card ≤ S.card := A.card_image_le S (w.take k.val)
    have hnotlt : ¬ (Sk k).card < S.card := by
      intro hlt
      have hb := hmin (w.take k.val) hlt
      rw [List.length_take] at hb
      omega
    omega
  have hSk_sub : ∀ k : Fin m, Sk k ⊆ congruenceClass s (cls k) := fun k =>
    image_subset_congruenceClass A s hcong.compat hSsub (w.take k.val)
  have hcls_card : ∀ k : Fin m, S.card ≤ (congruenceClass s (cls k)).card := by
    intro k
    rw [← hSk_card k]
    exact Finset.card_le_card (hSk_sub k)
  have hxy_ne : ∀ k : Fin m, x k ≠ y k := by
    intro k heq
    have hlt : (Sk k).card < S.card := by
      have himg_eq : Sk k = A.image (S.erase x₀) (w.take k.val) := by
        ext q
        simp only [Sk, DFA.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨p, hp, rfl⟩
          by_cases hpx : p = x₀
          · subst hpx; exact ⟨y₀, ⟨hx₀y₀.symm, hy₀⟩, heq.symm⟩
          · exact ⟨p, ⟨hpx, hp⟩, rfl⟩
        · rintro ⟨p, ⟨_, hp⟩, rfl⟩
          exact ⟨p, hp, rfl⟩
      rw [himg_eq]
      exact lt_of_le_of_lt (A.card_image_le _ _) (Finset.card_erase_lt_of_mem hx₀)
    have := hSk_card k
    omega
  let active : Finset (Quotient s) :=
    (quotClasses s).filter (fun c => S.card ≤ (congruenceClass s c).card)
  let I : Quotient s → Finset (Fin m) := fun c => Finset.univ.filter (fun k : Fin m => cls k = c)
  have hm_eq : m = ∑ c ∈ active, (I c).card := by
    calc m = (Finset.univ : Finset (Fin m)).card := by simp
      _ = (active.biUnion I).card := by
          congr 1
          ext k
          simp only [Finset.mem_univ, Finset.mem_biUnion, active, I, Finset.mem_filter, true_and,
            true_iff]
          exact ⟨cls k, ⟨mem_quotClasses s (cls k), hcls_card k⟩, rfl⟩
      _ = ∑ c ∈ active, (I c).card := by
          refine Finset.card_biUnion fun c₁ _ c₂ _ hne => ?_
          change Disjoint (I c₁) (I c₂)
          rw [Finset.disjoint_left]
          intro k hk₁ hk₂
          simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hk₁ hk₂
          exact hne (hk₁.symm.trans hk₂)
  change m ≤ ∑ c ∈ active, ((congruenceClass s c).card - S.card + 2).choose 2
  rw [hm_eq]
  refine Finset.sum_le_sum fun c hc => ?_
  let e : Fin (I c).card ≃o {k : Fin m // k ∈ I c} := (I c).orderIsoOfFin rfl
  let idx : Fin (I c).card → Fin m := fun t => (e t).val
  have hidx_cls : ∀ t : Fin (I c).card, cls (idx t) = c := fun t =>
    (Finset.mem_filter.mp (e t).property).2
  have hidx_sub : ∀ t : Fin (I c).card, Sk (idx t) ⊆ congruenceClass s c := by
    intro t
    rw [← hidx_cls t]
    exact hSk_sub (idx t)
  let x' : Fin (I c).card → Q := fun t => x (idx t)
  let y' : Fin (I c).card → Q := fun t => y (idx t)
  let B' : Fin (I c).card → Finset Q := fun t => congruenceClass s c \ Sk (idx t)
  have hB'_card : ∀ t : Fin (I c).card, (B' t).card ≤ (congruenceClass s c).card - S.card := by
    intro t
    dsimp [B']
    rw [Finset.card_sdiff_of_subset (hidx_sub t), hSk_card (idx t)]
  have hdisj : ∀ t : Fin (I c).card, x' t ∉ B' t ∧ y' t ∉ B' t := by
    intro t
    have hx_in : x' t ∈ Sk (idx t) := by rw [DFA.mem_image]; exact ⟨x₀, hx₀, rfl⟩
    have hy_in : y' t ∈ Sk (idx t) := by rw [DFA.mem_image]; exact ⟨y₀, hy₀, rfl⟩
    exact ⟨fun h => (Finset.mem_sdiff.mp h).2 hx_in, fun h => (Finset.mem_sdiff.mp h).2 hy_in⟩
  have hinter : ∀ t₁ t₂ : Fin (I c).card, t₂ < t₁ → x' t₁ ∈ B' t₂ ∨ y' t₁ ∈ B' t₂ := by
    intro t₁ t₂ ht
    by_contra hnot
    push Not at hnot
    have hx_mem_cls : x' t₁ ∈ congruenceClass s c :=
      hidx_sub t₁ (by rw [DFA.mem_image]; exact ⟨x₀, hx₀, rfl⟩)
    have hy_mem_cls : y' t₁ ∈ congruenceClass s c :=
      hidx_sub t₁ (by rw [DFA.mem_image]; exact ⟨y₀, hy₀, rfl⟩)
    have hxi_in : x' t₁ ∈ Sk (idx t₂) := by
      by_contra hnotS
      exact hnot.1 (Finset.mem_sdiff.mpr ⟨hx_mem_cls, hnotS⟩)
    have hyi_in : y' t₁ ∈ Sk (idx t₂) := by
      by_contra hnotS
      exact hnot.2 (Finset.mem_sdiff.mpr ⟨hy_mem_cls, hnotS⟩)
    let i := idx t₁
    let j := idx t₂
    have hji : j.val < i.val := e.strictMono ht
    have hmerge_drop : A.eval (x i) (w.drop i.val) = A.eval (y i) (w.drop i.val) := by
      dsimp [x, y]
      rw [← DFA.eval_append, ← DFA.eval_append, List.take_append_drop]
      exact hmerge
    let w' := w.take j.val ++ w.drop i.val
    have hcomp' : (A.image S w').card < S.card := by
      dsimp [w']
      rw [DFA.image_append]
      change (A.image (Sk j) (w.drop i.val)).card < S.card
      rw [← hSk_card j]
      have himg_eq :
          A.image (Sk j) (w.drop i.val) = A.image ((Sk j).erase (x i)) (w.drop i.val) := by
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
    simp only [w', List.length_append, List.length_take, List.length_drop, hwlen] at hb
    omega
  exact frankl_skew_two (I c).card ((congruenceClass s c).card - S.card)
    x' y' B' hB'_card hdisj hinter

end BlockPinFrankl

/-! ## Part 3: Combinatorial & Algebraic Helpers for Theorem S1(b)-(c) -/

section ArithmeticHelpers

private theorem sum_choose_two_sub (b d : ℕ) (hd : d ≤ b) :
    ∑ j ∈ Finset.range d, (b - j).choose 2 = (b + 1).choose 3 - (b - d + 1).choose 3 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have hpascal : (b - d + 1).choose 3 = (b - d).choose 2 + (b - d).choose 3 :=
      Nat.choose_succ_succ (b - d) 2
    have hle : (b - d + 1).choose 3 ≤ (b + 1).choose 3 :=
      Nat.choose_le_choose 3 (by omega)
    have harg : b - (d + 1) + 1 = b - d := by omega
    rw [harg]
    omega

private theorem two_mul_choose_two (x : ℕ) :
    2 * (x + 1).choose 2 = (x + 1) * x := by
  rw [Nat.choose_two_right]
  have heven : 2 ∣ (x + 1) * x := by
    rcases (Nat.even_mul_succ_self x).two_dvd with ⟨t, ht⟩
    exact ⟨t, by linarith⟩
  rcases heven with ⟨t, ht⟩
  have hsub : x + 1 - 1 = x := by omega
  rw [hsub, ht]
  omega

private theorem six_mul_choose_three (x : ℕ) :
    6 * (x + 1).choose 3 = x ^ 3 - x := by
  induction x with
  | zero => decide
  | succ x ih =>
    have hpascal : (x + 2).choose 3 = (x + 1).choose 2 + (x + 1).choose 3 :=
      Nat.choose_succ_succ (x + 1) 2
    have h2 := two_mul_choose_two x
    have h1 : x ≤ x ^ 3 := Nat.le_self_pow (by omega) x
    have h2' : x + 1 ≤ (x + 1) ^ 3 := Nat.le_self_pow (by omega) (x + 1)
    have hstep : 6 * (x + 2).choose 3 = 3 * ((x + 1) * x) + (x ^ 3 - x) := by
      rw [hpascal, mul_add, ih]
      omega
    rw [hstep]
    zify [h1, h2']
    ring

private theorem six_mul_choose_three_sub_int (b d : ℕ) (hd : d ≤ b) :
    (6 * ((b + 1).choose 3 - (b - d + 1).choose 3) : ℤ) =
      (d : ℤ) * (3 * (b : ℤ) ^ 2 - 3 * (d : ℤ) * (b : ℤ) + (d : ℤ) ^ 2 - 1) := by
  have hle : (b - d + 1).choose 3 ≤ (b + 1).choose 3 :=
    Nat.choose_le_choose 3 (by omega)
  have hnat : 6 * ((b + 1).choose 3 - (b - d + 1).choose 3) =
      (b ^ 3 - b) - ((b - d) ^ 3 - (b - d)) := by
    rw [Nat.mul_sub, six_mul_choose_three b, six_mul_choose_three (b - d)]
  have hb3 : b ≤ b ^ 3 := Nat.le_self_pow (by omega) b
  have hbd3 : b - d ≤ (b - d) ^ 3 := Nat.le_self_pow (by omega) (b - d)
  have hsub_le : (b - d) ^ 3 - (b - d) ≤ b ^ 3 - b := by
    rw [← six_mul_choose_three (b - d), ← six_mul_choose_three b]
    exact Nat.mul_le_mul_left 6 hle
  have hcast : (6 * ((b + 1).choose 3 - (b - d + 1).choose 3) : ℤ) =
      (((b ^ 3 - b) - ((b - d) ^ 3 - (b - d)) : ℕ) : ℤ) := by
    exact_mod_cast hnat
  rw [hcast]
  zify [hsub_le, hb3, hbd3, hd]
  ring

private theorem sum_sq_le_sq_sum {ι : Type*} (I : Finset ι) (y : ι → ℕ) :
    ∑ t ∈ I, (y t) ^ 2 ≤ (∑ t ∈ I, y t) ^ 2 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hexp :
        (y a + ∑ x ∈ s, y x) ^ 2 =
          y a ^ 2 + 2 * y a * (∑ x ∈ s, y x) + (∑ x ∈ s, y x) ^ 2 := by
      ring
    omega

/-- Greedy block compression from any nonempty subset `S ⊆ B_{c₀}` down to a singleton. -/
private theorem block_compress_to_singleton {Q α : Type*} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r) :
    ∀ r : ℕ, 1 ≤ r →
      ∀ (c₀ : Quotient s) (S : Finset Q), S ⊆ congruenceClass s c₀ → S.card = r →
        ∃ w : List α, (A.image S w).card = 1 ∧
          w.length ≤ ∑ j ∈ Finset.range (r - 1),
            ∑ c ∈ quotClasses s, ((congruenceClass s c).card - (j + 2) + 2).choose 2 := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr1 c₀ S hSsub hScard
    by_cases h1 : r = 1
    · subst h1
      exact ⟨[], by simpa using hScard, by simp⟩
    · have hr2 : 2 ≤ S.card := by omega
      obtain ⟨v, hvcomp, hvlen⟩ := block_pin_frankl_compress A hSync s hcong c₀ S hSsub hr2
      set S' := A.image S v
      let c' := (quotientDFA A s hcong.compat).eval c₀ v
      have hS'sub : S' ⊆ congruenceClass s c' :=
        image_subset_congruenceClass A s hcong.compat hSsub v
      have hS'ne : S'.Nonempty := by
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
        exact ⟨A.eval x v, by rw [DFA.mem_image]; exact ⟨x, hx, rfl⟩⟩
      have hS'pos : 1 ≤ S'.card := Finset.card_pos.mpr hS'ne
      have hS'lt : S'.card < r := by omega
      obtain ⟨u, hu1, hulen⟩ := ih S'.card hS'lt hS'pos c' S' hS'sub rfl
      refine ⟨v ++ u, ?_, ?_⟩
      · rw [DFA.image_append]; exact hu1
      · rw [List.length_append]
        have hvlen' :
            v.length ≤ ∑ c ∈ quotClasses s, ((congruenceClass s c).card - r + 2).choose 2 := by
          rw [hScard] at hvlen
          exact hvlen.trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
        have hsum_le :
            (∑ j ∈ Finset.range (S'.card - 1),
              ∑ c ∈ quotClasses s, ((congruenceClass s c).card - (j + 2) + 2).choose 2) ≤
            ∑ j ∈ Finset.range (r - 2),
              ∑ c ∈ quotClasses s, ((congruenceClass s c).card - (j + 2) + 2).choose 2 :=
          Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
        have hsplit :
            (∑ j ∈ Finset.range (r - 1),
              ∑ c ∈ quotClasses s, ((congruenceClass s c).card - (j + 2) + 2).choose 2) =
            (∑ j ∈ Finset.range (r - 2),
              ∑ c ∈ quotClasses s, ((congruenceClass s c).card - (j + 2) + 2).choose 2) +
            ∑ c ∈ quotClasses s, ((congruenceClass s c).card - r + 2).choose 2 := by
          have hr_eq : r - 1 = (r - 2) + 1 := by omega
          have harg : (r - 2) + 2 = r := by omega
          rw [hr_eq, Finset.sum_range_succ, harg]
        omega

/-- Hockey-stick evaluation of the greedy block compression budget for any `S ⊆ B_{c₀}` of size
`1 ≤ |S| ≤ m`. -/
private theorem block_compress_hockey_stick {Q α : Type*} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (m : ℕ) (hm : 2 ≤ m) (hmin_cls : ∀ c : Quotient s, m ≤ (congruenceClass s c).card)
    (c₀ : Quotient s) (S : Finset Q) (hSsub : S ⊆ congruenceClass s c₀)
    (hSpos : 1 ≤ S.card) (hSm : S.card ≤ m) :
    ∃ w : List α, (A.image S w).card = 1 ∧
      w.length ≤ ∑ c ∈ quotClasses s,
        (((congruenceClass s c).card + 1).choose 3 -
          ((congruenceClass s c).card - m + 2).choose 3) := by
  obtain ⟨w, hw1, hwlen⟩ :=
    block_compress_to_singleton A hSync s hcong S.card hSpos c₀ S hSsub rfl
  refine ⟨w, hw1, ?_⟩
  have hle_m :
      w.length ≤ ∑ j ∈ Finset.range (m - 1),
        ∑ c ∈ quotClasses s, ((congruenceClass s c).card - (j + 2) + 2).choose 2 :=
    hwlen.trans (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
  rw [Finset.sum_comm] at hle_m
  refine hle_m.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun c _ => ?_
  have hcb : m ≤ (congruenceClass s c).card := hmin_cls c
  have hrewrite :
      (∑ j ∈ Finset.range (m - 1), ((congruenceClass s c).card - (j + 2) + 2).choose 2) =
      ∑ j ∈ Finset.range (m - 1), ((congruenceClass s c).card - j).choose 2 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    congr 1
    omega
  rw [hrewrite, sum_choose_two_sub (congruenceClass s c).card (m - 1) (by omega)]
  have harg : (congruenceClass s c).card - (m - 1) + 1 = (congruenceClass s c).card - m + 2 := by
    omega
  rw [harg]

/-- Pure sum-of-squares algebraic core of Theorem S1(b):
for all integers `k ≥ 2`, `m ≥ 2`, `Y ≥ 0` with `n = Y + k * m ≥ 5`,
`16 * ((k^3 + 5*k - 6) + (m - 1) * (3*Y^2 + (3*m + 3)*Y + k*m*(m + 1))) ≤ 5 * (Y + k*m)^3`. -/
private theorem fat_cubic_sos (k m Y : ℤ) (hk : 2 ≤ k) (hm : 2 ≤ m) (hY : 0 ≤ Y)
    (hn : 5 ≤ Y + k * m) :
    16 * ((k ^ 3 + 5 * k - 6) + (m - 1) * (3 * Y ^ 2 + (3 * m + 3) * Y + k * m * (m + 1))) ≤
      5 * (Y + k * m) ^ 3 := by
  by_cases hk2 : k = 2
  · subst hk2
    set d : ℤ := m - 1
    have hd : 1 ≤ d := by omega
    have hident :
        5 * (Y + 2 * m) ^ 3 -
          16 * ((2 ^ 3 + 5 * 2 - 6) + (m - 1) * (3 * Y ^ 2 + (3 * m + 3) * Y + 2 * m * (m + 1))) =
        (Y + 2 * m - 4 * d) ^ 2 * (5 * (Y + 2 * m) - 8 * d) +
          16 * (6 * d * (Y + 2) - 4 * d - 12) := by
      dsimp [d]
      ring
    have h1 : 0 ≤ (Y + 2 * m - 4 * d) ^ 2 * (5 * (Y + 2 * m) - 8 * d) := by
      have hlin : 0 ≤ 5 * (Y + 2 * m) - 8 * d := by omega
      exact mul_nonneg (sq_nonneg _) hlin
    have h2 : 0 ≤ 6 * d * (Y + 2) - 4 * d - 12 := by
      by_cases hd1 : d = 1
      · have hY1 : 1 ≤ Y := by omega
        nlinarith
      · have hd2 : 2 ≤ d := by omega
        nlinarith
    linarith
  · by_cases hk3 : k = 3
    · subst hk3
      have hident :
          5 * (Y + 3 * m) ^ 3 -
            16 * ((3 ^ 3 + 5 * 3 - 6) + (m - 1) * (3 * Y ^ 2 + (3 * m + 3) * Y + 3 * m * (m + 1))) =
          Y * (5 * (Y - m) ^ 2 + 7 * m * Y + 82 * m ^ 2) +
            48 * Y ^ 2 + 48 * Y + (87 * m ^ 3 + 48 * m - 576) := by
        ring
      have h1 : 0 ≤ Y * (5 * (Y - m) ^ 2 + 7 * m * Y + 82 * m ^ 2) := by
        refine mul_nonneg hY ?_
        have hs1 : 0 ≤ 5 * (Y - m) ^ 2 := by nlinarith [sq_nonneg (Y - m)]
        have hs2 : 0 ≤ 7 * m * Y := by nlinarith
        have hs3 : 0 ≤ 82 * m ^ 2 := by nlinarith [sq_nonneg m]
        linarith
      have h2 : 0 ≤ 87 * m ^ 3 + 48 * m - 576 := by
        have hm2 : 4 ≤ m ^ 2 := by nlinarith
        have hm3 : 8 ≤ m ^ 3 := by nlinarith
        linarith
      have h3 : 0 ≤ 48 * Y ^ 2 + 48 * Y := by nlinarith [sq_nonneg Y]
      linarith
    · have hk4 : 4 ≤ k := by omega
      have hident :
          5 * (Y + k * m) ^ 3 -
            16 * ((k ^ 3 + 5 * k - 6) + (m - 1) * (3 * Y ^ 2 + (3 * m + 3) * Y + k * m * (m + 1))) =
          5 * Y ^ 3 +
            (15 * (k - 4) * m + 12 * m + 48) * Y ^ 2 +
            (15 * (k ^ 2 - 16) * m ^ 2 + 192 * m ^ 2 + 48) * Y +
            (4 * k ^ 3 * (m ^ 3 - 8) + k * (k ^ 2 - 16) * m ^ 3 +
              16 * k * (k ^ 2 - 5) + 16 * k * m + 96) := by
        ring
      have hk2_ge : 16 ≤ k ^ 2 := by nlinarith
      have hm2_ge : 4 ≤ m ^ 2 := by nlinarith
      have hm3_ge : 8 ≤ m ^ 3 := by nlinarith
      have ht0 : 0 ≤ 5 * Y ^ 3 := by nlinarith [sq_nonneg Y]
      have ht1 : 0 ≤ (15 * (k - 4) * m + 12 * m + 48) * Y ^ 2 := by
        refine mul_nonneg ?_ (sq_nonneg Y)
        nlinarith
      have ht2 : 0 ≤ (15 * (k ^ 2 - 16) * m ^ 2 + 192 * m ^ 2 + 48) * Y := by
        refine mul_nonneg ?_ hY
        nlinarith
      have ht3 : 0 ≤ 4 * k ^ 3 * (m ^ 3 - 8) := by
        have hk3_pos : 0 ≤ k ^ 3 := by nlinarith
        nlinarith
      have ht4 : 0 ≤ k * (k ^ 2 - 16) * m ^ 3 := by
        have hkm : 0 ≤ k * (k ^ 2 - 16) := by nlinarith
        nlinarith
      have ht5 : 0 ≤ 16 * k * (k ^ 2 - 5) + 16 * k * m + 96 := by nlinarith
      linarith

end ArithmeticHelpers

/-! ## Part 4: Theorem S1(a) — Singleton-Class Reduction -/

section TheoremS1a

variable {Q α : Type*}

/-- **Theorem S1(a) (Singleton-Class Reduction)**:
If `A` is strongly connected, synchronizing, admits a congruence `s` with a singleton class
`B_{c_*}`, and `u` synchronizes `A / ~`, then `A` admits a synchronizing word of length at most
`u.length + numClasses s - 1`. -/
theorem singleton_congruence_rt_bound [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSC : A.IsStronglyConnected)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (c_star : Quotient s) (hsingle : (congruenceClass s c_star).card = 1)
    (u : List α) (hu : (quotientDFA A s hcong.compat).IsSyncWord u) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ u.length + numClasses s - 1 := by
  classical
  rcases hu with ⟨c₀, hc₀⟩
  obtain ⟨v, hveval, hvlen⟩ :=
    quotientDFA_exists_reach_length_le A hSC s hcong c₀ c_star
  have himg_sub : A.image Finset.univ (u ++ v) ⊆ congruenceClass s c_star := by
    rw [DFA.image_append]
    have h1 : A.image Finset.univ u ⊆ congruenceClass s c₀ :=
      isSyncWord_quotientDFA_image_subset A s hcong.compat hc₀
    have h2 := image_subset_congruenceClass A s hcong.compat h1 v
    rw [hveval] at h2
    exact h2
  have himg_ne : (A.image Finset.univ (u ++ v)).Nonempty := by
    obtain ⟨q⟩ := ‹Nonempty Q›
    exact ⟨A.eval q (u ++ v), by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩⟩
  have himg_card_pos : 1 ≤ (A.image Finset.univ (u ++ v)).card := Finset.card_pos.mpr himg_ne
  have himg_card_le : (A.image Finset.univ (u ++ v)).card ≤ 1 := by
    calc (A.image Finset.univ (u ++ v)).card
        ≤ (congruenceClass s c_star).card := Finset.card_le_card himg_sub
      _ = 1 := hsingle
  have himg_eq_one : (A.image Finset.univ (u ++ v)).card = 1 := by omega
  have hsync_uv : A.IsSyncWord (u ++ v) :=
    (A.isSyncWord_iff_card_image_univ_eq_one (u ++ v)).mpr himg_eq_one
  refine ⟨u ++ v, hsync_uv, ?_⟩
  rw [List.length_append]
  have hk_pos : 1 ≤ numClasses s := numClasses_pos s
  omega

/-- Reset-threshold form of Theorem S1(a): `rt(A) ≤ rt(A / ~) + k - 1`. -/
theorem singleton_congruence_resetThreshold_le [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSC : A.IsStronglyConnected) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (c_star : Quotient s) (hsingle : (congruenceClass s c_star).card = 1) :
    A.resetThreshold hSync ≤
      (quotientDFA A s hcong.compat).resetThreshold
        (quotientDFA_isSynchronizing A s hcong.compat hSync) + numClasses s - 1 := by
  obtain ⟨u, huSync, hulen⟩ :=
    (quotientDFA A s hcong.compat).exists_isSyncWord_length_eq_resetThreshold
      (quotientDFA_isSynchronizing A s hcong.compat hSync)
  obtain ⟨w, hwSync, hwlen⟩ :=
    singleton_congruence_rt_bound A hSC s hcong c_star hsingle u huSync
  rw [hulen] at hwlen
  exact (A.resetThreshold_le_of_isSyncWord hSync hwSync).trans hwlen

/-- Exact Černý preservation corollary of Theorem S1(a):
if `A` is strongly connected with a proper congruence (`numClasses s < Fintype.card Q`) having a
singleton class, and `A / ~` satisfies Černý's bound `≤ (k - 1)^2`, then `A` satisfies
`w.length ≤ (Fintype.card Q - 1)^2`. -/
theorem singleton_congruence_preserves_cerny [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSC : A.IsStronglyConnected)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (hproper : numClasses s < Fintype.card Q)
    (c_star : Quotient s) (hsingle : (congruenceClass s c_star).card = 1)
    (u : List α) (hu : (quotientDFA A s hcong.compat).IsSyncWord u)
    (hulen : u.length ≤ (numClasses s - 1) ^ 2) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hwSync, hwlen⟩ :=
    singleton_congruence_rt_bound A hSC s hcong c_star hsingle u hu
  refine ⟨w, hwSync, ?_⟩
  set k := numClasses s
  set n := Fintype.card Q
  have hk1 : 1 ≤ k := numClasses_pos s
  have hn1 : 1 ≤ n := by omega
  have hquad : (k - 1) ^ 2 + k - 1 ≤ (n - 1) ^ 2 := by
    zify [hk1, hn1, show 1 ≤ (k - 1) ^ 2 + k by omega]
    have hkn : (k : ℤ) ≤ (n : ℤ) - 1 := by omega
    have hk1' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
    nlinarith
  omega

end TheoremS1a

/-! ## Part 5: Theorem S1(b) — Global Fat-Congruence Zero-Error Cubic Collapse -/

section TheoremS1b

variable {Q α : Type*}

/-- **Theorem S1(b) (General Sum Bound)**:
If `A` is strongly connected and synchronizing with congruence `s`, minimum class size `m ≥ 2`
achieved at class `c_min`, and `u` synchronizes `A / ~`, then `A` admits a synchronizing word `w`
with
`w.length ≤ u.length + (numClasses s - 1) + ∑ c ∈ quotClasses s, ((|B_c| + 1).choose 3 - (|B_c| - m + 2).choose 3)`. -/
theorem fat_congruence_sum_bound [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSC : A.IsStronglyConnected) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (m : ℕ) (hm : 2 ≤ m)
    (hmin_cls : ∀ c : Quotient s, m ≤ (congruenceClass s c).card)
    (c_min : Quotient s) (hc_min : (congruenceClass s c_min).card = m)
    (u : List α) (hu : (quotientDFA A s hcong.compat).IsSyncWord u) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ u.length + (numClasses s - 1) +
        ∑ c ∈ quotClasses s,
          (((congruenceClass s c).card + 1).choose 3 -
            ((congruenceClass s c).card - m + 2).choose 3) := by
  classical
  rcases hu with ⟨c₀, hc₀⟩
  obtain ⟨v, hveval, hvlen⟩ :=
    quotientDFA_exists_reach_length_le A hSC s hcong c₀ c_min
  let S₀ := A.image Finset.univ (u ++ v)
  have hS₀_sub : S₀ ⊆ congruenceClass s c_min := by
    dsimp [S₀]
    rw [DFA.image_append]
    have h1 : A.image Finset.univ u ⊆ congruenceClass s c₀ :=
      isSyncWord_quotientDFA_image_subset A s hcong.compat hc₀
    have h2 := image_subset_congruenceClass A s hcong.compat h1 v
    rw [hveval] at h2
    exact h2
  have hS₀_ne : S₀.Nonempty := by
    obtain ⟨q⟩ := ‹Nonempty Q›
    exact ⟨A.eval q (u ++ v), by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩⟩
  have hS₀_pos : 1 ≤ S₀.card := Finset.card_pos.mpr hS₀_ne
  have hS₀_le : S₀.card ≤ m := by
    rw [← hc_min]
    exact Finset.card_le_card hS₀_sub
  obtain ⟨z, hz1, hzlen⟩ :=
    block_compress_hockey_stick A hSync s hcong m hm hmin_cls c_min S₀ hS₀_sub hS₀_pos hS₀_le
  refine ⟨(u ++ v) ++ z, ?_, ?_⟩
  · rw [A.isSyncWord_iff_card_image_univ_eq_one, DFA.image_append]
    exact hz1
  · rw [List.length_append, List.length_append]
    omega

/-- **Theorem S1(b) (Global Zero-Error `5/96` Cubic Collapse)**:
Every strongly connected synchronizing DFA on `n ≥ 5` states admitting a nontrivial fat congruence
(`k ≥ 2` classes, each of size `≥ 2`) admits a synchronizing word `w` satisfying
`96 * w.length ≤ 5 * n ^ 3`. -/
theorem fat_congruence_five_ninety_six [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSC : A.IsStronglyConnected) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (hk : 2 ≤ numClasses s)
    (hfat : ∀ c : Quotient s, 2 ≤ (congruenceClass s c).card)
    (hn : 5 ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ 96 * w.length ≤ 5 * (Fintype.card Q) ^ 3 := by
  classical
  -- Pick a minimum-size congruence class
  have hne_cls : (quotClasses s).Nonempty := quotClasses_nonempty s
  obtain ⟨c_min, _, hc_min_le⟩ :=
    Finset.exists_min_image (quotClasses s) (fun c => (congruenceClass s c).card) hne_cls
  set m := (congruenceClass s c_min).card
  have hm : 2 ≤ m := hfat c_min
  have hmin_cls : ∀ c : Quotient s, m ≤ (congruenceClass s c).card := fun c =>
    hc_min_le c (mem_quotClasses s c)
  obtain ⟨u, huSync, hulen⟩ := quotientDFA_pin_frankl_bound A hSync s hcong
  obtain ⟨w, hwSync, hwlen⟩ :=
    fat_congruence_sum_bound A hSC hSync s hcong m hm hmin_cls c_min rfl u huSync
  refine ⟨w, hwSync, ?_⟩
  set k := numClasses s
  set n := Fintype.card Q
  set d := m - 1
  set y : Quotient s → ℕ := fun c => (congruenceClass s c).card - m
  set Y := ∑ c ∈ quotClasses s, y c
  have hsum_s : ∑ c ∈ quotClasses s, (congruenceClass s c).card = n :=
    sum_card_congruenceClass s
  have hn_eq : n = Y + k * m := by
    have hsplit : ∑ c ∈ quotClasses s, (congruenceClass s c).card =
        ∑ c ∈ quotClasses s, (y c + m) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      have := hmin_cls c
      dsimp [y]
      omega
    rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hsum_s
    exact hsum_s.symm
  have hsum_sq :
      (∑ c ∈ quotClasses s, ((congruenceClass s c).card : ℤ) ^ 2) ≤
        (Y : ℤ) ^ 2 + 2 * (m : ℤ) * (Y : ℤ) + (k : ℤ) * (m : ℤ) ^ 2 := by
    have hsq_nat : ∑ c ∈ quotClasses s, (y c) ^ 2 ≤ Y ^ 2 := sum_sq_le_sq_sum (quotClasses s) y
    have hsq_int : (∑ c ∈ quotClasses s, ((y c : ℤ) ^ 2)) ≤ (Y : ℤ) ^ 2 := by
      exact_mod_cast hsq_nat
    have hexpand :
        (∑ c ∈ quotClasses s, ((congruenceClass s c).card : ℤ) ^ 2) =
          (∑ c ∈ quotClasses s, ((y c : ℤ) ^ 2)) +
            2 * (m : ℤ) * (Y : ℤ) + (k : ℤ) * (m : ℤ) ^ 2 := by
      have hterm :
          (∑ c ∈ quotClasses s, ((congruenceClass s c).card : ℤ) ^ 2) =
            ∑ c ∈ quotClasses s, ((y c : ℤ) ^ 2 + 2 * (m : ℤ) * (y c : ℤ) + (m : ℤ) ^ 2) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hc_eq : ((congruenceClass s c).card : ℤ) = (y c : ℤ) + (m : ℤ) := by
          have := hmin_cls c
          dsimp [y]
          omega
        rw [hc_eq]
        ring
      rw [hterm, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      have hY_cast : (∑ c ∈ quotClasses s, (y c : ℤ)) = (Y : ℤ) := by
        exact_mod_cast rfl
      rw [hY_cast]
      change (∑ c ∈ quotClasses s, (y c : ℤ) ^ 2) + 2 * (m : ℤ) * (Y : ℤ) +
          (k : ℤ) * (m : ℤ) ^ 2 = _
      ring
    linarith
  have hsum_choose_int :
      (6 * ∑ c ∈ quotClasses s,
        (((congruenceClass s c).card + 1).choose 3 -
          ((congruenceClass s c).card - m + 2).choose 3) : ℤ) ≤
        ((m : ℤ) - 1) * (3 * (Y : ℤ) ^ 2 + (3 * (m : ℤ) + 3) * (Y : ℤ) +
          (k : ℤ) * (m : ℤ) * ((m : ℤ) + 1)) := by
    have hmul_in :
        (6 * ∑ c ∈ quotClasses s,
          (((congruenceClass s c).card + 1).choose 3 -
            ((congruenceClass s c).card - m + 2).choose 3) : ℤ) =
        ∑ c ∈ quotClasses s,
          (d : ℤ) * (3 * ((congruenceClass s c).card : ℤ) ^ 2 -
            3 * (d : ℤ) * ((congruenceClass s c).card : ℤ) + (d : ℤ) ^ 2 - 1) := by
      rw [Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hcm := hmin_cls c
      have harg : (congruenceClass s c).card - m + 2 = (congruenceClass s c).card - d + 1 := by
        omega
      rw [harg, Nat.cast_sub (Nat.choose_le_choose 3 (by omega))]
      exact six_mul_choose_three_sub_int (congruenceClass s c).card d (by omega)
    rw [hmul_in, ← Finset.mul_sum]
    have hd_eq : (d : ℤ) = (m : ℤ) - 1 := by omega
    have hd_nonneg : (0 : ℤ) ≤ (d : ℤ) := by omega
    have hinner :
        (∑ c ∈ quotClasses s,
          (3 * ((congruenceClass s c).card : ℤ) ^ 2 -
            3 * (d : ℤ) * ((congruenceClass s c).card : ℤ) + (d : ℤ) ^ 2 - 1)) =
        3 * (∑ c ∈ quotClasses s, ((congruenceClass s c).card : ℤ) ^ 2) -
          3 * (d : ℤ) * (n : ℤ) + (k : ℤ) * ((d : ℤ) ^ 2 - 1) := by
      have h1 :
          (∑ c ∈ quotClasses s,
            (3 * ((congruenceClass s c).card : ℤ) ^ 2 -
              3 * (d : ℤ) * ((congruenceClass s c).card : ℤ) + (d : ℤ) ^ 2 - 1)) =
          (∑ c ∈ quotClasses s, 3 * ((congruenceClass s c).card : ℤ) ^ 2) -
            (∑ c ∈ quotClasses s, 3 * (d : ℤ) * ((congruenceClass s c).card : ℤ)) +
            ∑ _c ∈ quotClasses s, ((d : ℤ) ^ 2 - 1) := by
        simp only [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
        ring
      rw [h1, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      have hsum_cast : (∑ c ∈ quotClasses s, ((congruenceClass s c).card : ℤ)) = (n : ℤ) := by
        exact_mod_cast hsum_s
      rw [hsum_cast]
      change 3 * (∑ c ∈ quotClasses s, ((congruenceClass s c).card : ℤ) ^ 2) -
          3 * (d : ℤ) * (n : ℤ) + (k : ℤ) * ((d : ℤ) ^ 2 - 1) = _
      rfl
    rw [hinner, hd_eq]
    have hn_cast : (n : ℤ) = (Y : ℤ) + (k : ℤ) * (m : ℤ) := by exact_mod_cast hn_eq
    have hinner_le :
        3 * (∑ c ∈ quotClasses s, ((congruenceClass s c).card : ℤ) ^ 2) -
          3 * ((m : ℤ) - 1) * (n : ℤ) + (k : ℤ) * (((m : ℤ) - 1) ^ 2 - 1) ≤
        3 * (Y : ℤ) ^ 2 + (3 * (m : ℤ) + 3) * (Y : ℤ) + (k : ℤ) * (m : ℤ) * ((m : ℤ) + 1) := by
      rw [hn_cast]
      linarith
    exact mul_le_mul_of_nonneg_left hinner_le (by omega)
  have hk3 : k ≤ k ^ 3 := Nat.le_self_pow (by omega) k
  have h6w :
      (6 * w.length : ℤ) ≤
        ((k : ℤ) ^ 3 + 5 * (k : ℤ) - 6) +
          ((m : ℤ) - 1) * (3 * (Y : ℤ) ^ 2 + (3 * (m : ℤ) + 3) * (Y : ℤ) +
            (k : ℤ) * (m : ℤ) * ((m : ℤ) + 1)) := by
    have hw_int :
        (6 * w.length : ℤ) ≤
          (6 * u.length : ℤ) + 6 * ((k : ℤ) - 1) +
            (6 * ∑ c ∈ quotClasses s,
              (((congruenceClass s c).card + 1).choose 3 -
                ((congruenceClass s c).card - m + 2).choose 3) : ℤ) := by
      have hk1 : 1 ≤ k := by omega
      have hmul6 : 6 * w.length ≤ 6 * u.length + 6 * (k - 1) +
          6 * ∑ c ∈ quotClasses s,
            (((congruenceClass s c).card + 1).choose 3 -
              ((congruenceClass s c).card - m + 2).choose 3) := by
        omega
      have hcast := Int.ofNat_le.mpr hmul6
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_sub hk1] at hcast
      simpa using hcast
    have hu_int : (6 * u.length : ℤ) ≤ (k : ℤ) ^ 3 - (k : ℤ) := by
      have := Int.ofNat_le.mpr hulen
      push_cast [hk3] at this
      exact this
    linarith
  have hsos := fat_cubic_sos (k : ℤ) (m : ℤ) (Y : ℤ) (by omega) (by omega) (by omega) (by omega)
  have h96_int : (96 * w.length : ℤ) ≤ 5 * (n : ℤ) ^ 3 := by
    have hn_cast : (n : ℤ) = (Y : ℤ) + (k : ℤ) * (m : ℤ) := by exact_mod_cast hn_eq
    rw [hn_cast]
    linarith
  exact_mod_cast h96_int

/-- **Theorem S1(b) (`n = 4` Case)**:
Every strongly connected synchronizing `4`-state DFA admitting a nontrivial fat congruence
satisfies `w.length ≤ 4`. -/
theorem fat_congruence_card_four [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSC : A.IsStronglyConnected) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (hk : 2 ≤ numClasses s)
    (hfat : ∀ c : Quotient s, 2 ≤ (congruenceClass s c).card)
    (hn : Fintype.card Q = 4) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ 4 := by
  classical
  have hsum : ∑ c ∈ quotClasses s, (congruenceClass s c).card = 4 := by
    rw [sum_card_congruenceClass, hn]
  have h2k : 2 * numClasses s ≤ 4 := by
    calc 2 * numClasses s = ∑ _c ∈ quotClasses s, 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]; rfl
      _ ≤ ∑ c ∈ quotClasses s, (congruenceClass s c).card :=
          Finset.sum_le_sum fun c _ => hfat c
      _ = 4 := hsum
  have hk2 : numClasses s = 2 := by omega
  have hall2 : ∀ c : Quotient s, (congruenceClass s c).card = 2 := by
    intro c
    by_contra hne
    have hgt : 3 ≤ (congruenceClass s c).card := by
      have := hfat c
      omega
    have hmem := mem_quotClasses s c
    have hsum_ge : 5 ≤ ∑ x ∈ quotClasses s, (congruenceClass s x).card := by
      rw [← Finset.add_sum_erase _ _ hmem]
      have herase_card : ((quotClasses s).erase c).card = 1 := by
        rw [Finset.card_erase_of_mem hmem]
        change numClasses s - 1 = 1
        omega
      have herase_ge : 2 ≤ ∑ x ∈ (quotClasses s).erase c, (congruenceClass s x).card := by
        calc 2 = ∑ _x ∈ (quotClasses s).erase c, 2 := by
              rw [Finset.sum_const, herase_card, smul_eq_mul, one_mul]
          _ ≤ ∑ x ∈ (quotClasses s).erase c, (congruenceClass s x).card :=
              Finset.sum_le_sum fun x _ => hfat x
      omega
    omega
  obtain ⟨c_min, _⟩ := quotClasses_nonempty s
  obtain ⟨u, huSync, hulen⟩ := quotientDFA_pin_frankl_bound A hSync s hcong
  rw [hk2] at hulen
  have hu1 : u.length ≤ 1 := by omega
  obtain ⟨w, hwSync, hwlen⟩ :=
    fat_congruence_sum_bound A hSC hSync s hcong 2 le_rfl hfat c_min (hall2 c_min) u huSync
  refine ⟨w, hwSync, ?_⟩
  have hsum_choose :
      (∑ c ∈ quotClasses s,
        (((congruenceClass s c).card + 1).choose 3 -
          ((congruenceClass s c).card - 2 + 2).choose 3)) = 2 := by
    calc (∑ c ∈ quotClasses s,
            (((congruenceClass s c).card + 1).choose 3 -
              ((congruenceClass s c).card - 2 + 2).choose 3))
        = ∑ _c ∈ quotClasses s, 1 := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [hall2 c]
            decide
      _ = numClasses s := by simp [numClasses]
      _ = 2 := hk2
  rw [hsum_choose, hk2] at hwlen
  omega

end TheoremS1b

/-! ## Part 6: Theorem S1(c) — Equipartition Congruence Collapse (No Strong Connectivity Needed) -/

section TheoremS1c

variable {Q α : Type*}

/-- **Theorem S1(c) (Equipartition Compression Bound — No Strong Connectivity Needed)**:
If `A` is any synchronizing DFA admitting an equipartition congruence (`k` classes all of size
`m ≥ 2`), and `u` synchronizes `A / ~`, then `A` admits a synchronizing word `w` with
`6 * w.length ≤ 6 * u.length + numClasses s * (m ^ 3 - m)`. -/
theorem equipartition_congruence_bound [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (m : ℕ) (hm : 2 ≤ m)
    (hequi : ∀ c : Quotient s, (congruenceClass s c).card = m)
    (u : List α) (hu : (quotientDFA A s hcong.compat).IsSyncWord u) :
    ∃ w : List α, A.IsSyncWord w ∧
      6 * w.length ≤ 6 * u.length + numClasses s * (m ^ 3 - m) := by
  classical
  rcases hu with ⟨c₀, hc₀⟩
  let S₀ := A.image Finset.univ u
  have hS₀_sub : S₀ ⊆ congruenceClass s c₀ :=
    isSyncWord_quotientDFA_image_subset A s hcong.compat hc₀
  have hS₀_ne : S₀.Nonempty := by
    obtain ⟨q⟩ := ‹Nonempty Q›
    exact ⟨A.eval q u, by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩⟩
  have hS₀_pos : 1 ≤ S₀.card := Finset.card_pos.mpr hS₀_ne
  have hS₀_le : S₀.card ≤ m := by
    rw [← hequi c₀]
    exact Finset.card_le_card hS₀_sub
  obtain ⟨z, hz1, hzlen⟩ :=
    block_compress_hockey_stick A hSync s hcong m hm (fun c => (hequi c).ge)
      c₀ S₀ hS₀_sub hS₀_pos hS₀_le
  refine ⟨u ++ z, ?_, ?_⟩
  · rw [A.isSyncWord_iff_card_image_univ_eq_one, DFA.image_append]
    exact hz1
  · have hsum_eval :
        (∑ c ∈ quotClasses s,
          (((congruenceClass s c).card + 1).choose 3 -
            ((congruenceClass s c).card - m + 2).choose 3)) =
        numClasses s * (m + 1).choose 3 := by
      calc (∑ c ∈ quotClasses s,
              (((congruenceClass s c).card + 1).choose 3 -
                ((congruenceClass s c).card - m + 2).choose 3))
          = ∑ _c ∈ quotClasses s, (m + 1).choose 3 := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [hequi c]
              have h0 : (m - m + 2).choose 3 = 0 := by
                have hsub : m - m + 2 = 2 := by omega
                rw [hsub]
                decide
              rw [h0, Nat.sub_zero]
        _ = numClasses s * (m + 1).choose 3 := by
            rw [Finset.sum_const, smul_eq_mul]
            rfl
    rw [hsum_eval] at hzlen
    rw [List.length_append, mul_add]
    have h6z : 6 * z.length ≤ numClasses s * (m ^ 3 - m) := by
      calc 6 * z.length ≤ 6 * (numClasses s * (m + 1).choose 3) := Nat.mul_le_mul_left 6 hzlen
        _ = numClasses s * (6 * (m + 1).choose 3) := by ring
        _ = numClasses s * (m ^ 3 - m) := by rw [six_mul_choose_three m]
    omega

/-- Exact division form for block size `m = 2`: `w.length ≤ u.length + Fintype.card Q / 2`. -/
theorem equipartition_block_two_bound [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (hequi : ∀ c : Quotient s, (congruenceClass s c).card = 2)
    (u : List α) (hu : (quotientDFA A s hcong.compat).IsSyncWord u) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ u.length + Fintype.card Q / 2 := by
  obtain ⟨w, hwSync, hwlen⟩ :=
    equipartition_congruence_bound A hSync s hcong 2 le_rfl hequi u hu
  have hn : Fintype.card Q = numClasses s * 2 := by
    rw [← sum_card_congruenceClass s]
    calc ∑ c ∈ quotClasses s, (congruenceClass s c).card
        = ∑ _c ∈ quotClasses s, 2 := Finset.sum_congr rfl fun c _ => hequi c
      _ = numClasses s * 2 := by rw [Finset.sum_const, smul_eq_mul]; rfl
  refine ⟨w, hwSync, ?_⟩
  omega

private theorem card_eq_numClasses_mul_of_equipartition [Fintype Q]
    (s : Setoid Q) (m : ℕ) (hequi : ∀ c : Quotient s, (congruenceClass s c).card = m) :
    Fintype.card Q = numClasses s * m := by
  rw [← sum_card_congruenceClass s]
  calc ∑ c ∈ quotClasses s, (congruenceClass s c).card
      = ∑ _c ∈ quotClasses s, m := Finset.sum_congr rfl fun c _ => hequi c
    _ = numClasses s * m := by rw [Finset.sum_const, smul_eq_mul]; rfl

/-- **Theorem S1(c)(1) (Zero-Error `1/24` Cubic Collapse — No Strong Connectivity Needed)**:
Every synchronizing DFA on `n ≥ 6` states admitting an equipartition congruence (`k ≥ 2` classes
all of size `m ≥ 2`) admits a synchronizing word `w` with `24 * w.length ≤ n ^ 3`. -/
theorem equipartition_congruence_one_twenty_fourth [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (m : ℕ) (hm : 2 ≤ m) (hk : 2 ≤ numClasses s)
    (hequi : ∀ c : Quotient s, (congruenceClass s c).card = m)
    (hn : 6 ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ 24 * w.length ≤ (Fintype.card Q) ^ 3 := by
  obtain ⟨u, huSync, hulen⟩ := quotientDFA_pin_frankl_bound A hSync s hcong
  obtain ⟨w, hwSync, hwlen⟩ :=
    equipartition_congruence_bound A hSync s hcong m hm hequi u huSync
  refine ⟨w, hwSync, ?_⟩
  set k := numClasses s
  have hn_eq : Fintype.card Q = k * m := card_eq_numClasses_mul_of_equipartition s m hequi
  have hk3 : k ≤ k ^ 3 := Nat.le_self_pow (by omega) k
  have hm3 : m ≤ m ^ 3 := Nat.le_self_pow (by omega) m
  have h6w : 6 * w.length ≤ (k ^ 3 - k) + k * (m ^ 3 - m) := by omega
  have h24_int : (24 * w.length : ℤ) ≤ ((k : ℤ) * (m : ℤ)) ^ 3 := by
    have h6_int : (6 * w.length : ℤ) ≤ ((k : ℤ) ^ 3 - (k : ℤ)) + (k : ℤ) * ((m : ℤ) ^ 3 - (m : ℤ)) := by
      have := Int.ofNat_le.mpr h6w
      push_cast [hk3, hm3] at this
      exact this
    have hfact :
        ((k : ℤ) * (m : ℤ)) ^ 3 -
          4 * (((k : ℤ) ^ 3 - (k : ℤ)) + (k : ℤ) * ((m : ℤ) ^ 3 - (m : ℤ))) =
        (k : ℤ) * (((k : ℤ) ^ 2 - 4) * ((m : ℤ) ^ 3 - 4) + 4 * ((m : ℤ) - 3)) := by
      ring
    have hnonneg :
        0 ≤ ((k : ℤ) ^ 2 - 4) * ((m : ℤ) ^ 3 - 4) + 4 * ((m : ℤ) - 3) := by
      by_cases hm2 : m = 2
      · have hk3' : 3 ≤ k := by
          rw [hn_eq, hm2] at hn
          omega
        have hm_z : (m : ℤ) = 2 := by exact_mod_cast hm2
        rw [hm_z]
        have hk_z : (3 : ℤ) ≤ k := by exact_mod_cast hk3'
        nlinarith
      · have hm3' : (3 : ℤ) ≤ m := by omega
        have hk2' : (2 : ℤ) ≤ k := by exact_mod_cast hk
        have h1 : (0 : ℤ) ≤ (k : ℤ) ^ 2 - 4 := by nlinarith
        have h2 : (0 : ℤ) ≤ (m : ℤ) ^ 3 - 4 := by
          have hm_sq : (9 : ℤ) ≤ (m : ℤ) ^ 2 := by nlinarith
          nlinarith
        have h3 : (0 : ℤ) ≤ 4 * ((m : ℤ) - 3) := by linarith
        nlinarith [mul_nonneg h1 h2]
    have hk_pos : (0 : ℤ) ≤ k := by omega
    nlinarith [mul_nonneg hk_pos hnonneg]
  rw [hn_eq]
  exact_mod_cast h24_int

/-- **Theorem S1(c) (`n = 4` Case)**:
Every synchronizing `4`-state DFA with an equipartition congruence (`k = m = 2`) has `w.length ≤ 3`. -/
theorem equipartition_congruence_card_four [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (m : ℕ) (hm : 2 ≤ m) (hk : 2 ≤ numClasses s)
    (hequi : ∀ c : Quotient s, (congruenceClass s c).card = m)
    (hn : Fintype.card Q = 4) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ 3 := by
  have hn_eq : Fintype.card Q = numClasses s * m :=
    card_eq_numClasses_mul_of_equipartition s m hequi
  have hk2 : numClasses s = 2 := by nlinarith
  have hm2 : m = 2 := by nlinarith
  obtain ⟨u, huSync, hulen⟩ := quotientDFA_pin_frankl_bound A hSync s hcong
  obtain ⟨w, hwSync, hwlen⟩ :=
    equipartition_congruence_bound A hSync s hcong m hm hequi u huSync
  rw [hk2] at hulen
  rw [hk2, hm2] at hwlen
  refine ⟨w, hwSync, ?_⟩
  omega

/-- **Theorem S1(c)(2) (Unconditional Exact Černý Window — No Strong Connectivity Needed)**:
If `A` is any synchronizing DFA with an equipartition congruence (`k ≥ 2` classes of size `m ≥ 2`)
satisfying `m ≤ 2 * k` and `k ≤ 2 * m ^ 2`, then `A` unconditionally satisfies Černý's bound
`w.length ≤ (Fintype.card Q - 1) ^ 2`. -/
theorem equipartition_congruence_cerny_window [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (m : ℕ) (hm : 2 ≤ m) (hk : 2 ≤ numClasses s)
    (hequi : ∀ c : Quotient s, (congruenceClass s c).card = m)
    (hwin1 : m ≤ 2 * numClasses s) (hwin2 : numClasses s ≤ 2 * m ^ 2) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  set k := numClasses s
  have hn_eq : Fintype.card Q = k * m := card_eq_numClasses_mul_of_equipartition s m hequi
  by_cases hn4 : Fintype.card Q = 4
  · obtain ⟨w, hwSync, hwlen⟩ :=
      equipartition_congruence_card_four A hSync s hcong m hm hk hequi hn4
    refine ⟨w, hwSync, ?_⟩
    rw [hn4]
    omega
  · have hn6 : 6 ≤ Fintype.card Q := by
      by_cases hkm : k = 2 ∧ m = 2
      · exfalso; apply hn4; rw [hn_eq, hkm.1, hkm.2]
      · have h3 : 3 ≤ k ∨ 3 ≤ m := by omega
        rcases h3 with hk3 | hm3 <;> nlinarith
    obtain ⟨u, huSync, hulen⟩ := quotientDFA_pin_frankl_bound A hSync s hcong
    obtain ⟨w, hwSync, hwlen⟩ :=
      equipartition_congruence_bound A hSync s hcong m hm hequi u huSync
    refine ⟨w, hwSync, ?_⟩
    have hk3_le : k ^ 3 ≤ 2 * (k * m) ^ 2 := by
      have h1 : k ^ 3 = k ^ 2 * k := by ring
      have h2 : k ^ 2 * k ≤ k ^ 2 * (2 * m ^ 2) := Nat.mul_le_mul_left (k ^ 2) hwin2
      calc k ^ 3 = k ^ 2 * k := h1
        _ ≤ k ^ 2 * (2 * m ^ 2) := h2
        _ = 2 * (k * m) ^ 2 := by ring
    have hkm3_le : k * m ^ 3 ≤ 2 * (k * m) ^ 2 := by
      have h1 : k * m ^ 3 = (k * m ^ 2) * m := by ring
      have h2 : (k * m ^ 2) * m ≤ (k * m ^ 2) * (2 * k) := Nat.mul_le_mul_left (k * m ^ 2) hwin1
      calc k * m ^ 3 = (k * m ^ 2) * m := h1
        _ ≤ (k * m ^ 2) * (2 * k) := h2
        _ = 2 * (k * m) ^ 2 := by ring
    have h6w : 6 * w.length ≤ 4 * (Fintype.card Q) ^ 2 := by
      have hsub1 : k ^ 3 - k ≤ k ^ 3 := Nat.sub_le _ _
      have hsub2 : k * (m ^ 3 - m) ≤ k * m ^ 3 := Nat.mul_le_mul_left k (Nat.sub_le _ _)
      change 6 * u.length ≤ k ^ 3 - k at hulen
      change 6 * w.length ≤ 6 * u.length + k * (m ^ 3 - m) at hwlen
      rw [hn_eq]
      omega
    have h4_le_6 : 4 * (Fintype.card Q) ^ 2 ≤ 6 * (Fintype.card Q - 1) ^ 2 := by
      set n := Fintype.card Q
      zify [show 1 ≤ n by omega]
      have hn6' : (6 : ℤ) ≤ n := by exact_mod_cast hn6
      nlinarith
    omega

/-- **Theorem S1(c)(3) (Conditional Černý Preservation — No Strong Connectivity Needed)**:
If `A` is any synchronizing DFA with an equipartition congruence (`k ≥ 2` classes of size `m ≥ 2`),
`u` synchronizes `A / ~` with `u.length ≤ (k - 1) ^ 2`, and `2 * m ^ 2 ≤ 9 * Fintype.card Q - 10`,
then `A` satisfies Černý's bound `w.length ≤ (Fintype.card Q - 1) ^ 2`. -/
theorem equipartition_congruence_preserves_cerny [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (s : Setoid Q) (hcong : A.IsCongruence s.r)
    (m : ℕ) (hm : 2 ≤ m) (hk : 2 ≤ numClasses s)
    (hequi : ∀ c : Quotient s, (congruenceClass s c).card = m)
    (u : List α) (hu : (quotientDFA A s hcong.compat).IsSyncWord u)
    (hulen : u.length ≤ (numClasses s - 1) ^ 2)
    (hm_bound : 2 * m ^ 2 ≤ 9 * Fintype.card Q - 10) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hwSync, hwlen⟩ :=
    equipartition_congruence_bound A hSync s hcong m hm hequi u hu
  refine ⟨w, hwSync, ?_⟩
  set k := numClasses s
  set n := Fintype.card Q
  have hn_eq : n = k * m := card_eq_numClasses_mul_of_equipartition s m hequi
  have h2k_le : 2 * k ≤ n := by
    rw [hn_eq]
    calc 2 * k = k * 2 := by ring
      _ ≤ k * m := Nat.mul_le_mul_left k hm
  have hn4 : 4 ≤ n := by omega
  have hm3 : m ≤ m ^ 3 := Nat.le_self_pow (by omega) m
  have h6w_int : (6 * w.length : ℤ) ≤ 6 * ((n : ℤ) - 1) ^ 2 := by
    have h6_bound : (6 * w.length : ℤ) ≤ 6 * ((k : ℤ) - 1) ^ 2 + (k : ℤ) * ((m : ℤ) ^ 3 - (m : ℤ)) := by
      have hnat : 6 * w.length ≤ 6 * (k - 1) ^ 2 + k * (m ^ 3 - m) := by omega
      have := Int.ofNat_le.mpr hnat
      push_cast [show 1 ≤ k by omega, hm3] at this
      exact this
    have hn_z : (n : ℤ) = (k : ℤ) * (m : ℤ) := by exact_mod_cast hn_eq
    have h2k_z : 2 * (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast h2k_le
    have hk_z : (2 : ℤ) ≤ k := by exact_mod_cast hk
    have hn4_z : (4 : ℤ) ≤ n := by exact_mod_cast hn4
    have hm_z : 2 * (m : ℤ) ^ 2 ≤ 9 * (n : ℤ) - 10 := by
      have h9n : 10 ≤ 9 * n := by omega
      have := Int.ofNat_le.mpr hm_bound
      push_cast [h9n] at this
      exact this
    have hsq_k : 4 * ((k : ℤ) - 1) ^ 2 ≤ ((n : ℤ) - 2) ^ 2 := by nlinarith
    have hdiff : 9 * (n : ℤ) ^ 2 - 12 * (n : ℤ) ≤ 12 * ((n : ℤ) - 1) ^ 2 - 12 * ((k : ℤ) - 1) ^ 2 := by
      linarith
    have hprod : 2 * (k : ℤ) * ((m : ℤ) ^ 3 - (m : ℤ)) ≤ 9 * (n : ℤ) ^ 2 - 12 * (n : ℤ) := by
      have hfactor : 2 * (k : ℤ) * ((m : ℤ) ^ 3 - (m : ℤ)) = (n : ℤ) * (2 * (m : ℤ) ^ 2 - 2) := by
        rw [hn_z]; ring
      rw [hfactor]
      have hinner : 2 * (m : ℤ) ^ 2 - 2 ≤ 9 * (n : ℤ) - 12 := by linarith
      nlinarith
    linarith
  have h6w_nat : 6 * w.length ≤ 6 * (n - 1) ^ 2 := by
    zify [show 1 ≤ n by omega]
    exact h6w_int
  omega

end TheoremS1c

end Cerny
