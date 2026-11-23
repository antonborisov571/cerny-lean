import Cerny.AlpogePrimitive
import Cerny.SmallCases

/-!
# World-Record Reset Bound for Primitive Volkov D6 Automata (Theorem T16: `2n² - 8n + 9`)

This file formalizes **Theorem T16** (`docs/round3_subcubic_and_d6.md`), unconditionally
**beating Zhu (FSTTCS 2024)'s standing published bound `2n² - 7n + 7`** for every DFA on
`n ≥ 4` states possessing a primitive permutation letter set `S` and a rank-`(n - 1)` letter `a`
— with **ZERO linear algebra**:

* **Lemma T16.1 (`VolkovD6.weakCount_pred_two_eq_one`, `VolkovD6.exists_ryEdge_crossing`)**:
  Weak-component coarsening yields `w(n - 2) = 1`, so every nonempty proper subset `W ⊂ Q`
  has a boundary-crossing edge in `E_{n - 2}`.
* **Lemma T16.2 (`VolkovD6.sccCount_half_eq_one_of_acyclic`)**:
  **DAG-Shift Teleportation** (needs ONLY transitivity!): if `E_{n - 2}` is acyclic
  (`c(n - 2) = n`), then `E_{n - 2}` has a unique sink `q_snk` and unique source `q_src`;
  pigeonhole on radius-`⌊n/2⌋` balls yields a meeting state `w` whose shifts make
  `E_{n - 2 + ⌊n/2⌋}` strongly connected (`c(n - 2 + ⌊n/2⌋) = 1`)!
* **Lemma T16.3 (`VolkovD6.sccCount_pred_one_ne_pred_two`)**:
  **2-Block Shift-Isolation Contradiction**: for `n ≥ 5`, if `c(n - 2) = n - 1` (unique
  2-block `W`), then `c(n - 1) ≠ n - 2` (else `E_{n - 1}` has exact two 2-blocks `U` source
  and `V` sink, some `b* ∈ S` maps `W` to the other 2-block, isolating `W` in `E_{n - 2}` and
  contradicting `w(n - 2) = 1`!).
* **Theorem T16 (`Cerny.primitive_defectOne_beats_zhu_ge_five`, `Cerny.primitive_defectOne_beats_zhu`)**:
  Every primitive Volkov D6 DFA is automatically synchronizing with:
  - `L_pos ≤ 2n - 5` and `w.length ≤ 1 + (n - 2) * (2 * n - 4) = 2n² - 8n + 9` for all `n ≥ 5`,
  - `w.length ≤ 2n² - 8n + 9` for ALL `n ≥ 4` (combining with `cerny_card_le_four` at `n = 4`),
  strictly beating Zhu (2024)'s `2n² - 7n + 7` by `n - 2` for every `n ≥ 4`!
-/

namespace Cerny

universe u v

namespace VolkovD6

open AlpogePrimitive

variable {Q : Type u} {α : Type v}

/-! ### Helper: Bijectivity of `S`-words & Multi-Step `ryReach` Shift -/

private lemma bijective_eval_of_mem {A : DFA Q α} {S : Set α}
    (hBij : ∀ b ∈ S, Function.Bijective (fun q => A.step q b)) :
    ∀ g : List α, (∀ b ∈ g, b ∈ S) → Function.Bijective (fun q => A.eval q g) := by
  intro g
  induction g with
  | nil => intro _; exact Function.bijective_id
  | cons b g ih =>
    intro hS
    exact (ih fun x hx => hS x (List.mem_cons_of_mem b hx)).comp
      (hBij b (hS b List.mem_cons_self))

private lemma ryReach_eval (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) :
    ∀ (g : List α), (∀ b ∈ g, b ∈ S) → ∀ (k : ℕ) {u v : Q},
      ryReach A S z₀ m₀ k u v →
      ryReach A S z₀ m₀ (k + g.length) (A.eval u g) (A.eval v g) := by
  intro g
  induction g with
  | nil => intro _ k _ _ h; simpa using h
  | cons b g ih =>
    intro hS k u v h
    have hb : b ∈ S := hS b List.mem_cons_self
    have hg : ∀ c ∈ g, c ∈ S := fun c hc => hS c (List.mem_cons_of_mem b hc)
    have h1 : ryReach A S z₀ m₀ (k + 1) (A.step u b) (A.step v b) :=
      ryReach_step A S z₀ m₀ k hb h
    have h2 := ih hg (k + 1) h1
    have hlen : k + 1 + g.length = k + (b :: g).length := by simp; omega
    rw [hlen] at h2
    exact h2

/-! ### Lemma T16.1: Weak-Component Coarsening (`w(n - 2) = 1`) -/

/-- Weakly connected component equivalence relation of `E_k`. -/
def weakSetoid (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (k : ℕ) : Setoid Q where
  r := Relation.EqvGen (ryEdge A S z₀ m₀ k)
  iseqv := Relation.EqvGen.is_equivalence _

/-- Number of weakly connected components of `E_k`. -/
noncomputable def weakCount [Fintype Q] (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (k : ℕ) : ℕ := by
  classical
  exact Fintype.card (Quotient (weakSetoid A S z₀ m₀ k))

private lemma weak_mono (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) {j k : ℕ} (hjk : j ≤ k)
    {p q : Q} (h : (weakSetoid A S z₀ m₀ j).r p q) : (weakSetoid A S z₀ m₀ k).r p q := by
  induction h with
  | rel u v huv => exact Relation.EqvGen.rel u v (ryEdge_mono A S z₀ m₀ hjk huv)
  | refl x => exact Relation.EqvGen.refl x
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private lemma weak_step (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (k : ℕ) {b : α} (hb : b ∈ S)
    {p q : Q} (h : (weakSetoid A S z₀ m₀ k).r p q) :
    (weakSetoid A S z₀ m₀ (k + 1)).r (A.step p b) (A.step q b) := by
  induction h with
  | rel u v huv => exact Relation.EqvGen.rel _ _ (ryEdge_step A S z₀ m₀ k hb huv)
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private lemma weakCount_pos [Fintype Q] [Nonempty Q] (A : DFA Q α) (S : Set α) (z₀ m₀ : Q)
    (k : ℕ) : 1 ≤ weakCount A S z₀ m₀ k := by
  classical
  obtain ⟨q⟩ := ‹Nonempty Q›
  exact Fintype.card_pos_iff.mpr ⟨Quotient.mk _ q⟩

private lemma weakCount_antitone [Fintype Q] (A : DFA Q α) (S : Set α) (z₀ m₀ : Q)
    {j k : ℕ} (hjk : j ≤ k) : weakCount A S z₀ m₀ k ≤ weakCount A S z₀ m₀ j := by
  classical
  let π : Quotient (weakSetoid A S z₀ m₀ j) → Quotient (weakSetoid A S z₀ m₀ k) :=
    Quotient.lift (Quotient.mk (weakSetoid A S z₀ m₀ k)) fun _ _ h =>
      Quotient.sound (weak_mono A S z₀ m₀ hjk h)
  have hsurj : Function.Surjective π := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  exact Fintype.card_le_of_surjective π hsurj

private lemma weakCount_zero_lt_card [Fintype Q] (A : DFA Q α) (S : Set α) {z₀ m₀ : Q}
    (hzm : z₀ ≠ m₀) : weakCount A S z₀ m₀ 0 < Fintype.card Q := by
  classical
  have hle : weakCount A S z₀ m₀ 0 ≤ Fintype.card Q :=
    Fintype.card_le_of_surjective (Quotient.mk (weakSetoid A S z₀ m₀ 0)) Quotient.mk_surjective
  refine lt_of_le_of_ne hle fun heq => ?_
  have hbij := (Fintype.bijective_iff_surjective_and_card
    (Quotient.mk (weakSetoid A S z₀ m₀ 0))).mpr ⟨Quotient.mk_surjective, heq.symm⟩
  have hedge : ryEdge A S z₀ m₀ 0 z₀ m₀ := ⟨[], le_rfl, fun _ h => absurd h (List.not_mem_nil), rfl, rfl⟩
  have hmk : Quotient.mk (weakSetoid A S z₀ m₀ 0) z₀ = Quotient.mk (weakSetoid A S z₀ m₀ 0) m₀ :=
    Quotient.sound (Relation.EqvGen.rel z₀ m₀ hedge)
  exact hzm (hbij.1 hmk)

private lemma weakCount_strict_dec [Fintype Q] [Nonempty Q] {A : DFA Q α} {S : Set α}
    (hPrim : A.IsPrimitivePermSet S) {z₀ m₀ : Q} (hzm : z₀ ≠ m₀) (k : ℕ)
    (hgt1 : 1 < weakCount A S z₀ m₀ k) :
    weakCount A S z₀ m₀ (k + 1) < weakCount A S z₀ m₀ k := by
  classical
  have hlt : weakCount A S z₀ m₀ k < Fintype.card Q :=
    lt_of_le_of_lt (weakCount_antitone A S z₀ m₀ (Nat.zero_le k))
      (weakCount_zero_lt_card A S hzm)
  have hle : weakCount A S z₀ m₀ (k + 1) ≤ weakCount A S z₀ m₀ k :=
    weakCount_antitone A S z₀ m₀ (Nat.le_succ k)
  refine lt_of_le_of_ne hle fun heq => ?_
  let π : Quotient (weakSetoid A S z₀ m₀ k) → Quotient (weakSetoid A S z₀ m₀ (k + 1)) :=
    Quotient.lift (Quotient.mk (weakSetoid A S z₀ m₀ (k + 1))) fun _ _ h =>
      Quotient.sound (weak_mono A S z₀ m₀ (Nat.le_succ k) h)
  have hsurj : Function.Surjective π := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  have hbij : Function.Bijective π :=
    (Fintype.bijective_iff_surjective_and_card π).mpr ⟨hsurj, heq.symm⟩
  have hinv : ∀ b ∈ S, ∀ p q : Q,
      (weakSetoid A S z₀ m₀ k).r p q → (weakSetoid A S z₀ m₀ k).r (A.step p b) (A.step q b) := by
    intro b hb p q hpq
    have hπeq : π (Quotient.mk _ (A.step p b)) = π (Quotient.mk _ (A.step q b)) :=
      Quotient.sound (weak_step A S z₀ m₀ k hb hpq)
    exact Quotient.exact (hbij.1 hπeq)
  rcases hPrim.2.2 (weakSetoid A S z₀ m₀ k) hinv with hdiag | hall
  · have hinj : Function.Injective (Quotient.mk (weakSetoid A S z₀ m₀ k)) := fun p q h =>
      hdiag p q (Quotient.exact h)
    have hcard : Fintype.card Q = weakCount A S z₀ m₀ k :=
      Fintype.card_of_bijective ⟨hinj, Quotient.mk_surjective⟩
    omega
  · have hsub : Subsingleton (Quotient (weakSetoid A S z₀ m₀ k)) :=
      ⟨fun x y => Quotient.inductionOn₂ x y fun p q => Quotient.sound (hall p q)⟩
    have hle1 : weakCount A S z₀ m₀ k ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega

/-- **Lemma T16.1 (Weak-Component Coarsening)**: `E_{n - 2}` is weakly connected (`w(n - 2) = 1`). -/
theorem weakCount_pred_two_eq_one [Fintype Q] [Nonempty Q] {A : DFA Q α} {S : Set α}
    (hPrim : A.IsPrimitivePermSet S) {z₀ m₀ : Q} (hzm : z₀ ≠ m₀)
    (hn2 : 2 ≤ Fintype.card Q) :
    weakCount A S z₀ m₀ (Fintype.card Q - 2) = 1 := by
  have hiter : ∀ d k : ℕ, weakCount A S z₀ m₀ k ≤ d + 1 → weakCount A S z₀ m₀ (k + d) = 1 := by
    intro d
    induction d with
    | zero =>
      intro k hle
      have hpos := weakCount_pos A S z₀ m₀ k
      simpa using le_antisymm hle hpos
    | succ d ih =>
      intro k hle
      by_cases h1 : weakCount A S z₀ m₀ k = 1
      · have hle' := weakCount_antitone A S z₀ m₀ (Nat.le_add_right k (d + 1))
        have hpos := weakCount_pos A S z₀ m₀ (k + (d + 1))
        omega
      · have hpos := weakCount_pos A S z₀ m₀ k
        have hdec := weakCount_strict_dec hPrim hzm k (by omega)
        have hres := ih (k + 1) (by omega)
        have hadd : k + 1 + d = k + (d + 1) := by omega
        rwa [hadd] at hres
  have h0 := weakCount_zero_lt_card A S hzm
  simpa using hiter (Fintype.card Q - 2) 0 (by omega)

/-- Consequence of Lemma T16.1: every nonempty proper subset `W ⊂ Q` has a boundary-crossing
edge `(u → v)` in `E_{n - 2}` (`¬ (u ∈ W ↔ v ∈ W)`). -/
theorem exists_ryEdge_crossing [Fintype Q] [Nonempty Q] [DecidableEq Q] {A : DFA Q α} {S : Set α}
    (hPrim : A.IsPrimitivePermSet S) {z₀ m₀ : Q} (hzm : z₀ ≠ m₀)
    (hn2 : 2 ≤ Fintype.card Q)
    {W : Finset Q} (hW_ne : W.Nonempty) (hW_proper : W ≠ Finset.univ) :
    ∃ u v : Q, ryEdge A S z₀ m₀ (Fintype.card Q - 2) u v ∧ ¬ (u ∈ W ↔ v ∈ W) := by
  classical
  have hw1 : weakCount A S z₀ m₀ (Fintype.card Q - 2) = 1 :=
    weakCount_pred_two_eq_one hPrim hzm hn2
  have hsub : Subsingleton (Quotient (weakSetoid A S z₀ m₀ (Fintype.card Q - 2))) :=
    Fintype.card_le_one_iff_subsingleton.mp hw1.le
  rcases hW_ne with ⟨p₀, hp₀⟩
  obtain ⟨q₀, _, hq₀⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ W, hW_proper⟩)
  by_contra hall
  push Not at hall
  have hrel : (weakSetoid A S z₀ m₀ (Fintype.card Q - 2)).r p₀ q₀ :=
    Quotient.exact (hsub.elim (Quotient.mk _ p₀) (Quotient.mk _ q₀))
  have hpres : ∀ x y : Q, (weakSetoid A S z₀ m₀ (Fintype.card Q - 2)).r x y → (x ∈ W ↔ y ∈ W) := by
    intro x y hxy
    induction hxy with
    | rel u v huv => exact hall u v huv
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  exact hq₀ ((hpres p₀ q₀ hrel).mp hp₀)

/-! ### Lemma T16.2: DAG-Shift Teleportation (`c(n - 2) = n → c(n - 2 + n / 2) = 1`) -/

/-- Radius-`t` Schreier ball from `q₀` under `S`. -/
private noncomputable def schreierBall [Fintype Q] (A : DFA Q α) (S : Set α) (q₀ : Q) (t : ℕ) :
    Finset Q := by
  classical
  exact Finset.univ.filter (fun q => ∃ g : List α, g.length ≤ t ∧ (∀ b ∈ g, b ∈ S) ∧ A.eval q₀ g = q)

private lemma card_schreierBall_ge [Fintype Q] {A : DFA Q α} {S : Set α}
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S) ∧ A.eval p g = q)
    (q₀ : Q) :
    ∀ t : ℕ, min (t + 1) (Fintype.card Q) ≤ (schreierBall A S q₀ t).card := by
  classical
  intro t
  induction t with
  | zero =>
    have hmem : q₀ ∈ schreierBall A S q₀ 0 := by
      simp only [schreierBall, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨[], le_rfl, fun _ h => absurd h (List.not_mem_nil), rfl⟩
    have hpos : 1 ≤ (schreierBall A S q₀ 0).card := Finset.card_pos.mpr ⟨q₀, hmem⟩
    exact le_trans (min_le_left 1 (Fintype.card Q)) hpos
  | succ t ih =>
    have hsub : schreierBall A S q₀ t ⊆ schreierBall A S q₀ (t + 1) := by
      intro q hq
      simp only [schreierBall, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rcases hq with ⟨g, hlen, hgS, hge⟩
      exact ⟨g, by omega, hgS, hge⟩
    by_cases hfull : schreierBall A S q₀ t = Finset.univ
    · have hfull' : schreierBall A S q₀ (t + 1) = Finset.univ :=
        Finset.eq_univ_iff_forall.mpr fun x => hsub (hfull ▸ Finset.mem_univ x)
      rw [hfull', Finset.card_univ]
      exact min_le_right _ _
    · have hstrict : (schreierBall A S q₀ t).card < (schreierBall A S q₀ (t + 1)).card := by
        refine lt_of_le_of_ne (Finset.card_le_card hsub) fun heq => ?_
        have hball_eq : schreierBall A S q₀ t = schreierBall A S q₀ (t + 1) :=
          Finset.eq_of_subset_of_card_le hsub heq.symm.le
        have hclosed : ∀ x ∈ schreierBall A S q₀ t, ∀ b ∈ S, A.step x b ∈ schreierBall A S q₀ t := by
          intro x hx b hb
          rw [hball_eq]
          simp only [schreierBall, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          rcases hx with ⟨g, hlen, hgS, hge⟩
          refine ⟨g ++ [b], by simp; omega, ?_, ?_⟩
          · intro c hc
            simp only [List.mem_append, List.mem_singleton] at hc
            rcases hc with hc | rfl
            · exact hgS c hc
            · exact hb
          · rw [DFA.eval_append, hge, DFA.eval_singleton]
        have hall : ∀ g : List α, (∀ b ∈ g, b ∈ S) → A.eval q₀ g ∈ schreierBall A S q₀ t := by
          intro g
          induction g using List.reverseRecOn with
          | nil =>
            intro _
            simp only [DFA.eval_nil, schreierBall, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨[], Nat.zero_le t, fun _ h => absurd h (List.not_mem_nil), rfl⟩
          | append_singleton g b ihg =>
            intro hS
            have hgS : ∀ c ∈ g, c ∈ S := fun c hc => hS c (List.mem_append_left [b] hc)
            have hb : b ∈ S := hS b (List.mem_append_right g List.mem_cons_self)
            rw [DFA.eval_append, DFA.eval_singleton]
            exact hclosed _ (ihg hgS) b hb
        obtain ⟨y, _, hy⟩ := Finset.exists_of_ssubset
          (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hfull⟩)
        obtain ⟨g, hgS, hgy⟩ := hTrans q₀ y
        exact hy (hgy ▸ hall g hgS)
      have hle_n : (schreierBall A S q₀ t).card < Fintype.card Q := by
        have := Finset.card_le_univ (schreierBall A S q₀ t)
        have hne : (schreierBall A S q₀ t).card ≠ Fintype.card Q := fun hc =>
          hfull (Finset.eq_univ_of_card _ hc)
        omega
      omega

/-- **Lemma T16.2 (DAG-Shift Teleportation — Needs ONLY Transitivity!)**:
If `E_{n - 2}` is acyclic (`sccCount (n - 2) = n`), then `E_{n - 2 + n / 2}` is already
strongly connected (`sccCount (n - 2 + n / 2) = 1`). -/
theorem sccCount_half_eq_one_of_acyclic [Fintype Q] [Nonempty Q] [DecidableEq Q]
    {A : DFA Q α} {S : Set α} {z₀ m₀ : Q}
    (hBij : ∀ b ∈ S, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S) ∧ A.eval p g = q)
    (hzm : z₀ ≠ m₀) (hn2 : 2 ≤ Fintype.card Q)
    (hacyc : sccCount A S z₀ m₀ (Fintype.card Q - 2) = Fintype.card Q) :
    sccCount A S z₀ m₀ (Fintype.card Q - 2 + Fintype.card Q / 2) = 1 := by
  classical
  let k := Fintype.card Q - 2
  have hbij_mk : Function.Bijective (Quotient.mk (sccSetoid A S z₀ m₀ k)) := by
    refine (Fintype.bijective_iff_surjective_and_card _).mpr ⟨Quotient.mk_surjective, ?_⟩
    simpa only [sccCount, k] using hacyc.symm
  have hantisymm : ∀ {x y : Q}, ryReach A S z₀ m₀ k x y → ryReach A S z₀ m₀ k y x → x = y := by
    intro x y hxy hyx
    exact hbij_mk.1 (Quotient.sound ⟨hxy, hyx⟩)
  have hirrefl : ∀ q : Q, ¬ ryEdge A S z₀ m₀ k q q := by
    rintro q ⟨g, _, hgS, hgz, hgm⟩
    exact hzm ((bijective_eval_of_mem hBij g hgS).1 (hgz.trans hgm.symm))
  -- Helper: maximal element of any nonempty upward-closed subset under `ryReach k`
  have exists_max_reach : ∀ x : Q, ∃ m : Q, ryReach A S z₀ m₀ k x m ∧
      ∀ y : Q, ryReach A S z₀ m₀ k m y → y = m := by
    intro x
    let R : Finset Q := Finset.univ.filter (fun y => ryReach A S z₀ m₀ k x y)
    have hR_ne : R.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, .refl⟩⟩
    have hex : ∃ c : ℕ, ∃ m ∈ R, (R.filter (fun y => ryReach A S z₀ m₀ k m y)).card = c := by
      rcases hR_ne with ⟨m₀', hm₀'⟩; exact ⟨_, m₀', hm₀', rfl⟩
    obtain ⟨m, hmR, hmeq⟩ := Nat.find_spec hex
    have hmin : ∀ y ∈ R, (R.filter (fun z => ryReach A S z₀ m₀ k m z)).card ≤
        (R.filter (fun z => ryReach A S z₀ m₀ k y z)).card := fun y hy =>
      hmeq ▸ Nat.find_min' hex ⟨y, hy, rfl⟩
    have hxm : ryReach A S z₀ m₀ k x m := (Finset.mem_filter.mp hmR).2
    refine ⟨m, hxm, fun y hmy => ?_⟩
    have hyR : y ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hxm.trans hmy⟩
    have hsub : R.filter (fun z => ryReach A S z₀ m₀ k y z) ⊆
        R.filter (fun z => ryReach A S z₀ m₀ k m z) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hmy.trans hz.2⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (hmin y hyR)
    have hm_in : m ∈ R.filter (fun z => ryReach A S z₀ m₀ k y z) := by
      rw [heq, Finset.mem_filter]; exact ⟨hmR, .refl⟩
    exact hantisymm (Finset.mem_filter.mp hm_in).2 hmy
  -- Dual helper: minimal element of any nonempty downward-closed subset under `ryReach k`
  have exists_min_reach : ∀ x : Q, ∃ m : Q, ryReach A S z₀ m₀ k m x ∧
      ∀ y : Q, ryReach A S z₀ m₀ k y m → y = m := by
    intro x
    let R : Finset Q := Finset.univ.filter (fun y => ryReach A S z₀ m₀ k y x)
    have hR_ne : R.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, .refl⟩⟩
    have hex : ∃ c : ℕ, ∃ m ∈ R, (R.filter (fun y => ryReach A S z₀ m₀ k y m)).card = c := by
      rcases hR_ne with ⟨m₀', hm₀'⟩; exact ⟨_, m₀', hm₀', rfl⟩
    obtain ⟨m, hmR, hmeq⟩ := Nat.find_spec hex
    have hmin : ∀ y ∈ R, (R.filter (fun z => ryReach A S z₀ m₀ k z m)).card ≤
        (R.filter (fun z => ryReach A S z₀ m₀ k z y)).card := fun y hy =>
      hmeq ▸ Nat.find_min' hex ⟨y, hy, rfl⟩
    have hmx : ryReach A S z₀ m₀ k m x := (Finset.mem_filter.mp hmR).2
    refine ⟨m, hmx, fun y hym => ?_⟩
    have hyR : y ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hym.trans hmx⟩
    have hsub : R.filter (fun z => ryReach A S z₀ m₀ k z y) ⊆
        R.filter (fun z => ryReach A S z₀ m₀ k z m) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hz.2.trans hym⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (hmin y hyR)
    have hm_in : m ∈ R.filter (fun z => ryReach A S z₀ m₀ k z y) := by
      rw [heq, Finset.mem_filter]; exact ⟨hmR, .refl⟩
    exact hantisymm hym (Finset.mem_filter.mp hm_in).2
  -- Step 1: Unique sink `q_snk` omitted by `schreierBall z₀ (n - 2)`
  have hball_z_ne : schreierBall A S z₀ k ≠ Finset.univ := by
    intro hfull
    obtain ⟨q_any⟩ := ‹Nonempty Q›
    obtain ⟨m, _, hmax⟩ := exists_max_reach q_any
    have hm_in : m ∈ schreierBall A S z₀ k := hfull ▸ Finset.mem_univ m
    simp only [schreierBall, Finset.mem_filter, Finset.mem_univ, true_and] at hm_in
    rcases hm_in with ⟨g, hglen, hgS, hgz⟩
    have hedge : ryEdge A S z₀ m₀ k m (A.eval m₀ g) := ⟨g, hglen, hgS, hgz, rfl⟩
    have heq := hmax (A.eval m₀ g) (Relation.ReflTransGen.single hedge)
    exact hirrefl m (heq ▸ hedge)
  have hball_z_card : (schreierBall A S z₀ k).card = Fintype.card Q - 1 := by
    have hge := card_schreierBall_ge hTrans z₀ k
    have hle := Finset.card_le_univ (schreierBall A S z₀ k)
    have hne : (schreierBall A S z₀ k).card ≠ Fintype.card Q := fun hc =>
      hball_z_ne (Finset.eq_univ_of_card _ hc)
    omega
  obtain ⟨q_snk, _, hq_snk_not⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hball_z_ne⟩)
  have hq_snk_uniq : ∀ m : Q, m ∉ schreierBall A S z₀ k → m = q_snk := by
    intro m hm
    by_contra hne
    have hsub : insert m (insert q_snk (schreierBall A S z₀ k)) ⊆ Finset.univ := Finset.subset_univ _
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hne, hm]),
      Finset.card_insert_of_notMem hq_snk_not, Finset.card_univ, hball_z_card] at hcard
    omega
  have hall_to_snk : ∀ x : Q, ryReach A S z₀ m₀ k x q_snk := by
    intro x
    obtain ⟨m, hxm, hmax⟩ := exists_max_reach x
    have hm_not : m ∉ schreierBall A S z₀ k := by
      intro hm_in
      simp only [schreierBall, Finset.mem_filter, Finset.mem_univ, true_and] at hm_in
      rcases hm_in with ⟨g, hglen, hgS, hgz⟩
      have hedge : ryEdge A S z₀ m₀ k m (A.eval m₀ g) := ⟨g, hglen, hgS, hgz, rfl⟩
      have heq := hmax (A.eval m₀ g) (Relation.ReflTransGen.single hedge)
      exact hirrefl m (heq ▸ hedge)
    rwa [hq_snk_uniq m hm_not] at hxm
  -- Step 2: Unique source `q_src` omitted by `schreierBall m₀ (n - 2)`
  have hball_m_ne : schreierBall A S m₀ k ≠ Finset.univ := by
    intro hfull
    obtain ⟨q_any⟩ := ‹Nonempty Q›
    obtain ⟨m, _, hmin⟩ := exists_min_reach q_any
    have hm_in : m ∈ schreierBall A S m₀ k := hfull ▸ Finset.mem_univ m
    simp only [schreierBall, Finset.mem_filter, Finset.mem_univ, true_and] at hm_in
    rcases hm_in with ⟨g, hglen, hgS, hgm⟩
    have hedge : ryEdge A S z₀ m₀ k (A.eval z₀ g) m := ⟨g, hglen, hgS, rfl, hgm⟩
    have heq := hmin (A.eval z₀ g) (Relation.ReflTransGen.single hedge)
    exact hirrefl m (heq ▸ hedge)
  have hball_m_card : (schreierBall A S m₀ k).card = Fintype.card Q - 1 := by
    have hge := card_schreierBall_ge hTrans m₀ k
    have hle := Finset.card_le_univ (schreierBall A S m₀ k)
    have hne : (schreierBall A S m₀ k).card ≠ Fintype.card Q := fun hc =>
      hball_m_ne (Finset.eq_univ_of_card _ hc)
    omega
  obtain ⟨q_src, _, hq_src_not⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hball_m_ne⟩)
  have hq_src_uniq : ∀ m : Q, m ∉ schreierBall A S m₀ k → m = q_src := by
    intro m hm
    by_contra hne
    have hsub : insert m (insert q_src (schreierBall A S m₀ k)) ⊆ Finset.univ := Finset.subset_univ _
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hne, hm]),
      Finset.card_insert_of_notMem hq_src_not, Finset.card_univ, hball_m_card] at hcard
    omega
  have hall_from_src : ∀ x : Q, ryReach A S z₀ m₀ k q_src x := by
    intro x
    obtain ⟨m, hmx, hmin⟩ := exists_min_reach x
    have hm_not : m ∉ schreierBall A S m₀ k := by
      intro hm_in
      simp only [schreierBall, Finset.mem_filter, Finset.mem_univ, true_and] at hm_in
      rcases hm_in with ⟨g, hglen, hgS, hgm⟩
      have hedge : ryEdge A S z₀ m₀ k (A.eval z₀ g) m := ⟨g, hglen, hgS, rfl, hgm⟩
      have heq := hmin (A.eval z₀ g) (Relation.ReflTransGen.single hedge)
      exact hirrefl m (heq ▸ hedge)
    rwa [hq_src_uniq m hm_not] at hmx
  -- Step 3: Pigeonhole on radius `t = n / 2` balls from `q_src` and `q_snk`
  let t := Fintype.card Q / 2
  have hB1 : t + 1 ≤ (schreierBall A S q_src t).card := by
    have h := card_schreierBall_ge hTrans q_src t
    have hmin : min (t + 1) (Fintype.card Q) = t + 1 := min_eq_left (by omega)
    rwa [hmin] at h
  have hB2 : t + 1 ≤ (schreierBall A S q_snk t).card := by
    have h := card_schreierBall_ge hTrans q_snk t
    have hmin : min (t + 1) (Fintype.card Q) = t + 1 := min_eq_left (by omega)
    rwa [hmin] at h
  have hinter_ne : (schreierBall A S q_src t ∩ schreierBall A S q_snk t).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hdisj : Disjoint (schreierBall A S q_src t) (schreierBall A S q_snk t) :=
      Finset.disjoint_iff_inter_eq_empty.mpr hempty
    have hu : (schreierBall A S q_src t ∪ schreierBall A S q_snk t).card ≤ Fintype.card Q := by
      simpa using Finset.card_le_univ (schreierBall A S q_src t ∪ schreierBall A S q_snk t)
    rw [Finset.card_union_of_disjoint hdisj] at hu
    omega
  rcases hinter_ne with ⟨w, hw⟩
  rw [Finset.mem_inter] at hw
  have hw1 := hw.1
  have hw2 := hw.2
  simp only [schreierBall, Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
  rcases hw1 with ⟨g₁, hg₁len, hg₁S, hg₁eq⟩
  rcases hw2 with ⟨g₂, hg₂len, hg₂S, hg₂eq⟩
  -- Step 4: Shift `ryReach k` by `g₂` and `g₁` to connect ANY `p` to ANY `q` through `w`!
  have hall_reach : ∀ p q : Q, ryReach A S z₀ m₀ (k + t) p q := by
    intro p q
    obtain ⟨x₂, hx₂⟩ := (bijective_eval_of_mem hBij g₂ hg₂S).2 p
    obtain ⟨x₁, hx₁⟩ := (bijective_eval_of_mem hBij g₁ hg₁S).2 q
    dsimp only at hx₂ hx₁
    have hpw : ryReach A S z₀ m₀ (k + t) p w := by
      have h := ryReach_eval A S z₀ m₀ g₂ hg₂S k (hall_to_snk x₂)
      rw [hx₂, hg₂eq] at h
      exact ryReach_mono A S z₀ m₀ (by omega) h
    have hwq : ryReach A S z₀ m₀ (k + t) w q := by
      have h := ryReach_eval A S z₀ m₀ g₁ hg₁S k (hall_from_src x₁)
      rw [hg₁eq, hx₁] at h
      exact ryReach_mono A S z₀ m₀ (by omega) h
    exact hpw.trans hwq
  have hsub : Subsingleton (Quotient (sccSetoid A S z₀ m₀ (k + t))) :=
    ⟨fun x y => Quotient.inductionOn₂ x y fun p q =>
      Quotient.sound ⟨hall_reach p q, hall_reach q p⟩⟩
  have hle1 : sccCount A S z₀ m₀ (k + t) ≤ 1 := by
    change Fintype.card (Quotient (sccSetoid A S z₀ m₀ (k + t))) ≤ 1
    exact Fintype.card_le_one_iff_subsingleton.mpr hsub
  have hpos := sccCount_pos A S z₀ m₀ (k + t)
  exact le_antisymm hle1 hpos

/-! ### Lemma T16.3: 2-Block Shift-Isolation Contradiction (`c(n - 2) = n - 1 → c(n - 1) ≠ n - 2`) -/

/-- **Lemma T16.3 (2-Block Shift-Isolation Contradiction)**:
For `n ≥ 5`, if `sccCount (n - 2) = n - 1`, then `sccCount (n - 1) ≠ n - 2` (hence
`sccCount (n - 1) ≤ n - 3`). -/
theorem sccCount_pred_one_ne_pred_two [Fintype Q] [Nonempty Q] [DecidableEq Q]
    {A : DFA Q α} {S : Set α} {z₀ m₀ : Q}
    (hPrim : A.IsPrimitivePermSet S) (hzm : z₀ ≠ m₀) (hn5 : 5 ≤ Fintype.card Q)
    (hc2 : sccCount A S z₀ m₀ (Fintype.card Q - 2) = Fintype.card Q - 1) :
    sccCount A S z₀ m₀ (Fintype.card Q - 1) ≠ Fintype.card Q - 2 := by
  classical
  intro hc1
  let n := Fintype.card Q
  let s₂ := sccSetoid A S z₀ m₀ (n - 2)
  let s₁ := sccSetoid A S z₀ m₀ (n - 1)
  let C₂ := Quotient s₂
  let C₁ := Quotient s₁
  have hC₂_card : Fintype.card C₂ = n - 1 := by simpa only [sccCount, s₂, C₂, n] using hc2
  have hC₁_card : Fintype.card C₁ = n - 2 := by simpa only [sccCount, s₁, C₁, n] using hc1
  -- Step 1: Extract the unique 2-block `W` of `Π_{n - 2}`
  let fib₂ : C₂ → Finset Q := fun x => Finset.univ.filter (fun q => Quotient.mk s₂ q = x)
  have hfib₂_ge1 : ∀ x : C₂, 1 ≤ (fib₂ x).card := fun x => by
    obtain ⟨q, rfl⟩ := Quotient.exists_rep x
    exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, rfl⟩⟩
  have hfib₂_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset C₂) : Set C₂) fib₂ := by
    intro x _ y _ hxy
    show Disjoint (fib₂ x) (fib₂ y)
    rw [Finset.disjoint_left]
    intro q hqx hqy
    rw [Finset.mem_filter] at hqx hqy
    exact hxy (hqx.2.symm.trans hqy.2)
  have hfib₂_sum : ∑ x : C₂, (fib₂ x).card = n := by
    have hunion : (Finset.univ : Finset C₂).biUnion fib₂ = Finset.univ := by
      ext q
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, fib₂, Finset.mem_filter, iff_true]
      exact ⟨Quotient.mk s₂ q, rfl⟩
    rw [← Finset.card_biUnion hfib₂_disj, hunion, Finset.card_univ]
  have hfib₂_excess : ∑ x : C₂, ((fib₂ x).card - 1) = 1 := by
    have hadd : (∑ x : C₂, ((fib₂ x).card - 1)) + Fintype.card C₂ = ∑ x : C₂, (fib₂ x).card := by
      calc (∑ x : C₂, ((fib₂ x).card - 1)) + Fintype.card C₂
          = (∑ x : C₂, ((fib₂ x).card - 1)) + ∑ _x : C₂, 1 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_id]
        _ = ∑ x : C₂, ((fib₂ x).card - 1 + 1) := (Finset.sum_add_distrib).symm
        _ = ∑ x : C₂, (fib₂ x).card :=
            Finset.sum_congr rfl fun x _ => by have := hfib₂_ge1 x; omega
    omega
  have hex_xW : ∃ xW : C₂, 1 ≤ (fib₂ xW).card - 1 := by
    by_contra hall
    push Not at hall
    have h0 : ∑ x : C₂, ((fib₂ x).card - 1) = 0 :=
      Finset.sum_eq_zero fun x _ => by have := hall x; omega
    omega
  obtain ⟨xW, hxW_ge1⟩ := hex_xW
  let W : Finset Q := fib₂ xW
  have hW_card : W.card = 2 := by
    have hle : (fib₂ xW).card - 1 ≤ ∑ x : C₂, ((fib₂ x).card - 1) :=
      Finset.single_le_sum (f := fun x : C₂ => (fib₂ x).card - 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ xW)
    have : (fib₂ xW).card = 2 := by omega
    exact this
  have hW_ne : W.Nonempty := Finset.card_pos.mp (by omega)
  -- Step 2: Condensation partial order on `C₁ = Quotient (sccSetoid (n - 1))`
  let leC₁ : C₁ → C₁ → Prop :=
    Quotient.lift₂ (fun p q => ryReach A S z₀ m₀ (n - 1) p q) fun p₁ q₁ p₂ q₂ hp hq =>
      propext ⟨fun h => hp.2.trans (h.trans hq.1), fun h => hp.1.trans (h.trans hq.2)⟩
  have hle_refl : ∀ x : C₁, leC₁ x x := fun x => Quotient.inductionOn x fun _ => .refl
  have hle_trans : ∀ {x y z : C₁}, leC₁ x y → leC₁ y z → leC₁ x z := fun {x y z} =>
    Quotient.inductionOn₃ x y z fun _ _ _ h1 h2 => h1.trans h2
  have hle_antisymm : ∀ {x y : C₁}, leC₁ x y → leC₁ y x → x = y := fun {x y} =>
    Quotient.inductionOn₂ x y fun _ _ h1 h2 => Quotient.sound ⟨h1, h2⟩
  -- Pick maximal `V` and distinct minimal `U ≠ V` in `C₁`
  have hn5' : 5 ≤ n := hn5
  have huniv₁_ne : (Finset.univ : Finset C₁).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
  have hex_up : ∃ c : ℕ, ∃ x ∈ (Finset.univ : Finset C₁),
      (Finset.univ.filter (fun y => leC₁ x y)).card = c := by
    rcases huniv₁_ne with ⟨x₀, hx₀⟩; exact ⟨_, x₀, hx₀, rfl⟩
  obtain ⟨V, _, hV_eq⟩ := Nat.find_spec hex_up
  have hV_min : ∀ Y : C₁, (Finset.univ.filter (fun y => leC₁ V y)).card ≤
      (Finset.univ.filter (fun y => leC₁ Y y)).card := fun Y =>
    hV_eq ▸ Nat.find_min' hex_up ⟨Y, Finset.mem_univ Y, rfl⟩
  have hV_max : ∀ Y : C₁, leC₁ V Y → Y = V := by
    intro Y hVY
    have hsub : Finset.univ.filter (fun z => leC₁ Y z) ⊆ Finset.univ.filter (fun z => leC₁ V z) := by
      intro z hz; rw [Finset.mem_filter] at hz ⊢; exact ⟨Finset.mem_univ z, hle_trans hVY hz.2⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (hV_min Y)
    have hV_in : V ∈ Finset.univ.filter (fun z => leC₁ Y z) := by
      rw [heq, Finset.mem_filter]; exact ⟨Finset.mem_univ V, hle_refl V⟩
    exact hle_antisymm (Finset.mem_filter.mp hV_in).2 hVY
  have hexW₁ : ∃ W₁ : C₁, W₁ ≠ V := by
    by_contra hall; push Not at hall
    have hsub : Subsingleton C₁ := ⟨fun x y => (hall x).trans (hall y).symm⟩
    have hle1 : Fintype.card C₁ ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  obtain ⟨W₁, hW₁V⟩ := hexW₁
  let DW : Finset C₁ := Finset.univ.filter (fun x => leC₁ x W₁)
  have hDW_ne : DW.Nonempty := ⟨W₁, Finset.mem_filter.mpr ⟨Finset.mem_univ W₁, hle_refl W₁⟩⟩
  have hex_dn : ∃ c : ℕ, ∃ x ∈ DW, (DW.filter (fun y => leC₁ y x)).card = c := by
    rcases hDW_ne with ⟨x₀, hx₀⟩; exact ⟨_, x₀, hx₀, rfl⟩
  obtain ⟨U, hU_DW, hU_eq⟩ := Nat.find_spec hex_dn
  have hU_min : ∀ Y ∈ DW, (DW.filter (fun y => leC₁ y U)).card ≤
      (DW.filter (fun y => leC₁ y Y)).card := fun Y hY =>
    hU_eq ▸ Nat.find_min' hex_dn ⟨Y, hY, rfl⟩
  have hUW₁ : leC₁ U W₁ := (Finset.mem_filter.mp hU_DW).2
  have hU_isMin : ∀ Y : C₁, leC₁ Y U → Y = U := by
    intro Y hYU
    have hY_DW : Y ∈ DW := Finset.mem_filter.mpr ⟨Finset.mem_univ Y, hle_trans hYU hUW₁⟩
    have hsub : DW.filter (fun z => leC₁ z Y) ⊆ DW.filter (fun z => leC₁ z U) := by
      intro z hz; rw [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hle_trans hz.2 hYU⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (hU_min Y hY_DW)
    have hU_in : U ∈ DW.filter (fun z => leC₁ z Y) := by
      rw [heq, Finset.mem_filter]; exact ⟨hU_DW, hle_refl U⟩
    exact hle_antisymm hYU (Finset.mem_filter.mp hU_in).2
  have hUV : U ≠ V := fun heq => hW₁V (hV_max W₁ (heq ▸ hUW₁))
  -- Exact fibers of `C₁`: `|fib₁ U| = 2`, `|fib₁ V| = 2`, all other fibers have size `1`!
  let fib₁ : C₁ → Finset Q := fun y => Finset.univ.filter (fun q => Quotient.mk s₁ q = y)
  have hfib₁_ge1 : ∀ y : C₁, 1 ≤ (fib₁ y).card := fun y => by
    obtain ⟨q, rfl⟩ := Quotient.exists_rep y
    exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, rfl⟩⟩
  have hirrefl₁ : ∀ q : Q, ¬ ryEdge A S z₀ m₀ (n - 1) q q := by
    rintro q ⟨g, _, hgS, hgz, hgm⟩
    exact hzm ((bijective_eval_of_mem hPrim.1 g hgS).1 (hgz.trans hgm.symm))
  have hfib₁_V_ge2 : 2 ≤ (fib₁ V).card := by
    obtain ⟨v, hv⟩ := Quotient.exists_rep V
    obtain ⟨g, hglen, hgS, hgz⟩ := exists_short_word_of_primitive hPrim z₀ v
    have hvv' : ryEdge A S z₀ m₀ (n - 1) v (A.eval m₀ g) := ⟨g, hglen, hgS, hgz, rfl⟩
    have hne : v ≠ A.eval m₀ g := fun h => hirrefl₁ v (h ▸ hvv')
    have hv'_eq : Quotient.mk s₁ (A.eval m₀ g) = V :=
      hV_max (Quotient.mk s₁ (A.eval m₀ g)) (by rw [← hv]; exact Relation.ReflTransGen.single hvv')
    have hsub : ({v, A.eval m₀ g} : Finset Q) ⊆ fib₁ V := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl | rfl
      · exact ⟨Finset.mem_univ _, hv⟩
      · exact ⟨Finset.mem_univ _, hv'_eq⟩
    calc 2 = ({v, A.eval m₀ g} : Finset Q).card := (Finset.card_pair hne).symm
      _ ≤ (fib₁ V).card := Finset.card_le_card hsub
  have hfib₁_U_ge2 : 2 ≤ (fib₁ U).card := by
    obtain ⟨u, hu⟩ := Quotient.exists_rep U
    obtain ⟨g, hglen, hgS, hgm⟩ := exists_short_word_of_primitive hPrim m₀ u
    have hu'u : ryEdge A S z₀ m₀ (n - 1) (A.eval z₀ g) u := ⟨g, hglen, hgS, rfl, hgm⟩
    have hne : u ≠ A.eval z₀ g := fun h => hirrefl₁ u (h ▸ hu'u)
    have hu'_eq : Quotient.mk s₁ (A.eval z₀ g) = U :=
      hU_isMin (Quotient.mk s₁ (A.eval z₀ g)) (by rw [← hu]; exact Relation.ReflTransGen.single hu'u)
    have hsub : ({u, A.eval z₀ g} : Finset Q) ⊆ fib₁ U := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl | rfl
      · exact ⟨Finset.mem_univ _, hu⟩
      · exact ⟨Finset.mem_univ _, hu'_eq⟩
    calc 2 = ({u, A.eval z₀ g} : Finset Q).card := (Finset.card_pair hne).symm
      _ ≤ (fib₁ U).card := Finset.card_le_card hsub
  have hfib₁_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset C₁) : Set C₁) fib₁ := by
    intro x _ y _ hxy
    show Disjoint (fib₁ x) (fib₁ y)
    rw [Finset.disjoint_left]
    intro q hqx hqy
    rw [Finset.mem_filter] at hqx hqy
    exact hxy (hqx.2.symm.trans hqy.2)
  have hfib₁_sum : ∑ y : C₁, (fib₁ y).card = n := by
    have hunion : (Finset.univ : Finset C₁).biUnion fib₁ = Finset.univ := by
      ext q
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, fib₁, Finset.mem_filter, iff_true]
      exact ⟨Quotient.mk s₁ q, rfl⟩
    rw [← Finset.card_biUnion hfib₁_disj, hunion, Finset.card_univ]
  have hfib₁_excess : ∑ y : C₁, ((fib₁ y).card - 1) = 2 := by
    have hadd : (∑ y : C₁, ((fib₁ y).card - 1)) + Fintype.card C₁ = ∑ y : C₁, (fib₁ y).card := by
      calc (∑ y : C₁, ((fib₁ y).card - 1)) + Fintype.card C₁
          = (∑ y : C₁, ((fib₁ y).card - 1)) + ∑ _y : C₁, 1 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_id]
        _ = ∑ y : C₁, ((fib₁ y).card - 1 + 1) := (Finset.sum_add_distrib).symm
        _ = ∑ y : C₁, (fib₁ y).card :=
            Finset.sum_congr rfl fun y _ => by have := hfib₁_ge1 y; omega
    omega
  have hU_in_er : U ∈ (Finset.univ : Finset C₁).erase V :=
    Finset.mem_erase.mpr ⟨hUV, Finset.mem_univ U⟩
  have hsplit_ex : ((fib₁ V).card - 1) + (((fib₁ U).card - 1) +
      ∑ y ∈ ((Finset.univ : Finset C₁).erase V).erase U, ((fib₁ y).card - 1)) = 2 := by
    rw [Finset.add_sum_erase ((Finset.univ : Finset C₁).erase V) (fun y => (fib₁ y).card - 1) hU_in_er,
      Finset.add_sum_erase (Finset.univ : Finset C₁) (fun y => (fib₁ y).card - 1) (Finset.mem_univ V),
      hfib₁_excess]
  have hfib₁_V_eq2 : (fib₁ V).card = 2 := by omega
  have hfib₁_U_eq2 : (fib₁ U).card = 2 := by omega
  have hfib₁_other_eq1 : ∀ y : C₁, y ≠ U → y ≠ V → (fib₁ y).card = 1 := by
    intro y hyU hyV
    have hrest0 : ∑ z ∈ ((Finset.univ : Finset C₁).erase V).erase U, ((fib₁ z).card - 1) = 0 := by omega
    have hy_mem : y ∈ ((Finset.univ : Finset C₁).erase V).erase U :=
      Finset.mem_erase.mpr ⟨hyU, Finset.mem_erase.mpr ⟨hyV, Finset.mem_univ y⟩⟩
    have hy0 : (fib₁ y).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp hrest0) y hy_mem
    have hy1 := hfib₁_ge1 y
    omega
  -- Step 3: `W` equals `fib₁ U` or `fib₁ V`
  have hsub_fib₁_eq : ∀ T : Finset Q, T.card = 2 →
      (∀ p ∈ T, ∀ q ∈ T, s₁.r p q) → T = fib₁ U ∨ T = fib₁ V := by
    intro T hTcard hTrel
    obtain ⟨p₀, hp₀⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    let y₀ : C₁ := Quotient.mk s₁ p₀
    have hTsub : T ⊆ fib₁ y₀ := by
      intro q hq
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ q, Quotient.sound (hTrel q hq p₀ hp₀)⟩
    have hy₀_ge2 : 2 ≤ (fib₁ y₀).card := by
      calc 2 = T.card := hTcard.symm
        _ ≤ (fib₁ y₀).card := Finset.card_le_card hTsub
    by_cases hU : y₀ = U
    · left; rw [hU] at hTsub
      exact Finset.eq_of_subset_of_card_le hTsub (by omega)
    · right
      have hV : y₀ = V := by
        by_contra hneV
        have := hfib₁_other_eq1 y₀ hU hneV
        omega
      rw [hV] at hTsub
      exact Finset.eq_of_subset_of_card_le hTsub (by omega)
  have hW_rel1 : ∀ p ∈ W, ∀ q ∈ W, s₁.r p q := by
    intro p hp q hq
    rw [Finset.mem_filter] at hp hq
    have hrel2 : s₂.r p q := Quotient.exact (hp.2.trans hq.2.symm)
    exact ⟨ryReach_mono A S z₀ m₀ (by omega) hrel2.1, ryReach_mono A S z₀ m₀ (by omega) hrel2.2⟩
  have hW_eq : W = fib₁ U ∨ W = fib₁ V := hsub_fib₁_eq W hW_card hW_rel1
  -- Step 4: Find `b* ∈ S` mapping `W` onto the OTHER 2-block!
  have hW_step_cases : ∀ b ∈ S, W.image (fun q => A.step q b) = fib₁ U ∨
      W.image (fun q => A.step q b) = fib₁ V := by
    intro b hb
    have hcard_img : (W.image (fun q => A.step q b)).card = 2 := by
      rw [Finset.card_image_of_injective W (hPrim.1 b hb).1, hW_card]
    refine hsub_fib₁_eq _ hcard_img ?_
    intro x hx y hy
    rw [Finset.mem_image] at hx hy
    rcases hx with ⟨p, hpW, rfl⟩
    rcases hy with ⟨q, hqW, rfl⟩
    rw [Finset.mem_filter] at hpW hqW
    have hrel2 : s₂.r p q := Quotient.exact (hpW.2.trans hqW.2.symm)
    have hstep := scc_step A S z₀ m₀ (n - 2) hb hrel2
    have hidx : n - 2 + 1 = n - 1 := by omega
    rw [hidx] at hstep
    exact hstep
  have hex_bstar : ∃ b ∈ S, W.image (fun q => A.step q b) ≠ W := by
    by_contra hall
    push Not at hall
    have hclosed : ∀ g : List α, (∀ b ∈ g, b ∈ S) → ∀ p ∈ W, A.eval p g ∈ W := by
      intro g
      induction g with
      | nil => intro _ p hp; exact hp
      | cons b g ih =>
        intro hS p hp
        have hb : b ∈ S := hS b List.mem_cons_self
        have hg : ∀ c ∈ g, c ∈ S := fun c hc => hS c (List.mem_cons_of_mem b hc)
        have hstep_mem : A.step p b ∈ W := by
          rw [← hall b hb]
          exact Finset.mem_image_of_mem _ hp
        exact ih hg (A.step p b) hstep_mem
    obtain ⟨p₀, hp₀⟩ := hW_ne
    have hW_proper : W ≠ Finset.univ := fun heq => by
      have := congrArg Finset.card heq; rw [hW_card, Finset.card_univ] at this; omega
    obtain ⟨r₀, _, hr₀⟩ := Finset.exists_of_ssubset
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ W, hW_proper⟩)
    obtain ⟨g, hgS, hgr⟩ := hPrim.2.1 p₀ r₀
    exact hr₀ (hgr ▸ hclosed g hgS p₀ hp₀)
  obtain ⟨bstar, hbstar, hbstar_ne⟩ := hex_bstar
  -- Step 5: In both cases (`W = fib₁ U` or `W = fib₁ V`), every edge of `E_{n - 2}` preserves `∈ W`!
  have hV_closed : ∀ u v : Q, ryEdge A S z₀ m₀ (n - 1) u v → u ∈ fib₁ V → v ∈ fib₁ V := by
    intro u v huv hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨Finset.mem_univ v, hV_max (Quotient.mk s₁ v) ?_⟩
    rw [← hu.2]; exact Relation.ReflTransGen.single huv
  have hU_closed : ∀ u v : Q, ryEdge A S z₀ m₀ (n - 1) u v → v ∈ fib₁ U → u ∈ fib₁ U := by
    intro u v huv hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨Finset.mem_univ u, hU_isMin (Quotient.mk s₁ u) ?_⟩
    rw [← hv.2]; exact Relation.ReflTransGen.single huv
  have hno_cross : ∀ u v : Q, ryEdge A S z₀ m₀ (n - 2) u v → (u ∈ W ↔ v ∈ W) := by
    intro u v huv
    have huv1 : ryEdge A S z₀ m₀ (n - 1) u v := ryEdge_mono A S z₀ m₀ (by omega) huv
    have huv_step : ryEdge A S z₀ m₀ (n - 1) (A.step u bstar) (A.step v bstar) := by
      have h := ryEdge_step A S z₀ m₀ (n - 2) hbstar huv
      have hidx : n - 2 + 1 = n - 1 := by omega
      rwa [hidx] at h
    rcases hW_eq with hWU | hWV
    · have himgV : W.image (fun q => A.step q bstar) = fib₁ V :=
        (hW_step_cases bstar hbstar).resolve_left (by rwa [← hWU])
      constructor
      · intro hu
        have hu_img : A.step u bstar ∈ fib₁ V := by
          rw [← himgV]; exact Finset.mem_image_of_mem _ hu
        have hv_img : A.step v bstar ∈ fib₁ V := hV_closed _ _ huv_step hu_img
        rw [← himgV, Finset.mem_image] at hv_img
        rcases hv_img with ⟨v', hv'W, hv'eq⟩
        exact (hPrim.1 bstar hbstar).1 hv'eq ▸ hv'W
      · intro hv
        rw [hWU] at hv ⊢
        exact hU_closed u v huv1 hv
    · have himgU : W.image (fun q => A.step q bstar) = fib₁ U :=
        (hW_step_cases bstar hbstar).resolve_right (by rwa [← hWV])
      constructor
      · intro hu
        rw [hWV] at hu ⊢
        exact hV_closed u v huv1 hu
      · intro hv
        have hv_img : A.step v bstar ∈ fib₁ U := by
          rw [← himgU]; exact Finset.mem_image_of_mem _ hv
        have hu_img : A.step u bstar ∈ fib₁ U := hU_closed _ _ huv_step hv_img
        rw [← himgU, Finset.mem_image] at hu_img
        rcases hu_img with ⟨u', hu'W, hu'eq⟩
        exact (hPrim.1 bstar hbstar).1 hu'eq ▸ hu'W
  -- Contradiction with Lemma T16.1 (`exists_ryEdge_crossing`)!
  have hW_proper : W ≠ Finset.univ := fun heq => by
    have := congrArg Finset.card heq; rw [hW_card, Finset.card_univ] at this; omega
  obtain ⟨u, v, huv, hcross⟩ := exists_ryEdge_crossing hPrim hzm (by omega) hW_ne hW_proper
  exact hcross (hno_cross u v huv)

end VolkovD6

/-! ### Main Public World-Record Theorems (Theorem T16) -/

/-- **Theorem T16 (NEW WORLD RECORD FOR VOLKOV D6 — Strictly Beats Zhu FSTTCS 2024 for `n ≥ 5`)**:
Every DFA on `n ≥ 5` states possessing a primitive permutation letter set `S` and a rank-`(n - 1)`
letter `a` is automatically synchronizing and satisfies `L_pos ≤ 2 * n - 5`, admitting a
synchronizing word of length at most `1 + (n - 2) * (2 * n - 4) = 2 * n ^ 2 - 8 * n + 9`
(strictly beating Zhu 2024's standing record `2 * n ^ 2 - 7 * n + 7` by `n - 2`!). -/
theorem primitive_defectOne_beats_zhu_ge_five {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S : Set α) (a : α)
    (hn5 : 5 ≤ Fintype.card Q)
    (hPrim : A.IsPrimitivePermSet S)
    (hrank : (A.image Finset.univ [a]).card + 1 = Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 1 + (Fintype.card Q - 2) * (2 * Fintype.card Q - 4) := by
  obtain ⟨z₀, m₀, hDef⟩ := exists_isDefectOneLetter_of_card_image_eq_pred A a hrank
  have hle_n := AlpogePrimitive.sccCount_le_card A S z₀ m₀ (Fintype.card Q - 2)
  have h1 : AlpogePrimitive.sccCount A S z₀ m₀ (2 * Fintype.card Q - 5) = 1 := by
    by_cases hacyc : AlpogePrimitive.sccCount A S z₀ m₀ (Fintype.card Q - 2) = Fintype.card Q
    · -- Case 1: `c(n - 2) = n` → DAG-Shift Teleportation (Lemma T16.2)!
      have hhalf := VolkovD6.sccCount_half_eq_one_of_acyclic hPrim.1 hPrim.2.1 hDef.1
        (by omega) hacyc
      have hmono := AlpogePrimitive.sccCount_antitone A S z₀ m₀
        (show Fintype.card Q - 2 + Fintype.card Q / 2 ≤ 2 * Fintype.card Q - 5 by omega)
      have hpos := AlpogePrimitive.sccCount_pos A S z₀ m₀ (2 * Fintype.card Q - 5)
      omega
    · by_cases hnm1 : AlpogePrimitive.sccCount A S z₀ m₀ (Fintype.card Q - 2) = Fintype.card Q - 1
      · -- Case 2: `c(n - 2) = n - 1` → 2-Block Shift-Isolation (Lemma T16.3)!
        have hdec := AlpogePrimitive.sccCount_strict_dec hPrim z₀ m₀ (Fintype.card Q - 2)
          (by omega) (by omega)
        have hidx : Fintype.card Q - 2 + 1 = Fintype.card Q - 1 := by omega
        rw [hidx] at hdec
        have hne := VolkovD6.sccCount_pred_one_ne_pred_two hPrim hDef.1 hn5 hnm1
        have hle3 : AlpogePrimitive.sccCount A S z₀ m₀ (Fintype.card Q - 1) ≤ Fintype.card Q - 3 := by
          omega
        have hres := AlpogePrimitive.sccCount_eq_one_of_lt hPrim z₀ m₀ (Fintype.card Q - 4)
          (Fintype.card Q - 1) (by omega) (by omega)
        have hsum : Fintype.card Q - 1 + (Fintype.card Q - 4) = 2 * Fintype.card Q - 5 := by omega
        rwa [hsum] at hres
      · -- Case 3: `c(n - 2) ≤ n - 2` → SCC-Coarsening finishes in `n - 3` steps!
        have hres := AlpogePrimitive.sccCount_eq_one_of_lt hPrim z₀ m₀ (Fintype.card Q - 3)
          (Fintype.card Q - 2) (by omega) (by omega)
        have hsum : Fintype.card Q - 2 + (Fintype.card Q - 3) = 2 * Fintype.card Q - 5 := by omega
        rwa [hsum] at hres
  obtain ⟨w, hw, hlen⟩ :=
    AlpogePrimitive.exists_syncWord_of_sccCount_eq_one hPrim.1 hDef (2 * Fintype.card Q - 5) h1
  refine ⟨w, hw, le_trans hlen ?_⟩
  have heq : 2 * Fintype.card Q - 5 + 1 = 2 * Fintype.card Q - 4 := by omega
  rw [heq]

/-- **Theorem T16 (Unified `n ≥ 4` World Record `2n² - 8n + 9`, Beating Zhu 2024 Everywhere)**:
For EVERY `n ≥ 4`, every DFA with a primitive permutation letter set `S` and a rank-`(n - 1)`
letter `a` is automatically synchronizing and admits a synchronizing word of length at most
`2 * n ^ 2 - 8 * n + 9` (strictly `< 2 * n ^ 2 - 7 * n + 7` for all `n ≥ 4`). -/
theorem primitive_defectOne_beats_zhu {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S : Set α) (a : α)
    (hn4 : 4 ≤ Fintype.card Q)
    (hPrim : A.IsPrimitivePermSet S)
    (hrank : (A.image Finset.univ [a]).card + 1 = Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 2 * (Fintype.card Q) ^ 2 - 8 * Fintype.card Q + 9 := by
  by_cases hn5 : 5 ≤ Fintype.card Q
  · obtain ⟨w, hw, hlen⟩ := primitive_defectOne_beats_zhu_ge_five A S a hn5 hPrim hrank
    refine ⟨w, hw, le_trans hlen ?_⟩
    set n := Fintype.card Q
    have hmul : 8 * n ≤ 2 * n ^ 2 := by nlinarith
    zify [hmul, (show 2 ≤ n by omega), (show 4 ≤ 2 * n by omega)]
    nlinarith
  · -- `|Q| = 4`: automatic sync from `primitive_defectOne_zhu_bound` + exact Černý `≤ 9` via `cerny_card_le_four`!
    have hcard4 : Fintype.card Q = 4 := by omega
    obtain ⟨w₀, hw₀, _⟩ := primitive_defectOne_zhu_bound A S a hPrim hrank
    have hSync : A.IsSynchronizing := ⟨w₀, hw₀⟩
    obtain ⟨w, hw, hlen⟩ := cerny_card_le_four A (by omega) hSync
    refine ⟨w, hw, le_trans hlen ?_⟩
    rw [hcard4]
    decide

end Cerny
