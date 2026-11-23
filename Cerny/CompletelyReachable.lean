import Cerny.Defs
import Cerny.AlpogePrimitive
import Cerny.VolkovD6Transitive
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push

/-!
# Completely Reachable Automata (Volkov D2 — Theorem T23 & Ferens–Szykuła 2025 Improvement)

This file formalizes **Theorem T23** (`docs/round5_general_bridge.md` §4, with the exact defect-1
omitted-state set `M₁ := {q | ∃ a, Q · a = Q \ {q}}` required by `lem:UnionPredecessor`) together
with a self-contained Lean 4 formalization of Ferens & Szykuła's (2025, `arXiv:2208.05956v5`)
laminar complement-merge engine:

* **Definitions (`Cerny.DFA.IsCompletelyReachable`, `Cerny.DFA.ProperlyExtends`,
  `Cerny.defectOneOmitted`, `Cerny.maxOrbitSize`, `Cerny.effOrbitCap`, `Cerny.harmonicRat`)**:
  Standard Volkov D2 complete reachability, proper extension (`∀ s ∈ S, 1 ≤ |{s} w⁻¹|` and
  `∃ s ∈ S, 2 ≤ |{s} w⁻¹|`), permutation-group orbits under bijective letters `Σ₀`, defect-1
  omitted-state set `M₁`, and effective orbit cap `ℓ_eff₁ := max_{O ∈ Orb(⟨Σ₀⟩)} |O \ M₁| + 1`.
* **Theorem T23(1) (`Cerny.volkovD6_d1_isCompletelyReachable`,
  `Cerny.primitive_defectOne_isCompletelyReachable`)**:
  Every synchronizing transitive defect-`≤ 1` DFA with `blockCount = 1` (in particular, **every**
  primitive Volkov D6 DFA!) is completely reachable.
* **Laminar Family Bound (`CompletelyReachable.laminar_bounded_card_le`)**:
  Exact combinatorial proof of Ferens–Szykuła's `lem:BoundedTriviallyIntersectingSubsets`: any
  laminar family `ℱ` of subsets of `Q` of size in `[2, k]` satisfies `k * |ℱ| + n ≤ k * n`
  (hence `|ℱ| ≤ n - ⌈n / k⌉` and `(|ℱ| : ℚ) ≤ n - n / k`).
* **Theorem T23(2) (`Cerny.completelyReachable_effOrbit_reaching_bound`,
  `Cerny.completelyReachable_effOrbit_bound`, `Cerny.completelyReachable_ferensSzykula_bound`,
  `Cerny.completelyReachable_beats_ferensSzykula`, `Cerny.completelyReachable_breaks_two_n_sq`)**:
  Every permutation-group orbit `O` of a completely reachable DFA meets `M₁`, yielding
  `ℓ_eff₁ ≤ min(ℓ_orb, n - |M₁| + 1)`, reaching threshold
  `≤ (n - |S|)(ℓ_eff₁ + n) - n H_{n - |S|}`, and reset threshold
  `≤ 1 + (n - 2)(ℓ_eff₁ + n) - n H_{n - 2}` — strictly beating Ferens–Szykuła (2025) whenever
  `|M₁| ≥ 2` (with `ℓ_orb = n`), and breaking `2n²` to `(2 - ε)n² - n H_{n - 2} + O(n)` whenever
  `|M₁| ≥ ε n`.
-/

namespace Cerny

universe u v

/-! ### Public Definitions -/

/-- A DFA `A` is **completely reachable** (Volkov D2) if every nonempty subset of states is
reachable as the image `A.image Finset.univ w` of some word `w`. -/
def DFA.IsCompletelyReachable {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) : Prop :=
  ∀ S : Finset Q, S.Nonempty → ∃ w : List α, A.image Finset.univ w = S

/-- Every completely reachable DFA on a nonempty state space is synchronizing. -/
theorem DFA.IsCompletelyReachable.isSynchronizing {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] {A : DFA Q α}
    (hCR : A.IsCompletelyReachable) : A.IsSynchronizing := by
  obtain ⟨q₀⟩ := ‹Nonempty Q›
  obtain ⟨w, hw⟩ := hCR {q₀} (Finset.singleton_nonempty q₀)
  refine ⟨w, q₀, fun q => ?_⟩
  have hmem : A.eval q w ∈ ({q₀} : Finset Q) := by
    rw [← hw, DFA.mem_image]
    exact ⟨q, Finset.mem_univ q, rfl⟩
  exact Finset.mem_singleton.mp hmem

/-- A word `w` **properly extends** a subset `S` (Ferens–Szykuła) if every `s ∈ S` has at least
one preimage under `w` (equivalently `A.image (A.preimage S w) w = S`) and at least one `s ∈ S`
has `≥ 2` preimages (equivalently `S.card < (A.preimage S w).card`). -/
def DFA.ProperlyExtends {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (S : Finset Q) (w : List α) : Prop :=
  (∀ s ∈ S, 1 ≤ (A.preimage {s} w).card) ∧ ∃ s ∈ S, 2 ≤ (A.preimage {s} w).card

/-- The set `Σ₀` of bijective (permutation) letters of `A`. -/
def bijectiveLetters {Q : Type u} {α : Type v} (A : DFA Q α) : Set α :=
  { b : α | Function.Bijective (fun q => A.step q b) }

/-- Orbit reachability under words over the bijective letters `Σ₀`. -/
def permOrbitRel {Q : Type u} {α : Type v} (A : DFA Q α) (p q : Q) : Prop :=
  ∃ g : List α, (∀ b ∈ g, b ∈ bijectiveLetters A) ∧ A.eval p g = q

/-- The permutation-group orbit `O(q)` of state `q` under `⟨Σ₀⟩`. -/
noncomputable def permOrbit {Q : Type u} {α : Type v} [Fintype Q] (A : DFA Q α) (q : Q) :
    Finset Q := by
  classical
  exact Finset.univ.filter (permOrbitRel A q)

/-- The set `M₁` of states omitted by some defect-1 (rank `n - 1`) letter of `A`:
`q ∈ M₁ ↔ ∃ a, A.image Finset.univ [a] = Finset.univ.erase q`. -/
noncomputable def defectOneOmitted {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) : Finset Q := by
  classical
  exact Finset.univ.filter (fun q => ∃ a : α, A.image Finset.univ [a] = Finset.univ.erase q)

/-- Maximum permutation-group orbit size `ℓ_orb = max_{O ∈ Orb(⟨Σ₀⟩)} |O|`. -/
noncomputable def maxOrbitSize {Q : Type u} {α : Type v} [Fintype Q] (A : DFA Q α) : ℕ :=
  (Finset.univ : Finset Q).sup (fun q => (permOrbit A q).card)

/-- Effective orbit cap `ℓ_eff₁ = max_{O ∈ Orb(⟨Σ₀⟩)} |O \ M₁| + 1`. -/
noncomputable def effOrbitCap {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) : ℕ :=
  (Finset.univ : Finset Q).sup (fun q => (permOrbit A q \ defectOneOmitted A).card) + 1

/-- Rational harmonic number `H_m = ∑_{k = 1}^m (1 / k)`. -/
def harmonicRat (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 m, (1 : ℚ) / (k : ℚ)

namespace CompletelyReachable

/-! ### Section 1: Proper Extension & Bijective-Letter Orbit Helpers -/

section BasicProps

variable {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]

lemma properlyExtends_iff_image_and_card (A : DFA Q α) (S : Finset Q) (w : List α) :
    A.ProperlyExtends S w ↔
      A.image (A.preimage S w) w = S ∧ S.card < (A.preimage S w).card := by
  constructor
  · rintro ⟨hge1, s₀, hs₀, hge2⟩
    refine ⟨?_, ?_⟩
    · ext s
      simp only [DFA.mem_image, DFA.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hs
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hge1 s hs))
        rw [DFA.mem_preimage, Finset.mem_singleton] at hx
        exact ⟨x, hx ▸ hs, hx⟩
    · rw [A.card_preimage_eq_sum_singleton S w]
      have hsplit : (A.preimage {s₀} w).card + ∑ s ∈ S.erase s₀, (A.preimage {s} w).card =
          ∑ s ∈ S, (A.preimage {s} w).card :=
        Finset.add_sum_erase S (fun s => (A.preimage {s} w).card) hs₀
      have hrest : (S.erase s₀).card ≤ ∑ s ∈ S.erase s₀, (A.preimage {s} w).card := by
        calc (S.erase s₀).card = ∑ _s ∈ S.erase s₀, 1 := by simp
          _ ≤ ∑ s ∈ S.erase s₀, (A.preimage {s} w).card :=
              Finset.sum_le_sum fun s hs => hge1 s (Finset.mem_of_mem_erase hs)
      have her := Finset.card_erase_of_mem hs₀
      have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨s₀, hs₀⟩
      omega
  · rintro ⟨himg, hlt⟩
    have hge1 : ∀ s ∈ S, 1 ≤ (A.preimage {s} w).card := by
      intro s hs
      rw [← himg, DFA.mem_image] at hs
      rcases hs with ⟨x, _, rfl⟩
      exact Finset.card_pos.mpr ⟨x, by rw [DFA.mem_preimage, Finset.mem_singleton]⟩
    refine ⟨hge1, ?_⟩
    by_contra hall
    push Not at hall
    rw [A.card_preimage_eq_sum_singleton S w] at hlt
    have hle : ∑ s ∈ S, (A.preimage {s} w).card ≤ ∑ _s ∈ S, 1 :=
      Finset.sum_le_sum fun s hs => by have := hall s hs; omega
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id] at hle
    omega

lemma properlyExtends_of_image_univ {A : DFA Q α} {S : Finset Q} {w : List α}
    (hw : A.image Finset.univ w = S) (hlt : S.card < Fintype.card Q) :
    A.ProperlyExtends S w := by
  rw [properlyExtends_iff_image_and_card]
  have hpre : A.preimage S w = Finset.univ := by
    ext x
    simp only [DFA.mem_preimage, Finset.mem_univ, iff_true]
    rw [← hw, DFA.mem_image]
    exact ⟨x, Finset.mem_univ x, rfl⟩
  rw [hpre, hw, Finset.card_univ]
  exact ⟨rfl, hlt⟩

/-- **Ferens–Szykuła `lem:UnionPredecessor`**: Any word properly extending `T₁ ∪ T₂` properly
extends `T₁` or properly extends `T₂`. -/
lemma properlyExtends_union {A : DFA Q α} {T₁ T₂ : Finset Q} {w : List α}
    (h : A.ProperlyExtends (T₁ ∪ T₂) w) :
    A.ProperlyExtends T₁ w ∨ A.ProperlyExtends T₂ w := by
  rcases h with ⟨hge1, s₀, hs₀, hge2⟩
  rw [Finset.mem_union] at hs₀
  rcases hs₀ with hs₀ | hs₀
  · left
    exact ⟨fun s hs => hge1 s (Finset.mem_union_left T₂ hs), s₀, hs₀, hge2⟩
  · right
    exact ⟨fun s hs => hge1 s (Finset.mem_union_right T₁ hs), s₀, hs₀, hge2⟩

/-- Lifting a proper extension backward across a single equal-size proper letter step. -/
lemma properlyExtends_append_singleton {A : DFA Q α} {T : Finset Q} {a : α} {w : List α}
    (hbij : ∀ s ∈ T, (A.preimage {s} [a]).card = 1)
    (hw : A.ProperlyExtends (A.preimage T [a]) w) :
    A.ProperlyExtends T (w ++ [a]) := by
  rcases hw with ⟨hge1, t₀, ht₀, hge2⟩
  have hpre_eq : ∀ s ∈ T, ∃ t ∈ A.preimage T [a], A.preimage {s} [a] = {t} := by
    intro s hs
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp (hbij s hs)
    have ht_mem : t ∈ A.preimage {s} [a] := by rw [ht]; exact Finset.mem_singleton_self t
    rw [DFA.mem_preimage, Finset.mem_singleton] at ht_mem
    refine ⟨t, ?_, ht⟩
    rw [DFA.mem_preimage, ht_mem]
    exact hs
  constructor
  · intro s hs
    obtain ⟨t, htT, hteq⟩ := hpre_eq s hs
    rw [DFA.preimage_append, hteq]
    exact hge1 t htT
  · rw [DFA.mem_preimage] at ht₀
    refine ⟨A.eval t₀ [a], ht₀, ?_⟩
    obtain ⟨t', _, ht'eq⟩ := hpre_eq (A.eval t₀ [a]) ht₀
    have ht₀_in : t₀ ∈ A.preimage {A.eval t₀ [a]} [a] := by
      rw [DFA.mem_preimage, Finset.mem_singleton]
    rw [ht'eq, Finset.mem_singleton] at ht₀_in
    subst ht₀_in
    rw [DFA.preimage_append, ht'eq]
    exact hge2

/-- Characterizing 1-letter proper extensions of `(n - 1)`-sets: `[a]` properly extends
`Finset.univ.erase q` if and only if `a` is a defect-1 letter omitting `q`. -/
lemma properlyExtends_erase_singleton_iff (A : DFA Q α) (q : Q) (a : α) :
    A.ProperlyExtends (Finset.univ.erase q) [a] ↔
      A.image Finset.univ [a] = Finset.univ.erase q := by
  constructor
  · intro h
    rw [properlyExtends_iff_image_and_card] at h
    rcases h with ⟨himg, hlt⟩
    have hpre_univ : A.preimage (Finset.univ.erase q) [a] = Finset.univ := by
      have hle := Finset.card_le_univ (A.preimage (Finset.univ.erase q) [a])
      have her := Finset.card_erase_of_mem (Finset.mem_univ q)
      rw [Finset.card_univ] at her
      exact Finset.eq_univ_of_card _ (by omega)
    rwa [hpre_univ] at himg
  · intro himg
    apply properlyExtends_of_image_univ himg
    have her := Finset.card_erase_of_mem (Finset.mem_univ q)
    rw [Finset.card_univ] at her
    have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q⟩
    omega

omit [DecidableEq Q] in
/-- Any finite bijection `f : Q → Q` has a finite iterate sending `f p` back to `p`. -/
lemma bijective_exists_iter_back {f : Q → Q} (hf : Function.Bijective f) (p : Q) :
    ∃ k : ℕ, f^[k] (f p) = p := by
  have hnotinj : ¬ Function.Injective (fun i : Fin (Fintype.card Q + 1) => f^[i.val] p) := by
    intro hinj
    have hle := Fintype.card_le_of_injective _ hinj
    simp at hle
  rw [Function.Injective] at hnotinj
  push Not at hnotinj
  rcases hnotinj with ⟨i, j, hij, hne⟩
  have hstep : ∀ x y : ℕ, x < y → f^[x] p = f^[y] p → ∃ k : ℕ, f^[k] (f p) = p := by
    intro x y hxy heq
    have hsplit : y = x + (y - x) := by omega
    rw [hsplit, Function.iterate_add_apply] at heq
    have hfix : f^[y - x] p = p := (hf.1.iterate x) heq.symm
    refine ⟨y - x - 1, ?_⟩
    have hsucc : y - x = (y - x - 1) + 1 := by omega
    rw [hsucc, Function.iterate_succ_apply] at hfix
    exact hfix
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact hstep i.val j.val hlt hij
  · exact hstep j.val i.val hgt hij.symm

omit [Fintype Q] [DecidableEq Q] in
lemma permOrbitRel_refl (A : DFA Q α) (p : Q) : permOrbitRel A p p :=
  ⟨[], fun _ h => absurd h (List.not_mem_nil), rfl⟩

omit [Fintype Q] [DecidableEq Q] in
lemma permOrbitRel_trans {A : DFA Q α} {p q r : Q}
    (h1 : permOrbitRel A p q) (h2 : permOrbitRel A q r) : permOrbitRel A p r := by
  rcases h1 with ⟨g₁, hg₁, h₁⟩
  rcases h2 with ⟨g₂, hg₂, h₂⟩
  refine ⟨g₁ ++ g₂, ?_, by rw [DFA.eval_append, h₁, h₂]⟩
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact hg₁ b hb
  · exact hg₂ b hb

omit [DecidableEq Q] in
lemma permOrbitRel_symm {A : DFA Q α} {p q : Q} (h : permOrbitRel A p q) :
    permOrbitRel A q p := by
  rcases h with ⟨g, hg, rfl⟩
  induction g generalizing p with
  | nil => exact permOrbitRel_refl A p
  | cons b g ih =>
    have hb : b ∈ bijectiveLetters A := hg b List.mem_cons_self
    have hg' : ∀ c ∈ g, c ∈ bijectiveLetters A := fun c hc => hg c (List.mem_cons_of_mem b hc)
    have htail : permOrbitRel A (A.eval (A.step p b) g) (A.step p b) := ih hg'
    obtain ⟨k, hk⟩ := bijective_exists_iter_back hb p
    have hback : permOrbitRel A (A.step p b) p := by
      refine ⟨List.replicate k b, ?_, ?_⟩
      · intro c hc
        rw [List.mem_replicate] at hc
        exact hc.2 ▸ hb
      · rw [DFA.eval_replicate]; exact hk
    exact permOrbitRel_trans htail hback

omit [DecidableEq Q] in
lemma mem_permOrbit (A : DFA Q α) (p q : Q) : q ∈ permOrbit A p ↔ permOrbitRel A p q := by
  classical
  simp [permOrbit]

lemma mem_defectOneOmitted (A : DFA Q α) (q : Q) :
    q ∈ defectOneOmitted A ↔ ∃ a : α, A.image Finset.univ [a] = Finset.univ.erase q := by
  classical
  simp [defectOneOmitted]

omit [Fintype Q] [DecidableEq Q] in
/-- Split any word containing at least one non-bijective letter at its LAST non-bijective letter. -/
lemma split_last_nonbijective (A : DFA Q α) :
    ∀ w : List α, (¬ ∀ b ∈ w, b ∈ bijectiveLetters A) →
      ∃ u : List α, ∃ a : α, ∃ g : List α,
        w = u ++ [a] ++ g ∧ a ∉ bijectiveLetters A ∧ (∀ b ∈ g, b ∈ bijectiveLetters A) := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro h; exact absurd (fun _ hm => absurd hm (List.not_mem_nil)) h
  | append_singleton w' c ih =>
    intro hnot
    by_cases hc : c ∈ bijectiveLetters A
    · have hnot' : ¬ ∀ b ∈ w', b ∈ bijectiveLetters A := by
        intro hall
        apply hnot
        intro b hb
        simp only [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact hall b hb
        · exact hc
      obtain ⟨u, a, g, hw', ha, hg⟩ := ih hnot'
      refine ⟨u, a, g ++ [c], ?_, ha, ?_⟩
      · rw [hw']; simp [List.append_assoc]
      · intro b hb
        simp only [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact hg b hb
        · exact hc
    · exact ⟨w', c, [], by simp, hc, fun _ hm => absurd hm (List.not_mem_nil)⟩

/-- In any completely reachable DFA (`n ≥ 2`), EVERY permutation-group orbit meets `M₁`. -/
theorem permOrbit_inter_defectOneOmitted_nonempty {A : DFA Q α}
    (hCR : A.IsCompletelyReachable) (hn2 : 2 ≤ Fintype.card Q) (q : Q) :
    ∃ q' ∈ permOrbit A q, q' ∈ defectOneOmitted A := by
  have her_card : (Finset.univ.erase q).card = Fintype.card Q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ]
  have her_ne : (Finset.univ.erase q).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w, hw⟩ := hCR (Finset.univ.erase q) her_ne
  have hnot_all : ¬ ∀ b ∈ w, b ∈ bijectiveLetters A := by
    intro hall
    have hbij := VolkovD6Transitive.bijective_eval_of_mem (S₀ := bijectiveLetters A)
      (fun b hb => hb) w hall
    have himg_card : (A.image Finset.univ w).card = Fintype.card Q := by
      rw [DFA.image, Finset.card_image_of_injective _ hbij.1, Finset.card_univ]
    rw [hw, her_card] at himg_card
    omega
  obtain ⟨u, a, g, rfl, ha_not, hg_bij⟩ := split_last_nonbijective A w hnot_all
  have hg_eval_bij : Function.Bijective (fun x => A.eval x g) :=
    VolkovD6Transitive.bijective_eval_of_mem (S₀ := bijectiveLetters A) (fun b hb => hb) g hg_bij
  let R : Finset Q := A.image Finset.univ [a]
  have hR_lt : R.card < Fintype.card Q := by
    have hle := Finset.card_le_univ R
    refine lt_of_le_of_ne hle fun heq => ha_not ?_
    have hRuniv : R = Finset.univ := Finset.eq_univ_of_card R heq
    have hsurj : Function.Surjective (fun x => A.step x a) := fun y => by
      have hy : y ∈ R := hRuniv ▸ Finset.mem_univ y
      rw [DFA.mem_image] at hy
      rcases hy with ⟨x, _, hx⟩
      exact ⟨x, by simpa only [DFA.eval_singleton] using hx⟩
    exact (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, rfl⟩
  have hsub : Finset.univ.erase q ⊆ A.image R g := by
    rw [← hw]
    intro y hy
    rw [DFA.mem_image] at hy ⊢
    rcases hy with ⟨x, _, rfl⟩
    refine ⟨A.eval (A.eval x u) [a], ?_, ?_⟩
    · rw [DFA.mem_image]; exact ⟨A.eval x u, Finset.mem_univ _, rfl⟩
    · rw [List.append_assoc, DFA.eval_append, DFA.eval_append]
  have hRg_card : (A.image R g).card = R.card := by
    rw [DFA.image, Finset.card_image_of_injective _ hg_eval_bij.1]
  have hR_card : R.card = Fintype.card Q - 1 := by
    have hle := Finset.card_le_card hsub
    rw [her_card, hRg_card] at hle
    omega
  have hRg_eq : A.image R g = Finset.univ.erase q :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [her_card, hRg_card, hR_card])).symm
  have hR_ne_univ : R ≠ Finset.univ := fun h => by rw [h, Finset.card_univ] at hR_lt; omega
  obtain ⟨q', _, hq'_not⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ R, hR_ne_univ⟩)
  have hR_eq : R = Finset.univ.erase q' := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; exact Finset.mem_erase.mpr ⟨fun h => hq'_not (h ▸ hx), Finset.mem_univ x⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_univ q'), Finset.card_univ, hR_card]
  have hq'_img : A.eval q' g = q := by
    by_contra hne
    have hmem : A.eval q' g ∈ A.image R g := by
      rw [hRg_eq]; exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
    rw [DFA.mem_image] at hmem
    rcases hmem with ⟨x, hxR, hxeq⟩
    exact hq'_not (hg_eval_bij.1 hxeq ▸ hxR)
  have horb : permOrbitRel A q q' := permOrbitRel_symm ⟨g, hg_bij, hq'_img⟩
  exact ⟨q', (mem_permOrbit A q q').mpr horb, (mem_defectOneOmitted A q').mpr ⟨a, hR_eq⟩⟩

/-- `ℓ_eff₁ ≤ ℓ_orb` for every completely reachable DFA (`n ≥ 2`). -/
theorem effOrbitCap_le_maxOrbitSize {A : DFA Q α}
    (hCR : A.IsCompletelyReachable) (hn2 : 2 ≤ Fintype.card Q) :
    effOrbitCap A ≤ maxOrbitSize A := by
  dsimp only [effOrbitCap, maxOrbitSize]
  have hsup : (Finset.univ : Finset Q).sup (fun q => (permOrbit A q \ defectOneOmitted A).card) + 1 ≤
      (Finset.univ : Finset Q).sup (fun q => (permOrbit A q).card) := by
    have hpos : ∀ q : Q, (permOrbit A q \ defectOneOmitted A).card + 1 ≤ (permOrbit A q).card := by
      intro q
      obtain ⟨q', hq'O, hq'M⟩ := permOrbit_inter_defectOneOmitted_nonempty hCR hn2 q
      have hssub : permOrbit A q \ defectOneOmitted A ⊂ permOrbit A q := by
        rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
        exact ⟨q', hq'O, fun h => (Finset.mem_sdiff.mp h).2 hq'M⟩
      exact Finset.card_lt_card hssub
    obtain ⟨q₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card Q)
    have hle : ∀ q ∈ (Finset.univ : Finset Q),
        (permOrbit A q \ defectOneOmitted A).card + 1 ≤
          (Finset.univ : Finset Q).sup (fun p => (permOrbit A p).card) := fun q hq =>
      (hpos q).trans (Finset.le_sup (f := fun p => (permOrbit A p).card) hq)
    have hsup_le : (Finset.univ : Finset Q).sup (fun q => (permOrbit A q \ defectOneOmitted A).card) ≤
        (Finset.univ : Finset Q).sup (fun p => (permOrbit A p).card) - 1 := by
      refine Finset.sup_le fun q hq => ?_
      have := hle q hq
      omega
    have hq₀_pos : 1 ≤ (Finset.univ : Finset Q).sup (fun p => (permOrbit A p).card) := by
      have := hle q₀ (Finset.mem_univ q₀); omega
    omega
  exact hsup

/-- `ℓ_eff₁ ≤ n - |M₁| + 1` unconditionally. -/
theorem effOrbitCap_le_card_sub_omitted (A : DFA Q α) :
    effOrbitCap A ≤ Fintype.card Q - (defectOneOmitted A).card + 1 := by
  dsimp only [effOrbitCap]
  have hsup : (Finset.univ : Finset Q).sup (fun q => (permOrbit A q \ defectOneOmitted A).card) ≤
      Fintype.card Q - (defectOneOmitted A).card := by
    refine Finset.sup_le fun q _ => ?_
    have hsub : permOrbit A q \ defectOneOmitted A ⊆ Finset.univ \ defectOneOmitted A :=
      Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _)
    have hcard := Finset.card_le_card hsub
    rwa [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at hcard
  omega

/-- Shortest `Σ₀`-path to `M₁`: every `(n - 1)`-subset `Finset.univ.erase q₀` has a proper
extension of length at most `effOrbitCap A`. -/
theorem exists_properExt_erase_singleton {A : DFA Q α}
    (hCR : A.IsCompletelyReachable) (hn2 : 2 ≤ Fintype.card Q) (q₀ : Q) :
    ∃ w : List α, A.ProperlyExtends (Finset.univ.erase q₀) w ∧ w.length ≤ effOrbitCap A := by
  classical
  have hex : ∃ k : ℕ, ∃ g : List α, g.length = k ∧ (∀ b ∈ g, b ∈ bijectiveLetters A) ∧
      ∃ q₁ ∈ defectOneOmitted A, A.eval q₁ g = q₀ := by
    obtain ⟨q₁, hq₁O, hq₁M⟩ := permOrbit_inter_defectOneOmitted_nonempty hCR hn2 q₀
    obtain ⟨g, hg, hgeq⟩ := permOrbitRel_symm ((mem_permOrbit A q₀ q₁).mp hq₁O)
    exact ⟨g.length, g, rfl, hg, q₁, hq₁M, hgeq⟩
  let k := Nat.find hex
  obtain ⟨g, hglen, hgBij, q₁, hq₁M, hgeq⟩ := Nat.find_spec hex
  -- The `k` intermediate states `z i = q₁ · g[0..i]` are distinct elements of `permOrbit q₀ \ M₁`
  let z : Fin k → Q := fun i => A.eval q₁ (g.take (i.val + 1))
  have hz_mem : ∀ i : Fin k, z i ∈ permOrbit A q₀ \ defectOneOmitted A := by
    intro i
    rw [Finset.mem_sdiff]
    have hdrop_bij : ∀ b ∈ g.drop (i.val + 1), b ∈ bijectiveLetters A := fun b hb =>
      hgBij b (List.mem_of_mem_drop hb)
    have hdrop_eval : A.eval (z i) (g.drop (i.val + 1)) = q₀ := by
      dsimp only [z]
      rw [← DFA.eval_append, List.take_append_drop, hgeq]
    constructor
    · exact (mem_permOrbit A q₀ (z i)).mpr (permOrbitRel_symm ⟨g.drop (i.val + 1), hdrop_bij, hdrop_eval⟩)
    · intro hM
      have hlen_lt : (g.drop (i.val + 1)).length < k := by
        rw [List.length_drop, hglen]; have := i.isLt; omega
      exact Nat.find_min hex hlen_lt ⟨g.drop (i.val + 1), rfl, hdrop_bij, z i, hM, hdrop_eval⟩
  have hz_inj : Function.Injective z := by
    intro i j hij
    by_contra hne
    have hstep : ∀ x y : ℕ, x < y → y < k →
        A.eval q₁ (g.take (x + 1)) = A.eval q₁ (g.take (y + 1)) → False := by
      intro x y hxy hyk heq
      let g' := g.take (x + 1) ++ g.drop (y + 1)
      have hg'_len : g'.length < k := by
        simp only [g', List.length_append, List.length_take, List.length_drop, hglen]
        omega
      have hg'_bij : ∀ b ∈ g', b ∈ bijectiveLetters A := by
        intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact hgBij b (List.mem_of_mem_take hb)
        · exact hgBij b (List.mem_of_mem_drop hb)
      have hg'_eval : A.eval q₁ g' = q₀ := by
        dsimp only [g']
        rw [DFA.eval_append, heq, ← DFA.eval_append, List.take_append_drop, hgeq]
      exact Nat.find_min hex hg'_len ⟨g', rfl, hg'_bij, q₁, hq₁M, hg'_eval⟩
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hstep i.val j.val hlt j.isLt hij
    · exact hstep j.val i.val hgt i.isLt hij.symm
  have hk_le : k ≤ (permOrbit A q₀ \ defectOneOmitted A).card := by
    let φ : Fin k → {x // x ∈ permOrbit A q₀ \ defectOneOmitted A} := fun i => ⟨z i, hz_mem i⟩
    have hφ_inj : Function.Injective φ := fun i j h => hz_inj (congrArg Subtype.val h)
    have hcard := Fintype.card_le_of_injective φ hφ_inj
    simpa only [Fintype.card_fin, Fintype.card_coe] using hcard
  -- Prepend the defect-1 letter `a` omitting `q₁`
  obtain ⟨a, ha_img⟩ := (mem_defectOneOmitted A q₁).mp hq₁M
  have hg_eval_bij : Function.Bijective (fun x => A.eval x g) :=
    VolkovD6Transitive.bijective_eval_of_mem (S₀ := bijectiveLetters A) (fun b hb => hb) g hgBij
  let e : Q ≃ Q := Equiv.ofBijective (fun x => A.eval x g) hg_eval_bij
  have hpre_erase : A.preimage (Finset.univ.erase q₀) (a :: g) = Finset.univ := by
    ext x
    simp only [DFA.mem_preimage, Finset.mem_erase, Finset.mem_univ, and_true, iff_true,
      DFA.eval_cons]
    intro heq
    have hstep_ne : A.step x a ≠ q₁ := by
      have hmem : A.step x a ∈ Finset.univ.erase q₁ := by
        rw [← ha_img, DFA.mem_image]; exact ⟨x, Finset.mem_univ x, rfl⟩
      exact (Finset.mem_erase.mp hmem).1
    exact hstep_ne (hg_eval_bij.1 (heq.trans hgeq.symm))
  have himg_ag : A.image Finset.univ (a :: g) = Finset.univ.erase q₀ := by
    ext y
    simp only [DFA.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · rintro ⟨x, rfl⟩
      have hmem : x ∈ A.preimage (Finset.univ.erase q₀) (a :: g) := by
        rw [hpre_erase]; exact Finset.mem_univ x
      rw [DFA.mem_preimage, Finset.mem_erase] at hmem
      exact hmem.1
    · intro hyne
      have hsymm_ne : e.symm y ≠ q₁ := fun h => hyne (by rw [← hgeq, ← h]; exact (e.apply_symm_apply y).symm)
      have hmem : e.symm y ∈ A.image Finset.univ [a] := by
        rw [ha_img]; exact Finset.mem_erase.mpr ⟨hsymm_ne, Finset.mem_univ _⟩
      rw [DFA.mem_image] at hmem
      rcases hmem with ⟨x, _, hx⟩
      refine ⟨x, ?_⟩
      rw [DFA.eval_cons]
      change e (A.step x a) = y
      have hx' : A.step x a = e.symm y := by simpa only [DFA.eval_singleton] using hx
      rw [hx', e.apply_symm_apply]
  have hlen_le : (a :: g).length ≤ effOrbitCap A := by
    dsimp only [effOrbitCap]
    rw [List.length_cons, hglen]
    have hsup := Finset.le_sup (f := fun q => (permOrbit A q \ defectOneOmitted A).card)
      (Finset.mem_univ q₀)
    omega
  refine ⟨a :: g, ?_, hlen_le⟩
  apply properlyExtends_of_image_univ himg_ag
  rw [Finset.card_erase_of_mem (Finset.mem_univ q₀), Finset.card_univ]
  omega

end BasicProps

/-! ### Section 2: Exact Laminar Family Bound (`lem:BoundedTriviallyIntersectingSubsets`) -/

section LaminarBound

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- A family `ℱ` of subsets of `Q` is **laminar** (trivially intersecting) if any two members are
disjoint or comparable by inclusion. -/
def IsLaminar (ℱ : Finset (Finset Q)) : Prop :=
  ∀ A ∈ ℱ, ∀ B ∈ ℱ, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A

/-- Any laminar family `ℱ` of subsets of `U` (`1 ≤ |U|`), each of size `≥ 2`, has `|ℱ| ≤ |U| - 1`. -/
lemma laminar_le_card_sub_one :
    ∀ m : ℕ, ∀ U : Finset Q, U.card = m → 1 ≤ U.card →
      ∀ ℱ : Finset (Finset Q), IsLaminar ℱ →
        (∀ A ∈ ℱ, A ⊆ U ∧ 2 ≤ A.card) →
        ℱ.card ≤ U.card - 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro U hUm hU1 ℱ hLam hSub
    -- Helper: for any subfamily `𝒢 ⊆ ℱ` with `U ∉ 𝒢`, bound `𝒢.card` via maximal elements
    have hproper_bound : ∀ 𝒢 : Finset (Finset Q), IsLaminar 𝒢 →
        (∀ A ∈ 𝒢, A ⊆ U ∧ 2 ≤ A.card) → U ∉ 𝒢 →
        let Max𝒢 := 𝒢.filter (fun M => ∀ B ∈ 𝒢, M ⊆ B → B = M)
        𝒢.card + Max𝒢.card ≤ U.card ∧ (Max𝒢.card = 1 → 𝒢.card ≤ U.card - 2) := by
      intro 𝒢 hLamG hSubG hUnotG Max𝒢
      have hMax_sub : Max𝒢 ⊆ 𝒢 := Finset.filter_subset _ _
      have hMax_disj : Set.PairwiseDisjoint (↑Max𝒢 : Set (Finset Q)) id := by
        intro M₁ hM₁ M₂ hM₂ hne
        have hM₁_spec := Finset.mem_filter.mp hM₁
        have hM₂_spec := Finset.mem_filter.mp hM₂
        rcases hLamG M₁ hM₁_spec.1 M₂ hM₂_spec.1 with hdisj | h12 | h21
        · exact hdisj
        · exact absurd (hM₁_spec.2 M₂ hM₂_spec.1 h12).symm hne
        · exact absurd (hM₂_spec.2 M₁ hM₁_spec.1 h21) hne
      have hex_max : ∀ A ∈ 𝒢, ∃ M ∈ Max𝒢, A ⊆ M := by
        intro A hA
        let Up := 𝒢.filter (fun B => A ⊆ B)
        have hUp_ne : Up.Nonempty := ⟨A, Finset.mem_filter.mpr ⟨hA, Finset.Subset.refl A⟩⟩
        obtain ⟨M, hMUp, hMmax⟩ := Finset.exists_max_image Up Finset.card hUp_ne
        have hM_spec := Finset.mem_filter.mp hMUp
        refine ⟨M, Finset.mem_filter.mpr ⟨hM_spec.1, fun B hBG hMB => ?_⟩, hM_spec.2⟩
        have hBUp : B ∈ Up := Finset.mem_filter.mpr ⟨hBG, hM_spec.2.trans hMB⟩
        exact (Finset.eq_of_subset_of_card_le hMB (hMmax B hBUp)).symm
      let part : Finset Q → Finset (Finset Q) := fun M => 𝒢.filter (fun A => A ⊆ M)
      have hpart_disj : Set.PairwiseDisjoint (↑Max𝒢 : Set (Finset Q)) part := by
        intro M₁ hM₁ M₂ hM₂ hne
        show Disjoint (part M₁) (part M₂)
        rw [Finset.disjoint_left]
        intro A hA1 hA2
        have hA_spec := Finset.mem_filter.mp hA1
        have hA2_spec := Finset.mem_filter.mp hA2
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by have := (hSubG A hA_spec.1).2; omega : 0 < A.card)
        exact Finset.disjoint_left.mp (hMax_disj hM₁ hM₂ hne) (hA_spec.2 hx) (hA2_spec.2 hx)
      have hG_eq : Max𝒢.biUnion part = 𝒢 := by
        ext A
        simp only [Finset.mem_biUnion, part, Finset.mem_filter]
        constructor
        · rintro ⟨_, _, hAG, _⟩; exact hAG
        · intro hAG; obtain ⟨M, hMM, hAM⟩ := hex_max A hAG; exact ⟨M, hMM, hAG, hAM⟩
      have hpart_bound : ∀ M ∈ Max𝒢, (part M).card + 1 ≤ M.card := by
        intro M hM
        have hMG : M ∈ 𝒢 := (Finset.mem_filter.mp hM).1
        have hMU : M ⊆ U := (hSubG M hMG).1
        have hM2 : 2 ≤ M.card := (hSubG M hMG).2
        have hM_lt : M.card < m := by
          rw [← hUm]
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hMU, fun h => hUnotG (h ▸ hMG)⟩)
        have hLamP : IsLaminar (part M) := fun A hA B hB =>
          hLamG A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1
        have hSubP : ∀ A ∈ part M, A ⊆ M ∧ 2 ≤ A.card := fun A hA =>
          ⟨(Finset.mem_filter.mp hA).2, (hSubG A (Finset.mem_filter.mp hA).1).2⟩
        have hle := ih M.card hM_lt M rfl (by omega) (part M) hLamP hSubP
        omega
      have hbiUnion_sub : Max𝒢.biUnion id ⊆ U := by
        intro x hx
        rw [Finset.mem_biUnion] at hx
        rcases hx with ⟨M, hM, hxM⟩
        exact (hSubG M (Finset.mem_filter.mp hM).1).1 hxM
      have hsum_M : ∑ M ∈ Max𝒢, M.card ≤ U.card := by
        have hcard_u := Finset.card_biUnion hMax_disj
        calc ∑ M ∈ Max𝒢, M.card = (Max𝒢.biUnion id).card := hcard_u.symm
          _ ≤ U.card := Finset.card_le_card hbiUnion_sub
      have hcard_G : 𝒢.card = ∑ M ∈ Max𝒢, (part M).card := by
        rw [← hG_eq, Finset.card_biUnion hpart_disj]
      constructor
      · calc 𝒢.card + Max𝒢.card
            = (∑ M ∈ Max𝒢, (part M).card) + ∑ _M ∈ Max𝒢, 1 := by simp [hcard_G]
          _ = ∑ M ∈ Max𝒢, ((part M).card + 1) := (Finset.sum_add_distrib).symm
          _ ≤ ∑ M ∈ Max𝒢, M.card := Finset.sum_le_sum hpart_bound
          _ ≤ U.card := hsum_M
      · intro hcard1
        obtain ⟨M, hMeq⟩ := Finset.card_eq_one.mp hcard1
        have hM_in : M ∈ Max𝒢 := by rw [hMeq]; exact Finset.mem_singleton_self M
        have hMG : M ∈ 𝒢 := (Finset.mem_filter.mp hM_in).1
        have hM_lt : M.card < U.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨(hSubG M hMG).1, fun h => hUnotG (h ▸ hMG)⟩)
        have h1 := hpart_bound M hM_in
        rw [hcard_G, hMeq, Finset.sum_singleton]
        omega
    by_cases hU : U ∈ ℱ
    · have hU2 : 2 ≤ U.card := (hSub U hU).2
      let ℱ' := ℱ.erase U
      have hLam' : IsLaminar ℱ' := fun A hA B hB =>
        hLam A (Finset.mem_of_mem_erase hA) B (Finset.mem_of_mem_erase hB)
      have hSub' : ∀ A ∈ ℱ', A ⊆ U ∧ 2 ≤ A.card := fun A hA =>
        hSub A (Finset.mem_of_mem_erase hA)
      have hpb := hproper_bound ℱ' hLam' hSub' (Finset.notMem_erase U ℱ)
      let Max' := ℱ'.filter (fun M => ∀ B ∈ ℱ', M ⊆ B → B = M)
      have hcard_er : ℱ'.card + 1 = ℱ.card := by
        dsimp only [ℱ']
        rw [Finset.card_erase_of_mem hU]
        have hpos : 1 ≤ ℱ.card := Finset.card_pos.mpr ⟨U, hU⟩
        omega
      by_cases h0 : Max'.card = 0
      · have hMax_empty : Max' = ∅ := Finset.card_eq_zero.mp h0
        have hF'_empty : ℱ' = ∅ := by
          by_contra hne
          obtain ⟨A, hA⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          let Up := ℱ'.filter (fun B => A ⊆ B)
          obtain ⟨M, hMUp, hMmax⟩ := Finset.exists_max_image Up Finset.card
            ⟨A, Finset.mem_filter.mpr ⟨hA, Finset.Subset.refl A⟩⟩
          have hM_spec := Finset.mem_filter.mp hMUp
          have hM_in : M ∈ Max' := Finset.mem_filter.mpr ⟨hM_spec.1, fun B hB hMB =>
            (Finset.eq_of_subset_of_card_le hMB
              (hMmax B (Finset.mem_filter.mpr ⟨hB, hM_spec.2.trans hMB⟩))).symm⟩
          rw [hMax_empty] at hM_in
          exact absurd hM_in (Finset.notMem_empty M)
        rw [hF'_empty, Finset.card_empty] at hcard_er
        omega
      · by_cases h1 : Max'.card = 1
        · have := hpb.2 h1; omega
        · have hge2 : 2 ≤ Max'.card := by omega
          have hsum : ℱ'.card + Max'.card ≤ U.card := hpb.1
          omega
    · have hpb := hproper_bound ℱ hLam hSub hU
      let Maxℱ := ℱ.filter (fun M => ∀ B ∈ ℱ, M ⊆ B → B = M)
      by_cases h0 : Maxℱ.card = 0
      · have hMax_empty : Maxℱ = ∅ := Finset.card_eq_zero.mp h0
        have hF_empty : ℱ = ∅ := by
          by_contra hne
          obtain ⟨A, hA⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          let Up := ℱ.filter (fun B => A ⊆ B)
          obtain ⟨M, hMUp, hMmax⟩ := Finset.exists_max_image Up Finset.card
            ⟨A, Finset.mem_filter.mpr ⟨hA, Finset.Subset.refl A⟩⟩
          have hM_spec := Finset.mem_filter.mp hMUp
          have hM_in : M ∈ Maxℱ := Finset.mem_filter.mpr ⟨hM_spec.1, fun B hB hMB =>
            (Finset.eq_of_subset_of_card_le hMB
              (hMmax B (Finset.mem_filter.mpr ⟨hB, hM_spec.2.trans hMB⟩))).symm⟩
          rw [hMax_empty] at hM_in
          exact absurd hM_in (Finset.notMem_empty M)
        rw [hF_empty, Finset.card_empty]
        omega
      · have hsum : ℱ.card + Maxℱ.card ≤ U.card := hpb.1; omega

/-- **Ferens–Szykuła `lem:BoundedTriviallyIntersectingSubsets` (Exact `ℕ` Form)**:
For any laminar family `ℱ` on `Q` whose sets all have size in `[2, k]` (`1 ≤ k`),
`k * ℱ.card + Fintype.card Q ≤ k * Fintype.card Q`. -/
theorem laminar_bounded_mul_le (ℱ : Finset (Finset Q)) (k : ℕ) (hk : 1 ≤ k)
    (hLam : IsLaminar ℱ) (hSize : ∀ A ∈ ℱ, 2 ≤ A.card ∧ A.card ≤ k) :
    k * ℱ.card + Fintype.card Q ≤ k * Fintype.card Q := by
  let Maxℱ := ℱ.filter (fun M => ∀ B ∈ ℱ, M ⊆ B → B = M)
  have hMax_disj : Set.PairwiseDisjoint (↑Maxℱ : Set (Finset Q)) id := by
    intro M₁ hM₁ M₂ hM₂ hne
    have h1 := Finset.mem_filter.mp hM₁
    have h2 := Finset.mem_filter.mp hM₂
    rcases hLam M₁ h1.1 M₂ h2.1 with hdisj | h12 | h21
    · exact hdisj
    · exact absurd (h1.2 M₂ h2.1 h12).symm hne
    · exact absurd (h2.2 M₁ h1.1 h21) hne
  have hex_max : ∀ A ∈ ℱ, ∃ M ∈ Maxℱ, A ⊆ M := by
    intro A hA
    let Up := ℱ.filter (fun B => A ⊆ B)
    obtain ⟨M, hMUp, hMmax⟩ := Finset.exists_max_image Up Finset.card
      ⟨A, Finset.mem_filter.mpr ⟨hA, Finset.Subset.refl A⟩⟩
    have hM_spec := Finset.mem_filter.mp hMUp
    refine ⟨M, Finset.mem_filter.mpr ⟨hM_spec.1, fun B hB hMB => ?_⟩, hM_spec.2⟩
    exact (Finset.eq_of_subset_of_card_le hMB
      (hMmax B (Finset.mem_filter.mpr ⟨hB, hM_spec.2.trans hMB⟩))).symm
  let part : Finset Q → Finset (Finset Q) := fun M => ℱ.filter (fun A => A ⊆ M)
  have hpart_disj : Set.PairwiseDisjoint (↑Maxℱ : Set (Finset Q)) part := by
    intro M₁ hM₁ M₂ hM₂ hne
    show Disjoint (part M₁) (part M₂)
    rw [Finset.disjoint_left]
    intro A hA1 hA2
    have h1 := Finset.mem_filter.mp hA1
    have h2 := Finset.mem_filter.mp hA2
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by have := (hSize A h1.1).1; omega : 0 < A.card)
    exact Finset.disjoint_left.mp (hMax_disj hM₁ hM₂ hne) (h1.2 hx) (h2.2 hx)
  have hF_eq : Maxℱ.biUnion part = ℱ := by
    ext A
    simp only [Finset.mem_biUnion, part, Finset.mem_filter]
    constructor
    · rintro ⟨_, _, hAF, _⟩; exact hAF
    · intro hAF; obtain ⟨M, hMM, hAM⟩ := hex_max A hAF; exact ⟨M, hMM, hAF, hAM⟩
  have hcard_F : ℱ.card = ∑ M ∈ Maxℱ, (part M).card := by
    rw [← hF_eq, Finset.card_biUnion hpart_disj]
  have hpart_le : ∀ M ∈ Maxℱ, (part M).card ≤ M.card - 1 := by
    intro M hM
    have hMF := (Finset.mem_filter.mp hM).1
    have hM2 := (hSize M hMF).1
    exact laminar_le_card_sub_one M.card M rfl (by omega) (part M)
      (fun A hA B hB => hLam A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1)
      (fun A hA => ⟨(Finset.mem_filter.mp hA).2, (hSize A (Finset.mem_filter.mp hA).1).1⟩)
  set sumM := ∑ M ∈ Maxℱ, M.card
  have hsumM_le : sumM ≤ Fintype.card Q := by
    have hcu := Finset.card_biUnion hMax_disj
    calc sumM = (Maxℱ.biUnion id).card := hcu.symm
      _ ≤ Fintype.card Q := Finset.card_le_univ _
  have hterm : ∀ M ∈ Maxℱ, k * (part M).card + M.card ≤ k * M.card := by
    intro M hM
    have hMF := (Finset.mem_filter.mp hM).1
    have hMsize := hSize M hMF
    have hp := hpart_le M hM
    have hmul : k * (M.card - 1) + k = k * M.card := by
      calc k * (M.card - 1) + k = k * ((M.card - 1) + 1) := by ring
        _ = k * M.card := by congr 1; omega
    have h1 : k * (part M).card ≤ k * (M.card - 1) := Nat.mul_le_mul_left k hp
    omega
  have hsum_bound : k * ℱ.card + sumM ≤ k * sumM := by
    calc k * ℱ.card + sumM
        = (∑ M ∈ Maxℱ, k * (part M).card) + ∑ M ∈ Maxℱ, M.card := by
            rw [hcard_F, Finset.mul_sum]
      _ = ∑ M ∈ Maxℱ, (k * (part M).card + M.card) := (Finset.sum_add_distrib).symm
      _ ≤ ∑ M ∈ Maxℱ, (k * M.card) := Finset.sum_le_sum hterm
      _ = k * sumM := (Finset.mul_sum Maxℱ Finset.card k).symm
  set rem := Fintype.card Q - sumM
  have hrem_le : rem ≤ k * rem := Nat.le_mul_of_pos_left rem (by omega)
  have hadd : k * sumM + k * rem = k * Fintype.card Q := by
    calc k * sumM + k * rem = k * (sumM + rem) := (Nat.mul_add k sumM rem).symm
      _ = k * Fintype.card Q := by congr 1; omega
  omega

/-- Rational form of `laminar_bounded_mul_le`: `(|ℱ| : ℚ) ≤ n - n / k`. -/
lemma laminar_bounded_rat_le (ℱ : Finset (Finset Q)) (k : ℕ) (hk : 1 ≤ k)
    (hLam : IsLaminar ℱ) (hSize : ∀ A ∈ ℱ, 2 ≤ A.card ∧ A.card ≤ k) :
    (ℱ.card : ℚ) ≤ (Fintype.card Q : ℚ) - (Fintype.card Q : ℚ) / (k : ℚ) := by
  have hnat := laminar_bounded_mul_le ℱ k hk hLam hSize
  have hQ : ((k : ℚ) * (ℱ.card : ℚ) + (Fintype.card Q : ℚ)) ≤ (k : ℚ) * (Fintype.card Q : ℚ) := by
    exact_mod_cast hnat
  have hkpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast (show 0 < k by omega)
  have hdiv : (Fintype.card Q : ℚ) / (k : ℚ) ≤ (Fintype.card Q : ℚ) - (ℱ.card : ℚ) :=
    (div_le_iff₀ hkpos).mpr (by nlinarith)
  linarith

/-- Complement-laminar predicate on a family `𝒳` of subsets of `Q`:
complements `{Q \ X | X ∈ 𝒳}` are laminar (`X ∪ Y = univ ∨ X ⊆ Y ∨ Y ⊆ X`). -/
def IsComplLaminar (𝒳 : Finset (Finset Q)) : Prop :=
  ∀ X ∈ 𝒳, ∀ Y ∈ 𝒳, X ∪ Y = Finset.univ ∨ X ⊆ Y ∨ Y ⊆ X

lemma complLaminar_rat_le (𝒳 : Finset (Finset Q)) (s : ℕ)
    (hs : s < Fintype.card Q) (hCL : IsComplLaminar 𝒳)
    (hSize : ∀ X ∈ 𝒳, s ≤ X.card ∧ X.card + 2 ≤ Fintype.card Q) :
    (𝒳.card : ℚ) ≤ (Fintype.card Q : ℚ) -
      (Fintype.card Q : ℚ) / ((Fintype.card Q - s : ℕ) : ℚ) := by
  let comp : Finset Q → Finset Q := fun X => Finset.univ \ X
  have hcomp_inj : Function.Injective comp := by
    intro X Y h
    ext q
    have hmem : q ∈ comp X ↔ q ∈ comp Y := by rw [h]
    simp only [comp, Finset.mem_sdiff, Finset.mem_univ, true_and] at hmem
    tauto
  let ℱ := 𝒳.image comp
  have hF_card : ℱ.card = 𝒳.card := Finset.card_image_of_injective 𝒳 hcomp_inj
  have hLam : IsLaminar ℱ := by
    intro A hA B hB
    rw [Finset.mem_image] at hA hB
    rcases hA with ⟨X, hX, rfl⟩
    rcases hB with ⟨Y, hY, rfl⟩
    rcases hCL X hX Y hY with huniv | hXY | hYX
    · left
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      simp only [comp, Finset.mem_sdiff, Finset.mem_univ, true_and] at hq1 hq2
      have hmem : q ∈ X ∪ Y := huniv ▸ Finset.mem_univ q
      rcases Finset.mem_union.mp hmem with hqX | hqY
      · exact hq1 hqX
      · exact hq2 hqY
    · right; right
      intro q hq
      simp only [comp, Finset.mem_sdiff, Finset.mem_univ, true_and] at hq ⊢
      exact fun hqX => hq (hXY hqX)
    · right; left
      intro q hq
      simp only [comp, Finset.mem_sdiff, Finset.mem_univ, true_and] at hq ⊢
      exact fun hqY => hq (hYX hqY)
  have hF_size : ∀ A ∈ ℱ, 2 ≤ A.card ∧ A.card ≤ Fintype.card Q - s := by
    intro A hA
    rw [Finset.mem_image] at hA
    rcases hA with ⟨X, hX, rfl⟩
    have hXs := hSize X hX
    have hc : (comp X).card = Fintype.card Q - X.card := by
      dsimp only [comp]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_univ]
    omega
  rw [← hF_card]
  exact laminar_bounded_rat_le ℱ (Fintype.card Q - s) (by omega) hLam hF_size

end LaminarBound

/-! ### Section 3: Pure-Inductive Laminar-Merge Search Engine (`FindShortProperlyExtendingWord`) -/

section SearchEngine

variable {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]

/-- Extension transfer invariant: any proper extension of `T` yields a proper extension of `S`
with at most `+ b` additional letters. -/
def CanTransfer (A : DFA Q α) (S : Finset Q) (b : ℕ) (T : Finset Q) : Prop :=
  ∀ w : List α, A.ProperlyExtends T w →
    ∃ w' : List α, A.ProperlyExtends S w' ∧ w'.length ≤ w.length + b

lemma canTransfer_mono {A : DFA Q α} {S T : Finset Q} {b₁ b₂ : ℕ}
    (hle : b₁ ≤ b₂) (h : CanTransfer A S b₁ T) : CanTransfer A S b₂ T := by
  intro w hw
  obtain ⟨w', hw', hlen⟩ := h w hw
  exact ⟨w', hw', by omega⟩

lemma canTransfer_refl (A : DFA Q α) (S : Finset Q) : CanTransfer A S 0 S :=
  fun w hw => ⟨w, hw, by omega⟩

lemma canTransfer_union {A : DFA Q α} {S T₁ T₂ : Finset Q} {b : ℕ}
    (h1 : CanTransfer A S b T₁) (h2 : CanTransfer A S b T₂) :
    CanTransfer A S b (T₁ ∪ T₂) := by
  intro w hw
  rcases properlyExtends_union hw with hw1 | hw2
  · exact h1 w hw1
  · exact h2 w hw2

lemma canTransfer_preimage_step {A : DFA Q α} {S T : Finset Q} {b : ℕ} {a : α}
    (hbij : ∀ s ∈ T, (A.preimage {s} [a]).card = 1)
    (hT : CanTransfer A S b T) :
    CanTransfer A S (b + 1) (A.preimage T [a]) := by
  intro w hw
  obtain ⟨w', hw', hlen⟩ := hT (w ++ [a]) (properlyExtends_append_singleton hbij hw)
  refine ⟨w', hw', ?_⟩
  simp only [List.length_append, List.length_singleton] at hlen
  omega

/-- If a nonempty family `Closed` is closed under all equal-size proper 1-letter preimages and
contains no subset with a 1-letter proper extension, then NO member of `Closed` admits ANY
properly extending word. -/
lemma not_properlyExtends_of_closed {A : DFA Q α} (Closed : Finset (Finset Q))
    (hClosed : ∀ P ∈ Closed, ∀ a : α,
      (∀ s ∈ P, (A.preimage {s} [a]).card = 1) → A.preimage P [a] ∈ Closed)
    (hNoExt : ∀ P ∈ Closed, ∀ a : α, ¬ A.ProperlyExtends P [a]) :
    ∀ w : List α, ∀ P ∈ Closed, ¬ A.ProperlyExtends P w := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro P _ hw
    rw [properlyExtends_iff_image_and_card, DFA.preimage_nil] at hw
    omega
  | append_singleton u a ih =>
    intro P hP hw
    rcases hw with ⟨hge1, s₀, hs₀, hge2⟩
    have hge1_a : ∀ s ∈ P, 1 ≤ (A.preimage {s} [a]).card := by
      intro s hs
      have hpos : 0 < (A.preimage {s} (u ++ [a])).card := by have := hge1 s hs; omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      rw [DFA.preimage_append, DFA.mem_preimage] at hx
      exact Finset.card_pos.mpr ⟨A.eval x u, hx⟩
    have hcard_eq1 : ∀ s ∈ P, (A.preimage {s} [a]).card = 1 := by
      intro s hs
      by_contra hne
      have hge2_a : 2 ≤ (A.preimage {s} [a]).card := by have := hge1_a s hs; omega
      exact hNoExt P hP a ⟨hge1_a, s, hs, hge2_a⟩
    have hP'_in : A.preimage P [a] ∈ Closed := hClosed P hP a hcard_eq1
    apply ih (A.preimage P [a]) hP'_in
    -- Every `t ∈ P a⁻¹` maps to a unique `s = t · a ∈ P` with `{s} a⁻¹ = {t}`!
    have hpre_sing_eq : ∀ t ∈ A.preimage P [a], A.preimage {A.eval t [a]} [a] = {t} := by
      intro t ht
      rw [DFA.mem_preimage] at ht
      obtain ⟨t', ht'⟩ := Finset.card_eq_one.mp (hcard_eq1 (A.eval t [a]) ht)
      have ht_in : t ∈ A.preimage {A.eval t [a]} [a] := by
        rw [DFA.mem_preimage, Finset.mem_singleton]
      rw [ht', Finset.mem_singleton] at ht_in
      rw [ht', ht_in]
    constructor
    · intro t ht
      have hst : A.eval t [a] ∈ P := (DFA.mem_preimage A P [a] t).mp ht
      have h1 := hge1 (A.eval t [a]) hst
      rw [DFA.preimage_append, hpre_sing_eq t ht] at h1
      exact h1
    · obtain ⟨t₀, ht₀eq⟩ := Finset.card_eq_one.mp (hcard_eq1 s₀ hs₀)
      have ht₀_mem : t₀ ∈ A.preimage {s₀} [a] := by rw [ht₀eq]; exact Finset.mem_singleton_self t₀
      rw [DFA.mem_preimage, Finset.mem_singleton] at ht₀_mem
      have ht₀_P' : t₀ ∈ A.preimage P [a] := by rw [DFA.mem_preimage, ht₀_mem]; exact hs₀
      refine ⟨t₀, ht₀_P', ?_⟩
      rw [DFA.preimage_append, ht₀eq] at hge2
      exact hge2

/-- **Core Laminar-Merge Extension Theorem**: For EVERY completely reachable DFA (`n ≥ 2`) and
EVERY nonempty proper subset `S ⊂ Q`, there exists a properly extending word `w` for `S` of
length at most `effOrbitCap A + n - n / (n - |S|)` (in `ℚ`). -/
theorem exists_short_properlyExtending {A : DFA Q α}
    (hCR : A.IsCompletelyReachable) (hn2 : 2 ≤ Fintype.card Q)
    {S : Finset Q} (hS_ne : S.Nonempty) (hS_lt : S.card < Fintype.card Q) :
    ∃ w : List α, A.ProperlyExtends S w ∧
      (w.length : ℚ) ≤ (effOrbitCap A : ℚ) + (Fintype.card Q : ℚ) -
        (Fintype.card Q : ℚ) / ((Fintype.card Q - S.card : ℕ) : ℚ) := by
  classical
  -- Outer strong induction on `d_rem = n - k` (level `k`, `|S| ≤ k ≤ n - 1`)
  have houter : ∀ d_rem : ℕ, ∀ k : ℕ, ∀ 𝒳_old : Finset (Finset Q), ∀ C : Finset Q,
      Fintype.card Q - k = d_rem →
      S.card ≤ k → k < Fintype.card Q →
      C.card = k →
      CanTransfer A S 𝒳_old.card C →
      (∀ X ∈ 𝒳_old, S.card ≤ X.card ∧ X.card < k) →
      (∀ X ∈ 𝒳_old, CanTransfer A S 𝒳_old.card X) →
      IsComplLaminar 𝒳_old →
      ∃ w : List α, A.ProperlyExtends S w ∧
        (w.length : ℚ) ≤ (effOrbitCap A : ℚ) + (Fintype.card Q : ℚ) -
          (Fintype.card Q : ℚ) / ((Fintype.card Q - S.card : ℕ) : ℚ) := by
    intro d_rem
    induction d_rem using Nat.strong_induction_on with
    | _ d_rem ih_outer =>
      intro k 𝒳_old C hd_rem hk_ge hk_lt hC_card hC_tr hX_size hX_tr hX_lam
      by_cases htop : k = Fintype.card Q - 1
      · -- Base level `k = n - 1`: `C = Finset.univ.erase q₀`, apply shortest `Σ₀`-path to `M₁`!
        have hC_ne_univ : C ≠ Finset.univ := fun h => by rw [h, Finset.card_univ] at hC_card; omega
        obtain ⟨q₀, _, hq₀_not⟩ := Finset.exists_of_ssubset
          (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ C, hC_ne_univ⟩)
        have hC_eq : C = Finset.univ.erase q₀ := by
          apply Finset.eq_of_subset_of_card_le
          · intro x hx; exact Finset.mem_erase.mpr ⟨fun h => hq₀_not (h ▸ hx), Finset.mem_univ x⟩
          · rw [Finset.card_erase_of_mem (Finset.mem_univ q₀), Finset.card_univ]; omega
        obtain ⟨u, hu_ext, hu_len⟩ := exists_properExt_erase_singleton hCR hn2 q₀
        rw [← hC_eq] at hu_ext
        obtain ⟨w, hw_ext, hw_len⟩ := hC_tr u hu_ext
        have hX_rat := complLaminar_rat_le 𝒳_old S.card hS_lt hX_lam
          (fun X hX => ⟨(hX_size X hX).1, by have := (hX_size X hX).2; omega⟩)
        refine ⟨w, hw_ext, ?_⟩
        have hw_Q : (w.length : ℚ) ≤ (u.length : ℚ) + (𝒳_old.card : ℚ) := by exact_mod_cast hw_len
        have hu_Q : (u.length : ℚ) ≤ (effOrbitCap A : ℚ) := by exact_mod_cast hu_len
        linarith
      · -- Lower level `k ≤ n - 2`: inner BFS induction on `m_rem = 2^n - Processed.card`!
        have hk_le2 : k + 2 ≤ Fintype.card Q := by omega
        have hinner : ∀ m_rem : ℕ, ∀ Processed Frontier : Finset (Finset Q),
            Fintype.card (Finset Q) - Processed.card = m_rem →
            Disjoint Processed Frontier →
            C ∈ Processed ∪ Frontier →
            (∀ P ∈ Processed, P.card = k) →
            (∀ F ∈ Frontier, F.card = k) →
            (∀ P ∈ Processed, ∀ a : α,
              (∀ s ∈ P, (A.preimage {s} [a]).card = 1) → A.preimage P [a] ∈ Processed ∪ Frontier) →
            (∀ P ∈ Processed, ∀ a : α, ¬ A.ProperlyExtends P [a]) →
            IsComplLaminar (𝒳_old ∪ Processed) →
            (∀ X ∈ 𝒳_old ∪ Processed, CanTransfer A S (𝒳_old ∪ Processed).card X) →
            (∀ F ∈ Frontier, CanTransfer A S (𝒳_old ∪ Processed).card F) →
            ∃ w : List α, A.ProperlyExtends S w ∧
              (w.length : ℚ) ≤ (effOrbitCap A : ℚ) + (Fintype.card Q : ℚ) -
                (Fintype.card Q : ℚ) / ((Fintype.card Q - S.card : ℕ) : ℚ) := by
          intro m_rem
          induction m_rem using Nat.strong_induction_on with
          | _ m_rem ih_inner =>
            intro Processed Frontier hm_rem hDisj_PF hC_in hP_card hF_card hClosed hNoExt
              hLam_XP hTr_XP hTr_F
            -- `Frontier` MUST be nonempty (otherwise `Processed` is closed, contradicting `hCR`!)
            have hFront_ne : Frontier.Nonempty := by
              by_contra hempty
              rw [Finset.not_nonempty_iff_eq_empty] at hempty
              rw [hempty, Finset.union_empty] at hC_in hClosed
              have hC_ne : C.Nonempty := Finset.card_pos.mp (by
                have := Finset.card_pos.mpr hS_ne; omega)
              obtain ⟨w_reach, hw_reach⟩ := hCR C hC_ne
              exact not_properlyExtends_of_closed Processed hClosed hNoExt w_reach C hC_in
                (properlyExtends_of_image_univ hw_reach (by omega))
            obtain ⟨T, hT_F⟩ := hFront_ne
            have hT_card : T.card = k := hF_card T hT_F
            -- Check 1: Does `T` cross some `U ∈ 𝒳_old ∪ Processed`?
            by_cases hCross : ∃ U ∈ 𝒳_old ∪ Processed,
                T ∪ U ≠ Finset.univ ∧ ¬ (T ⊆ U) ∧ ¬ (U ⊆ T)
            · rcases hCross with ⟨U, hU_XP, hTU_proper, hnotTU, hnotUT⟩
              let C_new := T ∪ U
              have hCnew_gt : k < C_new.card := by
                rw [← hT_card]
                exact Finset.card_lt_card (Finset.ssubset_iff_of_subset Finset.subset_union_left |>.mpr
                  (by
                    obtain ⟨x, hxU, hxT⟩ := Finset.not_subset.mp hnotUT
                    exact ⟨x, Finset.mem_union_right T hxU, hxT⟩))
              have hCnew_lt : C_new.card < Fintype.card Q :=
                lt_of_le_of_ne (Finset.card_le_univ C_new)
                  (fun h => hTU_proper (Finset.eq_univ_of_card C_new h))
              have hCnew_tr : CanTransfer A S (𝒳_old ∪ Processed).card C_new :=
                canTransfer_union (hTr_F T hT_F) (hTr_XP U hU_XP)
              have hXP_size : ∀ X ∈ 𝒳_old ∪ Processed, S.card ≤ X.card ∧ X.card < C_new.card := by
                intro X hX
                rcases Finset.mem_union.mp hX with hX | hX
                · exact ⟨(hX_size X hX).1, by have := (hX_size X hX).2; omega⟩
                · rw [hP_card X hX]; omega
              exact ih_outer (Fintype.card Q - C_new.card) (by omega) C_new.card
                (𝒳_old ∪ Processed) C_new rfl (by omega) hCnew_lt rfl
                hCnew_tr hXP_size hTr_XP hLam_XP
            · -- No crossing: `T` is complement-laminar with all of `𝒳_old ∪ Processed`!
              push Not at hCross
              let Processed' := insert T Processed
              have hT_notP : T ∉ Processed := Finset.disjoint_right.mp hDisj_PF hT_F
              have hT_notX : T ∉ 𝒳_old := fun h => by
                have := (hX_size T h).2; omega
              have hT_notXP : T ∉ 𝒳_old ∪ Processed := by
                rw [Finset.mem_union]; push Not; exact ⟨hT_notX, hT_notP⟩
              have hXP'_eq : 𝒳_old ∪ Processed' = insert T (𝒳_old ∪ Processed) := by
                ext X; simp only [Processed', Finset.mem_union, Finset.mem_insert]; tauto
              have hXP'_card : (𝒳_old ∪ Processed').card = (𝒳_old ∪ Processed).card + 1 := by
                rw [hXP'_eq, Finset.card_insert_of_notMem hT_notXP]
              have hLam_XP' : IsComplLaminar (𝒳_old ∪ Processed') := by
                rw [hXP'_eq]
                intro X hX Y hY
                simp only [Finset.mem_insert] at hX hY
                rcases hX with rfl | hX <;> rcases hY with rfl | hY
                · exact Or.inr (Or.inl (Finset.Subset.refl _))
                · by_cases hu : X ∪ Y = Finset.univ
                  · exact Or.inl hu
                  · by_cases hsub : X ⊆ Y
                    · exact Or.inr (Or.inl hsub)
                    · exact Or.inr (Or.inr (hCross Y hY hu hsub))
                · by_cases hu : Y ∪ X = Finset.univ
                  · rw [Finset.union_comm] at hu; exact Or.inl hu
                  · by_cases hsub : Y ⊆ X
                    · exact Or.inr (Or.inr hsub)
                    · exact Or.inr (Or.inl (hCross X hX hu hsub))
                · exact hLam_XP X hX Y hY
              -- Check 2: Does `T` have a 1-letter proper extension?
              by_cases hExtT : ∃ a : α, A.ProperlyExtends T [a]
              · rcases hExtT with ⟨a, ha_ext⟩
                obtain ⟨w, hw_ext, hw_len⟩ := hTr_F T hT_F [a] ha_ext
                have hw_le_card : w.length ≤ (𝒳_old ∪ Processed').card := by
                  simp only [List.length_singleton] at hw_len; omega
                have hXP'_size : ∀ X ∈ 𝒳_old ∪ Processed',
                    S.card ≤ X.card ∧ X.card + 2 ≤ Fintype.card Q := by
                  intro X hX
                  rw [hXP'_eq, Finset.mem_insert] at hX
                  rcases hX with rfl | hX
                  · omega
                  · rcases Finset.mem_union.mp hX with hX | hX
                    · have := hX_size X hX; omega
                    · rw [hP_card X hX]; omega
                have hrat := complLaminar_rat_le (𝒳_old ∪ Processed') S.card hS_lt hLam_XP' hXP'_size
                refine ⟨w, hw_ext, ?_⟩
                have hw_Q : (w.length : ℚ) ≤ ((𝒳_old ∪ Processed').card : ℚ) := by
                  exact_mod_cast hw_le_card
                have heff_nonneg : (0 : ℚ) ≤ (effOrbitCap A : ℚ) := Nat.cast_nonneg _
                linarith
              · -- No 1-letter proper extension at `T`: expand equal-size proper 1-letter preimages
                push Not at hExtT
                let NewKids : Finset (Finset Q) :=
                  Finset.univ.filter (fun T' : Finset Q =>
                    ∃ a : α, (∀ s ∈ T, (A.preimage {s} [a]).card = 1) ∧ A.preimage T [a] = T')
                let Frontier' := (Frontier.erase T ∪ NewKids) \ Processed'
                have hP'_card_inc : Processed'.card = Processed.card + 1 :=
                  Finset.card_insert_of_notMem hT_notP
                have hP_lt_univ : Processed.card < Fintype.card (Finset Q) := by
                  have hle := Finset.card_le_univ Processed'
                  rw [hP'_card_inc] at hle
                  omega
                have hDisj_PF' : Disjoint Processed' Frontier' := Finset.disjoint_sdiff
                have hPF_sub : Processed ∪ Frontier ⊆ Processed' ∪ Frontier' := by
                  intro X hX
                  by_cases hXP' : X ∈ Processed'
                  · exact Finset.mem_union_left Frontier' hXP'
                  · refine Finset.mem_union_right Processed' (Finset.mem_sdiff.mpr ⟨?_, hXP'⟩)
                    rcases Finset.mem_union.mp hX with hXP | hXF
                    · exact absurd (Finset.mem_insert_of_mem hXP) hXP'
                    · have hXT : X ≠ T := fun h => hXP' (h ▸ Finset.mem_insert_self T Processed)
                      exact Finset.mem_union_left NewKids (Finset.mem_erase.mpr ⟨hXT, hXF⟩)
                have hP'_sz : ∀ P ∈ Processed', P.card = k := by
                  intro P hP
                  rcases Finset.mem_insert.mp hP with rfl | hP
                  · exact hT_card
                  · exact hP_card P hP
                have hF'_sz : ∀ F ∈ Frontier', F.card = k := by
                  intro F hF
                  have hmem := (Finset.mem_sdiff.mp hF).1
                  rcases Finset.mem_union.mp hmem with hOld | hNew
                  · exact hF_card F (Finset.mem_of_mem_erase hOld)
                  · rcases (Finset.mem_filter.mp hNew).2 with ⟨a, hbij, rfl⟩
                    rw [A.card_preimage_eq_sum_singleton T [a]]
                    calc ∑ s ∈ T, (A.preimage {s} [a]).card = ∑ _s ∈ T, 1 :=
                          Finset.sum_congr rfl fun s hs => hbij s hs
                      _ = T.card := by simp
                      _ = k := hT_card
                have hClosed' : ∀ P ∈ Processed', ∀ a : α,
                    (∀ s ∈ P, (A.preimage {s} [a]).card = 1) →
                      A.preimage P [a] ∈ Processed' ∪ Frontier' := by
                  intro P hP a hbij
                  rcases Finset.mem_insert.mp hP with rfl | hP
                  · by_cases hin : A.preimage P [a] ∈ Processed'
                    · exact Finset.mem_union_left Frontier' hin
                    · refine Finset.mem_union_right Processed' (Finset.mem_sdiff.mpr ⟨?_, hin⟩)
                      exact Finset.mem_union_right _
                        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, hbij, rfl⟩)
                  · exact hPF_sub (hClosed P hP a hbij)
                have hNoExt' : ∀ P ∈ Processed', ∀ a : α, ¬ A.ProperlyExtends P [a] := by
                  intro P hP a
                  rcases Finset.mem_insert.mp hP with rfl | hP
                  · exact hExtT a
                  · exact hNoExt P hP a
                have hTr_XP' : ∀ X ∈ 𝒳_old ∪ Processed',
                    CanTransfer A S (𝒳_old ∪ Processed').card X := by
                  intro X hX
                  rw [hXP'_card]
                  rw [hXP'_eq, Finset.mem_insert] at hX
                  rcases hX with rfl | hX
                  · exact canTransfer_mono (Nat.le_succ _) (hTr_F X hT_F)
                  · exact canTransfer_mono (Nat.le_succ _) (hTr_XP X hX)
                have hTr_F' : ∀ F ∈ Frontier', CanTransfer A S (𝒳_old ∪ Processed').card F := by
                  intro F hF
                  rw [hXP'_card]
                  have hmem := (Finset.mem_sdiff.mp hF).1
                  rcases Finset.mem_union.mp hmem with hOld | hNew
                  · exact canTransfer_mono (Nat.le_succ _) (hTr_F F (Finset.mem_of_mem_erase hOld))
                  · rcases (Finset.mem_filter.mp hNew).2 with ⟨a, hbij, rfl⟩
                    exact canTransfer_preimage_step hbij (hTr_F T hT_F)
                exact ih_inner (Fintype.card (Finset Q) - Processed'.card) (by omega)
                  Processed' Frontier' rfl hDisj_PF' (hPF_sub hC_in) hP'_sz hF'_sz
                  hClosed' hNoExt' hLam_XP' hTr_XP' hTr_F'
        -- Start inner BFS at `Processed = ∅, Frontier = {C}`
        refine hinner (Fintype.card (Finset Q) - (∅ : Finset (Finset Q)).card) ∅ {C} rfl
          (Finset.disjoint_empty_left {C}) (by simp)
          (fun _ h => absurd h (Finset.notMem_empty _))
          (fun F hF => (Finset.mem_singleton.mp hF) ▸ hC_card)
          (fun _ h => absurd h (Finset.notMem_empty _))
          (fun _ h => absurd h (Finset.notMem_empty _))
          (by simpa using hX_lam)
          (by simpa using hX_tr)
          (fun F hF => by rw [Finset.mem_singleton.mp hF]; simpa using hC_tr)
  -- Launch outer induction at `k = S.card`, `𝒳_old = ∅`, `C = S`
  exact houter (Fintype.card Q - S.card) S.card ∅ S rfl le_rfl hS_lt rfl
    (canTransfer_refl A S)
    (fun _ h => absurd h (Finset.notMem_empty _))
    (fun _ h => absurd h (Finset.notMem_empty _))
    (fun _ h => absurd h (Finset.notMem_empty _))

end SearchEngine

end CompletelyReachable

/-! ### Main Public Theorems (Theorem T23 & Ferens–Szykuła 2025 Improvement) -/

/-- **Theorem T23(1a) (Volkov D6 `d = 1` ⊆ Volkov D2)**:
Every DFA in the transitive defect-`≤ 1` class with `blockCount = 1` (strongly connected orbit
digraph `Γ_∞`) is completely reachable (and hence automatically synchronizing!). -/
theorem volkovD6_d1_isCompletelyReachable {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S₀ S₁ : Set α)
    (hT : IsTransitiveDefectLeOne A S₀ S₁)
    (hd1 : VolkovD6Transitive.blockCount A S₀ S₁ = 1) :
    A.IsCompletelyReachable := by
  classical
  open VolkovD6Transitive in
  -- Strong induction on `k = n - |S|`
  have hreach : ∀ k : ℕ, ∀ S : Finset Q, S.Nonempty → Fintype.card Q - S.card = k →
      ∃ w : List α, A.image Finset.univ w = S := by
    intro k
    induction k with
    | zero =>
      intro S _ hk
      have hle : S.card ≤ Fintype.card Q := Finset.card_le_univ S
      exact ⟨[], by rw [DFA.image_nil, Finset.eq_univ_of_card S (by omega)]⟩
    | succ k ih =>
      intro S hSne hk
      have hS_lt : S.card < Fintype.card Q := by
        have := Finset.card_le_univ S; omega
      have hS_ne_univ : S ≠ Finset.univ := fun h => by rw [h, Finset.card_univ] at hS_lt; omega
      obtain ⟨p₀, hp₀⟩ := hSne
      obtain ⟨q₀, _, hq₀⟩ := Finset.exists_of_ssubset
        (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hS_ne_univ⟩)
      have hsub : Subsingleton (Quotient (transSCCInf A S₀ S₁)) := by
        have hc : Fintype.card (Quotient (transSCCInf A S₀ S₁)) = 1 :=
          (quotCard_eq_card (transSCCInf A S₀ S₁)).symm.trans hd1
        exact Fintype.card_le_one_iff_subsingleton.mp hc.le
      have hpq : transReachInf A S₀ S₁ p₀ q₀ :=
        (Quotient.exact (hsub.elim (Quotient.mk _ p₀) (Quotient.mk _ q₀))).1
      have hwalk : ∀ x y : Q, transReachInf A S₀ S₁ x y → x ∈ S → y ∉ S →
          ∃ u ∈ S, ∃ v, v ∉ S ∧ transEdgeInf A S₀ S₁ u v := by
        intro x y hr
        induction hr with
        | refl => intro hx hnx; exact absurd hx hnx
        | @tail b c _ hbc ihw =>
          intro hx hnc
          by_cases hb : b ∈ S
          · exact ⟨b, hb, c, hnc, hbc⟩
          · exact ihw hx hb
      obtain ⟨u, huS, v, hvS, _, a, ha, z₀, m₀, hDef, g, _, hgS, hgz, hgm⟩ :=
        hwalk p₀ q₀ hpq hp₀ hq₀
      let S' := A.preimage S g
      let T := A.preimage S' [a]
      have hg_bij := bijective_eval_of_mem hT.2.1 g hgS
      have hS'_card : S'.card = S.card := card_preimage_of_bijective S g hg_bij
      have hz_mem : z₀ ∈ S' := by rw [DFA.mem_preimage, hgz]; exact huS
      have hm_not : m₀ ∉ S' := by rw [DFA.mem_preimage, hgm]; exact hvS
      have hT_card : T.card = S.card + 1 := by
        have hc := card_preimage_defectOne hDef S'
        simp only [hz_mem, hm_not, ↓reduceIte, add_zero] at hc
        show (A.preimage S' [a]).card = S.card + 1
        omega
      have hT_ne : T.Nonempty := Finset.card_pos.mp (by omega)
      have hT_img_a : A.image T [a] = S' := by
        ext s
        simp only [DFA.mem_image, T, DFA.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact hx
        · intro hs
          have hne_m : s ≠ m₀ := fun h => hm_not (h ▸ hs)
          have hpos : 0 < (A.preimage {s} [a]).card := by
            by_cases hsz : s = z₀
            · rw [hsz, hDef.2.1]; decide
            · rw [hDef.2.2.2 s hsz hne_m]; decide
          obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
          rw [DFA.mem_preimage, Finset.mem_singleton] at hx
          exact ⟨x, hx ▸ hs, hx⟩
      have hS'_img_g : A.image S' g = S := by
        ext s
        simp only [DFA.mem_image, S', DFA.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact hx
        · intro hs
          obtain ⟨x, hx⟩ := hg_bij.2 s
          dsimp only at hx
          exact ⟨x, hx ▸ hs, hx⟩
      obtain ⟨w₀, hw₀⟩ := ih T hT_ne (by omega)
      refine ⟨w₀ ++ (a :: g), ?_⟩
      rw [DFA.image_append, hw₀]
      have hcons : A.image T (a :: g) = A.image (A.image T [a]) g := by
        ext y
        simp only [DFA.mem_image, DFA.eval_cons]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨A.step x a, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
      rw [hcons, hT_img_a, hS'_img_g]
  intro S hSne
  exact hreach (Fintype.card Q - S.card) S hSne rfl

/-- **Theorem T23(1b) (Primitive Volkov D6 ⊆ Volkov D2)**:
Every DFA with a primitive permutation letter set `S₀` and a rank-`(n - 1)` letter `a` is
completely reachable (and needs no extra letters or assumptions). -/
theorem primitive_defectOne_isCompletelyReachable {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S₀ : Set α) (a : α)
    (hPrim : A.IsPrimitivePermSet S₀)
    (hrank : (A.image Finset.univ [a]).card + 1 = Fintype.card Q) :
    A.IsCompletelyReachable := by
  classical
  open VolkovD6Transitive in
  obtain ⟨z₀, m₀, hDef⟩ := exists_isDefectOneLetter_of_card_image_eq_pred A a hrank
  -- Restrict to `S₀` and `{a}`: `transSCCInf A S₀ {a}` is `S₀`-invariant and merges `z₀ ≠ m₀`
  let sInf := transSCCInf A S₀ {a}
  have hInv : ∀ b ∈ S₀, ∀ p q : Q, sInf.r p q → sInf.r (A.step p b) (A.step q b) :=
    fun b hb _ _ h => ⟨transReachInf_step A S₀ {a} hb h.1, transReachInf_step A S₀ {a} hb h.2⟩
  have hzm_e : transEdgeInf A S₀ {a} z₀ m₀ :=
    ⟨0, a, Set.mem_singleton a, z₀, m₀, hDef, [], le_rfl, fun _ h => absurd h (List.not_mem_nil), rfl, rfl⟩
  have hzm_r : sInf.r z₀ m₀ :=
    (transSCCInf_iff_reachInf hPrim.1 hPrim.2.1).mpr (Relation.ReflTransGen.single hzm_e)
  have hall : ∀ p q : Q, sInf.r p q := by
    rcases hPrim.2.2 sInf hInv with hdiag | hall
    · exact absurd (hdiag z₀ m₀ hzm_r) hDef.1
    · exact hall
  have hreach : ∀ k : ℕ, ∀ S : Finset Q, S.Nonempty → Fintype.card Q - S.card = k →
      ∃ w : List α, A.image Finset.univ w = S := by
    intro k
    induction k with
    | zero =>
      intro S _ hk
      have hle : S.card ≤ Fintype.card Q := Finset.card_le_univ S
      exact ⟨[], by rw [DFA.image_nil, Finset.eq_univ_of_card S (by omega)]⟩
    | succ k ih =>
      intro S hSne hk
      have hS_lt : S.card < Fintype.card Q := by
        have := Finset.card_le_univ S; omega
      have hS_ne_univ : S ≠ Finset.univ := fun h => by rw [h, Finset.card_univ] at hS_lt; omega
      obtain ⟨p₀, hp₀⟩ := hSne
      obtain ⟨q₀, _, hq₀⟩ := Finset.exists_of_ssubset
        (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hS_ne_univ⟩)
      have hpq : transReachInf A S₀ {a} p₀ q₀ := (hall p₀ q₀).1
      have hwalk : ∀ x y : Q, transReachInf A S₀ {a} x y → x ∈ S → y ∉ S →
          ∃ u ∈ S, ∃ v, v ∉ S ∧ transEdgeInf A S₀ {a} u v := by
        intro x y hr
        induction hr with
        | refl => intro hx hnx; exact absurd hx hnx
        | @tail b c _ hbc ihw =>
          intro hx hnc
          by_cases hb : b ∈ S
          · exact ⟨b, hb, c, hnc, hbc⟩
          · exact ihw hx hb
      obtain ⟨u, huS, v, hvS, _, a', ha', z', m', hDef', g, _, hgS, hgz, hgm⟩ :=
        hwalk p₀ q₀ hpq hp₀ hq₀
      let S' := A.preimage S g
      let T := A.preimage S' [a']
      have hg_bij := bijective_eval_of_mem hPrim.1 g hgS
      have hS'_card : S'.card = S.card := card_preimage_of_bijective S g hg_bij
      have hz_mem : z' ∈ S' := by rw [DFA.mem_preimage, hgz]; exact huS
      have hm_not : m' ∉ S' := by rw [DFA.mem_preimage, hgm]; exact hvS
      have hT_card : T.card = S.card + 1 := by
        have hc := card_preimage_defectOne hDef' S'
        simp only [hz_mem, hm_not, ↓reduceIte, add_zero] at hc
        show (A.preimage S' [a']).card = S.card + 1
        omega
      have hT_ne : T.Nonempty := Finset.card_pos.mp (by omega)
      have hT_img_a : A.image T [a'] = S' := by
        ext s
        simp only [DFA.mem_image, T, DFA.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact hx
        · intro hs
          have hne_m : s ≠ m' := fun h => hm_not (h ▸ hs)
          have hpos : 0 < (A.preimage {s} [a']).card := by
            by_cases hsz : s = z'
            · rw [hsz, hDef'.2.1]; decide
            · rw [hDef'.2.2.2 s hsz hne_m]; decide
          obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
          rw [DFA.mem_preimage, Finset.mem_singleton] at hx
          exact ⟨x, hx ▸ hs, hx⟩
      have hS'_img_g : A.image S' g = S := by
        ext s
        simp only [DFA.mem_image, S', DFA.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact hx
        · intro hs
          obtain ⟨x, hx⟩ := hg_bij.2 s
          dsimp only at hx
          exact ⟨x, hx ▸ hs, hx⟩
      obtain ⟨w₀, hw₀⟩ := ih T hT_ne (by omega)
      refine ⟨w₀ ++ (a' :: g), ?_⟩
      rw [DFA.image_append, hw₀]
      have hcons : A.image T (a' :: g) = A.image (A.image T [a']) g := by
        ext y
        simp only [DFA.mem_image, DFA.eval_cons]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨A.step x a', ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
      rw [hcons, hT_img_a, hS'_img_g]
  intro S hSne
  exact hreach (Fintype.card Q - S.card) S hSne rfl

/-- **Theorem T23(2a) (Effective-Orbit Reaching Threshold Bound)**:
Every nonempty subset `S` of a completely reachable DFA on `n ≥ 2` states is reachable by a word
of length at most `(n - |S|) * (ℓ_eff₁ + n) - n * H_{n - |S|}`. -/
theorem completelyReachable_effOrbit_reaching_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hCR : A.IsCompletelyReachable) (hn2 : 2 ≤ Fintype.card Q)
    (S : Finset Q) (hSne : S.Nonempty) :
    ∃ w : List α, A.image Finset.univ w = S ∧
      (w.length : ℚ) ≤
        ((Fintype.card Q - S.card : ℕ) : ℚ) * ((effOrbitCap A : ℚ) + (Fintype.card Q : ℚ)) -
          (Fintype.card Q : ℚ) * harmonicRat (Fintype.card Q - S.card) := by
  have hmain : ∀ d : ℕ, ∀ T : Finset Q, T.Nonempty → Fintype.card Q - T.card = d →
      ∃ w : List α, A.image Finset.univ w = T ∧
        (w.length : ℚ) ≤
          (d : ℚ) * ((effOrbitCap A : ℚ) + (Fintype.card Q : ℚ)) -
            (Fintype.card Q : ℚ) * harmonicRat d := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro T hTne hd
      by_cases h0 : d = 0
      · have hle : T.card ≤ Fintype.card Q := Finset.card_le_univ T
        refine ⟨[], by rw [DFA.image_nil, Finset.eq_univ_of_card T (by omega)], ?_⟩
        simp [h0, harmonicRat]
      · have hT_lt : T.card < Fintype.card Q := by
          have := Finset.card_le_univ T; omega
        obtain ⟨u, hu_ext, hu_len⟩ :=
          CompletelyReachable.exists_short_properlyExtending hCR hn2 hTne hT_lt
        rw [hd] at hu_len
        have hu_ic := (CompletelyReachable.properlyExtends_iff_image_and_card A T u).mp hu_ext
        set T' := A.preimage T u
        have hT'_ne : T'.Nonempty := Finset.card_pos.mp (by
          have := Finset.card_pos.mpr hTne; omega)
        set d' := Fintype.card Q - T'.card
        have hd'_lt : d' < d := by
          have := Finset.card_le_univ T'; omega
        obtain ⟨v, hv_img, hv_len⟩ := ih d' hd'_lt T' hT'_ne rfl
        refine ⟨v ++ u, by rw [DFA.image_append, hv_img, hu_ic.1], ?_⟩
        -- Monotonicity of `m ↦ m * (ℓ_eff₁ + n) - n * H_m` across skipped sizes `d' + 1 .. d - 1`
        have hstep_mono : ∀ m : ℕ,
            (m : ℚ) * ((effOrbitCap A : ℚ) + (Fintype.card Q : ℚ)) -
              (Fintype.card Q : ℚ) * harmonicRat m ≤
            ((m + 1 : ℕ) : ℚ) * ((effOrbitCap A : ℚ) + (Fintype.card Q : ℚ)) -
              (Fintype.card Q : ℚ) * harmonicRat (m + 1) := by
          intro m
          have hH_succ : harmonicRat (m + 1) = harmonicRat m + (1 : ℚ) / ((m + 1 : ℕ) : ℚ) := by
            dsimp only [harmonicRat]
            have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hIcc, Finset.sum_insert (by simp)]
            ring
          rw [hH_succ]
          have hm1 : (1 : ℚ) ≤ ((m + 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
          have hn_nonneg : (0 : ℚ) ≤ (Fintype.card Q : ℚ) := Nat.cast_nonneg _
          have hdiv_le : (Fintype.card Q : ℚ) * ((1 : ℚ) / ((m + 1 : ℕ) : ℚ)) ≤ (Fintype.card Q : ℚ) := by
            rw [mul_one_div, div_le_iff₀ (by linarith)]
            nlinarith
          have heff_nonneg : (0 : ℚ) ≤ (effOrbitCap A : ℚ) := Nat.cast_nonneg _
          push_cast at hdiv_le ⊢
          nlinarith
        have hmono : ∀ a b : ℕ, a ≤ b →
            (a : ℚ) * ((effOrbitCap A : ℚ) + (Fintype.card Q : ℚ)) -
              (Fintype.card Q : ℚ) * harmonicRat a ≤
            (b : ℚ) * ((effOrbitCap A : ℚ) + (Fintype.card Q : ℚ)) -
              (Fintype.card Q : ℚ) * harmonicRat b := by
          intro a b hab
          induction hab with
          | refl => exact le_rfl
          | step _ ih_m => exact ih_m.trans (hstep_mono _)
        have hdm1 : d' ≤ d - 1 := by omega
        have hv_dm1 := hv_len.trans (hmono d' (d - 1) hdm1)
        have hH_d : harmonicRat d = harmonicRat (d - 1) + (1 : ℚ) / (d : ℚ) := by
          have hd_eq : d = (d - 1) + 1 := by omega
          conv_lhs => rw [hd_eq]
          dsimp only [harmonicRat]
          have hIcc : Finset.Icc 1 ((d - 1) + 1) = insert d (Finset.Icc 1 (d - 1)) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
          ring
        have hlen_vu : ((v ++ u).length : ℚ) = (v.length : ℚ) + (u.length : ℚ) := by
          rw [List.length_append, Nat.cast_add]
        have hd_cast : ((d - 1 : ℕ) : ℚ) + 1 = (d : ℚ) := by
          have : (d - 1) + 1 = d := by omega
          exact_mod_cast this
        rw [hlen_vu, hH_d]
        have hdiv : (Fintype.card Q : ℚ) * ((1 : ℚ) / (d : ℚ)) = (Fintype.card Q : ℚ) / (d : ℚ) := by
          ring
        nlinarith
  exact hmain (Fintype.card Q - S.card) S hSne rfl

/-- **Theorem T23(2b) (Main Effective-Orbit Reset Threshold Bound)**:
Every completely reachable DFA on `n ≥ 2` states admits a synchronizing word `w` with
`w.length ≤ 1 + (n - 2) * (ℓ_eff₁ + n) - n * H_{n - 2}` (where `ℓ_eff₁ ≤ min(ℓ_orb, n - |M₁| + 1)`). -/
theorem completelyReachable_effOrbit_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hCR : A.IsCompletelyReachable) (hn2 : 2 ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧
      (w.length : ℚ) ≤
        1 + ((Fintype.card Q - 2 : ℕ) : ℚ) * ((effOrbitCap A : ℚ) + (Fintype.card Q : ℚ)) -
          (Fintype.card Q : ℚ) * harmonicRat (Fintype.card Q - 2) := by
  obtain ⟨q₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card Q)
  obtain ⟨q₁, _, hq₁M⟩ :=
    CompletelyReachable.permOrbit_inter_defectOneOmitted_nonempty hCR hn2 q₀
  obtain ⟨a, ha_img⟩ := (CompletelyReachable.mem_defectOneOmitted A q₁).mp hq₁M
  have hrank : (A.image Finset.univ [a]).card + 1 = Fintype.card Q := by
    rw [ha_img, Finset.card_erase_of_mem (Finset.mem_univ q₁), Finset.card_univ]
    omega
  obtain ⟨z₀, m₀, hDef⟩ := exists_isDefectOneLetter_of_card_image_eq_pred A a hrank
  let S₀ := A.preimage {z₀} [a]
  have hS₀_card : S₀.card = 2 := hDef.2.1
  have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, hu_img, hu_len⟩ := completelyReachable_effOrbit_reaching_bound A hCR hn2 S₀ hS₀_ne
  rw [hS₀_card] at hu_len
  refine ⟨u ++ [a], ?_, ?_⟩
  · refine ⟨z₀, fun q => ?_⟩
    have hmem : A.eval q u ∈ S₀ := by
      rw [← hu_img, DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩
    rw [DFA.mem_preimage, Finset.mem_singleton] at hmem
    rw [DFA.eval_append]; exact hmem
  · simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
    linarith

/-- **Ferens & Szykuła (2025) Reset Threshold Bound** (immediate corollary via `ℓ_eff₁ ≤ ℓ_orb`):
`w.length ≤ 1 + (n - 2) * (ℓ_orb + n) - n * H_{n - 2}`. -/
theorem completelyReachable_ferensSzykula_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hCR : A.IsCompletelyReachable) (hn2 : 2 ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧
      (w.length : ℚ) ≤
        1 + ((Fintype.card Q - 2 : ℕ) : ℚ) * ((maxOrbitSize A : ℚ) + (Fintype.card Q : ℚ)) -
          (Fintype.card Q : ℚ) * harmonicRat (Fintype.card Q - 2) := by
  obtain ⟨w, hw, hlen⟩ := completelyReachable_effOrbit_bound A hCR hn2
  have heff : (effOrbitCap A : ℚ) ≤ (maxOrbitSize A : ℚ) := by
    exact_mod_cast CompletelyReachable.effOrbitCap_le_maxOrbitSize hCR hn2
  have hn2_nonneg : (0 : ℚ) ≤ ((Fintype.card Q - 2 : ℕ) : ℚ) := Nat.cast_nonneg _
  refine ⟨w, hw, ?_⟩
  nlinarith

/-- **Theorem T23(2c) (Strict Improvement Over Ferens–Szykuła Whenever `|M₁| ≥ 2` and `ℓ_orb = n`)**:
For every completely reachable DFA on `n ≥ 3` states with `maxOrbitSize A = n` and `|M₁| ≥ 2`,
the bound strictly beats Ferens–Szykuła (2025) by at least `(|M₁| - 1) * (n - 2) > 0`. -/
theorem completelyReachable_beats_ferensSzykula {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hCR : A.IsCompletelyReachable) (hn3 : 3 ≤ Fintype.card Q)
    (horb : maxOrbitSize A = Fintype.card Q)
    (hM2 : 2 ≤ (defectOneOmitted A).card) :
    ∃ w : List α, A.IsSyncWord w ∧
      (w.length : ℚ) ≤
        1 + ((Fintype.card Q - 2 : ℕ) : ℚ) * ((maxOrbitSize A : ℚ) + (Fintype.card Q : ℚ)) -
          (Fintype.card Q : ℚ) * harmonicRat (Fintype.card Q - 2) -
          (((defectOneOmitted A).card - 1 : ℕ) : ℚ) * ((Fintype.card Q - 2 : ℕ) : ℚ) ∧
      (w.length : ℚ) <
        1 + ((Fintype.card Q - 2 : ℕ) : ℚ) * ((maxOrbitSize A : ℚ) + (Fintype.card Q : ℚ)) -
          (Fintype.card Q : ℚ) * harmonicRat (Fintype.card Q - 2) := by
  obtain ⟨w, hw, hlen⟩ := completelyReachable_effOrbit_bound A hCR (by omega)
  have hle_sub := CompletelyReachable.effOrbitCap_le_card_sub_omitted A
  have hM_le : (defectOneOmitted A).card ≤ Fintype.card Q := Finset.card_le_univ _
  have heff_Q : (effOrbitCap A : ℚ) ≤
      (maxOrbitSize A : ℚ) - (((defectOneOmitted A).card - 1 : ℕ) : ℚ) := by
    rw [horb]
    have hnat : effOrbitCap A + ((defectOneOmitted A).card - 1) ≤ Fintype.card Q := by omega
    have hQ : (effOrbitCap A : ℚ) + (((defectOneOmitted A).card - 1 : ℕ) : ℚ) ≤
        (Fintype.card Q : ℚ) := by exact_mod_cast hnat
    linarith
  have hn2_pos : (0 : ℚ) < ((Fintype.card Q - 2 : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < Fintype.card Q - 2 by omega)
  have hM1_pos : (0 : ℚ) < (((defectOneOmitted A).card - 1 : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < (defectOneOmitted A).card - 1 by omega)
  refine ⟨w, hw, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- **Theorem T23(2d) (Breaking Leading Constant `2` to `(2 - ε) n²` Whenever `|M₁| ≥ ε n`)**:
Whenever `ε * n ≤ |M₁|`, every completely reachable DFA on `n ≥ 2` states admits a synchronizing
word of length `≤ 1 + (n - 2) * ((2 - ε) * n + 1) - n * H_{n - 2}`. -/
theorem completelyReachable_breaks_two_n_sq {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hCR : A.IsCompletelyReachable) (hn2 : 2 ≤ Fintype.card Q)
    (ε : ℚ) (hε : ε * (Fintype.card Q : ℚ) ≤ ((defectOneOmitted A).card : ℚ)) :
    ∃ w : List α, A.IsSyncWord w ∧
      (w.length : ℚ) ≤
        1 + ((Fintype.card Q - 2 : ℕ) : ℚ) * ((2 - ε) * (Fintype.card Q : ℚ) + 1) -
          (Fintype.card Q : ℚ) * harmonicRat (Fintype.card Q - 2) := by
  obtain ⟨w, hw, hlen⟩ := completelyReachable_effOrbit_bound A hCR hn2
  have hle_sub := CompletelyReachable.effOrbitCap_le_card_sub_omitted A
  have hM_le : (defectOneOmitted A).card ≤ Fintype.card Q := Finset.card_le_univ _
  have heff_Q : (effOrbitCap A : ℚ) + (Fintype.card Q : ℚ) ≤
      (2 - ε) * (Fintype.card Q : ℚ) + 1 := by
    have hnat : effOrbitCap A + (defectOneOmitted A).card ≤ Fintype.card Q + 1 := by omega
    have hQ : (effOrbitCap A : ℚ) + ((defectOneOmitted A).card : ℚ) ≤
        (Fintype.card Q : ℚ) + 1 := by exact_mod_cast hnat
    linarith
  have hn2_nonneg : (0 : ℚ) ≤ ((Fintype.card Q - 2 : ℕ) : ℚ) := Nat.cast_nonneg _
  refine ⟨w, hw, ?_⟩
  nlinarith

end Cerny
