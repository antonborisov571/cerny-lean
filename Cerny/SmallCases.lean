import Cerny.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto

/-!
# Černý's Conjecture for Small State Spaces (`n = 1, 2, 3, 4`)

This file proves the Černý Conjecture for all synchronizing DFAs with `Fintype.card Q ≤ 4`
using purely structural, zero-brute-force proofs:
* `cerny_card_eq_one`: `n = 1` (`w = []`, length `0`).
* `cerny_card_eq_two`: `n = 2` (any non-injective letter, length `1`).
* `cerny_card_eq_three`: `n = 3` (pair-graph layer growth gives length `≤ 4`).
* `cerny_card_eq_four`: `n = 4` (purely structural 7-step proof via unique pair-distance
  bijection, Golden Rule, unique rank-3 image triangle, and permutation orbit of vertex `3`,
  giving length `≤ 9`).
* `cerny_card_le_four`: unified theorem for all `1 ≤ Fintype.card Q ≤ 4`.
-/

namespace Cerny

section Helpers

variable {Q Q' α : Type*}

/-- Transport a DFA along an equivalence of state sets. -/
def DFA.reindex (A : DFA Q α) (e : Q ≃ Q') : DFA Q' α where
  step q a := e (A.step (e.symm q) a)

@[simp]
theorem DFA.reindex_eval (A : DFA Q α) (e : Q ≃ Q') (q : Q) (w : List α) :
    (A.reindex e).eval (e q) w = e (A.eval q w) := by
  induction w generalizing q with
  | nil => simp
  | cons a w ih =>
    simp only [DFA.eval_cons, DFA.reindex, Equiv.symm_apply_apply]
    exact ih (A.step q a)

theorem DFA.reindex_eval' (A : DFA Q α) (e : Q ≃ Q') (q' : Q') (w : List α) :
    (A.reindex e).eval q' w = e (A.eval (e.symm q') w) := by
  have := A.reindex_eval e (e.symm q') w
  simpa using this

theorem DFA.reindex_isSyncWord_iff (A : DFA Q α) (e : Q ≃ Q') (w : List α) :
    (A.reindex e).IsSyncWord w ↔ A.IsSyncWord w := by
  constructor
  · rintro ⟨q₀', hq₀'⟩
    refine ⟨e.symm q₀', fun q => ?_⟩
    have h := hq₀' (e q)
    rw [A.reindex_eval] at h
    exact e.injective (by simpa using h)
  · rintro ⟨q₀, hq₀⟩
    refine ⟨e q₀, fun q' => ?_⟩
    rw [A.reindex_eval', hq₀]

theorem DFA.reindex_isSynchronizing_iff (A : DFA Q α) (e : Q ≃ Q') :
    (A.reindex e).IsSynchronizing ↔ A.IsSynchronizing := by
  simp only [DFA.IsSynchronizing, DFA.reindex_isSyncWord_iff]

theorem DFA.reindex_image [DecidableEq Q] [DecidableEq Q'] (A : DFA Q α) (e : Q ≃ Q')
    (S : Finset Q) (w : List α) :
    (A.reindex e).image (S.image e) w = (A.image S w).image e := by
  ext q'
  simp only [DFA.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨p', ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨A.eval p w, ⟨p, hp, rfl⟩, (A.reindex_eval e p w).symm⟩
  · rintro ⟨r, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨e p, ⟨p, hp, rfl⟩, A.reindex_eval e p w⟩

theorem exists_non_injective_letter [Fintype Q] (A : DFA Q α) (hSync : A.IsSynchronizing)
    (hcard : 2 ≤ Fintype.card Q) :
    ∃ a : α, ¬ Function.Injective (fun q => A.step q a) := by
  by_contra hall
  push Not at hall
  have hword : ∀ w : List α, Function.Injective (fun q => A.eval q w) := by
    intro w
    induction w with
    | nil => exact Function.injective_id
    | cons a w ih =>
      intro p q hpq
      simp only [DFA.eval_cons] at hpq
      exact hall a (ih hpq)
  rcases hSync with ⟨w, q₀, hq₀⟩
  have h1 : 1 < Fintype.card Q := by omega
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card h1
  exact hpq (hword w ((hq₀ p).trans (hq₀ q).symm))

theorem card_image_lt_of_merge [DecidableEq Q] (A : DFA Q α) {S : Finset Q} (w : List α)
    {x y : Q} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hmerge : A.eval x w = A.eval y w) :
    (A.image S w).card < S.card := by
  have heq : A.image S w = A.image (S.erase x) w := by
    ext q
    simp only [DFA.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨p, hp, rfl⟩
      by_cases hpx : p = x
      · subst hpx
        exact ⟨y, ⟨hxy.symm, hy⟩, hmerge.symm⟩
      · exact ⟨p, ⟨hpx, hp⟩, rfl⟩
    · rintro ⟨p, ⟨_, hp⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [heq]
  have hle := A.card_image_le (S.erase x) w
  have hlt : (S.erase x).card < S.card := Finset.card_erase_lt_of_mem hx
  exact lt_of_le_of_lt hle hlt

theorem exists_merge_of_card_image_lt [DecidableEq Q] (A : DFA Q α) {S : Finset Q} {w : List α}
    (hlt : (A.image S w).card < S.card) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ A.eval x w = A.eval y w := by
  by_contra hall
  push Not at hall
  have hinj : Set.InjOn (fun q => A.eval q w) S := by
    intro x hx y hy hxy
    by_contra hne
    exact hall x hx y hy hne hxy
  have heq : (A.image S w).card = S.card := Finset.card_image_of_injOn hinj
  omega

theorem card_image_eq_one_iff_pair [DecidableEq Q] (A : DFA Q α) {x y : Q}
    (w : List α) : (A.image {x, y} w).card = 1 ↔ A.eval x w = A.eval y w := by
  have himg : A.image {x, y} w = {A.eval x w, A.eval y w} := by
    ext q
    simp [DFA.mem_image]
    tauto
  rw [himg]
  constructor
  · intro h1
    rw [Finset.card_eq_one] at h1
    rcases h1 with ⟨z, hz⟩
    have hx : A.eval x w ∈ ({z} : Finset Q) := by rw [← hz]; simp
    have hy : A.eval y w ∈ ({z} : Finset Q) := by rw [← hz]; simp
    simp only [Finset.mem_singleton] at hx hy
    exact hx.trans hy.symm
  · intro heq
    rw [heq]
    simp

/-- General pair-graph distance: minimum length of a word merging a subset `e`. -/
theorem exists_merge_word [Fintype Q] [DecidableEq Q] (A : DFA Q α) (hSync : A.IsSynchronizing)
    (e : Finset Q) (he : e.Nonempty) :
    ∃ k : ℕ, ∃ w : List α, w.length = k ∧ (A.image e w).card = 1 := by
  rcases hSync with ⟨w, q₀, hq₀⟩
  refine ⟨w.length, w, rfl, ?_⟩
  rw [Finset.card_eq_one]
  refine ⟨q₀, ?_⟩
  ext q
  simp only [DFA.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨p, _, rfl⟩
    exact hq₀ p
  · rintro rfl
    rcases he with ⟨p, hp⟩
    exact ⟨p, hp, hq₀ p⟩

noncomputable def pairDist [Fintype Q] [DecidableEq Q] (A : DFA Q α) (hSync : A.IsSynchronizing)
    (e : Finset Q) : ℕ := by
  classical
  exact if he : e.Nonempty then Nat.find (exists_merge_word A hSync e he) else 0

theorem pairDist_spec [Fintype Q] [DecidableEq Q] (A : DFA Q α) (hSync : A.IsSynchronizing)
    {e : Finset Q} (he : e.Nonempty) :
    ∃ w : List α, w.length = pairDist A hSync e ∧ (A.image e w).card = 1 := by
  classical
  unfold pairDist
  simp only [he, ↓reduceDIte]
  exact Nat.find_spec (exists_merge_word A hSync e he)

theorem pairDist_le_of_merge [Fintype Q] [DecidableEq Q] (A : DFA Q α) (hSync : A.IsSynchronizing)
    {e : Finset Q} (he : e.Nonempty) {w : List α} (hw : (A.image e w).card = 1) :
    pairDist A hSync e ≤ w.length := by
  classical
  unfold pairDist
  simp only [he, ↓reduceDIte]
  exact Nat.find_min' (exists_merge_word A hSync e he) ⟨w, rfl, hw⟩

theorem pairDist_pos_of_card_two [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {e : Finset Q} (he : e.card = 2) :
    1 ≤ pairDist A hSync e := by
  have hne : e.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w, hlen, hw⟩ := pairDist_spec A hSync hne
  by_contra hlt
  have h0 : w.length = 0 := by omega
  have hnil : w = [] := List.eq_nil_of_length_eq_zero h0
  rw [hnil, DFA.image_nil] at hw
  omega

/-- Pairs of states merged in at most `k` steps. -/
noncomputable def pairLayer [Fintype Q] [DecidableEq Q] (A : DFA Q α) (hSync : A.IsSynchronizing)
    (k : ℕ) : Finset (Finset Q) := by
  classical
  exact ((Finset.univ : Finset Q).powersetCard 2).filter (fun e => pairDist A hSync e ≤ k)

theorem pairLayer_mono [Fintype Q] [DecidableEq Q] (A : DFA Q α) (hSync : A.IsSynchronizing)
    {j k : ℕ} (hjk : j ≤ k) :
    pairLayer A hSync j ⊆ pairLayer A hSync k := by
  classical
  intro e he
  simp only [pairLayer, Finset.mem_filter] at he ⊢
  exact ⟨he.1, le_trans he.2 hjk⟩

theorem pairLayer_one_nonempty [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hcard : 2 ≤ Fintype.card Q) :
    (pairLayer A hSync 1).Nonempty := by
  classical
  obtain ⟨a, hni⟩ := exists_non_injective_letter A hSync hcard
  unfold Function.Injective at hni
  push Not at hni
  rcases hni with ⟨x, y, hxy_eq, hxy_ne⟩
  refine ⟨{x, y}, ?_⟩
  simp only [pairLayer, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  refine ⟨Finset.card_pair hxy_ne, ?_⟩
  have hne : ({x, y} : Finset Q).Nonempty := ⟨x, by simp⟩
  have hmerge : (A.image {x, y} [a]).card = 1 :=
    (card_image_eq_one_iff_pair A [a]).mpr hxy_eq
  exact pairDist_le_of_merge A hSync hne hmerge

theorem pairLayer_strict_growth [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (k : ℕ)
    (hstrict : pairLayer A hSync k ≠ (Finset.univ : Finset Q).powersetCard 2) :
    (pairLayer A hSync k).card + 1 ≤ (pairLayer A hSync (k + 1)).card := by
  classical
  have hsub : pairLayer A hSync k ⊆ (Finset.univ : Finset Q).powersetCard 2 :=
    Finset.filter_subset _ _
  have hssub : pairLayer A hSync k ⊂ (Finset.univ : Finset Q).powersetCard 2 :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hstrict⟩
  obtain ⟨e, heP, heNot⟩ := Finset.exists_of_ssubset hssub
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at heP
  simp only [pairLayer, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
    true_and, heP, true_and, not_le] at heNot
  have hne : e.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w, hlen, hw⟩ := pairDist_spec A hSync hne
  have hm_ge : k + 1 ≤ w.length := by omega
  let pref := w.take (w.length - (k + 1))
  let suf := w.drop (w.length - (k + 1))
  let e' := A.image e pref
  have hps : pref ++ suf = w := List.take_append_drop _ w
  have hsuf_len : suf.length = k + 1 := by
    simp only [suf, List.length_drop]
    omega
  have hpref_len : pref.length = w.length - (k + 1) := by
    simp only [pref, List.length_take]
    omega
  have he'_card_le : e'.card ≤ 2 := le_trans (A.card_image_le e pref) heP.le
  have he'_card_ne_zero : e'.card ≠ 0 := by
    have : e'.Nonempty := by
      rcases hne with ⟨p, hp⟩
      exact ⟨A.eval p pref, by rw [DFA.mem_image]; exact ⟨p, hp, rfl⟩⟩
    exact (Finset.card_pos.mpr this).ne'
  have he'_card_ne_one : e'.card ≠ 1 := by
    intro h1
    have hle := pairDist_le_of_merge A hSync hne h1
    omega
  have he'_card : e'.card = 2 := by omega
  have he'_ne : e'.Nonempty := Finset.card_pos.mp (by omega)
  have he'_merge : (A.image e' suf).card = 1 := by
    rw [← DFA.image_append, hps]
    exact hw
  have hdist_le : pairDist A hSync e' ≤ k + 1 := by
    rw [← hsuf_len]
    exact pairDist_le_of_merge A hSync he'_ne he'_merge
  have hdist_gt : k < pairDist A hSync e' := by
    by_contra hle
    push Not at hle
    obtain ⟨u, hulen, hu⟩ := pairDist_spec A hSync he'_ne
    have hmerge' : (A.image e (pref ++ u)).card = 1 := by
      rw [DFA.image_append]
      exact hu
    have hbound := pairDist_le_of_merge A hSync hne hmerge'
    rw [List.length_append] at hbound
    omega
  have he'_mem : e' ∈ pairLayer A hSync (k + 1) := by
    simp only [pairLayer, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact ⟨he'_card, hdist_le⟩
  have he'_not_mem : e' ∉ pairLayer A hSync k := by
    simp only [pairLayer, Finset.mem_filter, not_and, not_le]
    intro _
    exact hdist_gt
  have hsub2 : pairLayer A hSync k ⊂ pairLayer A hSync (k + 1) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨pairLayer_mono A hSync (by omega), fun heq => by
      rw [← heq] at he'_mem
      exact he'_not_mem he'_mem⟩
  exact Finset.card_lt_card hsub2

theorem pairLayer_card_ge [Fintype Q] [DecidableEq Q] (A : DFA Q α) (hSync : A.IsSynchronizing)
    (hcard : 2 ≤ Fintype.card Q) (k : ℕ) (hk : 1 ≤ k) :
    min ((Fintype.card Q).choose 2) k ≤ (pairLayer A hSync k).card := by
  classical
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp only [zero_add]
      have hne := pairLayer_one_nonempty A hSync hcard
      have hpos : 1 ≤ (pairLayer A hSync 1).card := Finset.card_pos.mpr hne
      omega
    · have ih' := ih (by omega)
      by_cases hfull : pairLayer A hSync k = (Finset.univ : Finset Q).powersetCard 2
      · have hle : (pairLayer A hSync k).card ≤ (pairLayer A hSync (k + 1)).card :=
          Finset.card_le_card (pairLayer_mono A hSync (by omega))
        rw [hfull, Finset.card_powersetCard, Finset.card_univ] at hle
        omega
      · have hgrow := pairLayer_strict_growth A hSync k hfull
        omega

theorem pairDist_le_choose_two [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hcard : 2 ≤ Fintype.card Q)
    {e : Finset Q} (he : e.card = 2) :
    pairDist A hSync e ≤ (Fintype.card Q).choose 2 := by
  classical
  have hchoose_pos : 1 ≤ (Fintype.card Q).choose 2 := by
    have h1 : (2 : ℕ).choose 2 ≤ (Fintype.card Q).choose 2 := Nat.choose_le_choose 2 hcard
    simpa using h1
  have hge := pairLayer_card_ge A hSync hcard ((Fintype.card Q).choose 2) hchoose_pos
  rw [min_self] at hge
  have hsub : pairLayer A hSync ((Fintype.card Q).choose 2) ⊆
      (Finset.univ : Finset Q).powersetCard 2 := Finset.filter_subset _ _
  have heq : pairLayer A hSync ((Fintype.card Q).choose 2) =
      (Finset.univ : Finset Q).powersetCard 2 := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_powersetCard, Finset.card_univ]
    exact hge
  have hmem : e ∈ pairLayer A hSync ((Fintype.card Q).choose 2) := by
    rw [heq, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ e, he⟩
  simp only [pairLayer, Finset.mem_filter] at hmem
  exact hmem.2

end Helpers

section SmallOneTwoThree

variable {Q α : Type*}

/-- Černý's Conjecture for `n = 1`: the empty word synchronizes in length `0 = (1 - 1) ^ 2`. -/
theorem cerny_card_eq_one [Fintype Q] (A : DFA Q α)
    (hcard : Fintype.card Q = 1) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨q₀⟩ := hSync.nonempty
  refine ⟨[], ⟨q₀, fun q => Subsingleton.elim _ _⟩, ?_⟩
  simp [hcard]

/-- Černý's Conjecture for `n = 2`: any non-injective letter synchronizes in length `1 = (2 - 1) ^ 2`. -/
theorem cerny_card_eq_two [Fintype Q] (A : DFA Q α)
    (hcard : Fintype.card Q = 2) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  obtain ⟨a, hni⟩ := exists_non_injective_letter A hSync (by omega)
  unfold Function.Injective at hni
  push Not at hni
  rcases hni with ⟨x, y, hxy_eq, hxy_ne⟩
  have huniv : ({x, y} : Finset Q) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Finset.card_pair hxy_ne, hcard]
  refine ⟨[a], ⟨A.step x a, fun q => ?_⟩, ?_⟩
  · have hmem : q ∈ ({x, y} : Finset Q) := by rw [huniv]; exact Finset.mem_univ q
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · rfl
    · exact hxy_eq.symm
  · simp [hcard]

/-- Černý's Conjecture for `n = 3`: a non-injective letter followed by a pair-merging word
has length at most `1 + 3 = 4 = (3 - 1) ^ 2`. -/
theorem cerny_card_eq_three [Fintype Q] (A : DFA Q α)
    (hcard : Fintype.card Q = 3) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  obtain ⟨a, hni⟩ := exists_non_injective_letter A hSync (by omega)
  unfold Function.Injective at hni
  push Not at hni
  rcases hni with ⟨x, y, hxy_eq, hxy_ne⟩
  have hlt : (A.image Finset.univ [a]).card < (Finset.univ : Finset Q).card :=
    card_image_lt_of_merge A [a] (Finset.mem_univ x) (Finset.mem_univ y) hxy_ne hxy_eq
  rw [Finset.card_univ, hcard] at hlt
  have hne : (A.image Finset.univ [a]).Nonempty :=
    ⟨A.eval x [a], by rw [DFA.mem_image]; exact ⟨x, Finset.mem_univ x, rfl⟩⟩
  have hpos : 1 ≤ (A.image Finset.univ [a]).card := Finset.card_pos.mpr hne
  by_cases h1 : (A.image Finset.univ [a]).card = 1
  · refine ⟨[a], (A.isSyncWord_iff_card_image_univ_eq_one [a]).mpr h1, ?_⟩
    simp [hcard]
  · have h2 : (A.image Finset.univ [a]).card = 2 := by omega
    obtain ⟨v, hvlen, hv⟩ := pairDist_spec A hSync hne
    have hdist : pairDist A hSync (A.image Finset.univ [a]) ≤ 3 := by
      have h := pairDist_le_choose_two A hSync (by omega) h2
      rw [hcard] at h
      have h32 : (3 : ℕ).choose 2 = 3 := by decide
      omega
    refine ⟨a :: v, ?_, ?_⟩
    · rw [A.isSyncWord_iff_card_image_univ_eq_one, A.image_cons]
      exact hv
    · simp only [List.length_cons, hcard]
      omega

end SmallOneTwoThree

section SmallFour

variable {α : Type*}

/-- Elementary `n = 4, r = 3` compression lemma: every 3-subset of `Fin 4` in a synchronizing
DFA is compressed in at most `3` steps (pure `Finset` pigeonhole, zero linear algebra!). -/
private theorem compress_three_fin4 (A : DFA (Fin 4) α) (hSync : A.IsSynchronizing)
    (T : Finset (Fin 4)) (hT : T.card = 3) :
    ∃ w : List α, w.length ≤ 3 ∧ (A.image T w).card < 3 ∧
      ∀ v : List α, (A.image T v).card < 3 → w.length ≤ v.length := by
  classical
  have hex : ∃ k : ℕ, ∃ w : List α, w.length = k ∧ (A.image T w).card < 3 := by
    rcases hSync with ⟨w, q₀, hq₀⟩
    refine ⟨w.length, w, rfl, ?_⟩
    have hsub : A.image T w ⊆ {q₀} := by
      intro q hq
      rw [DFA.mem_image] at hq
      rcases hq with ⟨p, _, rfl⟩
      simp [hq₀ p]
    have := Finset.card_le_card hsub
    simp at this
    omega
  obtain ⟨w, hwlen, hwcomp⟩ := Nat.find_spec hex
  have hmin : ∀ v : List α, (A.image T v).card < 3 → w.length ≤ v.length := by
    intro v hv
    rw [hwlen]
    exact Nat.find_min' hex ⟨v, rfl, hv⟩
  refine ⟨w, ?_, hwcomp, hmin⟩
  by_contra hgt
  push Not at hgt
  let Ti : Fin 4 → Finset (Fin 4) := fun i => A.image T (w.take i.val)
  have hTi_card : ∀ i : Fin 4, (Ti i).card = 3 := by
    intro i
    have hle : (Ti i).card ≤ 3 := le_trans (A.card_image_le T _) hT.le
    have hnotlt : ¬ (Ti i).card < 3 := by
      intro hlt
      have := hmin (w.take i.val) hlt
      rw [List.length_take] at this
      omega
    omega
  have hcut : ∀ i j : Fin 4, i.val < j.val → Ti i ≠ Ti j := by
    intro i j hlt hij
    let w' := w.take i.val ++ w.drop j.val
    have himg : A.image T w' = A.image T w := by
      dsimp [w']
      rw [DFA.image_append]
      change A.image (Ti i) (w.drop j.val) = A.image T w
      rw [hij]
      dsimp [Ti]
      rw [← DFA.image_append, List.take_append_drop]
    have hlt' : (A.image T w').card < 3 := by rw [himg]; exact hwcomp
    have hbound := hmin w' hlt'
    simp only [w', List.length_append, List.length_take, List.length_drop] at hbound
    omega
  have hTi_inj : Function.Injective Ti := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt'
    · exact hcut i j hlt hij
    · exact hcut j i hgt' hij.symm
  have hTi_surj : ∀ S : Finset (Fin 4), S.card = 3 → ∃ i : Fin 4, Ti i = S := by
    intro S hS
    let imgSet : Finset (Finset (Fin 4)) := Finset.univ.image Ti
    have himg_sub : imgSet ⊆ (Finset.univ : Finset (Fin 4)).powersetCard 3 := by
      intro U hU
      rw [Finset.mem_image] at hU
      rcases hU with ⟨i, _, rfl⟩
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hTi_card i⟩
    have himg_card : imgSet.card = 4 := by
      rw [Finset.card_image_of_injective _ hTi_inj, Finset.card_univ, Fintype.card_fin]
    have heq : imgSet = (Finset.univ : Finset (Fin 4)).powersetCard 3 := by
      apply Finset.eq_of_subset_of_card_le himg_sub
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, himg_card]
      decide
    have hmem : S ∈ imgSet := by
      rw [heq, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hS⟩
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  have hw_ne : w ≠ [] := by
    intro hnil
    rw [hnil] at hgt
    simp at hgt
  let w' := w.dropLast
  let c := w.getLast hw_ne
  have hw_eq : w' ++ [c] = w := List.dropLast_append_getLast hw_ne
  have hprev_card : (A.image T w').card = 3 := by
    have hle : (A.image T w').card ≤ 3 := le_trans (A.card_image_le T w') hT.le
    have hnotlt : ¬ (A.image T w').card < 3 := by
      intro hlt
      have := hmin w' hlt
      have hlen' : w'.length = w.length - 1 := List.length_dropLast
      omega
    omega
  have hcomp_c : (A.image (A.image T w') [c]).card < (A.image T w').card := by
    rw [← DFA.image_append, hw_eq, hprev_card]
    exact hwcomp
  obtain ⟨x, _, y, _, hxy_ne, hxy_merge⟩ := exists_merge_of_card_image_lt A hcomp_c
  have hcompl_card : (Finset.univ \ ({x, y} : Finset (Fin 4))).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_pair hxy_ne]
  rw [Finset.card_eq_two] at hcompl_card
  rcases hcompl_card with ⟨z₁, z₂, hz_ne, hz_eq⟩
  let S₁ : Finset (Fin 4) := Finset.univ.erase z₁
  let S₂ : Finset (Fin 4) := Finset.univ.erase z₂
  have hS₁_card : S₁.card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hS₂_card : S₂.card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hS₁_ne_S₂ : S₁ ≠ S₂ := by
    intro heq
    have hz₁_not : z₁ ∉ S₁ := Finset.notMem_erase z₁ _
    have hz₁_in : z₁ ∈ S₂ := Finset.mem_erase.mpr ⟨hz_ne, Finset.mem_univ z₁⟩
    rw [heq] at hz₁_not
    exact hz₁_not hz₁_in
  have hxy_in : ∀ z ∈ ({z₁, z₂} : Finset (Fin 4)),
      x ∈ Finset.univ.erase z ∧ y ∈ Finset.univ.erase z := by
    intro z hz
    have hz' : z ∈ Finset.univ \ ({x, y} : Finset (Fin 4)) := by rw [hz_eq]; exact hz
    rw [Finset.mem_sdiff] at hz'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz'
    exact ⟨Finset.mem_erase.mpr ⟨Ne.symm hz'.2.1, Finset.mem_univ x⟩,
      Finset.mem_erase.mpr ⟨Ne.symm hz'.2.2, Finset.mem_univ y⟩⟩
  obtain ⟨i₁, hi₁⟩ := hTi_surj S₁ hS₁_card
  obtain ⟨i₂, hi₂⟩ := hTi_surj S₂ hS₂_card
  have hi_ne : i₁ ≠ i₂ := by
    intro heq
    rw [heq] at hi₁
    exact hS₁_ne_S₂ (hi₁.symm.trans hi₂)
  have hex_le2 : ∃ i : Fin 4, i.val ≤ 2 ∧ x ∈ Ti i ∧ y ∈ Ti i := by
    by_cases h1 : i₁.val ≤ 2
    · refine ⟨i₁, h1, ?_⟩
      rw [hi₁]
      exact hxy_in z₁ (by simp)
    · refine ⟨i₂, by omega, ?_⟩
      rw [hi₂]
      exact hxy_in z₂ (by simp)
  rcases hex_le2 with ⟨i, hi_le, hxTi, hyTi⟩
  let w_short := w.take i.val ++ [c]
  have hcomp_short : (A.image T w_short).card < 3 := by
    dsimp [w_short]
    rw [DFA.image_append]
    have hlt' := card_image_lt_of_merge A [c] hxTi hyTi hxy_ne hxy_merge
    rw [hTi_card i] at hlt'
    exact hlt'
  have hbound := hmin w_short hcomp_short
  simp only [w_short, List.length_append, List.length_take, List.length_singleton] at hbound
  omega

private def IsBijLetter (A : DFA (Fin 4) α) (c : α) : Prop :=
  Function.Bijective (fun q : Fin 4 => A.step q c)

private def IsBijWord (A : DFA (Fin 4) α) (g : List α) : Prop :=
  ∀ c ∈ g, IsBijLetter A c

private theorem image_erase_of_isBijLetter (A : DFA (Fin 4) α) {c : α} (hc : IsBijLetter A c)
    (x : Fin 4) :
    A.image (Finset.univ.erase x) [c] = Finset.univ.erase (A.step x c) := by
  ext q
  simp only [DFA.mem_image, DFA.eval_singleton, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨p, hpx, rfl⟩
    intro heq
    exact hpx (hc.1 heq)
  · intro hne
    obtain ⟨p, rfl⟩ := hc.2 q
    refine ⟨p, ?_, rfl⟩
    intro rfl
    exact hne rfl

private theorem image_erase_of_isBijWord (A : DFA (Fin 4) α) {g : List α} (hg : IsBijWord A g)
    (x : Fin 4) :
    A.image (Finset.univ.erase x) g = Finset.univ.erase (A.eval x g) := by
  induction g generalizing x with
  | nil => simp
  | cons c g ih =>
    rw [DFA.image_cons, DFA.eval_cons]
    have hc : IsBijLetter A c := hg c List.mem_cons_self
    have hg' : IsBijWord A g := fun a ha => hg a (List.mem_cons_of_mem c ha)
    rw [image_erase_of_isBijLetter A hc x, ih hg' (A.step x c)]

private theorem fin4_pair_eq_02 {a b : Fin 4} (ha : a ∈ ({0, 1, 2} : Finset (Fin 4)))
    (hb : b ∈ ({0, 1, 2} : Finset (Fin 4))) (hab : a ≠ b) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ({a, b} : Finset (Fin 4)) = {0, 2} := by
  fin_cases a <;> fin_cases b <;> revert ha hb hab ha1 hb1 <;> decide

private theorem fin4_cases_three_distinct {a b c : Fin 4}
    (ha : a ∈ ({0, 1, 2} : Finset (Fin 4))) (hb : b ∈ ({0, 1, 2} : Finset (Fin 4)))
    (hc : c ∈ ({0, 1, 2} : Finset (Fin 4)))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hb1 : b ≠ 1) :
    c = 1 ∨ a = 1 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> revert ha hb hc hab hac hbc hb1 <;> decide

private theorem fin4_injOn_erase_of_ker (f : Fin 4 → Fin 4)
    (h03 : f 0 = f 3) (h01 : f 0 ≠ f 1) (h02 : f 0 ≠ f 2) (h12 : f 1 ≠ f 2)
    {x : Fin 4} (hx : x = 0 ∨ x = 3) :
    Set.InjOn f (Finset.univ.erase x : Set (Fin 4)) := by
  intro p hp q hq hpq
  simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true] at hp hq
  rcases hx with rfl | rfl <;> fin_cases p <;> fin_cases q
  all_goals first | rfl | exact absurd rfl hp | exact absurd rfl hq |
    exact absurd hpq h01 | exact absurd hpq.symm h01 |
    exact absurd hpq h02 | exact absurd hpq.symm h02 |
    exact absurd hpq h12 | exact absurd hpq.symm h12 |
    exact absurd (h03.trans hpq.symm) h01 | exact absurd (h03.trans hpq) h01 |
    exact absurd (h03.trans hpq.symm) h02 | exact absurd (h03.trans hpq) h02

/-- Step 6 contradiction (`|O₃| = 3`, with `1 ∉ O₃` and `2 ∈ O₃`). -/
private theorem cerny_fin4_step6_false (A : DFA (Fin 4) α) (hSync : A.IsSynchronizing)
    (hdist_inj : ∀ e₁ e₂ : Finset (Fin 4), e₁.card = 2 → e₂.card = 2 →
      pairDist A hSync e₁ = pairDist A hSync e₂ → e₁ = e₂)
    (hrank_or : ∀ c : α, IsBijLetter A c ∨ (A.image Finset.univ [c]).card = 3)
    (hT3_of_rank3 : ∀ a : α, (A.image Finset.univ [a]).card = 3 →
      A.image Finset.univ [a] = ({0, 1, 2} : Finset (Fin 4)))
    (hker_of_rank3 : ∀ a : α, (A.image Finset.univ [a]).card = 3 →
      A.step 0 a = A.step 3 a ∧
      A.step 0 a ≠ A.step 1 a ∧ A.step 0 a ≠ A.step 2 a ∧ A.step 1 a ≠ A.step 2 a)
    (hgolden_card : ∀ (e : Finset (Fin 4)) (c : α), e.card = 2 → 2 ≤ pairDist A hSync e →
      (A.image e [c]).card = 2)
    (hgolden_dist : ∀ (e : Finset (Fin 4)) (c : α), e.card = 2 → 2 ≤ pairDist A hSync e →
      pairDist A hSync e - 1 ≤ pairDist A hSync (A.image e [c]))
    (he1 : pairDist A hSync ({0, 3} : Finset (Fin 4)) = 1)
    (he2 : pairDist A hSync ({2, 3} : Finset (Fin 4)) = 2)
    (e₃ e₄ e₆ : Finset (Fin 4))
    (he₃_card : e₃.card = 2) (he₃_dist : pairDist A hSync e₃ = 3) (he₃_sub : e₃ ⊆ {0, 1, 2})
    (he₄_card : e₄.card = 2) (he₄_dist : pairDist A hSync e₄ = 4)
    (he₆_card : e₆.card = 2) (he₆_dist : pairDist A hSync e₆ = 6) (he₆_sub : e₆ ⊆ {0, 1, 2})
    (b₂ b₃ : α) (hb₂_bij : IsBijLetter A b₂)
    (hb₂_img : A.image ({2, 3} : Finset (Fin 4)) [b₂] = {0, 3})
    (hb₃_bij : IsBijLetter A b₃) (hb₃_img : A.image e₃ [b₃] = {2, 3})
    (hfix1 : ∀ b : α, IsBijLetter A b → A.step 1 b = 1) :
    False := by
  classical
  let T₃ : Finset (Fin 4) := {0, 1, 2}
  have h1_not_e3 : (1 : Fin 4) ∉ e₃ := by
    intro h1in
    have h1mem : (1 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)) := by
      rw [← hb₃_img, DFA.mem_image]
      exact ⟨1, h1in, hfix1 b₃ hb₃_bij⟩
    exact absurd h1mem (by decide)
  have he₃_eq_02 : e₃ = {0, 2} := by
    have hsub : e₃ ⊆ ({0, 2} : Finset (Fin 4)) := by
      intro q hq
      have hqT := he₃_sub hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqT ⊢
      rcases hqT with rfl | rfl | rfl
      · left; rfl
      · exact absurd hq h1_not_e3
      · right; rfl
    exact Finset.eq_of_subset_of_card_le hsub (by rw [he₃_card]; decide)
  have h1_mem_of_ge4 : ∀ e : Finset (Fin 4), e.card = 2 → 4 ≤ pairDist A hSync e →
      (1 : Fin 4) ∈ e := by
    intro e heCard hge4
    by_contra h1not
    have hsub : e ⊆ ({0, 2, 3} : Finset (Fin 4)) := by
      intro q hq
      fin_cases q <;> simp_all
    have hmem : e ∈ ({0, 2, 3} : Finset (Fin 4)).powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨hsub, heCard⟩
    have hset : ({0, 2, 3} : Finset (Fin 4)).powersetCard 2 = {{0, 2}, {0, 3}, {2, 3}} := by
      decide
    rw [hset] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [← he₃_eq_02, he₃_dist] at hge4; omega
    · rw [he1] at hge4; omega
    · rw [he2] at hge4; omega
  -- Pick c₄ mapping e₄ → {0, 2}
  have hc₄_ex : ∃ c₄ : α, A.image e₄ [c₄] = {0, 2} := by
    have he₄_ne : e₄.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨w, hwlen, hw⟩ := pairDist_spec A hSync he₄_ne
    rw [he₄_dist] at hwlen
    cases w with
    | nil => simp at hwlen
    | cons c rest =>
      have hcard2 := hgolden_card e₄ c he₄_card (by omega)
      have hne : (A.image e₄ [c]).Nonempty := Finset.card_pos.mp (by omega)
      have hmerge : (A.image (A.image e₄ [c]) rest).card = 1 := by
        rw [← DFA.image_cons]; exact hw
      have hle : pairDist A hSync (A.image e₄ [c]) ≤ 3 := by
        have := pairDist_le_of_merge A hSync hne hmerge
        simp only [List.length_cons] at hwlen
        omega
      have hge := hgolden_dist e₄ c he₄_card (by omega)
      have himg : A.image e₄ [c] = e₃ := hdist_inj _ _ hcard2 he₃_card (by omega)
      rw [he₃_eq_02] at himg
      exact ⟨c, himg⟩
  obtain ⟨c₄, hc₄_img⟩ := hc₄_ex
  have h1_in_e4 : (1 : Fin 4) ∈ e₄ := h1_mem_of_ge4 e₄ he₄_card (by omega)
  have hc₄_step1_in : A.step 1 c₄ ∈ ({0, 2} : Finset (Fin 4)) := by
    rw [← hc₄_img, DFA.mem_image]
    exact ⟨1, h1_in_e4, rfl⟩
  have hc₄_rank3 : (A.image Finset.univ [c₄]).card = 3 := by
    rcases hrank_or c₄ with hbij | h3
    · exfalso
      rw [hfix1 c₄ hbij] at hc₄_step1_in
      exact absurd hc₄_step1_in (by decide)
    · exact h3
  have hc₄_T3 := hT3_of_rank3 c₄ hc₄_rank3
  have hc₄_ker := hker_of_rank3 c₄ hc₄_rank3
  have h012_mem : ∀ q : Fin 4, A.step q c₄ ∈ ({0, 1, 2} : Finset (Fin 4)) := by
    intro q
    rw [← hc₄_T3, DFA.mem_image]
    exact ⟨q, Finset.mem_univ q, rfl⟩
  have hc₄_step1_ne1 : A.step 1 c₄ ≠ 1 := by
    intro h1
    rw [h1] at hc₄_step1_in
    exact absurd hc₄_step1_in (by decide)
  have hcases_c4 : A.step 2 c₄ = 1 ∨ A.step 0 c₄ = 1 :=
    fin4_cases_three_distinct (h012_mem 0) (h012_mem 1) (h012_mem 2)
      hc₄_ker.2.1 hc₄_ker.2.2.1 hc₄_ker.2.2.2 hc₄_step1_ne1
  -- Helper: any pair different from {0,3}, {2,3}, {0,2} has pairDist ≥ 4
  have hge4_of_ne : ∀ e : Finset (Fin 4), e.card = 2 →
      e ≠ {0, 3} → e ≠ {2, 3} → e ≠ {0, 2} → 4 ≤ pairDist A hSync e := by
    intro e hec h1 h2 h3
    have hpos := pairDist_pos_of_card_two A hSync hec
    have hd1 : pairDist A hSync e ≠ 1 := fun h => h1 (hdist_inj _ _ hec (by decide) (by omega))
    have hd2 : pairDist A hSync e ≠ 2 := fun h => h2 (hdist_inj _ _ hec (by decide) (by omega))
    have hd3 : pairDist A hSync e ≠ 3 := fun h =>
      h3 (by rw [← he₃_eq_02]; exact hdist_inj _ _ hec he₃_card (by omega))
    omega
  rcases hcases_c4 with h2_eq_1 | h0_eq_1
  · -- Subcase 6a: A.step 2 c₄ = 1 ⇒ {0, 1} · c₄ = {1, 3} · c₄ = {0, 2} = e₃
    have h01_img : A.image ({0, 1} : Finset (Fin 4)) [c₄] = {0, 2} := by
      have heq_pair : A.image ({0, 1} : Finset (Fin 4)) [c₄] = {A.step 0 c₄, A.step 1 c₄} := by
        ext q
        simp only [DFA.mem_image, DFA.eval_singleton, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨p, rfl | rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨0, Or.inl rfl, rfl⟩
          · exact ⟨1, Or.inr rfl, rfl⟩
      rw [heq_pair]
      exact fin4_pair_eq_02 (h012_mem 0) (h012_mem 1) hc₄_ker.2.1
        (fun h => hc₄_ker.2.2.1 (h.trans h2_eq_1.symm)) hc₄_step1_ne1
    have h13_img : A.image ({1, 3} : Finset (Fin 4)) [c₄] = {0, 2} := by
      rw [← h01_img]
      ext q
      simp only [DFA.mem_image, DFA.eval_singleton, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨p, rfl | rfl, rfl⟩
        · exact ⟨1, Or.inr rfl, rfl⟩
        · exact ⟨0, Or.inl rfl, hc₄_ker.1⟩
      · rintro ⟨p, rfl | rfl, rfl⟩
        · exact ⟨3, Or.inr rfl, hc₄_ker.1.symm⟩
        · exact ⟨1, Or.inl rfl, rfl⟩
    have hd01 := hge4_of_ne {0, 1} (by decide) (by decide) (by decide) (by decide)
    have hd13 := hge4_of_ne {1, 3} (by decide) (by decide) (by decide) (by decide)
    have hg01 := hgolden_dist {0, 1} c₄ (by decide) (by omega)
    have hg13 := hgolden_dist {1, 3} c₄ (by decide) (by omega)
    rw [h01_img, ← he₃_eq_02, he₃_dist] at hg01
    rw [h13_img, ← he₃_eq_02, he₃_dist] at hg13
    have heq_pairs : ({0, 1} : Finset (Fin 4)) = {1, 3} :=
      hdist_inj _ _ (by decide) (by decide) (by omega)
    exact absurd heq_pairs (by decide)
  · -- Subcase 6b: A.step 0 c₄ = 1 ⇒ {1, 2} · c₄ = {0, 2} = e₃ ⇒ e₄ = {1, 2}, e₆ = {0, 1}, b₂(0) = 2
    have h12_img : A.image ({1, 2} : Finset (Fin 4)) [c₄] = {0, 2} := by
      have heq_pair : A.image ({1, 2} : Finset (Fin 4)) [c₄] = {A.step 1 c₄, A.step 2 c₄} := by
        ext q
        simp only [DFA.mem_image, DFA.eval_singleton, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨p, rfl | rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨1, Or.inl rfl, rfl⟩
          · exact ⟨2, Or.inr rfl, rfl⟩
      rw [heq_pair]
      exact fin4_pair_eq_02 (h012_mem 1) (h012_mem 2) hc₄_ker.2.2.2
        hc₄_step1_ne1 (fun h => hc₄_ker.2.2.1 (h0_eq_1.trans h.symm))
    have hd12 := hge4_of_ne {1, 2} (by decide) (by decide) (by decide) (by decide)
    have hg12 := hgolden_dist {1, 2} c₄ (by decide) (by omega)
    rw [h12_img, ← he₃_eq_02, he₃_dist] at hg12
    have hd12_eq4 : pairDist A hSync ({1, 2} : Finset (Fin 4)) = 4 := by omega
    have he₆_eq_01 : e₆ = {0, 1} := by
      have hmem : e₆ ∈ T₃.powersetCard 2 := Finset.mem_powersetCard.mpr ⟨he₆_sub, he₆_card⟩
      have hset : T₃.powersetCard 2 = {{0, 1}, {0, 2}, {1, 2}} := by decide
      rw [hset] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact h
      · rw [← he₃_eq_02] at h; rw [h, he₃_dist] at he₆_dist; omega
      · rw [h, hd12_eq4] at he₆_dist; omega
    have hb2_0 : A.step 0 b₂ = 2 := by
      have hne1 : A.step 0 b₂ ≠ 1 := fun h =>
        (by decide : (0 : Fin 4) ≠ 1) (hb₂_bij.1 (h.trans (hfix1 b₂ hb₂_bij).symm))
      have hne0 : A.step 0 b₂ ≠ 0 := by
        intro h
        have h0mem : (0 : Fin 4) ∈ A.image ({2, 3} : Finset (Fin 4)) [b₂] := by rw [hb₂_img]; simp
        rw [DFA.mem_image] at h0mem
        rcases h0mem with ⟨p, hp, hpeq⟩
        simp only [DFA.eval_singleton] at hpeq
        have hp0 : p = 0 := hb₂_bij.1 (hpeq.trans h.symm)
        subst hp0
        exact absurd hp (by decide)
      have hne3 : A.step 0 b₂ ≠ 3 := by
        intro h
        have h3mem : (3 : Fin 4) ∈ A.image ({2, 3} : Finset (Fin 4)) [b₂] := by rw [hb₂_img]; simp
        rw [DFA.mem_image] at h3mem
        rcases h3mem with ⟨p, hp, hpeq⟩
        simp only [DFA.eval_singleton] at hpeq
        have hp0 : p = 0 := hb₂_bij.1 (hpeq.trans h.symm)
        subst hp0
        exact absurd hp (by decide)
      generalize h0v : A.step 0 b₂ = v at hne0 hne1 hne3
      fin_cases v <;> simp_all
    have himg01 : A.image ({0, 1} : Finset (Fin 4)) [b₂] = {1, 2} := by
      ext q
      simp only [DFA.mem_image, DFA.eval_singleton, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨p, rfl | rfl, rfl⟩
        · right; exact hb2_0
        · left; exact hfix1 b₂ hb₂_bij
      · rintro (rfl | rfl)
        · exact ⟨1, Or.inr rfl, hfix1 b₂ hb₂_bij⟩
        · exact ⟨0, Or.inl rfl, hb2_0⟩
    have hg01 := hgolden_dist {0, 1} b₂ (by decide) (by rw [← he₆_eq_01, he₆_dist]; omega)
    rw [himg01, hd12_eq4, ← he₆_eq_01, he₆_dist] at hg01
    omega

/-- Step 7 contradiction (`|O₃| = 4`, given `gx` of len ≤ 2 reaching `x` and `gy` of len ≤ 3 reaching `y`
where `{x, y} = {1, 2}`). -/
private theorem cerny_fin4_step7_false (A : DFA (Fin 4) α) (hSync : A.IsSynchronizing)
    (hdist_le6 : ∀ e : Finset (Fin 4), e.card = 2 → pairDist A hSync e ≤ 6)
    (hdist_inj : ∀ e₁ e₂ : Finset (Fin 4), e₁.card = 2 → e₂.card = 2 →
      pairDist A hSync e₁ = pairDist A hSync e₂ → e₁ = e₂)
    (hgolden_dist : ∀ (e : Finset (Fin 4)) (c : α), e.card = 2 → 2 ≤ pairDist A hSync e →
      pairDist A hSync e - 1 ≤ pairDist A hSync (A.image e [c]))
    (hreach_pair : ∀ (u : List α), u.length ≤ 9 → (A.image Finset.univ u).card ≤ 2 →
      (A.image Finset.univ u).card = 2 ∧ 10 ≤ u.length + pairDist A hSync (A.image Finset.univ u))
    (he1 : pairDist A hSync ({0, 3} : Finset (Fin 4)) = 1)
    (he2 : pairDist A hSync ({2, 3} : Finset (Fin 4)) = 2)
    (e₃ : Finset (Fin 4)) (he₃_card : e₃.card = 2) (he₃_dist : pairDist A hSync e₃ = 3)
    (he₃_sub : e₃ ⊆ {0, 1, 2})
    (a₀ : α) (ha₀_img : A.image Finset.univ [a₀] = {0, 1, 2})
    (hker0 : A.step 0 a₀ = A.step 3 a₀ ∧
      A.step 0 a₀ ≠ A.step 1 a₀ ∧ A.step 0 a₀ ≠ A.step 2 a₀ ∧ A.step 1 a₀ ≠ A.step 2 a₀)
    (b₃ : α) (hb₃_bij : IsBijLetter A b₃) (hb₃_img : A.image e₃ [b₃] = {2, 3})
    (hb₃_step3 : A.step 3 b₃ = 0 ∨ A.step 3 b₃ = 3)
    (x y : Fin 4) (hxy_cases : (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1))
    (gx gy : List α) (hgx_len : gx.length ≤ 2) (hgx_bij : IsBijWord A gx) (hgx_ev : A.eval 3 gx = x)
    (hgy_len : gy.length ≤ 3) (hgy_bij : IsBijWord A gy) (hgy_ev : A.eval 3 gy = y) :
    False := by
  classical
  have hT3_erase : ({0, 1, 2} : Finset (Fin 4)) = Finset.univ.erase 3 := by decide
  let Px : Finset (Fin 4) := {A.step 0 a₀, A.step y a₀}
  let Py : Finset (Fin 4) := {A.step 0 a₀, A.step x a₀}
  let Q₃ : Finset (Fin 4) := {A.step 1 a₀, A.step 2 a₀}
  have hPx_eq : A.image Finset.univ ([a₀] ++ gx ++ [a₀]) = Px := by
    rw [List.append_assoc, DFA.image_append, ha₀_img, hT3_erase, DFA.image_append,
      image_erase_of_isBijWord A hgx_bij 3, hgx_ev]
    rcases hxy_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · ext q
      simp only [Px, DFA.mem_image, DFA.eval_singleton, Finset.mem_erase, Finset.mem_univ,
        and_true, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨p, hp, rfl⟩
        fin_cases p
        · left; rfl
        · exact absurd rfl hp
        · right; rfl
        · left; exact hker0.1.symm
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨2, by decide, rfl⟩
    · ext q
      simp only [Px, DFA.mem_image, DFA.eval_singleton, Finset.mem_erase, Finset.mem_univ,
        and_true, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨p, hp, rfl⟩
        fin_cases p
        · left; rfl
        · right; rfl
        · exact absurd rfl hp
        · left; exact hker0.1.symm
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨1, by decide, rfl⟩
  have hPy_eq : A.image Finset.univ ([a₀] ++ gy ++ [a₀]) = Py := by
    rw [List.append_assoc, DFA.image_append, ha₀_img, hT3_erase, DFA.image_append,
      image_erase_of_isBijWord A hgy_bij 3, hgy_ev]
    rcases hxy_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · ext q
      simp only [Py, DFA.mem_image, DFA.eval_singleton, Finset.mem_erase, Finset.mem_univ,
        and_true, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨p, hp, rfl⟩
        fin_cases p
        · left; rfl
        · right; rfl
        · exact absurd rfl hp
        · left; exact hker0.1.symm
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨1, by decide, rfl⟩
    · ext q
      simp only [Py, DFA.mem_image, DFA.eval_singleton, Finset.mem_erase, Finset.mem_univ,
        and_true, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨p, hp, rfl⟩
        fin_cases p
        · left; rfl
        · exact absurd rfl hp
        · right; rfl
        · left; exact hker0.1.symm
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨2, by decide, rfl⟩
  have hPx_card : Px.card = 2 := by
    rcases hxy_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Finset.card_pair hker0.2.2.1
    · exact Finset.card_pair hker0.2.1
  have hPy_card : Py.card = 2 := by
    rcases hxy_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Finset.card_pair hker0.2.1
    · exact Finset.card_pair hker0.2.2.1
  have hQ₃_card : Q₃.card = 2 := Finset.card_pair hker0.2.2.2
  have hPx_ne_Py : Px ≠ Py := by
    intro heq
    rcases hxy_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hmem : A.step 2 a₀ ∈ Py := by rw [← heq]; simp [Px]
      simp only [Py, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hker0.2.2.1 h.symm
      · exact hker0.2.2.2 h.symm
    · have hmem : A.step 1 a₀ ∈ Py := by rw [← heq]; simp [Px]
      simp only [Py, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hker0.2.1 h.symm
      · exact hker0.2.2.2 h
  have hPx_dist : pairDist A hSync Px = 6 := by
    have hlen : ([a₀] ++ gx ++ [a₀]).length ≤ 4 := by simp; omega
    have hcard_le : (A.image Finset.univ ([a₀] ++ gx ++ [a₀])).card ≤ 2 := by
      rw [hPx_eq, hPx_card]
    have ⟨_, hsum⟩ := hreach_pair _ (by omega) hcard_le
    rw [hPx_eq] at hsum
    have hd6 := hdist_le6 Px hPx_card
    omega
  have hPy_dist : pairDist A hSync Py = 5 := by
    have hlen : ([a₀] ++ gy ++ [a₀]).length ≤ 5 := by simp; omega
    have hcard_le : (A.image Finset.univ ([a₀] ++ gy ++ [a₀])).card ≤ 2 := by
      rw [hPy_eq, hPy_card]
    have ⟨_, hsum⟩ := hreach_pair _ (by omega) hcard_le
    rw [hPy_eq] at hsum
    have hd6 := hdist_le6 Py hPy_card
    have hne6 : pairDist A hSync Py ≠ 6 := fun h =>
      hPx_ne_Py (hdist_inj Px Py hPx_card hPy_card (by omega))
    omega
  have hPx_sub : Px ⊆ ({0, 1, 2} : Finset (Fin 4)) := by
    rw [← hPx_eq, DFA.image_append, ← ha₀_img]
    exact A.image_mono (Finset.subset_univ _) [a₀]
  have hPy_sub : Py ⊆ ({0, 1, 2} : Finset (Fin 4)) := by
    rw [← hPy_eq, DFA.image_append, ← ha₀_img]
    exact A.image_mono (Finset.subset_univ _) [a₀]
  have hQ₃_img_12 : A.image ({1, 2} : Finset (Fin 4)) [a₀] = Q₃ := by
    ext q
    simp only [Q₃, DFA.mem_image, DFA.eval_singleton, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨p, rfl | rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨1, Or.inl rfl, rfl⟩
      · exact ⟨2, Or.inr rfl, rfl⟩
  have hQ₃_sub : Q₃ ⊆ ({0, 1, 2} : Finset (Fin 4)) := by
    rw [← hQ₃_img_12, ← ha₀_img]
    exact A.image_mono (Finset.subset_univ _) [a₀]
  have hQ₃_ne_Px : Q₃ ≠ Px := by
    intro heq
    have h0mem : A.step 0 a₀ ∈ Q₃ := by rw [heq]; simp [Px]
    simp only [Q₃, Finset.mem_insert, Finset.mem_singleton] at h0mem
    rcases h0mem with h | h
    · exact hker0.2.1 h
    · exact hker0.2.2.1 h
  have hQ₃_ne_Py : Q₃ ≠ Py := by
    intro heq
    have h0mem : A.step 0 a₀ ∈ Q₃ := by rw [heq]; simp [Py]
    simp only [Q₃, Finset.mem_insert, Finset.mem_singleton] at h0mem
    rcases h0mem with h | h
    · exact hker0.2.1 h
    · exact hker0.2.2.1 h
  have hT3_pairs : ∀ e : Finset (Fin 4), e ⊆ ({0, 1, 2} : Finset (Fin 4)) → e.card = 2 →
      e = Px ∨ e = Py ∨ e = Q₃ := by
    intro e heSub heCard
    let S3 : Finset (Finset (Fin 4)) := {Px, Py, Q₃}
    have hS3_sub : S3 ⊆ ({0, 1, 2} : Finset (Fin 4)).powersetCard 2 := by
      intro u hu
      simp only [S3, Finset.mem_insert, Finset.mem_singleton] at hu
      rw [Finset.mem_powersetCard]
      rcases hu with rfl | rfl | rfl
      · exact ⟨hPx_sub, hPx_card⟩
      · exact ⟨hPy_sub, hPy_card⟩
      · exact ⟨hQ₃_sub, hQ₃_card⟩
    have hS3_card : S3.card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hQ₃_ne_Py.symm]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hPx_ne_Py, hQ₃_ne_Px.symm⟩
    have hS3_eq : S3 = ({0, 1, 2} : Finset (Fin 4)).powersetCard 2 := by
      apply Finset.eq_of_subset_of_card_le hS3_sub
      rw [Finset.card_powersetCard, hS3_card]
      decide
    have hmem : e ∈ S3 := by
      rw [hS3_eq, Finset.mem_powersetCard]
      exact ⟨heSub, heCard⟩
    simpa [S3] using hmem
  have he₃_eq_Q₃ : e₃ = Q₃ := by
    rcases hT3_pairs e₃ he₃_sub he₃_card with rfl | rfl | h
    · omega
    · omega
    · exact h
  have h12_img : A.image ({1, 2} : Finset (Fin 4)) [a₀] = e₃ := by
    rw [he₃_eq_Q₃]
    exact hQ₃_img_12
  have h12_dist_ge2 : 2 ≤ pairDist A hSync ({1, 2} : Finset (Fin 4)) := by
    have hpos := pairDist_pos_of_card_two A hSync (by decide : ({1, 2} : Finset (Fin 4)).card = 2)
    have hne1 : pairDist A hSync ({1, 2} : Finset (Fin 4)) ≠ 1 := fun h =>
      (by decide : ({1, 2} : Finset (Fin 4)) ≠ {0, 3}) (hdist_inj _ _ (by decide) (by decide) (by omega))
    omega
  have h12_le4 : pairDist A hSync ({1, 2} : Finset (Fin 4)) ≤ 4 := by
    have hg := hgolden_dist {1, 2} a₀ (by decide) h12_dist_ge2
    rw [h12_img, he₃_dist] at hg
    omega
  have he₃_eq_12 : e₃ = {1, 2} := by
    rcases hT3_pairs {1, 2} (by decide) (by decide) with h | h | h
    · rw [h, hPx_dist] at h12_le4; omega
    · rw [h, hPy_dist] at h12_le4; omega
    · rw [he₃_eq_Q₃, h]
  have h01_ge5 : 5 ≤ pairDist A hSync ({0, 1} : Finset (Fin 4)) := by
    rcases hT3_pairs {0, 1} (by decide) (by decide) with h | h | h
    · rw [h, hPx_dist]; omega
    · rw [h, hPy_dist]
    · rw [← he₃_eq_Q₃, he₃_eq_12] at h
      exact absurd h (by decide)
  have h13_dist : pairDist A hSync ({1, 3} : Finset (Fin 4)) = 4 := by
    have hpos := pairDist_pos_of_card_two A hSync (by decide : ({1, 3} : Finset (Fin 4)).card = 2)
    have hd6 := hdist_le6 ({1, 3} : Finset (Fin 4)) (by decide)
    have hne1 : pairDist A hSync ({1, 3} : Finset (Fin 4)) ≠ 1 := fun h =>
      (by decide : ({1, 3} : Finset (Fin 4)) ≠ {0, 3}) (hdist_inj _ _ (by decide) (by decide) (by omega))
    have hne2 : pairDist A hSync ({1, 3} : Finset (Fin 4)) ≠ 2 := fun h =>
      (by decide : ({1, 3} : Finset (Fin 4)) ≠ {2, 3}) (hdist_inj _ _ (by decide) (by decide) (by omega))
    have hne3 : pairDist A hSync ({1, 3} : Finset (Fin 4)) ≠ 3 := fun h =>
      (by decide : ({1, 3} : Finset (Fin 4)) ≠ {1, 2}) (by
        rw [← he₃_eq_12]; exact hdist_inj _ _ (by decide) he₃_card (by omega))
    have hne5 : pairDist A hSync ({1, 3} : Finset (Fin 4)) ≠ 5 := fun h => by
      have heq : ({1, 3} : Finset (Fin 4)) = Py := hdist_inj _ _ (by decide) hPy_card (by omega)
      have h3 : (3 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4)) := hPy_sub (by rw [← heq]; simp)
      exact (by decide : (3 : Fin 4) ∉ ({0, 1, 2} : Finset (Fin 4))) h3
    have hne6 : pairDist A hSync ({1, 3} : Finset (Fin 4)) ≠ 6 := fun h => by
      have heq : ({1, 3} : Finset (Fin 4)) = Px := hdist_inj _ _ (by decide) hPx_card (by omega)
      have h3 : (3 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4)) := hPx_sub (by rw [← heq]; simp)
      exact (by decide : (3 : Fin 4) ∉ ({0, 1, 2} : Finset (Fin 4))) h3
    omega
  rw [he₃_eq_12] at hb₃_img
  have hb3_1_in : A.step 1 b₃ ∈ ({2, 3} : Finset (Fin 4)) := by
    rw [← hb₃_img, DFA.mem_image]
    exact ⟨1, by simp, rfl⟩
  have hb3_3 : A.step 3 b₃ = 0 := by
    rcases hb₃_step3 with h0 | h3
    · exact h0
    · exfalso
      have h3mem : (3 : Fin 4) ∈ A.image ({1, 2} : Finset (Fin 4)) [b₃] := by rw [hb₃_img]; simp
      rw [DFA.mem_image] at h3mem
      rcases h3mem with ⟨p, hp, hpeq⟩
      simp only [DFA.eval_singleton] at hpeq
      have hp3 : p = 3 := hb₃_bij.1 (hpeq.trans h3.symm)
      subst hp3
      exact absurd hp (by decide)
  have hb3_0 : A.step 0 b₃ = 1 := by
    have hne0 : A.step 0 b₃ ≠ 0 := fun h =>
      (by decide : (0 : Fin 4) ≠ 3) (hb₃_bij.1 (h.trans hb3_3.symm))
    have hne2 : A.step 0 b₃ ≠ 2 := by
      intro h
      have h2mem : (2 : Fin 4) ∈ A.image ({1, 2} : Finset (Fin 4)) [b₃] := by rw [hb₃_img]; simp
      rw [DFA.mem_image] at h2mem
      rcases h2mem with ⟨p, hp, hpeq⟩
      simp only [DFA.eval_singleton] at hpeq
      have hp0 : p = 0 := hb₃_bij.1 (hpeq.trans h.symm)
      subst hp0
      exact absurd hp (by decide)
    have hne3 : A.step 0 b₃ ≠ 3 := by
      intro h
      have h3mem : (3 : Fin 4) ∈ A.image ({1, 2} : Finset (Fin 4)) [b₃] := by rw [hb₃_img]; simp
      rw [DFA.mem_image] at h3mem
      rcases h3mem with ⟨p, hp, hpeq⟩
      simp only [DFA.eval_singleton] at hpeq
      have hp0 : p = 0 := hb₃_bij.1 (hpeq.trans h.symm)
      subst hp0
      exact absurd hp (by decide)
    generalize h0v : A.step 0 b₃ = v at hne0 hne2 hne3
    fin_cases v <;> simp_all
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb3_1_in
  rcases hb3_1_in with hb3_1 | hb3_1
  · have himg01 : A.image ({0, 1} : Finset (Fin 4)) [b₃] = {1, 2} := by
      ext q
      simp only [DFA.mem_image, DFA.eval_singleton, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨p, rfl | rfl, rfl⟩
        · left; exact hb3_0
        · right; exact hb3_1
      · rintro (rfl | rfl)
        · exact ⟨0, Or.inl rfl, hb3_0⟩
        · exact ⟨1, Or.inr rfl, hb3_1⟩
    have hg := hgolden_dist {0, 1} b₃ (by decide) (by omega)
    rw [himg01, ← he₃_eq_12, he₃_dist] at hg
    omega
  · have himg13 : A.image ({1, 3} : Finset (Fin 4)) [b₃] = {0, 3} := by
      ext q
      simp only [DFA.mem_image, DFA.eval_singleton, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨p, rfl | rfl, rfl⟩
        · right; exact hb3_1
        · left; exact hb3_3
      · rintro (rfl | rfl)
        · exact ⟨3, Or.inr rfl, hb3_3⟩
        · exact ⟨1, Or.inl rfl, hb3_1⟩
    have hg := hgolden_dist {1, 3} b₃ (by decide) (by omega)
    rw [himg13, he1] at hg
    omega

/-- Normalized contradiction for `n = 4` (Steps 1–5 dispatching to Step 6 and Step 7). -/
private theorem cerny_fin4_normalized_false (A : DFA (Fin 4) α) (hSync : A.IsSynchronizing)
    (hlong : ∀ w : List α, A.IsSyncWord w → 10 ≤ w.length)
    (hdist_le6 : ∀ e : Finset (Fin 4), e.card = 2 → pairDist A hSync e ≤ 6)
    (hdist_inj : ∀ e₁ e₂ : Finset (Fin 4), e₁.card = 2 → e₂.card = 2 →
      pairDist A hSync e₁ = pairDist A hSync e₂ → e₁ = e₂)
    (hdist_surj : ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
      ∃ e : Finset (Fin 4), e.card = 2 ∧ pairDist A hSync e = k)
    (he1 : pairDist A hSync ({0, 3} : Finset (Fin 4)) = 1)
    (he2 : pairDist A hSync ({2, 3} : Finset (Fin 4)) = 2) :
    False := by
  classical
  have hrank_ge3 : ∀ c : α, 3 ≤ (A.image Finset.univ [c]).card := by
    intro c
    by_contra hlt
    have hne : (A.image Finset.univ [c]).Nonempty :=
      ⟨A.step 0 c, by rw [DFA.mem_image]; exact ⟨0, Finset.mem_univ _, rfl⟩⟩
    have hpos : 1 ≤ (A.image Finset.univ [c]).card := Finset.card_pos.mpr hne
    by_cases h1 : (A.image Finset.univ [c]).card = 1
    · have := hlong [c] ((A.isSyncWord_iff_card_image_univ_eq_one [c]).mpr h1)
      simp at this
    · have h2 : (A.image Finset.univ [c]).card = 2 := by omega
      obtain ⟨v, hvlen, hv⟩ := pairDist_spec A hSync hne
      have hd := hdist_le6 _ h2
      have hsync' : A.IsSyncWord (c :: v) := by
        rw [A.isSyncWord_iff_card_image_univ_eq_one, A.image_cons]
        exact hv
      have := hlong (c :: v) hsync'
      simp only [List.length_cons] at this
      omega
  have hrank_or : ∀ c : α, IsBijLetter A c ∨ (A.image Finset.univ [c]).card = 3 := by
    intro c
    have hle4 : (A.image Finset.univ [c]).card ≤ 4 := by
      calc (A.image Finset.univ [c]).card ≤ (Finset.univ : Finset (Fin 4)).card := A.card_image_le _ _
        _ = 4 := by simp
    have hge3 := hrank_ge3 c
    by_cases h4 : (A.image Finset.univ [c]).card = 4
    · left
      have hinj : Function.Injective (fun q : Fin 4 => A.step q c) := by
        by_contra hni
        unfold Function.Injective at hni
        push Not at hni
        rcases hni with ⟨x, y, hxy, hne⟩
        have hlt := card_image_lt_of_merge A [c] (Finset.mem_univ x) (Finset.mem_univ y) hne hxy
        simp at hlt
        omega
      exact Finite.injective_iff_bijective.mp hinj
    · right
      omega
  have hgolden_card : ∀ (e : Finset (Fin 4)) (c : α), e.card = 2 → 2 ≤ pairDist A hSync e →
      (A.image e [c]).card = 2 := by
    intro e c he hd
    have hle : (A.image e [c]).card ≤ 2 := le_trans (A.card_image_le e [c]) he.le
    have hne : e.Nonempty := Finset.card_pos.mp (by omega)
    have hne' : (A.image e [c]).Nonempty := by
      rcases hne with ⟨p, hp⟩
      exact ⟨A.step p c, by rw [DFA.mem_image]; exact ⟨p, hp, rfl⟩⟩
    have hpos : 1 ≤ (A.image e [c]).card := Finset.card_pos.mpr hne'
    by_contra hne2
    have h1 : (A.image e [c]).card = 1 := by omega
    have := pairDist_le_of_merge A hSync hne h1
    simp at this
    omega
  have hgolden_dist : ∀ (e : Finset (Fin 4)) (c : α), e.card = 2 → 2 ≤ pairDist A hSync e →
      pairDist A hSync e - 1 ≤ pairDist A hSync (A.image e [c]) := by
    intro e c he hd
    have hne : e.Nonempty := Finset.card_pos.mp (by omega)
    have hcard' := hgolden_card e c he hd
    have hne' : (A.image e [c]).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hvlen, hv⟩ := pairDist_spec A hSync hne'
    have hmerge : (A.image e (c :: v)).card = 1 := by
      rw [DFA.image_cons]
      exact hv
    have hle := pairDist_le_of_merge A hSync hne hmerge
    simp only [List.length_cons] at hle
    omega
  have hreach_pair : ∀ (u : List α), u.length ≤ 9 → (A.image Finset.univ u).card ≤ 2 →
      (A.image Finset.univ u).card = 2 ∧ 10 ≤ u.length + pairDist A hSync (A.image Finset.univ u) := by
    intro u hulen hle
    have hne : (A.image Finset.univ u).Nonempty :=
      ⟨A.eval 0 u, by rw [DFA.mem_image]; exact ⟨0, Finset.mem_univ _, rfl⟩⟩
    have hpos : 1 ≤ (A.image Finset.univ u).card := Finset.card_pos.mpr hne
    by_cases h1 : (A.image Finset.univ u).card = 1
    · exfalso
      have h10 := hlong u ((A.isSyncWord_iff_card_image_univ_eq_one u).mpr h1)
      omega
    · have h2 : (A.image Finset.univ u).card = 2 := by omega
      refine ⟨h2, ?_⟩
      obtain ⟨v, hvlen, hv⟩ := pairDist_spec A hSync hne
      have hsync' : A.IsSyncWord (u ++ v) := by
        rw [A.isSyncWord_iff_card_image_univ_eq_one, A.image_append]
        exact hv
      have h10 := hlong (u ++ v) hsync'
      rw [List.length_append, hvlen] at h10
      exact h10
  let T₃ : Finset (Fin 4) := {0, 1, 2}
  have hT3_erase : T₃ = Finset.univ.erase 3 := by decide
  have hT3_of_rank3 : ∀ a : α, (A.image Finset.univ [a]).card = 3 →
      A.image Finset.univ [a] = T₃ := by
    intro a ha
    have hnot1 : ¬ ({0, 3} : Finset (Fin 4)) ⊆ A.image Finset.univ [a] := by
      intro hsub
      obtain ⟨v, hvlen, hv⟩ := pairDist_spec A hSync (⟨0, by simp⟩ : ({0, 3} : Finset (Fin 4)).Nonempty)
      rw [he1] at hvlen
      have hmerge : A.eval 0 v = A.eval 3 v := (card_image_eq_one_iff_pair A v).mp hv
      have hlt : (A.image (A.image Finset.univ [a]) v).card < (A.image Finset.univ [a]).card :=
        card_image_lt_of_merge A v (hsub (by simp)) (hsub (by simp)) (by decide) hmerge
      rw [← DFA.image_cons, ha] at hlt
      have hlen : (a :: v).length ≤ 9 := by simp [hvlen]
      have ⟨hcard2, hsum⟩ := hreach_pair (a :: v) hlen (by omega)
      have hd6 := hdist_le6 _ hcard2
      simp only [List.length_cons, hvlen] at hsum
      omega
    have hnot2 : ¬ ({2, 3} : Finset (Fin 4)) ⊆ A.image Finset.univ [a] := by
      intro hsub
      obtain ⟨v, hvlen, hv⟩ := pairDist_spec A hSync (⟨2, by simp⟩ : ({2, 3} : Finset (Fin 4)).Nonempty)
      rw [he2] at hvlen
      have hmerge : A.eval 2 v = A.eval 3 v := (card_image_eq_one_iff_pair A v).mp hv
      have hlt : (A.image (A.image Finset.univ [a]) v).card < (A.image Finset.univ [a]).card :=
        card_image_lt_of_merge A v (hsub (by simp)) (hsub (by simp)) (by decide) hmerge
      rw [← DFA.image_cons, ha] at hlt
      have hlen : (a :: v).length ≤ 9 := by simp [hvlen]
      have ⟨hcard2, hsum⟩ := hreach_pair (a :: v) hlen (by omega)
      have hd6 := hdist_le6 _ hcard2
      simp only [List.length_cons, hvlen] at hsum
      omega
    have hsdiff : (Finset.univ \ A.image Finset.univ [a]).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, ha]
    rw [Finset.card_eq_one] at hsdiff
    rcases hsdiff with ⟨x, hx⟩
    have hTa : A.image Finset.univ [a] = Finset.univ.erase x := by
      ext q
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hq hqx
        subst hqx
        have hmem : q ∈ Finset.univ \ A.image Finset.univ [a] := by rw [hx]; simp
        exact (Finset.mem_sdiff.mp hmem).2 hq
      · intro hne
        by_contra hnot
        have hmem : q ∈ Finset.univ \ A.image Finset.univ [a] :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hnot⟩
        rw [hx, Finset.mem_singleton] at hmem
        exact hne hmem
    rw [hTa] at hnot1 hnot2 ⊢
    fin_cases x
    · exact absurd (by decide : ({2, 3} : Finset (Fin 4)) ⊆ Finset.univ.erase 0) hnot2
    · exact absurd (by decide : ({0, 3} : Finset (Fin 4)) ⊆ Finset.univ.erase 1) hnot1
    · exact absurd (by decide : ({0, 3} : Finset (Fin 4)) ⊆ Finset.univ.erase 2) hnot1
    · exact hT3_erase.symm
  have hker_of_rank3 : ∀ a : α, (A.image Finset.univ [a]).card = 3 →
      A.step 0 a = A.step 3 a ∧
      A.step 0 a ≠ A.step 1 a ∧ A.step 0 a ≠ A.step 2 a ∧ A.step 1 a ≠ A.step 2 a := by
    intro a ha
    have hmerge_eq : ∀ p q : Fin 4, p ≠ q → A.step p a = A.step q a →
        ({p, q} : Finset (Fin 4)) = {0, 3} := by
      intro p q hpq hstep
      have hcard2 : ({p, q} : Finset (Fin 4)).card = 2 := Finset.card_pair hpq
      have h1 : (A.image {p, q} [a]).card = 1 := (card_image_eq_one_iff_pair A [a]).mpr hstep
      have hle : pairDist A hSync {p, q} ≤ 1 := pairDist_le_of_merge A hSync ⟨p, by simp⟩ h1
      have hge : 1 ≤ pairDist A hSync {p, q} := pairDist_pos_of_card_two A hSync hcard2
      exact hdist_inj _ _ hcard2 (by decide) (by omega)
    have hlt : (A.image Finset.univ [a]).card < (Finset.univ : Finset (Fin 4)).card := by
      rw [ha]; simp
    obtain ⟨p, _, q, _, hpq, hstep⟩ := exists_merge_of_card_image_lt A hlt
    have heq03 := hmerge_eq p q hpq hstep
    have h03 : A.step 0 a = A.step 3 a := by
      have h0 : (0 : Fin 4) ∈ ({p, q} : Finset (Fin 4)) := by rw [heq03]; simp
      have h3 : (3 : Fin 4) ∈ ({p, q} : Finset (Fin 4)) := by rw [heq03]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h3
      rcases h0 with rfl | rfl <;> rcases h3 with h3' | h3'
      · exact absurd h3' (by decide)
      · rw [h3']; exact hstep
      · rw [h3']; exact hstep.symm
      · exact absurd h3' (by decide)
    refine ⟨h03, ?_, ?_, ?_⟩
    · intro h; exact absurd (hmerge_eq 0 1 (by decide) h) (by decide)
    · intro h; exact absurd (hmerge_eq 0 2 (by decide) h) (by decide)
    · intro h; exact absurd (hmerge_eq 1 2 (by decide) h) (by decide)
  obtain ⟨a₀, ha₀_ni⟩ := exists_non_injective_letter A hSync (by simp)
  have ha₀ : (A.image Finset.univ [a₀]).card = 3 := by
    rcases hrank_or a₀ with hbij | h3
    · exact absurd hbij.1 ha₀_ni
    · exact h3
  have ha₀_img : A.image Finset.univ [a₀] = T₃ := hT3_of_rank3 a₀ ha₀
  obtain ⟨e₃, he₃_card, he₃_dist⟩ := hdist_surj 3 (by omega) (by omega)
  obtain ⟨e₄, he₄_card, he₄_dist⟩ := hdist_surj 4 (by omega) (by omega)
  obtain ⟨e₆, he₆_card, he₆_dist⟩ := hdist_surj 6 (by omega) (by omega)
  obtain ⟨w₃, hw₃_len, hw₃_comp, hw₃_min⟩ := compress_three_fin4 A hSync T₃ (by decide)
  have he₃_sub : e₃ ⊆ T₃ := by
    have hlt : (A.image T₃ w₃).card < T₃.card := by simpa [T₃] using hw₃_comp
    obtain ⟨x, hx, y, hy, hxy, hmerge⟩ := exists_merge_of_card_image_lt A hlt
    have hsub : ({x, y} : Finset (Fin 4)) ⊆ T₃ := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption
    have hcard2 : ({x, y} : Finset (Fin 4)).card = 2 := Finset.card_pair hxy
    have hdist_le : pairDist A hSync {x, y} ≤ 3 := by
      have h1 : (A.image {x, y} w₃).card = 1 := (card_image_eq_one_iff_pair A w₃).mpr hmerge
      exact le_trans (pairDist_le_of_merge A hSync ⟨x, by simp⟩ h1) hw₃_len
    have hnot3 : (3 : Fin 4) ∉ ({x, y} : Finset (Fin 4)) := fun h3 =>
      (by decide : (3 : Fin 4) ∉ T₃) (hsub h3)
    have hne1 : ({x, y} : Finset (Fin 4)) ≠ {0, 3} := fun h => hnot3 (by rw [h]; simp)
    have hne2 : ({x, y} : Finset (Fin 4)) ≠ {2, 3} := fun h => hnot3 (by rw [h]; simp)
    have hpos := pairDist_pos_of_card_two A hSync hcard2
    have hne_d1 : pairDist A hSync {x, y} ≠ 1 := fun h => hne1 (hdist_inj _ _ hcard2 (by decide) (by omega))
    have hne_d2 : pairDist A hSync {x, y} ≠ 2 := fun h => hne2 (hdist_inj _ _ hcard2 (by decide) (by omega))
    have heq : e₃ = {x, y} := hdist_inj _ _ he₃_card hcard2 (by omega)
    rw [heq]
    exact hsub
  have he₆_sub : e₆ ⊆ T₃ := by
    have hw₃_ne : w₃ ≠ [] := by
      intro hnil
      rw [hnil, DFA.image_nil] at hw₃_comp
      exact absurd hw₃_comp (by decide)
    let w' := w₃.dropLast
    let c := w₃.getLast hw₃_ne
    have hw₃_eq : w' ++ [c] = w₃ := List.dropLast_append_getLast hw₃_ne
    have hc_rank3 : (A.image Finset.univ [c]).card = 3 := by
      rcases hrank_or c with hbij | h3
      · exfalso
        have hprev_card : (A.image T₃ w').card = 3 := by
          have hle : (A.image T₃ w').card ≤ 3 := le_trans (A.card_image_le T₃ w') (by decide)
          have hnotlt : ¬ (A.image T₃ w').card < 3 := by
            intro hlt
            have := hw₃_min w' hlt
            have hlen' : w'.length = w₃.length - 1 := List.length_dropLast
            have hpos_w3 : 1 ≤ w₃.length := List.length_pos_of_ne_nil hw₃_ne
            omega
          omega
        have hinj : Set.InjOn (fun q => A.eval q [c]) (A.image T₃ w') := fun x _ y _ h => hbij.1 h
        have heq : (A.image T₃ w₃).card = 3 := by
          rw [← hw₃_eq, DFA.image_append, DFA.image, Finset.card_image_of_injOn hinj, hprev_card]
        omega
      · exact h3
    have hsub : A.image Finset.univ (a₀ :: w₃) ⊆ T₃ := by
      rw [DFA.image_cons, ha₀_img, ← hw₃_eq, DFA.image_append, ← hT3_of_rank3 c hc_rank3]
      exact A.image_mono (Finset.subset_univ _) [c]
    have hcard_le2 : (A.image Finset.univ (a₀ :: w₃)).card ≤ 2 := by
      rw [DFA.image_cons, ha₀_img]
      omega
    have hlen_le4 : (a₀ :: w₃).length ≤ 4 := by simp only [List.length_cons]; omega
    have ⟨hcard2, hsum⟩ := hreach_pair (a₀ :: w₃) (by omega) hcard_le2
    have hd6 := hdist_le6 _ hcard2
    have heq : e₆ = A.image Finset.univ (a₀ :: w₃) := hdist_inj _ _ he₆_card hcard2 (by omega)
    rw [heq]
    exact hsub
  have hbij_of_mem_three : ∀ (S : Finset (Fin 4)) (c : α),
      (3 : Fin 4) ∈ A.image S [c] → IsBijLetter A c := by
    intro S c h3
    rcases hrank_or c with hbij | hrank3
    · exact hbij
    · exfalso
      have hsub : A.image S [c] ⊆ T₃ := by
        rw [← hT3_of_rank3 c hrank3]
        exact A.image_mono (Finset.subset_univ S) [c]
      exact (by decide : (3 : Fin 4) ∉ T₃) (hsub h3)
  have hb₂_ex : ∃ b₂ : α, IsBijLetter A b₂ ∧ A.image ({2, 3} : Finset (Fin 4)) [b₂] = {0, 3} := by
    obtain ⟨w, hwlen, hw⟩ := pairDist_spec A hSync (⟨2, by simp⟩ : ({2, 3} : Finset (Fin 4)).Nonempty)
    rw [he2] at hwlen
    cases w with
    | nil => simp at hwlen
    | cons b rest =>
      have hcard2 := hgolden_card {2, 3} b (by decide) (by omega)
      have hne : (A.image ({2, 3} : Finset (Fin 4)) [b]).Nonempty := Finset.card_pos.mp (by omega)
      have hmerge : (A.image (A.image ({2, 3} : Finset (Fin 4)) [b]) rest).card = 1 := by
        rw [← DFA.image_cons]; exact hw
      have hle : pairDist A hSync (A.image ({2, 3} : Finset (Fin 4)) [b]) ≤ 1 := by
        have := pairDist_le_of_merge A hSync hne hmerge
        simp only [List.length_cons] at hwlen
        omega
      have hge : 1 ≤ pairDist A hSync (A.image ({2, 3} : Finset (Fin 4)) [b]) :=
        pairDist_pos_of_card_two A hSync hcard2
      have himg : A.image ({2, 3} : Finset (Fin 4)) [b] = {0, 3} :=
        hdist_inj _ _ hcard2 (by decide) (by omega)
      refine ⟨b, hbij_of_mem_three {2, 3} b (by rw [himg]; simp), himg⟩
  obtain ⟨b₂, hb₂_bij, hb₂_img⟩ := hb₂_ex
  have hb₃_ex : ∃ b₃ : α, IsBijLetter A b₃ ∧ A.image e₃ [b₃] = {2, 3} := by
    have he₃_ne : e₃.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨w, hwlen, hw⟩ := pairDist_spec A hSync he₃_ne
    rw [he₃_dist] at hwlen
    cases w with
    | nil => simp at hwlen
    | cons b rest =>
      have hcard2 := hgolden_card e₃ b he₃_card (by omega)
      have hne : (A.image e₃ [b]).Nonempty := Finset.card_pos.mp (by omega)
      have hmerge : (A.image (A.image e₃ [b]) rest).card = 1 := by
        rw [← DFA.image_cons]; exact hw
      have hle : pairDist A hSync (A.image e₃ [b]) ≤ 2 := by
        have := pairDist_le_of_merge A hSync hne hmerge
        simp only [List.length_cons] at hwlen
        omega
      have hge := hgolden_dist e₃ b he₃_card (by omega)
      have himg : A.image e₃ [b] = {2, 3} := hdist_inj _ _ hcard2 (by decide) (by omega)
      refine ⟨b, hbij_of_mem_three e₃ b (by rw [himg]; simp), himg⟩
  obtain ⟨b₃, hb₃_bij, hb₃_img⟩ := hb₃_ex
  have hb_step3 : ∀ b : α, IsBijLetter A b → A.step 3 b = 0 ∨ A.step 3 b = 3 := by
    intro b hb
    by_contra hnot
    push Not at hnot
    have h0_mem : (0 : Fin 4) ∈ Finset.univ.erase (A.step 3 b) :=
      Finset.mem_erase.mpr ⟨Ne.symm hnot.1, Finset.mem_univ _⟩
    have h3_mem : (3 : Fin 4) ∈ Finset.univ.erase (A.step 3 b) :=
      Finset.mem_erase.mpr ⟨Ne.symm hnot.2, Finset.mem_univ _⟩
    have himg_eq : A.image Finset.univ [a₀, b, a₀] =
        A.image (Finset.univ.erase (A.step 3 b)) [a₀] := by
      rw [DFA.image_cons, ha₀_img, hT3_erase, DFA.image_cons,
        image_erase_of_isBijLetter A hb 3]
    have hlt : (A.image Finset.univ [a₀, b, a₀]).card < (Finset.univ.erase (A.step 3 b)).card := by
      rw [himg_eq]
      exact card_image_lt_of_merge A [a₀] h0_mem h3_mem (by decide) (hker_of_rank3 a₀ ha₀).1
    have hcard_erase : (Finset.univ.erase (A.step 3 b)).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have ⟨hcard2, hsum⟩ := hreach_pair [a₀, b, a₀] (by simp) (by omega)
    have hd6 := hdist_le6 _ hcard2
    simp only [List.length_cons, List.length_nil] at hsum
    omega
  let O₃ : Finset (Fin 4) := Finset.univ.filter (fun q => ∃ g : List α, IsBijWord A g ∧ A.eval 3 g = q)
  let L : ℕ → Finset (Fin 4) := fun k =>
    Finset.univ.filter (fun q => ∃ g : List α, g.length ≤ k ∧ IsBijWord A g ∧ A.eval 3 g = q)
  have h3_O3 : (3 : Fin 4) ∈ O₃ := by
    simp only [O₃, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨[], fun _ h => by simp at h, rfl⟩
  have hO3_closed : ∀ q ∈ O₃, ∀ b : α, IsBijLetter A b → A.step q b ∈ O₃ := by
    intro q hq b hb
    simp only [O₃, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rcases hq with ⟨g, hg, rfl⟩
    refine ⟨g ++ [b], ?_, by simp⟩
    intro c hc
    rw [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hg c hc
    · exact hb
  have hL_sub_O3 : ∀ k, L k ⊆ O₃ := by
    intro k q hq
    simp only [L, O₃, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rcases hq with ⟨g, _, hg, hev⟩
    exact ⟨g, hg, hev⟩
  have hL_mono : ∀ {j k}, j ≤ k → L j ⊆ L k := by
    intro j k hjk q hq
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rcases hq with ⟨g, hglen, hg, hev⟩
    exact ⟨g, le_trans hglen hjk, hg, hev⟩
  have hL0 : L 0 = {3} := by
    ext q
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨g, hglen, _, rfl⟩
      have hnil : g = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [hnil]
    · rintro rfl
      exact ⟨[], by simp, fun _ h => by simp at h, rfl⟩
  have hL1_sub : L 1 ⊆ {0, 3} := by
    intro q hq
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rcases hq with ⟨g, hglen, hg, rfl⟩
    cases g with
    | nil => simp
    | cons b rest =>
      simp only [List.length_cons] at hglen
      have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      simp only [DFA.eval_singleton, Finset.mem_insert, Finset.mem_singleton]
      exact hb_step3 b (hg b List.mem_cons_self)
  have hL_grow : ∀ k : ℕ, (∃ q ∈ O₃, q ∉ L k) → (L k).card + 1 ≤ (L (k + 1)).card := by
    intro k ⟨q, hqO, hqNot⟩
    simp only [O₃, Finset.mem_filter, Finset.mem_univ, true_and] at hqO
    have hex : ∃ m : ℕ, ∃ g : List α, g.length = m ∧ IsBijWord A g ∧ A.eval 3 g = q := by
      rcases hqO with ⟨g, hg, hev⟩
      exact ⟨g.length, g, rfl, hg, hev⟩
    obtain ⟨g, hglen, hg, hgev⟩ := Nat.find_spec hex
    have hgt : k < g.length := by
      by_contra hle
      push Not at hle
      exact hqNot (by
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨g, hle, hg, hgev⟩)
    let g₁ := g.take (k + 1)
    let g₂ := g.drop (k + 1)
    let q' := A.eval 3 g₁
    have hg₁_bij : IsBijWord A g₁ := fun c hc => hg c (List.mem_of_mem_take hc)
    have hg₂_bij : IsBijWord A g₂ := fun c hc => hg c (List.mem_of_mem_drop hc)
    have hq'_mem : q' ∈ L (k + 1) := by
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨g₁, by simp [g₁], hg₁_bij, rfl⟩
    have hq'_not : q' ∉ L k := by
      intro hmem
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rcases hmem with ⟨h, hhlen, hhbij, hhev⟩
      have hcomb_bij : IsBijWord A (h ++ g₂) := by
        intro c hc
        rw [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hhbij c hc
        · exact hg₂_bij c hc
      have hcomb_ev : A.eval 3 (h ++ g₂) = q := by
        rw [DFA.eval_append, hhev]
        dsimp [q', g₁, g₂]
        rw [← DFA.eval_append, List.take_append_drop]
        exact hgev
      have hmin := Nat.find_min' hex ⟨h ++ g₂, rfl, hcomb_bij, hcomb_ev⟩
      simp only [List.length_append, g₂, List.length_drop] at hmin
      omega
    have hssub : L k ⊂ L (k + 1) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hL_mono (by omega), fun heq => by
        rw [← heq] at hq'_mem
        exact hq'_not hq'_mem⟩
    exact Finset.card_lt_card hssub
  have h12_O3 : (1 : Fin 4) ∈ O₃ ∨ (2 : Fin 4) ∈ O₃ := by
    by_contra hnot
    push Not at hnot
    have hO3_sub : ∀ x ∈ O₃, x = 0 ∨ x = 3 := by
      intro x hx
      fin_cases x
      · left; rfl
      · exact absurd hx hnot.1
      · exact absurd hx hnot.2
      · right; rfl
    have hinv : ∀ (w : List α) (x : Fin 4), x ∈ O₃ →
        ∃ y ∈ O₃, A.image (Finset.univ.erase x) w = Finset.univ.erase y := by
      intro w
      induction w with
      | nil =>
        intro x hx
        exact ⟨x, hx, by simp⟩
      | cons c w ih =>
        intro x hx
        rw [DFA.image_cons]
        rcases hrank_or c with hbij | hrank3
        · rw [image_erase_of_isBijLetter A hbij x]
          exact ih (A.step x c) (hO3_closed x hx c hbij)
        · have himg3 : A.image (Finset.univ.erase x) [c] = Finset.univ.erase 3 := by
            have hsub : A.image (Finset.univ.erase x) [c] ⊆ Finset.univ.erase 3 := by
              rw [← hT3_erase, ← hT3_of_rank3 c hrank3]
              exact A.image_mono (Finset.subset_univ _) [c]
            apply Finset.eq_of_subset_of_card_le hsub
            have hker := hker_of_rank3 c hrank3
            have hinj : Set.InjOn (fun q => A.eval q [c]) (Finset.univ.erase x) :=
              fin4_injOn_erase_of_ker (fun q => A.step q c)
                hker.1 hker.2.1 hker.2.2.1 hker.2.2.2 (hO3_sub x hx)
            rw [DFA.image, Finset.card_image_of_injOn hinj,
              Finset.card_erase_of_mem (Finset.mem_univ x),
              Finset.card_erase_of_mem (Finset.mem_univ 3)]
          rw [himg3]
          exact ih 3 h3_O3
    rcases hSync with ⟨w, hw⟩
    have hsync2 : A.IsSyncWord (a₀ :: w) := A.isSyncWord_append_left [a₀] hw
    have hcard1 : (A.image (Finset.univ.erase 3) w).card = 1 := by
      rw [← hT3_erase, ← ha₀_img, ← DFA.image_cons]
      exact (A.isSyncWord_iff_card_image_univ_eq_one (a₀ :: w)).mp hsync2
    obtain ⟨y, _, hy⟩ := hinv w 3 h3_O3
    rw [hy, Finset.card_erase_of_mem (Finset.mem_univ y), Finset.card_univ, Fintype.card_fin] at hcard1
    omega
  have hL1_eq : L 1 = {0, 3} := by
    have hne : ∃ q ∈ O₃, q ∉ L 0 := by
      rw [hL0]
      rcases h12_O3 with h1 | h2
      · exact ⟨1, h1, by decide⟩
      · exact ⟨2, h2, by decide⟩
    have hgrow : (L 0).card + 1 ≤ (L 1).card := hL_grow 0 hne
    rw [hL0] at hgrow
    apply Finset.eq_of_subset_of_card_le hL1_sub
    have : ({0, 3} : Finset (Fin 4)).card = 2 := by decide
    simp at hgrow
    omega
  have h0_O3 : (0 : Fin 4) ∈ O₃ := hL_sub_O3 1 (by rw [hL1_eq]; simp)
  by_cases hall12 : (1 : Fin 4) ∈ O₃ ∧ (2 : Fin 4) ∈ O₃
  · -- Dispatch to Step 7
    have hL2_card : 3 ≤ (L 2).card := by
      have hne : ∃ q ∈ O₃, q ∉ L 1 := ⟨1, hall12.1, by rw [hL1_eq]; decide⟩
      have hgrow : (L 1).card + 1 ≤ (L 2).card := hL_grow 1 hne
      rw [hL1_eq] at hgrow
      have : ({0, 3} : Finset (Fin 4)).card = 2 := by decide
      omega
    have hL3_univ : L 3 = Finset.univ := by
      by_cases hfull2 : L 2 = Finset.univ
      · exact Finset.eq_univ_iff_forall.mpr fun q =>
          hL_mono (by omega : 2 ≤ 3) (by rw [hfull2]; exact Finset.mem_univ q)
      · have hne : ∃ q ∈ O₃, q ∉ L 2 := by
          have hssub : L 2 ⊂ Finset.univ :=
            Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hfull2⟩
          obtain ⟨q, _, hqNot⟩ := Finset.exists_of_ssubset hssub
          refine ⟨q, ?_, hqNot⟩
          fin_cases q
          · exact h0_O3
          · exact hall12.1
          · exact hall12.2
          · exact h3_O3
        have hgrow : (L 2).card + 1 ≤ (L 3).card := hL_grow 2 hne
        apply Finset.eq_univ_of_card
        have hle : (L 3).card ≤ 4 := by
          simpa using Finset.card_le_univ (L 3)
        rw [Fintype.card_fin]
        omega
    have hxy_ex : ∃ x y : Fin 4, ((x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1)) ∧ x ∈ L 2 ∧ y ∈ L 3 := by
      by_cases h1L2 : (1 : Fin 4) ∈ L 2
      · exact ⟨1, 2, Or.inl ⟨rfl, rfl⟩, h1L2, by rw [hL3_univ]; exact Finset.mem_univ _⟩
      · have h2L2 : (2 : Fin 4) ∈ L 2 := by
          by_contra h2not
          have hsub : L 2 ⊆ {0, 3} := by
            intro q hq
            fin_cases q
            · simp
            · exact absurd hq h1L2
            · exact absurd hq h2not
            · simp
          have := Finset.card_le_card hsub
          have : ({0, 3} : Finset (Fin 4)).card = 2 := by decide
          omega
        exact ⟨2, 1, Or.inr ⟨rfl, rfl⟩, h2L2, by rw [hL3_univ]; exact Finset.mem_univ _⟩
    obtain ⟨x, y, hxy_cases, hxL2, hyL3⟩ := hxy_ex
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hxL2 hyL3
    obtain ⟨gx, hgx_len, hgx_bij, hgx_ev⟩ := hxL2
    obtain ⟨gy, hgy_len, hgy_bij, hgy_ev⟩ := hyL3
    exact cerny_fin4_step7_false A hSync hdist_le6 hdist_inj hgolden_dist hreach_pair
      he1 he2 e₃ he₃_card he₃_dist he₃_sub a₀ ha₀_img (hker_of_rank3 a₀ ha₀)
      b₃ hb₃_bij hb₃_img (hb_step3 b₃ hb₃_bij) x y hxy_cases gx gy hgx_len hgx_bij hgx_ev
      hgy_len hgy_bij hgy_ev
  · -- Dispatch to Step 6
    have hfix_out : ∀ y : Fin 4, y ∉ O₃ → (∀ q : Fin 4, q ≠ y → q ∈ O₃) →
        ∀ b : α, IsBijLetter A b → A.step y b = y := by
      intro y hyNot hother b hb
      by_contra hne
      have himg_in : A.step y b ∈ O₃ := hother _ hne
      have hsub : O₃.image (fun q => A.step q b) ⊆ O₃ := by
        intro r hr
        rw [Finset.mem_image] at hr
        rcases hr with ⟨q, hq, rfl⟩
        exact hO3_closed q hq b hb
      have heq : O₃.image (fun q => A.step q b) = O₃ := by
        apply Finset.eq_of_subset_of_card_le hsub
        rw [Finset.card_image_of_injective _ hb.1]
      have hmem : A.step y b ∈ O₃.image (fun q => A.step q b) := by rw [heq]; exact himg_in
      rw [Finset.mem_image] at hmem
      rcases hmem with ⟨q, hq, hqeq⟩
      have hyq : q = y := hb.1 hqeq
      subst hyq
      exact hyNot hq
    have h1_not_O3 : (1 : Fin 4) ∉ O₃ := by
      intro h1in
      have h2not : (2 : Fin 4) ∉ O₃ := fun h2in => hall12 ⟨h1in, h2in⟩
      have hfix2 : A.step 2 b₂ = 2 := by
        refine hfix_out 2 h2not (fun q hq => ?_) b₂ hb₂_bij
        fin_cases q
        · exact h0_O3
        · exact h1in
        · exact absurd rfl hq
        · exact h3_O3
      have h2mem : (2 : Fin 4) ∈ ({0, 3} : Finset (Fin 4)) := by
        rw [← hb₂_img, DFA.mem_image]
        exact ⟨2, by simp, hfix2⟩
      exact absurd h2mem (by decide)
    have h2_O3 : (2 : Fin 4) ∈ O₃ := by
      rcases h12_O3 with h1 | h2
      · exact absurd h1 h1_not_O3
      · exact h2
    have hfix1 : ∀ b : α, IsBijLetter A b → A.step 1 b = 1 := by
      refine hfix_out 1 h1_not_O3 (fun q hq => ?_)
      fin_cases q
      · exact h0_O3
      · exact absurd rfl hq
      · exact h2_O3
      · exact h3_O3
    exact cerny_fin4_step6_false A hSync hdist_inj hrank_or hT3_of_rank3 hker_of_rank3
      hgolden_card hgolden_dist he1 he2 e₃ e₄ e₆ he₃_card he₃_dist he₃_sub he₄_card he₄_dist
      he₆_card he₆_dist he₆_sub b₂ b₃ hb₂_bij hb₂_img hb₃_bij hb₃_img hfix1

/-- Purely structural proof of Černý's conjecture for `Fin 4`: every synchronizing
4-state DFA admits a synchronizing word of length at most `9 = (4 - 1) ^ 2`. -/
private theorem cerny_fin4 (A : DFA (Fin 4) α) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ 9 := by
  classical
  by_contra hno
  push Not at hno
  have hlong : ∀ w : List α, A.IsSyncWord w → 10 ≤ w.length := fun w hw => hno w hw
  have h42 : (4 : ℕ).choose 2 = 6 := by decide
  have hdist_le6 : ∀ e : Finset (Fin 4), e.card = 2 → pairDist A hSync e ≤ 6 := by
    intro e he
    have h := pairDist_le_choose_two A hSync (by simp) he
    rw [Fintype.card_fin, h42] at h
    exact h
  have hrank_ge3 : ∀ c : α, 3 ≤ (A.image Finset.univ [c]).card := by
    intro c
    by_contra hlt
    have hne : (A.image Finset.univ [c]).Nonempty :=
      ⟨A.step 0 c, by rw [DFA.mem_image]; exact ⟨0, Finset.mem_univ _, rfl⟩⟩
    have hpos : 1 ≤ (A.image Finset.univ [c]).card := Finset.card_pos.mpr hne
    by_cases h1 : (A.image Finset.univ [c]).card = 1
    · have := hlong [c] ((A.isSyncWord_iff_card_image_univ_eq_one [c]).mpr h1)
      simp at this
    · have h2 : (A.image Finset.univ [c]).card = 2 := by omega
      obtain ⟨v, hvlen, hv⟩ := pairDist_spec A hSync hne
      have hd := hdist_le6 _ h2
      have hsync' : A.IsSyncWord (c :: v) := by
        rw [A.isSyncWord_iff_card_image_univ_eq_one, A.image_cons]
        exact hv
      have := hlong (c :: v) hsync'
      simp only [List.length_cons] at this
      omega
  obtain ⟨a₀, ha₀_ni⟩ := exists_non_injective_letter A hSync (by simp)
  have ha₀_rank3 : (A.image Finset.univ [a₀]).card = 3 := by
    have hge3 := hrank_ge3 a₀
    unfold Function.Injective at ha₀_ni
    push Not at ha₀_ni
    rcases ha₀_ni with ⟨x, y, hxy, hne⟩
    have hlt := card_image_lt_of_merge A [a₀] (Finset.mem_univ x) (Finset.mem_univ y) hne hxy
    simp at hlt
    omega
  obtain ⟨w₃, hw₃_len, hw₃_comp, _⟩ := compress_three_fin4 A hSync (A.image Finset.univ [a₀]) ha₀_rank3
  have hS_ne : (A.image Finset.univ (a₀ :: w₃)).Nonempty :=
    ⟨A.eval 0 (a₀ :: w₃), by rw [DFA.mem_image]; exact ⟨0, Finset.mem_univ _, rfl⟩⟩
  have hS_card2 : (A.image Finset.univ (a₀ :: w₃)).card = 2 := by
    have hpos : 1 ≤ (A.image Finset.univ (a₀ :: w₃)).card := Finset.card_pos.mpr hS_ne
    have hle2 : (A.image Finset.univ (a₀ :: w₃)).card ≤ 2 := by
      rw [DFA.image_cons]
      omega
    by_contra hne2
    have h1 : (A.image Finset.univ (a₀ :: w₃)).card = 1 := by omega
    have h10 := hlong (a₀ :: w₃) ((A.isSyncWord_iff_card_image_univ_eq_one _).mpr h1)
    simp only [List.length_cons] at h10
    omega
  have hS_dist6 : pairDist A hSync (A.image Finset.univ (a₀ :: w₃)) = 6 := by
    obtain ⟨v, hvlen, hv⟩ := pairDist_spec A hSync hS_ne
    have hsync' : A.IsSyncWord ((a₀ :: w₃) ++ v) := by
      rw [A.isSyncWord_iff_card_image_univ_eq_one, A.image_append]
      exact hv
    have h10 := hlong _ hsync'
    simp only [List.length_append, List.length_cons] at h10
    have hd6 := hdist_le6 _ hS_card2
    omega
  have hlayer_ne_full : ∀ k : ℕ, k ≤ 5 →
      pairLayer A hSync k ≠ (Finset.univ : Finset (Fin 4)).powersetCard 2 := by
    intro k hk heq
    have hmem : A.image Finset.univ (a₀ :: w₃) ∈ pairLayer A hSync k := by
      rw [heq, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hS_card2⟩
    simp only [pairLayer, Finset.mem_filter] at hmem
    omega
  have hlayer_card_eq : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → (pairLayer A hSync k).card = k := by
    have h6_le : (pairLayer A hSync 6).card ≤ 6 := by
      have hsub : pairLayer A hSync 6 ⊆ (Finset.univ : Finset (Fin 4)).powersetCard 2 :=
        Finset.filter_subset _ _
      have h := Finset.card_le_card hsub
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, h42] at h
      exact h
    have h1_ge : 1 ≤ (pairLayer A hSync 1).card :=
      Finset.card_pos.mpr (pairLayer_one_nonempty A hSync (by simp))
    have hg1 : (pairLayer A hSync 1).card + 1 ≤ (pairLayer A hSync 2).card :=
      pairLayer_strict_growth A hSync 1 (hlayer_ne_full 1 (by omega))
    have hg2 : (pairLayer A hSync 2).card + 1 ≤ (pairLayer A hSync 3).card :=
      pairLayer_strict_growth A hSync 2 (hlayer_ne_full 2 (by omega))
    have hg3 : (pairLayer A hSync 3).card + 1 ≤ (pairLayer A hSync 4).card :=
      pairLayer_strict_growth A hSync 3 (hlayer_ne_full 3 (by omega))
    have hg4 : (pairLayer A hSync 4).card + 1 ≤ (pairLayer A hSync 5).card :=
      pairLayer_strict_growth A hSync 4 (hlayer_ne_full 4 (by omega))
    have hg5 : (pairLayer A hSync 5).card + 1 ≤ (pairLayer A hSync 6).card :=
      pairLayer_strict_growth A hSync 5 (hlayer_ne_full 5 (by omega))
    intro k hk1 hk6
    interval_cases k <;> omega
  have hfiber_card : ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
      (((Finset.univ : Finset (Fin 4)).powersetCard 2).filter
        (fun e => pairDist A hSync e = k)).card = 1 := by
    intro k hk1 hk6
    have heq_sdiff :
        ((Finset.univ : Finset (Fin 4)).powersetCard 2).filter (fun e => pairDist A hSync e = k) =
        pairLayer A hSync k \ pairLayer A hSync (k - 1) := by
      ext e
      simp only [pairLayer, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      constructor
      · rintro ⟨h2, hdk⟩
        exact ⟨⟨h2, by omega⟩, fun h => by omega⟩
      · rintro ⟨⟨h2, hle⟩, hnot⟩
        refine ⟨h2, ?_⟩
        by_contra hne
        exact hnot ⟨h2, by omega⟩
    rw [heq_sdiff, Finset.card_sdiff_of_subset (pairLayer_mono A hSync (by omega))]
    by_cases hk1' : k = 1
    · subst hk1'
      have h0 : pairLayer A hSync 0 = ∅ := by
        ext e
        simp only [pairLayer, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
          true_and, Finset.notMem_empty, iff_false, not_and]
        intro h2 hle
        have := pairDist_pos_of_card_two A hSync h2
        omega
      rw [h0, Finset.card_empty, hlayer_card_eq 1 (by omega) (by omega)]
    · rw [hlayer_card_eq k hk1 hk6, hlayer_card_eq (k - 1) (by omega) (by omega)]
      omega
  have hdist_surj : ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
      ∃ e : Finset (Fin 4), e.card = 2 ∧ pairDist A hSync e = k := by
    intro k hk1 hk6
    have hc := hfiber_card k hk1 hk6
    have hpos : 0 < (((Finset.univ : Finset (Fin 4)).powersetCard 2).filter
        (fun e => pairDist A hSync e = k)).card := by rw [hc]; omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at he
    exact ⟨e, he.1, he.2⟩
  have hdist_inj : ∀ e₁ e₂ : Finset (Fin 4), e₁.card = 2 → e₂.card = 2 →
      pairDist A hSync e₁ = pairDist A hSync e₂ → e₁ = e₂ := by
    intro e₁ e₂ h1 h2 hdeq
    let k := pairDist A hSync e₁
    have hk1 : 1 ≤ k := pairDist_pos_of_card_two A hSync h1
    have hk6 : k ≤ 6 := hdist_le6 e₁ h1
    have hc := hfiber_card k hk1 hk6
    rw [Finset.card_eq_one] at hc
    rcases hc with ⟨e₀, he₀⟩
    have hm1 : e₁ ∈ ({e₀} : Finset (Finset (Fin 4))) := by
      rw [← he₀, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, h1⟩, rfl⟩
    have hm2 : e₂ ∈ ({e₀} : Finset (Finset (Fin 4))) := by
      rw [← he₀, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, h2⟩, hdeq.symm⟩
    simp only [Finset.mem_singleton] at hm1 hm2
    exact hm1.trans hm2.symm
  obtain ⟨e₁, he₁_card, he₁_dist⟩ := hdist_surj 1 (by omega) (by omega)
  obtain ⟨e₂, he₂_card, he₂_dist⟩ := hdist_surj 2 (by omega) (by omega)
  have hnot_sub : ∀ e : Finset (Fin 4), e.card = 2 → pairDist A hSync e ≤ 2 →
      ¬ (e ⊆ A.image Finset.univ [a₀]) := by
    intro e he_card he_dist hsub
    rw [Finset.card_eq_two] at he_card
    rcases he_card with ⟨x, y, hxy, rfl⟩
    obtain ⟨v, hvlen, hv⟩ := pairDist_spec A hSync (⟨x, by simp⟩ : ({x, y} : Finset (Fin 4)).Nonempty)
    have hmerge := (card_image_eq_one_iff_pair A v).mp hv
    have hlt := card_image_lt_of_merge A v (hsub (by simp)) (hsub (by simp)) hxy hmerge
    rw [← DFA.image_cons, ha₀_rank3] at hlt
    have hne : (A.image Finset.univ (a₀ :: v)).Nonempty :=
      ⟨A.eval 0 (a₀ :: v), by rw [DFA.mem_image]; exact ⟨0, Finset.mem_univ _, rfl⟩⟩
    have hpos : 1 ≤ (A.image Finset.univ (a₀ :: v)).card := Finset.card_pos.mpr hne
    by_cases h1 : (A.image Finset.univ (a₀ :: v)).card = 1
    · have h10 := hlong (a₀ :: v) ((A.isSyncWord_iff_card_image_univ_eq_one _).mpr h1)
      simp only [List.length_cons] at h10
      omega
    · have h2 : (A.image Finset.univ (a₀ :: v)).card = 2 := by omega
      obtain ⟨u, hulen, hu⟩ := pairDist_spec A hSync hne
      have hd6 := hdist_le6 _ h2
      have hsync' : A.IsSyncWord ((a₀ :: v) ++ u) := by
        rw [A.isSyncWord_iff_card_image_univ_eq_one, A.image_append]
        exact hu
      have h10 := hlong _ hsync'
      simp only [List.length_append, List.length_cons] at h10
      omega
  have hinter_nonempty : (e₁ ∩ e₂).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hdisj : Disjoint e₁ e₂ := Finset.disjoint_iff_inter_eq_empty.mpr hemp
    have hunion : e₁ ∪ e₂ = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_union_of_disjoint hdisj, he₁_card, he₂_card]
      simp
    have hsdiff : (Finset.univ \ A.image Finset.univ [a₀]).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, ha₀_rank3]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hsdiff
    have hz_in : z ∈ e₁ ∪ e₂ := by rw [hunion]; exact Finset.mem_univ z
    have hsub_of_not_mem : ∀ S : Finset (Fin 4), z ∉ S → S ⊆ A.image Finset.univ [a₀] := by
      intro S hzS q hq
      by_contra hqNot
      have hmem : q ∈ Finset.univ \ A.image Finset.univ [a₀] :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hqNot⟩
      rw [hz, Finset.mem_singleton] at hmem
      subst hmem
      exact hzS hq
    rw [Finset.mem_union] at hz_in
    rcases hz_in with hz1 | hz2
    · exact hnot_sub e₂ he₂_card (by omega) (hsub_of_not_mem e₂ (Finset.disjoint_left.mp hdisj hz1))
    · exact hnot_sub e₁ he₁_card (by omega) (hsub_of_not_mem e₁ (Finset.disjoint_right.mp hdisj hz2))
  obtain ⟨p₃, hp₃_inter⟩ := hinter_nonempty
  have hp₃_1 : p₃ ∈ e₁ := (Finset.mem_inter.mp hp₃_inter).1
  have hp₃_2 : p₃ ∈ e₂ := (Finset.mem_inter.mp hp₃_inter).2
  have he₁_erase : (e₁.erase p₃).card = 1 := by rw [Finset.card_erase_of_mem hp₃_1, he₁_card]
  obtain ⟨p₀, hp₀_eq⟩ := Finset.card_eq_one.mp he₁_erase
  have hp₀_ne_p₃ : p₀ ≠ p₃ := by
    have hmem : p₀ ∈ e₁.erase p₃ := by rw [hp₀_eq]; simp
    exact (Finset.mem_erase.mp hmem).1
  have he₁_eq : e₁ = {p₀, p₃} := by
    ext q
    by_cases hq : q = p₃
    · subst hq; simp [hp₃_1]
    · have : q ∈ e₁ ↔ q ∈ e₁.erase p₃ := (Finset.mem_erase.trans (and_iff_right hq)).symm
      rw [this, hp₀_eq]
      simp [hq]
  have he₂_erase : (e₂.erase p₃).card = 1 := by rw [Finset.card_erase_of_mem hp₃_2, he₂_card]
  obtain ⟨p₂, hp₂_eq⟩ := Finset.card_eq_one.mp he₂_erase
  have hp₂_ne_p₃ : p₂ ≠ p₃ := by
    have hmem : p₂ ∈ e₂.erase p₃ := by rw [hp₂_eq]; simp
    exact (Finset.mem_erase.mp hmem).1
  have he₂_eq : e₂ = {p₂, p₃} := by
    ext q
    by_cases hq : q = p₃
    · subst hq; simp [hp₃_2]
    · have : q ∈ e₂ ↔ q ∈ e₂.erase p₃ := (Finset.mem_erase.trans (and_iff_right hq)).symm
      rw [this, hp₂_eq]
      simp [hq]
  have hp₀_ne_p₂ : p₀ ≠ p₂ := by
    intro h
    subst h
    have : e₁ = e₂ := he₁_eq.trans he₂_eq.symm
    rw [this, he₂_dist] at he₁_dist
    omega
  have htriple_card : ({p₀, p₂, p₃} : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hp₂_ne_p₃]
    simp [hp₀_ne_p₂, hp₀_ne_p₃]
  have hrem_card : (Finset.univ \ ({p₀, p₂, p₃} : Finset (Fin 4))).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, htriple_card]
  obtain ⟨p₁, hp₁_eq⟩ := Finset.card_eq_one.mp hrem_card
  have hp₁_not : p₁ ∉ ({p₀, p₂, p₃} : Finset (Fin 4)) := by
    have hmem : p₁ ∈ Finset.univ \ ({p₀, p₂, p₃} : Finset (Fin 4)) := by rw [hp₁_eq]; simp
    exact (Finset.mem_sdiff.mp hmem).2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp₁_not
  let f : Fin 4 → Fin 4 := fun i =>
    match i with
    | ⟨0, _⟩ => p₀
    | ⟨1, _⟩ => p₁
    | ⟨2, _⟩ => p₂
    | ⟨3, _⟩ => p₃
  have hf_inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp [f] at hij
    all_goals first | rfl | exact absurd hij hp₀_ne_p₂ | exact absurd hij hp₀_ne_p₃ |
      exact absurd hij hp₂_ne_p₃ | exact absurd hij.symm hp₀_ne_p₂ | exact absurd hij.symm hp₀_ne_p₃ |
      exact absurd hij.symm hp₂_ne_p₃ | exact absurd hij hp₁_not.1 | exact absurd hij hp₁_not.2.1 |
      exact absurd hij hp₁_not.2.2 | exact absurd hij.symm hp₁_not.1 | exact absurd hij.symm hp₁_not.2.1 |
      exact absurd hij.symm hp₁_not.2.2
  let σ : Fin 4 ≃ Fin 4 := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  let A' : DFA (Fin 4) α := A.reindex σ.symm
  have hSync' : A'.IsSynchronizing := (A.reindex_isSynchronizing_iff σ.symm).mpr hSync
  have hlong' : ∀ w : List α, A'.IsSyncWord w → 10 ≤ w.length := fun w hw =>
    hlong w ((A.reindex_isSyncWord_iff σ.symm w).mp hw)
  have hdist_transport : ∀ S : Finset (Fin 4),
      pairDist A' hSync' S = pairDist A hSync (S.image σ) := by
    intro S
    by_cases hne : S.Nonempty
    · have hne' : (S.image σ).Nonempty := hne.image σ
      have himg_eq : ∀ w : List α, (A'.image S w).card = (A.image (S.image σ) w).card := by
        intro w
        have h1 : S = (S.image σ).image σ.symm := by
          ext q; simp [Finset.mem_image]
        conv_lhs => rw [h1]
        rw [A.reindex_image σ.symm (S.image σ) w,
          Finset.card_image_of_injective _ σ.symm.injective]
      apply le_antisymm
      · obtain ⟨w, hwlen, hw⟩ := pairDist_spec A hSync hne'
        rw [← himg_eq w] at hw
        exact le_trans (pairDist_le_of_merge A' hSync' hne hw) hwlen.le
      · obtain ⟨w, hwlen, hw⟩ := pairDist_spec A' hSync' hne
        rw [himg_eq w] at hw
        exact le_trans (pairDist_le_of_merge A hSync hne' hw) hwlen.le
    · have hne' : ¬ (S.image σ).Nonempty := by simpa using hne
      unfold pairDist
      simp only [hne, hne', ↓reduceDIte]
  have hdist_le6' : ∀ e : Finset (Fin 4), e.card = 2 → pairDist A' hSync' e ≤ 6 := by
    intro e he
    rw [hdist_transport]
    exact hdist_le6 _ (by rw [Finset.card_image_of_injective _ σ.injective, he])
  have hdist_inj' : ∀ e₁' e₂' : Finset (Fin 4), e₁'.card = 2 → e₂'.card = 2 →
      pairDist A' hSync' e₁' = pairDist A' hSync' e₂' → e₁' = e₂' := by
    intro e₁' e₂' h1 h2 hdeq
    rw [hdist_transport, hdist_transport] at hdeq
    have himg := hdist_inj _ _ (by rw [Finset.card_image_of_injective _ σ.injective, h1])
      (by rw [Finset.card_image_of_injective _ σ.injective, h2]) hdeq
    ext q
    constructor
    · intro hq
      have hmem : σ q ∈ e₂'.image σ := by rw [← himg]; exact Finset.mem_image_of_mem σ hq
      rcases Finset.mem_image.mp hmem with ⟨r, hr, hrq⟩
      exact (σ.injective hrq) ▸ hr
    · intro hq
      have hmem : σ q ∈ e₁'.image σ := by rw [himg]; exact Finset.mem_image_of_mem σ hq
      rcases Finset.mem_image.mp hmem with ⟨r, hr, hrq⟩
      exact (σ.injective hrq) ▸ hr
  have hdist_surj' : ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
      ∃ e : Finset (Fin 4), e.card = 2 ∧ pairDist A' hSync' e = k := by
    intro k hk1 hk6
    obtain ⟨e, heCard, hed⟩ := hdist_surj k hk1 hk6
    refine ⟨e.image σ.symm, by rw [Finset.card_image_of_injective _ σ.symm.injective, heCard], ?_⟩
    rw [hdist_transport]
    have hback : (e.image σ.symm).image σ = e := by ext q; simp [Finset.mem_image]
    rw [hback]
    exact hed
  have he1' : pairDist A' hSync' ({0, 3} : Finset (Fin 4)) = 1 := by
    rw [hdist_transport]
    have himg : ({0, 3} : Finset (Fin 4)).image σ = e₁ := by
      rw [he₁_eq]
      ext q
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl | rfl, rfl⟩
        · left; rfl
        · right; rfl
      · rintro (rfl | rfl)
        · exact ⟨0, Or.inl rfl, rfl⟩
        · exact ⟨3, Or.inr rfl, rfl⟩
    rw [himg, he₁_dist]
  have he2' : pairDist A' hSync' ({2, 3} : Finset (Fin 4)) = 2 := by
    rw [hdist_transport]
    have himg : ({2, 3} : Finset (Fin 4)).image σ = e₂ := by
      rw [he₂_eq]
      ext q
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl | rfl, rfl⟩
        · left; rfl
        · right; rfl
      · rintro (rfl | rfl)
        · exact ⟨2, Or.inl rfl, rfl⟩
        · exact ⟨3, Or.inr rfl, rfl⟩
    rw [himg, he₂_dist]
  exact cerny_fin4_normalized_false A' hSync' hlong' hdist_le6' hdist_inj' hdist_surj' he1' he2'

/-- Černý's Conjecture for `n = 4`: every 4-state synchronizing DFA admits a synchronizing
word of length at most `9 = (4 - 1) ^ 2`. -/
theorem cerny_card_eq_four {Q : Type*} [Fintype Q] (A : DFA Q α)
    (hcard : Fintype.card Q = 4) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  let e : Q ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  have hSync' : (A.reindex e).IsSynchronizing := (A.reindex_isSynchronizing_iff e).mpr hSync
  obtain ⟨w, hw, hlen⟩ := cerny_fin4 (A.reindex e) hSync'
  refine ⟨w, (A.reindex_isSyncWord_iff e w).mp hw, ?_⟩
  rw [hcard]
  exact hlen

/-- Unified Černý Conjecture for all synchronizing DFAs with at most 4 states. -/
theorem cerny_card_le_four {Q : Type*} [Fintype Q] [Nonempty Q] (A : DFA Q α)
    (hcard : Fintype.card Q ≤ 4) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos
  have hcases : Fintype.card Q = 1 ∨ Fintype.card Q = 2 ∨ Fintype.card Q = 3 ∨ Fintype.card Q = 4 := by
    omega
  rcases hcases with h1 | h2 | h3 | h4
  · exact cerny_card_eq_one A h1 hSync
  · exact cerny_card_eq_two A h2 hSync
  · exact cerny_card_eq_three A h3 hSync
  · exact cerny_card_eq_four A h4 hSync

end SmallFour

end Cerny
