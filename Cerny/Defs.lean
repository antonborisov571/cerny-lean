module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod

/-!
# Core Definitions for the Černý Conjecture

This file defines deterministic finite (semi)automata (`DFA`), word evaluation (`DFA.eval`),
forward images (`DFA.image`) and backward preimages (`DFA.preimage`), synchronizing words
(`DFA.IsSyncWord`), synchronizing automata (`DFA.IsSynchronizing`), reset thresholds
(`DFA.resetThreshold`), the statement of the Černý Conjecture (`CernyConjecture`), the
extremal Černý automaton family (`cernyDFA`), and standard subclasses (`DFA.IsEulerian`,
`DFA.IsCircular`, `DFA.IsOneCluster`, `DFA.IsStronglyConnected`).
-/

@[expose] public section

namespace Cerny

universe u v

/-- A deterministic finite (semi)automaton with state set `Q` and input alphabet `α`. -/
structure DFA (Q : Type u) (α : Type v) where
  /-- Transition function: `step q a` is the state reached from `q` on input letter `a`. -/
  step : Q → α → Q

namespace DFA

variable {Q : Type u} {α : Type v}

/-! ### Word evaluation -/

/-- Evaluate a word `w` starting from state `q` by folding transitions from left to right. -/
def eval (A : DFA Q α) (q : Q) (w : List α) : Q :=
  w.foldl A.step q

@[simp]
theorem eval_nil (A : DFA Q α) (q : Q) : A.eval q [] = q :=
  rfl

@[simp]
theorem eval_cons (A : DFA Q α) (q : Q) (a : α) (w : List α) :
    A.eval q (a :: w) = A.eval (A.step q a) w :=
  rfl

@[simp]
theorem eval_singleton (A : DFA Q α) (q : Q) (a : α) : A.eval q [a] = A.step q a :=
  rfl

@[simp]
theorem eval_append (A : DFA Q α) (q : Q) (u v : List α) :
    A.eval q (u ++ v) = A.eval (A.eval q u) v := by
  simp [eval, List.foldl_append]

theorem eval_replicate (A : DFA Q α) (q : Q) (n : ℕ) (a : α) :
    A.eval q (List.replicate n a) = (fun x => A.step x a)^[n] q := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, eval_cons, ih, Function.iterate_succ_apply]

/-! ### Forward images and backward preimages -/

/-- Forward image of a finite set of states `S` under word `w`. -/
def image [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α) : Finset Q :=
  S.image (fun q => A.eval q w)

/-- Backward preimage of a finite set of states `S` under word `w`. -/
def preimage [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α) : Finset Q :=
  Finset.univ.filter (fun q => A.eval q w ∈ S)

@[simp]
theorem mem_image [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α) (q : Q) :
    q ∈ A.image S w ↔ ∃ p ∈ S, A.eval p w = q :=
  Finset.mem_image

@[simp]
theorem image_nil [DecidableEq Q] (A : DFA Q α) (S : Finset Q) :
    A.image S [] = S := by
  simp [image]

@[simp]
theorem image_append [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (u v : List α) :
    A.image S (u ++ v) = A.image (A.image S u) v := by
  ext q
  simp only [mem_image, eval_append]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨A.eval p u, ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨r, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩

theorem image_cons [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (a : α) (w : List α) :
    A.image S (a :: w) = A.image (A.image S [a]) w := by
  simpa using A.image_append S [a] w

@[simp]
theorem image_empty [DecidableEq Q] (A : DFA Q α) (w : List α) :
    A.image ∅ w = ∅ := by
  simp [image]

@[simp]
theorem image_singleton [DecidableEq Q] (A : DFA Q α) (q : Q) (w : List α) :
    A.image {q} w = {A.eval q w} := by
  simp [image]

theorem image_mono [DecidableEq Q] (A : DFA Q α) {S T : Finset Q} (h : S ⊆ T) (w : List α) :
    A.image S w ⊆ A.image T w :=
  Finset.image_subset_image h

theorem card_image_le [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α) :
    (A.image S w).card ≤ S.card :=
  Finset.card_image_le

@[simp]
theorem mem_preimage [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α)
    (q : Q) : q ∈ A.preimage S w ↔ A.eval q w ∈ S := by
  simp [preimage]

@[simp]
theorem preimage_nil [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) :
    A.preimage S [] = S := by
  ext q
  simp

@[simp]
theorem preimage_append [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (u v : List α) :
    A.preimage S (u ++ v) = A.preimage (A.preimage S v) u := by
  ext q
  simp

theorem preimage_cons [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (a : α)
    (w : List α) : A.preimage S (a :: w) = A.preimage (A.preimage S w) [a] := by
  ext q
  simp

@[simp]
theorem preimage_empty [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) :
    A.preimage ∅ w = ∅ := by
  ext q
  simp

@[simp]
theorem preimage_univ [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) :
    A.preimage Finset.univ w = Finset.univ := by
  ext q
  simp

theorem preimage_mono [Fintype Q] [DecidableEq Q] (A : DFA Q α) {S T : Finset Q} (h : S ⊆ T)
    (w : List α) : A.preimage S w ⊆ A.preimage T w := by
  intro q hq
  simp only [mem_preimage] at hq ⊢
  exact h hq

theorem preimage_union [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S T : Finset Q) (w : List α) :
    A.preimage (S ∪ T) w = A.preimage S w ∪ A.preimage T w := by
  ext q
  simp

theorem preimage_inter [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S T : Finset Q) (w : List α) :
    A.preimage (S ∩ T) w = A.preimage S w ∩ A.preimage T w := by
  ext q
  simp

theorem preimage_compl [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α) :
    A.preimage Sᶜ w = (A.preimage S w)ᶜ := by
  ext q
  simp

theorem image_subset_iff_subset_preimage [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (S T : Finset Q) (w : List α) : A.image S w ⊆ T ↔ S ⊆ A.preimage T w := by
  simp [Finset.subset_iff]

theorem card_preimage_eq_sum_singleton [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q)
    (w : List α) : (A.preimage S w).card = ∑ q ∈ S, (A.preimage {q} w).card := by
  have h : A.preimage S w = S.biUnion (fun q => A.preimage {q} w) := by
    ext p
    simp
  rw [h, Finset.card_biUnion]
  intro q₁ _ q₂ _ hne
  change Disjoint (A.preimage {q₁} w) (A.preimage {q₂} w)
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  simp only [mem_preimage, Finset.mem_singleton] at hp₁ hp₂
  exact hne (hp₁.symm.trans hp₂)

theorem sum_card_preimage_singleton [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) :
    ∑ q : Q, (A.preimage {q} w).card = Fintype.card Q := by
  rw [← card_preimage_eq_sum_singleton, preimage_univ, Finset.card_univ]

/-! ### Synchronizing words and reset threshold -/

/-- A word `w` is a synchronizing (reset) word for `A` if it sends every state to the same state. -/
def IsSyncWord (A : DFA Q α) (w : List α) : Prop :=
  ∃ q₀ : Q, ∀ q : Q, A.eval q w = q₀

theorem IsSyncWord.nonempty {A : DFA Q α} {w : List α} (hw : A.IsSyncWord w) : Nonempty Q :=
  let ⟨q₀, _⟩ := hw
  ⟨q₀⟩

theorem isSyncWord_iff_card_image_univ_eq_one [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (w : List α) : A.IsSyncWord w ↔ (A.image Finset.univ w).card = 1 := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨q₀, hq₀⟩
    refine ⟨q₀, ?_⟩
    ext q
    simp only [mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨p, hp⟩ => hp.symm.trans (hq₀ p), fun h => ⟨q₀, (hq₀ q₀).trans h.symm⟩⟩
  · rintro ⟨q₀, hq₀⟩
    refine ⟨q₀, fun q => ?_⟩
    have hmem : A.eval q w ∈ A.image Finset.univ w := by
      rw [mem_image]
      exact ⟨q, Finset.mem_univ q, rfl⟩
    rw [hq₀, Finset.mem_singleton] at hmem
    exact hmem

theorem isSyncWord_iff_exists_preimage_eq_univ [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (w : List α) : A.IsSyncWord w ↔ ∃ q₀ : Q, A.preimage {q₀} w = Finset.univ := by
  constructor
  · rintro ⟨q₀, hq₀⟩
    refine ⟨q₀, ?_⟩
    ext q
    simp [hq₀ q]
  · rintro ⟨q₀, hq₀⟩
    refine ⟨q₀, fun q => ?_⟩
    have hmem : q ∈ A.preimage {q₀} w := by
      rw [hq₀]
      exact Finset.mem_univ q
    simpa using hmem

theorem isSyncWord_append_right (A : DFA Q α) {u : List α} (hu : A.IsSyncWord u) (v : List α) :
    A.IsSyncWord (u ++ v) := by
  rcases hu with ⟨q₀, hq₀⟩
  exact ⟨A.eval q₀ v, fun q => by rw [eval_append, hq₀ q]⟩

theorem isSyncWord_append_left (A : DFA Q α) (u : List α) {v : List α} (hv : A.IsSyncWord v) :
    A.IsSyncWord (u ++ v) := by
  rcases hv with ⟨q₀, hq₀⟩
  exact ⟨q₀, fun q => by rw [eval_append, hq₀]⟩

/-- A DFA is synchronizing if it admits at least one synchronizing word. -/
def IsSynchronizing (A : DFA Q α) : Prop :=
  ∃ w : List α, A.IsSyncWord w

theorem IsSynchronizing.nonempty {A : DFA Q α} (h : A.IsSynchronizing) : Nonempty Q :=
  let ⟨_, hw⟩ := h
  hw.nonempty

theorem exists_length_isSyncWord {A : DFA Q α} (h : A.IsSynchronizing) :
    ∃ k : ℕ, ∃ w : List α, w.length = k ∧ A.IsSyncWord w :=
  let ⟨w, hw⟩ := h
  ⟨w.length, w, rfl, hw⟩

/-- The reset threshold of a synchronizing DFA: the minimum length of a synchronizing word. -/
noncomputable def resetThreshold (A : DFA Q α) (h : A.IsSynchronizing) : ℕ := by
  classical
  exact Nat.find (exists_length_isSyncWord h)

theorem resetThreshold_le_of_isSyncWord (A : DFA Q α) (h : A.IsSynchronizing) {w : List α}
    (hw : A.IsSyncWord w) : A.resetThreshold h ≤ w.length := by
  classical
  unfold resetThreshold
  exact Nat.find_min' (exists_length_isSyncWord h) ⟨w, rfl, hw⟩

theorem exists_isSyncWord_length_eq_resetThreshold (A : DFA Q α) (h : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length = A.resetThreshold h := by
  classical
  unfold resetThreshold
  obtain ⟨w, hlen, hw⟩ := Nat.find_spec (exists_length_isSyncWord h)
  exact ⟨w, hw, hlen⟩

theorem le_resetThreshold_iff (A : DFA Q α) (h : A.IsSynchronizing) (n : ℕ) :
    n ≤ A.resetThreshold h ↔ ∀ w : List α, A.IsSyncWord w → n ≤ w.length := by
  constructor
  · intro hn w hw
    exact hn.trans (A.resetThreshold_le_of_isSyncWord h hw)
  · intro hall
    obtain ⟨w, hw, hlen⟩ := A.exists_isSyncWord_length_eq_resetThreshold h
    rw [← hlen]
    exact hall w hw

/-! ### Standard automaton subclasses -/

/-- A DFA is strongly connected if every state is reachable from every other state. -/
def IsStronglyConnected (A : DFA Q α) : Prop :=
  ∀ p q : Q, ∃ w : List α, A.eval p w = q

/-- A DFA is Eulerian (balanced) if every state has total in-degree equal to `|α|`. -/
def IsEulerian [Fintype Q] [Fintype α] [DecidableEq Q] (A : DFA Q α) : Prop :=
  ∀ q : Q, (∑ a : α, (A.preimage {q} [a]).card) = Fintype.card α

theorem isEulerian_iff_card_filter_eq [Fintype Q] [Fintype α] [DecidableEq Q] (A : DFA Q α) :
    A.IsEulerian ↔
      ∀ q : Q, (Finset.univ.filter (fun p : Q × α => A.step p.1 p.2 = q)).card = Fintype.card α := by
  refine forall_congr' fun q => ?_
  have hcard :
      (Finset.univ.filter (fun p : Q × α => A.step p.1 p.2 = q)).card =
        ∑ a : α, (A.preimage {q} [a]).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [preimage, Finset.card_filter]
  rw [hcard]

theorem IsEulerian.sum_card_preimage [Fintype Q] [Fintype α] [DecidableEq Q] {A : DFA Q α}
    (hE : A.IsEulerian) (S : Finset Q) :
    ∑ a : α, (A.preimage S [a]).card = Fintype.card α * S.card := by
  calc
    ∑ a : α, (A.preimage S [a]).card
        = ∑ a : α, ∑ q ∈ S, (A.preimage {q} [a]).card :=
      Finset.sum_congr rfl fun a _ => A.card_preimage_eq_sum_singleton S [a]
    _ = ∑ q ∈ S, ∑ a : α, (A.preimage {q} [a]).card := Finset.sum_comm
    _ = ∑ _q ∈ S, Fintype.card α :=
      Finset.sum_congr rfl fun q _ => hE q
    _ = S.card * Fintype.card α := by simp
    _ = Fintype.card α * S.card := Nat.mul_comm _ _

/-- A DFA is circular if some letter acts as a single transitive cycle on all of `Q`. -/
def IsCircular [Fintype Q] (A : DFA Q α) : Prop :=
  ∃ a : α,
    Function.Bijective (fun q => A.step q a) ∧
    ∀ p q : Q, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q

/-- A DFA is one-cluster if some letter `a` has a unique cycle in its functional graph,
equivalently a nonempty `a`-invariant transitive cycle `C` that every state eventually enters. -/
def IsOneCluster [Fintype Q] (A : DFA Q α) : Prop :=
  ∃ a : α, ∃ C : Set Q,
    C.Nonempty ∧
    (∀ q ∈ C, A.step q a ∈ C) ∧
    (∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) ∧
    (∀ q : Q, ∃ k : ℕ, (fun x => A.step x a)^[k] q ∈ C)

theorem IsCircular.isOneCluster [Fintype Q] [Nonempty Q] {A : DFA Q α} (h : A.IsCircular) :
    A.IsOneCluster := by
  rcases h with ⟨a, _, htrans⟩
  exact ⟨a, Set.univ, Set.univ_nonempty, fun _ _ => trivial, fun p _ q _ => htrans p q,
    fun _ => ⟨0, trivial⟩⟩

end DFA

/-! ### The Černý Conjecture and the Černý automaton family -/

/-- The Černý Conjecture: every synchronizing DFA on `n ≥ 1` states admits a synchronizing word
of length at most `(n - 1) ^ 2`. -/
def CernyConjecture : Prop :=
  ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : DFA Q α),
    A.IsSynchronizing → ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2

theorem cernyConjecture_iff_resetThreshold :
    CernyConjecture.{u, v} ↔
      ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : DFA Q α) (h : A.IsSynchronizing),
        A.resetThreshold h ≤ (Fintype.card Q - 1) ^ 2 := by
  constructor
  · intro hC Q _ _ α A hSync
    obtain ⟨w, hw, hlen⟩ := hC A hSync
    exact (A.resetThreshold_le_of_isSyncWord hSync hw).trans hlen
  · intro hR Q _ _ α A hSync
    obtain ⟨w, hw, hlen⟩ := A.exists_isSyncWord_length_eq_resetThreshold hSync
    exact ⟨w, hw, hlen.le.trans (hR A hSync)⟩

/-- The `n`-state Černý automaton `𝒞_n` (`n ≥ 2`) on `Fin n` with alphabet `Bool`:
- `false` is the cyclic shift `i ↦ (i + 1) mod n`;
- `true` sends `n - 1 ↦ 0` and fixes every `i < n - 1`. -/
def cernyDFA (n : ℕ) (hn : 2 ≤ n) : DFA (Fin n) Bool where
  step q
    | false => ⟨(q.val + 1) % n, Nat.mod_lt _ (by omega)⟩
    | true => if q.val = n - 1 then ⟨0, by omega⟩ else q

@[simp]
theorem cernyDFA_step_false (n : ℕ) (hn : 2 ≤ n) (q : Fin n) :
    (cernyDFA n hn).step q false = ⟨(q.val + 1) % n, Nat.mod_lt _ (by omega)⟩ :=
  rfl

@[simp]
theorem cernyDFA_step_true (n : ℕ) (hn : 2 ≤ n) (q : Fin n) :
    (cernyDFA n hn).step q true = if q.val = n - 1 then ⟨0, by omega⟩ else q :=
  rfl

theorem cernyDFA_iterate_false (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (q : Fin n) :
    ((fun x => (cernyDFA n hn).step x false)^[k] q).val = (q.val + k) % n := by
  induction k generalizing q with
  | zero =>
    simp [Nat.mod_eq_of_lt q.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, cernyDFA_step_false]
    simp only [Nat.mod_add_mod]
    congr 1
    omega

theorem cernyDFA_isCircular (n : ℕ) (hn : 2 ≤ n) : (cernyDFA n hn).IsCircular := by
  refine ⟨false, ⟨?_, ?_⟩, ?_⟩
  · intro p q hpq
    have hval := congrArg Fin.val hpq
    simp only [cernyDFA_step_false] at hval
    ext
    have hp := p.isLt
    have hq := q.isLt
    by_cases hp' : p.val + 1 < n <;> by_cases hq' : q.val + 1 < n
    · rw [Nat.mod_eq_of_lt hp', Nat.mod_eq_of_lt hq'] at hval
      omega
    · have hqe : q.val + 1 = n := by omega
      rw [Nat.mod_eq_of_lt hp', hqe, Nat.mod_self] at hval
      omega
    · have hpe : p.val + 1 = n := by omega
      rw [hpe, Nat.mod_self, Nat.mod_eq_of_lt hq'] at hval
      omega
    · omega
  · intro q
    by_cases h0 : q.val = 0
    · refine ⟨⟨n - 1, by omega⟩, ?_⟩
      ext
      simp only [cernyDFA_step_false]
      have : n - 1 + 1 = n := by omega
      rw [this, Nat.mod_self, h0]
    · refine ⟨⟨q.val - 1, by omega⟩, ?_⟩
      ext
      simp only [cernyDFA_step_false]
      have hq := q.isLt
      have : q.val - 1 + 1 = q.val := by omega
      rw [this, Nat.mod_eq_of_lt hq]
  · intro p q
    by_cases hle : p.val ≤ q.val
    · refine ⟨q.val - p.val, ?_⟩
      ext
      rw [cernyDFA_iterate_false]
      have : p.val + (q.val - p.val) = q.val := by omega
      rw [this, Nat.mod_eq_of_lt q.isLt]
    · refine ⟨n + q.val - p.val, ?_⟩
      ext
      rw [cernyDFA_iterate_false]
      have hp := p.isLt
      have hq := q.isLt
      have : p.val + (n + q.val - p.val) = q.val + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hq]

theorem cernyDFA_isOneCluster (n : ℕ) (hn : 2 ≤ n) : (cernyDFA n hn).IsOneCluster := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact (cernyDFA_isCircular n hn).isOneCluster

end Cerny
