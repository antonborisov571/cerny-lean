import Cerny.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Kari's Theorem for Eulerian Synchronizing Automata (2003)

This file formalizes Jarkko Kari's 2003 theorem proving the Černý conjecture for all
synchronizing Eulerian automata, with the sharp quadratic bound `(n - 1) * (n - 2) + 1`.

## Main results

- `Cerny.DFA.IsEulerian.isStronglyConnected`: every synchronizing Eulerian DFA is strongly
  connected.
- `Cerny.DFA.IsEulerian.sum_card_preimage_ofFn`: exact fixed-length preimage averaging
  `∑ w : Fin k → α, (A.preimage S (List.ofFn w)).card = (Fintype.card α) ^ k * S.card`.
- `Cerny.DFA.IsEulerian.exists_extending_word`: every nonempty proper subset `S` admits an
  extending word `w` of length at most `Fintype.card Q - 1`.
- `Cerny.eulerian_reset_bound`: every synchronizing Eulerian DFA on `n ≥ 1` states admits a
  synchronizing word of length at most `(n - 1) * (n - 2) + 1`.
- `Cerny.eulerian_cerny`: every synchronizing Eulerian DFA satisfies the Černý bound
  `(n - 1) ^ 2`.
-/

namespace Cerny

universe u v

namespace DFA

section Eulerian

variable {Q : Type u} {α : Type v}

/-! ### Step 1: Automatic strong connectivity -/

/-- In a synchronizing Eulerian DFA, every state is reachable from every other state. -/
theorem IsEulerian.isStronglyConnected [Fintype Q] [DecidableEq Q] [Fintype α]
    {A : DFA Q α} (hE : A.IsEulerian) (hSync : A.IsSynchronizing) :
    A.IsStronglyConnected := by
  classical
  rcases hSync with ⟨w₀, q₀, hq₀⟩
  let C : Finset Q := Finset.univ.filter (fun q => ∃ u : List α, A.eval q₀ u = q)
  have hq₀C : q₀ ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨[], rfl⟩
  have hC_step : ∀ p ∈ C, ∀ a : α, A.step p a ∈ C := by
    intro p hp a
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rcases hp with ⟨u, hu⟩
    exact ⟨u ++ [a], by rw [eval_append, hu, eval_singleton]⟩
  have hC_sub : ∀ a : α, C ⊆ A.preimage C [a] := by
    intro a p hp
    rw [mem_preimage, eval_singleton]
    exact hC_step p hp a
  have hC_card_le : ∀ a : α, C.card ≤ (A.preimage C [a]).card :=
    fun a => Finset.card_le_card (hC_sub a)
  have hsum_eq : ∑ a : α, C.card = ∑ a : α, (A.preimage C [a]).card := by
    rw [hE.sum_card_preimage C, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hC_card_eq : ∀ a : α, (A.preimage C [a]).card = C.card := by
    have hall := (Finset.sum_eq_sum_iff_of_le (fun a _ => hC_card_le a)).mp hsum_eq
    intro a
    exact (hall a (Finset.mem_univ a)).symm
  have hC_pre_letter : ∀ a : α, A.preimage C [a] = C := fun a =>
    Finset.eq_of_subset_of_card_le (hC_sub a) (hC_card_eq a).le |>.symm
  have hC_pre_word : ∀ u : List α, A.preimage C u = C := by
    intro u
    induction u with
    | nil => exact A.preimage_nil C
    | cons a u ih => rw [preimage_cons, ih, hC_pre_letter a]
  have hC_all : ∀ q : Q, q ∈ C := by
    intro q
    have hmem : q ∈ A.preimage C w₀ := by
      rw [mem_preimage, hq₀ q]
      exact hq₀C
    rwa [hC_pre_word w₀] at hmem
  intro p q
  have hqC := hC_all q
  simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hqC
  rcases hqC with ⟨u, hu⟩
  exact ⟨w₀ ++ u, by rw [eval_append, hq₀ p, hu]⟩

/-- In a synchronizing Eulerian DFA, for every target state `q` there exists a word resetting
all states to `q`. -/
theorem IsEulerian.exists_reset_to [Fintype Q] [DecidableEq Q] [Fintype α]
    {A : DFA Q α} (hE : A.IsEulerian) (hSync : A.IsSynchronizing) (q : Q) :
    ∃ w : List α, ∀ p : Q, A.eval p w = q := by
  rcases hSync with ⟨w₀, q₀, hq₀⟩
  obtain ⟨u, hu⟩ := hE.isStronglyConnected ⟨w₀, q₀, hq₀⟩ q₀ q
  exact ⟨w₀ ++ u, fun p => by rw [eval_append, hq₀ p, hu]⟩

/-! ### Step 2: Combinatorial fixed-length averaging -/

/-- Sum of preimage cardinalities over all words of exact length `k` in an Eulerian DFA. -/
theorem IsEulerian.sum_card_preimage_ofFn [Fintype Q] [DecidableEq Q] [Fintype α]
    {A : DFA Q α} (hE : A.IsEulerian) (S : Finset Q) (k : ℕ) :
    ∑ w : Fin k → α, (A.preimage S (List.ofFn w)).card = Fintype.card α ^ k * S.card := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    let e : (α × (Fin k → α)) ≃ (Fin (k + 1) → α) :=
      (Fin.consEquiv (fun _ : Fin (k + 1) => α))
    rw [← Fintype.sum_equiv e
      (fun p => (A.preimage S (List.ofFn (e p))).card)
      (fun w => (A.preimage S (List.ofFn w)).card)
      (fun _ => rfl)]
    rw [Fintype.sum_prod_type_right]
    have hcons : ∀ (a : α) (v : Fin k → α), List.ofFn (e (a, v)) = a :: List.ofFn v := by
      intro a v
      simp [e, List.ofFn_succ]
    calc
      ∑ v : Fin k → α, ∑ a : α, (A.preimage S (List.ofFn (e (a, v)))).card
          = ∑ v : Fin k → α, ∑ a : α, (A.preimage (A.preimage S (List.ofFn v)) [a]).card := by
            refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => ?_
            rw [hcons, preimage_cons]
      _ = ∑ v : Fin k → α, Fintype.card α * (A.preimage S (List.ofFn v)).card := by
            refine Finset.sum_congr rfl fun v _ => ?_
            exact hE.sum_card_preimage (A.preimage S (List.ofFn v))
      _ = Fintype.card α * ∑ v : Fin k → α, (A.preimage S (List.ofFn v)).card := by
            rw [← Finset.mul_sum]
      _ = Fintype.card α * (Fintype.card α ^ k * S.card) := by rw [ih]
      _ = Fintype.card α ^ (k + 1) * S.card := by ring

/-- If some word of length `k` changes the preimage size of `S`, then in an Eulerian DFA some
word of length `k` strictly increases it. -/
theorem IsEulerian.exists_gt_of_ne [Fintype Q] [DecidableEq Q] [Fintype α]
    {A : DFA Q α} (hE : A.IsEulerian) (S : Finset Q) {k : ℕ}
    (u : Fin k → α) (hne : (A.preimage S (List.ofFn u)).card ≠ S.card) :
    ∃ w : Fin k → α, S.card < (A.preimage S (List.ofFn w)).card := by
  by_contra h
  push Not at h
  have hlt : (A.preimage S (List.ofFn u)).card < S.card :=
    lt_of_le_of_ne (h u) hne
  have hsum_lt :
      ∑ w : Fin k → α, (A.preimage S (List.ofFn w)).card <
        ∑ _w : Fin k → α, S.card :=
    Finset.sum_lt_sum (fun w _ => h w) ⟨u, Finset.mem_univ u, hlt⟩
  have hsum_rhs : ∑ _w : Fin k → α, S.card = Fintype.card α ^ k * S.card := by
    simp [Fintype.card_fin]
  rw [hE.sum_card_preimage_ofFn S k, hsum_rhs] at hsum_lt
  exact lt_irrefl _ hsum_lt

/-! ### Step 3: Linear-algebraic ascending subspace chain over `ℚ` -/

/-- Pullback (precomposition) linear operator on `Q → ℚ` induced by a word `w`. -/
private def pullback (A : DFA Q α) (w : List α) : (Q → ℚ) →ₗ[ℚ] (Q → ℚ) where
  toFun v q := v (A.eval q w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem pullback_nil (A : DFA Q α) (v : Q → ℚ) :
    pullback A [] v = v :=
  rfl

private theorem pullback_append (A : DFA Q α) (u v : List α) (x : Q → ℚ) :
    pullback A (u ++ v) x = pullback A u (pullback A v x) := by
  ext q
  simp [pullback]

private theorem pullback_cons (A : DFA Q α) (a : α) (w : List α) (x : Q → ℚ) :
    pullback A (a :: w) x = pullback A [a] (pullback A w x) := by
  simpa using pullback_append A [a] w x

/-- Coordinate-sum linear functional `v ↦ ∑ q, v q` on `Q → ℚ`. -/
private def sumLin [Fintype Q] : (Q → ℚ) →ₗ[ℚ] ℚ where
  toFun v := ∑ q : Q, v q
  map_add' x y := Finset.sum_add_distrib
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

private theorem finrank_ker_sumLin [Fintype Q] [Nonempty Q] :
    Module.finrank ℚ (LinearMap.ker (sumLin (Q := Q))) = Fintype.card Q - 1 := by
  have hsurj : Function.Surjective (sumLin (Q := Q)) := by
    classical
    intro c
    obtain ⟨q₀⟩ := ‹Nonempty Q›
    refine ⟨Pi.single q₀ c, ?_⟩
    simp [sumLin, Pi.single_apply]
  have hrange : LinearMap.range (sumLin (Q := Q)) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker (sumLin (Q := Q))
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_pi] at hrn
  omega

/-- Centered indicator vector `γ_S(q) = 1_{q ∈ S} - |S| / |Q|`. -/
private def centeredVec [Fintype Q] [DecidableEq Q] (S : Finset Q) : Q → ℚ :=
  fun q => (if q ∈ S then (1 : ℚ) else 0) - (S.card : ℚ) / (Fintype.card Q : ℚ)

private theorem sumLin_pullback_centeredVec [Fintype Q] [Nonempty Q] [DecidableEq Q]
    (A : DFA Q α) (S : Finset Q) (w : List α) :
    sumLin (pullback A w (centeredVec S)) = ((A.preimage S w).card : ℚ) - (S.card : ℚ) := by
  have hcard_pos : (Fintype.card Q : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [sumLin, pullback, centeredVec, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_div_cancel₀ _ hcard_pos]
  congr 1
  rw [show (A.preimage S w).card = ∑ q : Q, if A.eval q w ∈ S then 1 else 0 by
    rw [preimage, Finset.card_filter]]
  push_cast
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> simp

private theorem centeredVec_ne_zero [Fintype Q] [DecidableEq Q] {S : Finset Q}
    (hS_ne : S.Nonempty) (hS_lt : S.card < Fintype.card Q) :
    centeredVec S ≠ 0 := by
  rcases hS_ne with ⟨q, hq⟩
  intro hzero
  have hq0 : centeredVec S q = 0 := congrFun hzero q
  simp only [centeredVec, hq, ↓reduceIte, sub_eq_zero] at hq0
  have hcard_ne : (Fintype.card Q : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hS_lt))
  have hlt_q : (S.card : ℚ) < (Fintype.card Q : ℚ) := Nat.cast_lt.mpr hS_lt
  have heq : (Fintype.card Q : ℚ) = (S.card : ℚ) := by
    have := (eq_div_iff hcard_ne).mp hq0
    linarith
  linarith

/-- Kari's short extending-word lemma: in a synchronizing Eulerian DFA on `n` states, every
nonempty proper subset `S` has a word `w` of length at most `n - 1` with `|S w⁻¹| > |S|`. -/
theorem IsEulerian.exists_extending_word [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype α]
    {A : DFA Q α} (hE : A.IsEulerian) (hSync : A.IsSynchronizing)
    {S : Finset Q} (hS_ne : S.Nonempty) (hS_lt : S.card < Fintype.card Q) :
    ∃ w : List α, w.length ≤ Fintype.card Q - 1 ∧ S.card < (A.preimage S w).card := by
  classical
  let H : Submodule ℚ (Q → ℚ) := LinearMap.ker (sumLin (Q := Q))
  let W : ℕ → Submodule ℚ (Q → ℚ) := fun k =>
    Submodule.span ℚ { v | ∃ w : List α, w.length ≤ k ∧ v = pullback A w (centeredVec S) }
  have hW_mono : ∀ {i j : ℕ}, i ≤ j → W i ≤ W j := by
    intro i j hij
    apply Submodule.span_mono
    rintro v ⟨w, hw, rfl⟩
    exact ⟨w, hw.trans hij, rfl⟩
  have hW_mem : ∀ (w : List α) {k : ℕ}, w.length ≤ k → pullback A w (centeredVec S) ∈ W k := by
    intro w k hwk
    exact Submodule.subset_span ⟨w, hwk, rfl⟩
  have hW0_le_H : W 0 ≤ H := by
    rw [Submodule.span_le]
    rintro v ⟨w, hw, rfl⟩
    have hwnil : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)
    subst hwnil
    change sumLin (pullback A [] (centeredVec S)) = 0
    rw [sumLin_pullback_centeredVec, preimage_nil, sub_self]
  have hW0_finrank : 1 ≤ Module.finrank ℚ (W 0) := by
    have hγ_mem : centeredVec S ∈ W 0 := by
      simpa [pullback_nil] using hW_mem [] (le_refl 0)
    have hne : centeredVec S ≠ 0 := centeredVec_ne_zero hS_ne hS_lt
    have hspan_le : Submodule.span ℚ ({centeredVec S} : Set (Q → ℚ)) ≤ W 0 := by
      rw [Submodule.span_le]
      simpa using hγ_mem
    have h1 : Module.finrank ℚ (Submodule.span ℚ ({centeredVec S} : Set (Q → ℚ))) = 1 :=
      finrank_span_singleton hne
    rw [← h1]
    exact Submodule.finrank_mono hspan_le
  -- Synchronization + strong connectivity yield a word escaping `H`.
  rcases hS_ne with ⟨s₀, hs₀⟩
  obtain ⟨y, hy⟩ := hE.exists_reset_to hSync s₀
  have hy_not_H : pullback A y (centeredVec S) ∉ H := by
    intro hmem
    change sumLin (pullback A y (centeredVec S)) = 0 at hmem
    rw [sumLin_pullback_centeredVec] at hmem
    have hpre_univ : A.preimage S y = Finset.univ := by
      ext q
      simp [hy q, hs₀]
    rw [hpre_univ, Finset.card_univ] at hmem
    have hcard_eq : Fintype.card Q = S.card := by
      exact_mod_cast sub_eq_zero.mp hmem
    omega
  have hex_escape : ∃ k : ℕ, ¬ (W k ≤ H) :=
    ⟨y.length, fun hle => hy_not_H (hle (hW_mem y (le_refl _)))⟩
  let k₀ : ℕ := Nat.find hex_escape
  have hk₀_not_H : ¬ (W k₀ ≤ H) := Nat.find_spec hex_escape
  have hk₀_min : ∀ j < k₀, W j ≤ H := fun j hj =>
    not_not.mp (Nat.find_min hex_escape hj)
  have hk₀_pos : 1 ≤ k₀ := by
    by_contra h0
    have hzero : k₀ = 0 := by omega
    rw [hzero] at hk₀_not_H
    exact hk₀_not_H hW0_le_H
  -- If `W (j + 1) ≤ W j`, then `W j` is invariant under all `pullback A [a]`, hence contains `y`.
  have hstrict : ∀ j, j + 1 < k₀ → W j < W (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hW_mono (Nat.le_succ j)) ?_
    intro heq
    have hclosed : ∀ a : α, ∀ v ∈ W j, pullback A [a] v ∈ W j := by
      intro a v hv
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨w, hwk, rfl⟩
        rw [← pullback_cons, heq]
        exact hW_mem (a :: w) (by simp; omega)
      · simp
      · intro x y _ _ hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [map_smul]
        exact Submodule.smul_mem _ c hx
    have hall : ∀ u : List α, pullback A u (centeredVec S) ∈ W j := by
      intro u
      induction u with
      | nil => simpa [pullback_nil] using hW_mem [] (Nat.zero_le j)
      | cons a u ih =>
        rw [pullback_cons]
        exact hclosed a _ ih
    have hy_in_H : pullback A y (centeredVec S) ∈ H :=
      hk₀_min j (by omega) (hall y)
    exact hy_not_H hy_in_H
  -- Strict ascending chain gives `j + 1 ≤ finrank (W j)` for all `j ≤ k₀ - 1`.
  have hdim_grow : ∀ j, j ≤ k₀ - 1 → j + 1 ≤ Module.finrank ℚ (W j) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact hW0_finrank
    | succ j ih =>
      intro hj
      have hlt : W j < W (j + 1) := hstrict j (by omega)
      have hflt : Module.finrank ℚ (W j) < Module.finrank ℚ (W (j + 1)) :=
        Submodule.finrank_lt_finrank_of_lt hlt
      have ihj := ih (by omega)
      omega
  have hk₀_le : k₀ ≤ Fintype.card Q - 1 := by
    have h1 : k₀ ≤ Module.finrank ℚ (W (k₀ - 1)) := by
      have := hdim_grow (k₀ - 1) (le_refl _)
      omega
    have h2 : Module.finrank ℚ (W (k₀ - 1)) ≤ Module.finrank ℚ H :=
      Submodule.finrank_mono (hk₀_min (k₀ - 1) (by omega))
    rw [finrank_ker_sumLin] at h2
    exact h1.trans h2
  -- Extract a generator word `u` of length `≤ k₀` not in `H`.
  have hex_gen : ∃ u : List α, u.length ≤ k₀ ∧ pullback A u (centeredVec S) ∉ H := by
    by_contra hall
    push Not at hall
    apply hk₀_not_H
    rw [Submodule.span_le]
    rintro v ⟨u, hu, rfl⟩
    exact hall u hu
  rcases hex_gen with ⟨u, hu_len, hu_not_H⟩
  have hu_card_ne : (A.preimage S u).card ≠ S.card := by
    intro heq
    apply hu_not_H
    change sumLin (pullback A u (centeredVec S)) = 0
    rw [sumLin_pullback_centeredVec, heq, sub_self]
  let uFn : Fin u.length → α := fun i => u.get i
  have huFn_eq : List.ofFn uFn = u := List.ofFn_get u
  have huFn_ne : (A.preimage S (List.ofFn uFn)).card ≠ S.card := by
    rwa [huFn_eq]
  obtain ⟨wFn, hwFn_gt⟩ := hE.exists_gt_of_ne S uFn huFn_ne
  refine ⟨List.ofFn wFn, ?_, hwFn_gt⟩
  rw [List.length_ofFn]
  exact hu_len.trans hk₀_le

/-! ### Step 4: Chain assembly and Kari's reset threshold bound -/

/-- If a synchronizing DFA has at least 2 states, some letter merges at least two states. -/
private theorem exists_letter_card_preimage_ge_two [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (hcard : 2 ≤ Fintype.card Q) :
    ∃ (q₀ : Q) (a₀ : α), 2 ≤ (A.preimage {q₀} [a₀]).card := by
  rcases hSync with ⟨w, q_sync, hq_sync⟩
  have hnot_inj : ¬ Function.Injective (fun q => A.eval q w) := by
    intro hinj
    have h1lt : 1 < Fintype.card Q := by omega
    obtain ⟨p₁, p₂, hne⟩ := Fintype.exists_pair_of_one_lt_card h1lt
    exact hne (hinj ((hq_sync p₁).trans (hq_sync p₂).symm))
  have hex_letter : ∃ a₀ : α, ¬ Function.Injective (fun q => A.step q a₀) := by
    by_contra hall
    push Not at hall
    have hinj_all : ∀ u : List α, Function.Injective (fun q => A.eval q u) := by
      intro u
      induction u with
      | nil => exact Function.injective_id
      | cons a u ih =>
        have hcomp :
            (fun q => A.eval q (a :: u)) = (fun q => A.eval q u) ∘ (fun q => A.step q a) := rfl
        rw [hcomp]
        exact ih.comp (hall a)
    exact hnot_inj (hinj_all w)
  rcases hex_letter with ⟨a₀, hna₀⟩
  simp only [Function.Injective, not_forall] at hna₀
  rcases hna₀ with ⟨p₁, p₂, heq, hne⟩
  refine ⟨A.step p₁ a₀, a₀, ?_⟩
  have hsub : ({p₁, p₂} : Finset Q) ⊆ A.preimage {A.step p₁ a₀} [a₀] := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_preimage, eval_singleton, Finset.mem_singleton]
    rcases hx with rfl | rfl
    · rfl
    · exact heq.symm
  have hpair : ({p₁, p₂} : Finset Q).card = 2 := Finset.card_pair hne
  rw [← hpair]
  exact Finset.card_le_card hsub

/-- Iterating Kari's extending-word lemma expands any nonempty subset `S` to `Finset.univ`
in at most `(n - |S|) * (n - 1)` steps. -/
private theorem IsEulerian.exists_preimage_eq_univ [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype α] {A : DFA Q α} (hE : A.IsEulerian) (hSync : A.IsSynchronizing) :
    ∀ (d : ℕ) (S : Finset Q), S.Nonempty → Fintype.card Q - S.card ≤ d →
      ∃ w : List α, A.preimage S w = Finset.univ ∧ w.length ≤ d * (Fintype.card Q - 1) := by
  intro d
  induction d with
  | zero =>
    intro S _ hle
    have hcard_le : S.card ≤ Fintype.card Q := Finset.card_le_univ S
    have hcard_eq : S.card = Fintype.card Q := by omega
    have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S hcard_eq
    exact ⟨[], by rw [preimage_nil, hSuniv], by simp⟩
  | succ d ih =>
    intro S hS_ne hle
    by_cases hfull : S.card = Fintype.card Q
    · have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S hfull
      exact ⟨[], by rw [preimage_nil, hSuniv], Nat.zero_le _⟩
    · have hlt : S.card < Fintype.card Q :=
        lt_of_le_of_ne (Finset.card_le_univ S) hfull
      obtain ⟨u, hu_len, hu_gt⟩ := hE.exists_extending_word hSync hS_ne hlt
      set S' : Finset Q := A.preimage S u
      have hS'_ne : S'.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hpos : 0 < S.card := hS_ne.card_pos
        rw [show S'.card = 0 by simp [hemp]] at hu_gt
        omega
      have hS'_diff : Fintype.card Q - S'.card ≤ d := by omega
      obtain ⟨v, hv_univ, hv_len⟩ := ih S' hS'_ne hS'_diff
      refine ⟨v ++ u, ?_, ?_⟩
      · rw [preimage_append]
        exact hv_univ
      · rw [List.length_append]
        calc
          v.length + u.length ≤ d * (Fintype.card Q - 1) + (Fintype.card Q - 1) :=
            Nat.add_le_add hv_len hu_len
          _ = (d + 1) * (Fintype.card Q - 1) := by ring

end Eulerian

end DFA

/-- **Kari's Theorem (2003)**: every synchronizing Eulerian DFA on `n ≥ 1` states admits a
synchronizing word of length at most `(n - 1) * (n - 2) + 1`. -/
theorem eulerian_reset_bound {Q : Type u} [Fintype Q] [Nonempty Q] [DecidableEq Q]
    {α : Type v} [Fintype α] (A : DFA Q α)
    (hE : A.IsEulerian) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ (Fintype.card Q - 1) * (Fintype.card Q - 2) + 1 := by
  by_cases h1 : Fintype.card Q ≤ 1
  · obtain ⟨q₀⟩ := ‹Nonempty Q›
    have hsub : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp h1
    refine ⟨[], ⟨q₀, fun q => Subsingleton.elim _ _⟩, ?_⟩
    simp
  · have h2 : 2 ≤ Fintype.card Q := by omega
    obtain ⟨q₀, a₀, hge2⟩ := DFA.exists_letter_card_preimage_ge_two A hSync h2
    set S₀ : Finset Q := A.preimage {q₀} [a₀]
    have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨w, hw_univ, hw_len⟩ :=
      hE.exists_preimage_eq_univ hSync (Fintype.card Q - 2) S₀ hS₀_ne (by omega)
    refine ⟨w ++ [a₀], ?_, ?_⟩
    · rw [DFA.isSyncWord_iff_exists_preimage_eq_univ]
      refine ⟨q₀, ?_⟩
      rw [DFA.preimage_append]
      exact hw_univ
    · rw [List.length_append, List.length_singleton]
      calc
        w.length + 1 ≤ (Fintype.card Q - 2) * (Fintype.card Q - 1) + 1 :=
          Nat.add_le_add_right hw_len 1
        _ = (Fintype.card Q - 1) * (Fintype.card Q - 2) + 1 := by ring

/-- **Černý Conjecture for Eulerian Automata** (corollary of Kari 2003): every synchronizing
Eulerian DFA on `n ≥ 1` states admits a synchronizing word of length at most `(n - 1) ^ 2`. -/
theorem eulerian_cerny {Q : Type u} [Fintype Q] [Nonempty Q] [DecidableEq Q]
    {α : Type v} [Fintype α] (A : DFA Q α)
    (hE : A.IsEulerian) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  by_cases h1 : Fintype.card Q ≤ 1
  · obtain ⟨q₀⟩ := ‹Nonempty Q›
    have hsub : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp h1
    exact ⟨[], ⟨q₀, fun q => Subsingleton.elim _ _⟩, by simp⟩
  · obtain ⟨w, hw, hlen⟩ := eulerian_reset_bound A hE hSync
    refine ⟨w, hw, hlen.trans ?_⟩
    have h2 : 2 ≤ Fintype.card Q := by omega
    have hsub : Fintype.card Q - 1 = (Fintype.card Q - 2) + 1 := by omega
    rw [sq, hsub]
    nlinarith

end Cerny
