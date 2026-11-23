import Cerny.Defs
import Cerny.ClusterBalanced

/-!
# Dubuc's Theorem for Circular Synchronizing Automata (1998)

This file deduces Louis Dubuc's 1998 theorem proving the Černý Conjecture for all synchronizing
circular automata as the `c = 1` (single-cycle) corollary of our Cluster-Balanced Equal-Cycle
Spectral Descent theorem (`Cerny.clusterBalanced_equalCycle_cerny`), lifting from finite
alphabets to arbitrary (possibly infinite) alphabets `α` via finite sub-alphabet restriction.

## Main results

- `Cerny.circular_exists_extending_word`: Dubuc's `1`-extensibility theorem — every nonempty
  proper subset `S ⊂ Q` of a synchronizing circular DFA admits an extending word `w` of length
  at most `Fintype.card Q`.
- `Cerny.circular_cerny`: **Dubuc's Theorem (1998)** — every synchronizing circular DFA on
  `n ≥ 1` states (over an arbitrary alphabet `α`) admits a synchronizing word of length at
  most `(n - 1) ^ 2`.
- `Cerny.circular_resetThreshold_le`: reset-threshold formulation `A.resetThreshold hSync ≤ (n - 1) ^ 2`.
-/

namespace Cerny

universe u v

namespace Circular

section Helpers

variable {Q : Type u} {α : Type v}

/-- Restrict a DFA `A` to a finite subset of letters `S_α : Finset α`. -/
def restrictDFA (A : DFA Q α) (S_α : Finset α) : DFA Q S_α where
  step q x := A.step q x.val

private lemma restrictDFA_eval (A : DFA Q α) (S_α : Finset α) (q : Q) (w : List S_α) :
    (restrictDFA A S_α).eval q w = A.eval q (w.map Subtype.val) := by
  induction w generalizing q with
  | nil => rfl
  | cons x u ih =>
    rw [DFA.eval_cons, List.map_cons, DFA.eval_cons, ih]
    rfl

private lemma restrictDFA_preimage [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S_α : Finset α)
    (T : Finset Q) (w : List S_α) :
    (restrictDFA A S_α).preimage T w = A.preimage T (w.map Subtype.val) := by
  ext q
  simp only [DFA.mem_preimage, restrictDFA_eval]

private lemma lift_word (S_α : Finset α) :
    ∀ w : List α, (∀ x ∈ w, x ∈ S_α) → ∃ w' : List S_α, w'.map Subtype.val = w
  | [], _ => ⟨[], rfl⟩
  | x :: u, hw => by
    have hx : x ∈ S_α := hw x (by simp)
    obtain ⟨u', hu'⟩ := lift_word S_α u (fun y hy => hw y (by simp [hy]))
    exact ⟨⟨x, hx⟩ :: u', by simp [hu']⟩

/-- A circular letter `a` acts as an equal-cycle permutation of exact cycle length `|Q|`. -/
private lemma isEqualCyclePerm_of_circular [Fintype Q] [Nonempty Q] (A : DFA Q α) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (htrans : ∀ p q : Q, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) :
    A.IsEqualCyclePerm a (Fintype.card Q) := by
  classical
  let f : Q → Q := fun q => A.step q a
  have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos
  refine ⟨hpos, hbij, fun q => ?_⟩
  have hlt_ne : ∀ k : ℕ, 0 < k → k < Fintype.card Q → f^[k] q ≠ q := by
    intro k hk0 hkn hfix
    have hmul : ∀ t : ℕ, f^[k * t] q = q := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hfix]
    have hmod : ∀ t : ℕ, f^[t] q = f^[t % k] q := by
      intro t
      have hdiv : t = t % k + k * (t / k) := by
        have := Nat.div_add_mod t k
        omega
      conv_lhs => rw [hdiv, Function.iterate_add_apply, hmul]
    have hsub : (Finset.univ : Finset Q) ⊆ (Finset.range k).image (fun j => f^[j] q) := by
      intro p _
      obtain ⟨t, rfl⟩ := htrans q p
      rw [Finset.mem_image]
      exact ⟨t % k, Finset.mem_range.mpr (Nat.mod_lt t hk0), (hmod t).symm⟩
    have hcard_le : Fintype.card Q ≤ k := by
      calc
        Fintype.card Q = (Finset.univ : Finset Q).card := Finset.card_univ.symm
        _ ≤ ((Finset.range k).image (fun j => f^[j] q)).card := Finset.card_le_card hsub
        _ ≤ (Finset.range k).card := Finset.card_image_le
        _ = k := Finset.card_range k
    omega
  refine ⟨hlt_ne, ?_⟩
  let g : Fin (Fintype.card Q) → Q := fun i => f^[i.val] q
  have hg_inj : Function.Injective g := by
    intro i j hij
    dsimp only [g] at hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have hsplit : j.val = i.val + (j.val - i.val) := by omega
      rw [hsplit, Function.iterate_add_apply] at hij
      have hfix : f^[j.val - i.val] q = q := (hbij.1.iterate i.val) hij.symm
      exact hlt_ne (j.val - i.val) (by omega) (by omega) hfix
    · have hsplit : i.val = j.val + (i.val - j.val) := by omega
      rw [hsplit, Function.iterate_add_apply] at hij
      have hfix : f^[i.val - j.val] q = q := (hbij.1.iterate j.val) hij
      exact hlt_ne (i.val - j.val) (by omega) (by omega) hfix
  have hg_surj : Function.Surjective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_inj, Fintype.card_fin _⟩ |>.2
  obtain ⟨i, hi⟩ := hg_surj (f^[Fintype.card Q] q)
  dsimp only [g] at hi
  by_cases hi0 : i.val = 0
  · rw [hi0, Function.iterate_zero_apply] at hi
    exact hi.symm
  · have hsplit : Fintype.card Q = i.val + (Fintype.card Q - i.val) := by omega
    have hiter : f^[Fintype.card Q] q = f^[i.val] (f^[Fintype.card Q - i.val] q) := by
      rw [← Function.iterate_add_apply, ← hsplit]
    rw [hiter] at hi
    have hfix : f^[Fintype.card Q - i.val] q = q := (hbij.1.iterate i.val) hi.symm
    exact absurd hfix (hlt_ne (Fintype.card Q - i.val) (by omega) (by omega))

/-- Every circular DFA on a finite alphabet is vacuously cluster-balanced (`c = 1`, `C₁ = Q`)
with uniform weights `β = 1`. -/
private lemma isClusterBalanced_of_circular [Fintype Q] [Fintype α] [DecidableEq Q] [DecidableEq α]
    (A : DFA Q α) (a : α)
    (hbij : Function.Bijective (fun q => A.step q a))
    (htrans : ∀ p q : Q, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) :
    A.IsClusterBalanced a := by
  refine ⟨hbij, fun _ => (1 : ℝ), fun _ _ => zero_lt_one, fun q₀ => ?_⟩
  have hC_univ :
      @Finset.filter Q (fun q => ∃ k : ℕ, (fun x => A.step x a)^[k] q₀ = q)
        (Classical.decPred _) Finset.univ = Finset.univ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact htrans q₀ q
  dsimp only
  rw [hC_univ]
  simp [DFA.preimage_univ]

end Helpers

end Circular

/-- **Dubuc's `1`-Extensibility Theorem (1998)**: In any synchronizing circular DFA on `n` states
(over an arbitrary alphabet `α`), every nonempty proper subset `S ⊂ Q` admits an extending word
`w` of length at most `n` with `|S w⁻¹| > |S|`. -/
theorem circular_exists_extending_word {Q : Type u} [Fintype Q] [Nonempty Q] [DecidableEq Q]
    {α : Type v} (A : DFA Q α) (hCirc : A.IsCircular) (hSync : A.IsSynchronizing)
    {S : Finset Q} (hS_ne : S.Nonempty) (hS_lt : S.card < Fintype.card Q) :
    ∃ w : List α, w.length ≤ Fintype.card Q ∧ S.card < (A.preimage S w).card := by
  classical
  rcases hCirc with ⟨a, hbij, htrans⟩
  rcases hSync with ⟨w₀, q₀, hq₀⟩
  let S_α : Finset α := insert a w₀.toFinset
  let A' : DFA Q S_α := Circular.restrictDFA A S_α
  let a' : S_α := ⟨a, Finset.mem_insert_self a _⟩
  have hbij' : Function.Bijective (fun q => A'.step q a') := hbij
  have htrans' : ∀ p q : Q, ∃ k : ℕ, (fun x => A'.step x a')^[k] p = q := htrans
  have hCB' : A'.IsClusterBalanced a' :=
    Circular.isClusterBalanced_of_circular A' a' hbij' htrans'
  have hEq' : A'.IsEqualCyclePerm a' (Fintype.card Q) :=
    Circular.isEqualCyclePerm_of_circular A' a' hbij' htrans'
  have hSync' : A'.IsSynchronizing := by
    obtain ⟨w₀', hw₀'⟩ := Circular.lift_word S_α w₀
      (fun x hx => Finset.mem_insert_of_mem (List.mem_toFinset.mpr hx))
    refine ⟨w₀', q₀, fun q => ?_⟩
    rw [Circular.restrictDFA_eval, hw₀', hq₀ q]
  obtain ⟨w', hw'_len, hw'_gt⟩ :=
    clusterBalanced_equalCycle_exists_extending_word A' a' (Fintype.card Q) hCB' hEq' hSync'
      hS_ne hS_lt
  refine ⟨w'.map Subtype.val, by simpa using hw'_len, ?_⟩
  rwa [Circular.restrictDFA_preimage] at hw'_gt

/-- **Dubuc's Theorem (1998)**: Every synchronizing circular DFA on `n ≥ 1` states (over an
arbitrary alphabet `α`) admits a synchronizing word of length at most `(n - 1) ^ 2`. -/
theorem circular_cerny {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : DFA Q α)
    (hCirc : A.IsCircular) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  rcases hCirc with ⟨a, hbij, htrans⟩
  rcases hSync with ⟨w₀, q₀, hq₀⟩
  let S_α : Finset α := insert a w₀.toFinset
  let A' : DFA Q S_α := Circular.restrictDFA A S_α
  let a' : S_α := ⟨a, Finset.mem_insert_self a _⟩
  have hbij' : Function.Bijective (fun q => A'.step q a') := hbij
  have htrans' : ∀ p q : Q, ∃ k : ℕ, (fun x => A'.step x a')^[k] p = q := htrans
  have hCB' : A'.IsClusterBalanced a' :=
    Circular.isClusterBalanced_of_circular A' a' hbij' htrans'
  have hEq' : A'.IsEqualCyclePerm a' (Fintype.card Q) :=
    Circular.isEqualCyclePerm_of_circular A' a' hbij' htrans'
  have hSync' : A'.IsSynchronizing := by
    obtain ⟨w₀', hw₀'⟩ := Circular.lift_word S_α w₀
      (fun x hx => Finset.mem_insert_of_mem (List.mem_toFinset.mpr hx))
    refine ⟨w₀', q₀, fun q => ?_⟩
    rw [Circular.restrictDFA_eval, hw₀', hq₀ q]
  obtain ⟨w', ⟨q_sync, hq_sync⟩, hw'_len⟩ :=
    clusterBalanced_equalCycle_cerny A' a' (Fintype.card Q) hCB' hEq' hSync'
  refine ⟨w'.map Subtype.val, ⟨q_sync, fun q => ?_⟩, by simpa using hw'_len⟩
  rw [← Circular.restrictDFA_eval A S_α q w']
  exact hq_sync q

/-- Reset-threshold formulation of Dubuc's Theorem (1998). -/
theorem circular_resetThreshold_le {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v}
    (A : DFA Q α) (hCirc : A.IsCircular) (hSync : A.IsSynchronizing) :
    A.resetThreshold hSync ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ := circular_cerny A hCirc hSync
  exact (A.resetThreshold_le_of_isSyncWord hSync hw).trans hlen

end Cerny
