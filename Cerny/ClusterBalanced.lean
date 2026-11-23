import Cerny.Defs
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity

/-!
# Cluster-Balanced Permutation Automata & Multi-Cycle Spectral Descent (Theorems B & C)

This file formalizes the Unified Multi-Cycle Permutation Spectral Descent engine and proves:

- **Theorem C (`clusterBalanced_equalCycle_cerny`)**: Exact Černý Conjecture `(n - 1) ^ 2` for
  every synchronizing cluster-balanced equal-cycle permutation DFA (`m₁ = ... = m_c = m`,
  `n = c * m`, arbitrary `c ≥ 1`), unifying Dubuc's circular theorem (`c = 1`) and
  pseudo-Eulerian / Kari-type automata (`c = n`) into one spectrum `1 ≤ c ≤ n`.
- **Theorem B (`clusterBalanced_reset_bound`, `clusterBalanced_quadratic_bound`)**: Universal
  quadratic bound `1 + (n - 2) * L(a) ≤ 2 * (n - 1) ^ 2 < 2 * n ^ 2` for ALL synchronizing
  cluster-balanced permutation DFAs with arbitrary cycle lengths `m₁ ≤ ... ≤ m_c` (no
  coprimality assumption required).
- **Lemma S.0 (`DFA.IsClusterBalanced.isStronglyConnected`)**: Every synchronizing
  cluster-balanced permutation DFA is automatically strongly connected.
-/

namespace Cerny

universe u v

/-! ### Public definitions: Equal-cycle and cluster-balanced permutation DFAs -/

namespace DFA

/-- Letter `a` acts as a permutation whose every orbit has the exact same length `m ≥ 1`. -/
def IsEqualCyclePerm {Q : Type u} {α : Type v} [Fintype Q] (A : DFA Q α) (a : α) (m : ℕ) : Prop :=
  1 ≤ m ∧
  Function.Bijective (fun q => A.step q a) ∧
  ∀ q : Q, (∀ k : ℕ, 0 < k → k < m → (fun x => A.step x a)^[k] q ≠ q) ∧
           (fun x => A.step x a)^[m] q = q

/-- A DFA is cluster-balanced with respect to a permutation letter `a` if there exist strictly
positive real weights `β` on `α \ {a}` such that every cycle `C` of `a` satisfies the weighted
balance identity `∑ f ≠ a, β f * |C f⁻¹| = (∑ f ≠ a, β f) * |C|` (equivalently, weighted
incoming transitions into `C` equal weighted outgoing transitions from `C`). -/
def IsClusterBalanced {Q : Type u} {α : Type v} [Fintype Q] [Fintype α] [DecidableEq Q]
    [DecidableEq α] (A : DFA Q α) (a : α) : Prop :=
  Function.Bijective (fun q => A.step q a) ∧
  ∃ β : α → ℝ, (∀ f : α, f ≠ a → 0 < β f) ∧
    ∀ q₀ : Q,
      let C : Finset Q :=
        @Finset.filter Q (fun q => ∃ k : ℕ, (fun x => A.step x a)^[k] q₀ = q)
          (Classical.decPred _) Finset.univ
      ∑ f ∈ Finset.univ.erase a, β f * ((A.preimage C [f]).card : ℝ) =
        (∑ f ∈ Finset.univ.erase a, β f) * (C.card : ℝ)

/-- Flow-balance characterization: for any subset `C` and letter `f`,
`|C f⁻¹| - |C| = |C f⁻¹ \ C| - |Cᶜ f⁻¹ ∩ C|`. -/
theorem card_preimage_sub_eq_flow {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (C : Finset Q) (f : α) :
    ((A.preimage C [f]).card : ℝ) - (C.card : ℝ) =
      ((A.preimage C [f] \ C).card : ℝ) - ((A.preimage Cᶜ [f] ∩ C).card : ℝ) := by
  have h1 : (A.preimage C [f] \ C).card + (A.preimage C [f] ∩ C).card =
      (A.preimage C [f]).card := Finset.card_sdiff_add_card_inter _ _
  have h2 : (A.preimage Cᶜ [f] ∩ C).card + (A.preimage C [f] ∩ C).card = C.card := by
    have hunion : (A.preimage Cᶜ [f] ∩ C) ∪ (A.preimage C [f] ∩ C) = C := by
      ext q
      simp only [Finset.mem_union, Finset.mem_inter, mem_preimage, eval_singleton,
        Finset.mem_compl]
      tauto
    have hdisj : Disjoint (A.preimage Cᶜ [f] ∩ C) (A.preimage C [f] ∩ C) := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      simp only [Finset.mem_inter, mem_preimage, Finset.mem_compl] at hq1 hq2
      exact hq1.1 hq2.1
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have h1r : ((A.preimage C [f] \ C).card : ℝ) + ((A.preimage C [f] ∩ C).card : ℝ) =
      ((A.preimage C [f]).card : ℝ) := by exact_mod_cast h1
  have h2r : ((A.preimage Cᶜ [f] ∩ C).card : ℝ) + ((A.preimage C [f] ∩ C).card : ℝ) =
      (C.card : ℝ) := by exact_mod_cast h2
  linarith

/-- Equivalence between `IsClusterBalanced` and weighted incoming = outgoing boundary flow
for every cycle of `a`. -/
theorem isClusterBalanced_iff_flow {Q : Type u} {α : Type v} [Fintype Q] [Fintype α]
    [DecidableEq Q] [DecidableEq α] (A : DFA Q α) (a : α) :
    A.IsClusterBalanced a ↔
      Function.Bijective (fun q => A.step q a) ∧
      ∃ β : α → ℝ, (∀ f : α, f ≠ a → 0 < β f) ∧
        ∀ q₀ : Q,
          let C : Finset Q :=
            @Finset.filter Q (fun q => ∃ k : ℕ, (fun x => A.step x a)^[k] q₀ = q)
              (Classical.decPred _) Finset.univ
          ∑ f ∈ Finset.univ.erase a, β f * ((A.preimage C [f] \ C).card : ℝ) =
            ∑ f ∈ Finset.univ.erase a, β f * ((A.preimage Cᶜ [f] ∩ C).card : ℝ) := by
  constructor <;> rintro ⟨hbij, β, hβ, hbal⟩ <;> refine ⟨hbij, β, hβ, fun q₀ => ?_⟩
  · set C : Finset Q :=
      @Finset.filter Q (fun q => ∃ k : ℕ, (fun x => A.step x a)^[k] q₀ = q)
        (Classical.decPred _) Finset.univ
    have hq : ∑ f ∈ Finset.univ.erase a, β f * ((A.preimage C [f]).card : ℝ) =
        (∑ f ∈ Finset.univ.erase a, β f) * (C.card : ℝ) := hbal q₀
    have hdiff :
        ∑ f ∈ Finset.univ.erase a,
          β f * (((A.preimage C [f]).card : ℝ) - (C.card : ℝ)) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      linarith
    have hflow :
        ∑ f ∈ Finset.univ.erase a,
          β f * (((A.preimage C [f] \ C).card : ℝ) - ((A.preimage Cᶜ [f] ∩ C).card : ℝ)) = 0 := by
      rw [← hdiff]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [card_preimage_sub_eq_flow]
    simp_rw [mul_sub, Finset.sum_sub_distrib] at hflow
    linarith
  · set C : Finset Q :=
      @Finset.filter Q (fun q => ∃ k : ℕ, (fun x => A.step x a)^[k] q₀ = q)
        (Classical.decPred _) Finset.univ
    have hq : ∑ f ∈ Finset.univ.erase a, β f * ((A.preimage C [f] \ C).card : ℝ) =
        ∑ f ∈ Finset.univ.erase a, β f * ((A.preimage Cᶜ [f] ∩ C).card : ℝ) := hbal q₀
    have hflow :
        ∑ f ∈ Finset.univ.erase a,
          β f * (((A.preimage C [f] \ C).card : ℝ) - ((A.preimage Cᶜ [f] ∩ C).card : ℝ)) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      linarith
    have hdiff :
        ∑ f ∈ Finset.univ.erase a,
          β f * (((A.preimage C [f]).card : ℝ) - (C.card : ℝ)) = 0 := by
      rw [← hflow]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [card_preimage_sub_eq_flow]
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hdiff
    linarith

end DFA

/-! ### Section 1: Cycle decomposition of a finite permutation -/

namespace ClusterBalanced

section PermCycles

variable {Q : Type u} [Fintype Q]

/-- Orbit (cycle) of `q` under a bijection `e : Q ≃ Q`. -/
noncomputable def orbitFinset (e : Q ≃ Q) (q : Q) : Finset Q := by
  classical
  exact Finset.univ.filter (fun p => ∃ k : ℕ, e^[k] q = p)

private lemma mem_orbitFinset (e : Q ≃ Q) (q p : Q) :
    p ∈ orbitFinset e q ↔ ∃ k : ℕ, e^[k] q = p := by
  classical
  simp [orbitFinset]

private lemma self_mem_orbitFinset (e : Q ≃ Q) (q : Q) : q ∈ orbitFinset e q :=
  (mem_orbitFinset e q q).mpr ⟨0, rfl⟩

private lemma orbitFinset_nonempty (e : Q ≃ Q) (q : Q) : (orbitFinset e q).Nonempty :=
  ⟨q, self_mem_orbitFinset e q⟩

private lemma exists_pos_iterate_eq (e : Q ≃ Q) (q : Q) : ∃ k : ℕ, 0 < k ∧ e^[k] q = q := by
  have hnot_inj : ¬ Function.Injective (fun i : Fin (Fintype.card Q + 1) => e^[i.val] q) := by
    intro hinj
    have hle := Fintype.card_le_of_injective _ hinj
    simp at hle
  simp only [Function.Injective, not_forall] at hnot_inj
  rcases hnot_inj with ⟨i, j, hij_eq, hij_ne⟩
  have hlt_or : i.val < j.val ∨ j.val < i.val := lt_or_gt_of_ne (Fin.val_ne_of_ne hij_ne)
  rcases hlt_or with hlt | hlt
  · refine ⟨j.val - i.val, by omega, ?_⟩
    have hsplit : j.val = i.val + (j.val - i.val) := by omega
    rw [hsplit, Function.iterate_add_apply] at hij_eq
    exact (e.injective.iterate i.val) hij_eq.symm
  · refine ⟨i.val - j.val, by omega, ?_⟩
    have hsplit : i.val = j.val + (i.val - j.val) := by omega
    rw [hsplit, Function.iterate_add_apply] at hij_eq
    exact (e.injective.iterate j.val) hij_eq

/-- Exact cycle length (order) of state `q` under `e`. -/
noncomputable def cycleLen (e : Q ≃ Q) (q : Q) : ℕ := by
  classical
  exact Nat.find (exists_pos_iterate_eq e q)

private lemma cycleLen_pos (e : Q ≃ Q) (q : Q) : 0 < cycleLen e q := by
  classical
  exact (Nat.find_spec (exists_pos_iterate_eq e q)).1

private lemma iterate_cycleLen (e : Q ≃ Q) (q : Q) : e^[cycleLen e q] q = q := by
  classical
  exact (Nat.find_spec (exists_pos_iterate_eq e q)).2

private lemma iterate_ne_of_lt_cycleLen (e : Q ≃ Q) (q : Q) {k : ℕ}
    (hk0 : 0 < k) (hkl : k < cycleLen e q) : e^[k] q ≠ q := by
  classical
  intro heq
  exact Nat.find_min (exists_pos_iterate_eq e q) hkl ⟨hk0, heq⟩

private lemma cycleLen_le_of_pos_iterate_eq (e : Q ≃ Q) (q : Q) {m : ℕ}
    (hm : 0 < m) (hfix : e^[m] q = q) : cycleLen e q ≤ m := by
  classical
  exact Nat.find_min' (exists_pos_iterate_eq e q) ⟨hm, hfix⟩

private lemma iterate_mul_cycleLen (e : Q ≃ Q) (q : Q) (t : ℕ) :
    e^[cycleLen e q * t] q = q := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, iterate_cycleLen]

private lemma iterate_mod_cycleLen (e : Q ≃ Q) (q : Q) (k : ℕ) :
    e^[k] q = e^[k % cycleLen e q] q := by
  have hdiv : k = k % cycleLen e q + cycleLen e q * (k / cycleLen e q) := by
    have := Nat.div_add_mod k (cycleLen e q)
    omega
  conv_lhs => rw [hdiv, Function.iterate_add_apply, iterate_mul_cycleLen]

private lemma iterate_cycleLen_inj (e : Q ≃ Q) (q : Q) :
    Function.Injective (fun i : Fin (cycleLen e q) => e^[i.val] q) := by
  intro i j hij
  dsimp only at hij
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · have hsplit : j.val = i.val + (j.val - i.val) := by omega
    rw [hsplit, Function.iterate_add_apply] at hij
    have hfix : e^[j.val - i.val] q = q := (e.injective.iterate i.val) hij.symm
    exact iterate_ne_of_lt_cycleLen e q (by omega) (by omega) hfix
  · have hsplit : i.val = j.val + (i.val - j.val) := by omega
    rw [hsplit, Function.iterate_add_apply] at hij
    have hfix : e^[i.val - j.val] q = q := (e.injective.iterate j.val) hij
    exact iterate_ne_of_lt_cycleLen e q (by omega) (by omega) hfix

private lemma orbitFinset_eq_image_fin [DecidableEq Q] (e : Q ≃ Q) (q : Q) :
    orbitFinset e q = Finset.univ.image (fun i : Fin (cycleLen e q) => e^[i.val] q) := by
  ext p
  rw [mem_orbitFinset, Finset.mem_image]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨⟨k % cycleLen e q, Nat.mod_lt k (cycleLen_pos e q)⟩, Finset.mem_univ _, ?_⟩
    exact (iterate_mod_cycleLen e q k).symm
  · rintro ⟨i, _, rfl⟩
    exact ⟨i.val, rfl⟩

private lemma card_orbitFinset (e : Q ≃ Q) (q : Q) :
    (orbitFinset e q).card = cycleLen e q := by
  classical
  rw [orbitFinset_eq_image_fin, Finset.card_image_of_injective _ (iterate_cycleLen_inj e q),
    Finset.card_univ, Fintype.card_fin]

private lemma mem_orbitFinset_symm (e : Q ≃ Q) {p q : Q} (hp : p ∈ orbitFinset e q) :
    q ∈ orbitFinset e p := by
  rw [mem_orbitFinset] at hp ⊢
  rcases hp with ⟨k, rfl⟩
  let m := cycleLen e q
  have hm : 0 < m := cycleLen_pos e q
  refine ⟨m - k % m, ?_⟩
  rw [iterate_mod_cycleLen e q k, ← Function.iterate_add_apply]
  have hsum : m - k % m + k % m = m := Nat.sub_add_cancel (Nat.mod_lt k hm).le
  rw [hsum]
  exact iterate_cycleLen e q

private lemma orbitFinset_eq_of_mem (e : Q ≃ Q) {p q : Q} (hp : p ∈ orbitFinset e q) :
    orbitFinset e p = orbitFinset e q := by
  have hq : q ∈ orbitFinset e p := mem_orbitFinset_symm e hp
  rw [mem_orbitFinset] at hp hq
  rcases hp with ⟨k₁, rfl⟩
  rcases hq with ⟨k₂, hk₂⟩
  ext x
  simp only [mem_orbitFinset]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j + k₁, by rw [Function.iterate_add_apply]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j + k₂, by rw [Function.iterate_add_apply, hk₂]⟩

private lemma cycleLen_eq_of_mem (e : Q ≃ Q) {p q : Q} (hp : p ∈ orbitFinset e q) :
    cycleLen e p = cycleLen e q := by
  rw [← card_orbitFinset, ← card_orbitFinset, orbitFinset_eq_of_mem e hp]

private lemma orbitFinset_step_mem (e : Q ≃ Q) {q p : Q} (hp : p ∈ orbitFinset e q) :
    e p ∈ orbitFinset e q := by
  rw [mem_orbitFinset] at hp ⊢
  rcases hp with ⟨k, rfl⟩
  exact ⟨k + 1, by rw [Function.iterate_succ_apply']⟩

private lemma orbitFinset_symm_step_mem (e : Q ≃ Q) {q p : Q} (hp : p ∈ orbitFinset e q) :
    e.symm p ∈ orbitFinset e q := by
  have hmem : e.symm p ∈ orbitFinset e p := by
    rw [mem_orbitFinset]
    let m := cycleLen e p
    have hm : 0 < m := cycleLen_pos e p
    refine ⟨m - 1, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply]
    have hsucc : e ((⇑e)^[m - 1] p) = (⇑e)^[m - 1 + 1] p :=
      (Function.iterate_succ_apply' (⇑e) (m - 1) p).symm
    rw [hsucc, Nat.sub_add_cancel hm]
    exact iterate_cycleLen e p
  rwa [orbitFinset_eq_of_mem e hp] at hmem

omit [Fintype Q] in
private lemma iterate_symm_cancel (e : Q ≃ Q) (k : ℕ) (x : Q) :
    e^[k] ((e.symm)^[k] x) = x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ih, e.apply_symm_apply]

omit [Fintype Q] in
private lemma symm_iterate_cancel (e : Q ≃ Q) (k : ℕ) (x : Q) :
    (e.symm)^[k] (e^[k] x) = x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ih, e.symm_apply_apply]

/-- The set of disjoint cycles (orbits) of `e : Q ≃ Q`. -/
noncomputable def orbits [DecidableEq Q] (e : Q ≃ Q) : Finset (Finset Q) :=
  Finset.univ.image (orbitFinset e)

private lemma mem_orbits_iff [DecidableEq Q] (e : Q ≃ Q) (C : Finset Q) :
    C ∈ orbits e ↔ ∃ q : Q, orbitFinset e q = C := by
  simp [orbits]

private lemma orbits_nonempty [DecidableEq Q] [Nonempty Q] (e : Q ≃ Q) : (orbits e).Nonempty := by
  obtain ⟨q⟩ := ‹Nonempty Q›
  exact ⟨orbitFinset e q, (mem_orbits_iff e _).mpr ⟨q, rfl⟩⟩

private lemma card_pos_of_mem_orbits [DecidableEq Q] (e : Q ≃ Q) {C : Finset Q}
    (hC : C ∈ orbits e) : 0 < C.card := by
  rcases (mem_orbits_iff e C).mp hC with ⟨q, rfl⟩
  exact (orbitFinset_nonempty e q).card_pos

private lemma disjoint_of_mem_orbits_ne [DecidableEq Q] (e : Q ≃ Q) {C₁ C₂ : Finset Q}
    (h₁ : C₁ ∈ orbits e) (h₂ : C₂ ∈ orbits e) (hne : C₁ ≠ C₂) : Disjoint C₁ C₂ := by
  rcases (mem_orbits_iff e C₁).mp h₁ with ⟨q₁, rfl⟩
  rcases (mem_orbits_iff e C₂).mp h₂ with ⟨q₂, rfl⟩
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  exact hne ((orbitFinset_eq_of_mem e hp₁).symm.trans (orbitFinset_eq_of_mem e hp₂))

private lemma biUnion_orbits [DecidableEq Q] (e : Q ≃ Q) : (orbits e).biUnion id = Finset.univ := by
  ext q
  simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
  exact ⟨orbitFinset e q, (mem_orbits_iff e _).mpr ⟨q, rfl⟩, self_mem_orbitFinset e q⟩

private lemma sum_card_orbits [DecidableEq Q] (e : Q ≃ Q) :
    ∑ C ∈ orbits e, C.card = Fintype.card Q := by
  have h := Finset.card_biUnion (s := orbits e) (t := id) (fun C₁ h₁ C₂ h₂ hne =>
    disjoint_of_mem_orbits_ne e h₁ h₂ hne)
  rw [biUnion_orbits, Finset.card_univ] at h
  exact h.symm

/-- Least common multiple of all cycle lengths of `e`. -/
noncomputable def permOrder [DecidableEq Q] (e : Q ≃ Q) : ℕ :=
  (orbits e).lcm Finset.card

private lemma permOrder_pos [DecidableEq Q] [Nonempty Q] (e : Q ≃ Q) : 0 < permOrder e := by
  by_contra h0
  have hzero : permOrder e = 0 := by omega
  have hex : ∃ C' ∈ orbits e, C'.card = 0 := Finset.lcm_eq_zero_iff.mp hzero
  rcases hex with ⟨C', hC', hC'0⟩
  have := card_pos_of_mem_orbits e hC'
  omega

private lemma dvd_permOrder [DecidableEq Q] (e : Q ≃ Q) {C : Finset Q} (hC : C ∈ orbits e) :
    C.card ∣ permOrder e :=
  Finset.dvd_lcm hC

private lemma iterate_permOrder [DecidableEq Q] (e : Q ≃ Q) (q : Q) : e^[permOrder e] q = q := by
  have hC : orbitFinset e q ∈ orbits e := (mem_orbits_iff e _).mpr ⟨q, rfl⟩
  obtain ⟨t, ht⟩ := dvd_permOrder e hC
  rw [ht, card_orbitFinset]
  exact iterate_mul_cycleLen e q t

private lemma iterate_symm_permOrder [DecidableEq Q] (e : Q ≃ Q) (q : Q) :
    (e.symm)^[permOrder e] q = q := by
  apply (e.injective.iterate (permOrder e))
  rw [iterate_symm_cancel, iterate_permOrder]

private lemma card_orbit_eq_of_isEqualCyclePerm [DecidableEq Q] {α : Type v}
    (A : DFA Q α) (a : α) (m : ℕ) (heq : A.IsEqualCyclePerm a m)
    (e : Q ≃ Q) (he : ∀ q, A.step q a = e q) {C : Finset Q} (hC : C ∈ orbits e) :
    C.card = m := by
  rcases (mem_orbits_iff e C).mp hC with ⟨q₀, rfl⟩
  rw [card_orbitFinset]
  have hfn : (fun x => A.step x a) = e := funext he
  rcases heq with ⟨hm1, _, hord⟩
  rcases hord q₀ with ⟨hmin, hfix⟩
  rw [hfn] at hmin hfix
  apply le_antisymm
  · exact cycleLen_le_of_pos_iterate_eq e q₀ (by omega) hfix
  · by_contra hlt
    exact hmin (cycleLen e q₀) (cycleLen_pos e q₀) (by omega) (iterate_cycleLen e q₀)

end PermCycles

end ClusterBalanced

/-! ### Lemma S.0: Automatic strong connectivity for cluster-balanced permutation DFAs -/

namespace DFA

/-- **Lemma S.0**: Every synchronizing cluster-balanced permutation DFA is strongly connected. -/
theorem IsClusterBalanced.isStronglyConnected {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q] [DecidableEq α]
    {A : DFA Q α} {a : α} (hCB : A.IsClusterBalanced a) (hSync : A.IsSynchronizing) :
    A.IsStronglyConnected := by
  classical
  rcases hCB with ⟨hbij, β, hβ, hbal⟩
  let e : Q ≃ Q := Equiv.ofBijective (fun q => A.step q a) hbij
  have he : ∀ q, A.step q a = e q := fun _ => rfl
  rcases hSync with ⟨w₀, q₀, hq₀⟩
  let K : Finset Q := Finset.univ.filter (fun q => ∃ u : List α, A.eval q₀ u = q)
  have hq₀K : q₀ ∈ K := by
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨[], rfl⟩
  have hK_step : ∀ p ∈ K, ∀ g : α, A.step p g ∈ K := by
    intro p hp g
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rcases hp with ⟨u, hu⟩
    exact ⟨u ++ [g], by rw [eval_append, hu, eval_singleton]⟩
  have hK_iter : ∀ p ∈ K, ∀ k : ℕ, e^[k] p ∈ K := by
    intro p hp k
    induction k with
    | zero => exact hp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hK_step _ ih a
  let I : Finset (Finset Q) := (ClusterBalanced.orbits e).filter (fun C => C ⊆ K)
  have hK_eq_biUnion : K = I.biUnion id := by
    ext q
    simp only [I, Finset.mem_biUnion, Finset.mem_filter, id_eq]
    constructor
    · intro hqK
      refine ⟨ClusterBalanced.orbitFinset e q,
        ⟨(ClusterBalanced.mem_orbits_iff e _).mpr ⟨q, rfl⟩, ?_⟩,
        ClusterBalanced.self_mem_orbitFinset e q⟩
      intro p hp
      rw [ClusterBalanced.mem_orbitFinset] at hp
      rcases hp with ⟨k, rfl⟩
      exact hK_iter q hqK k
    · rintro ⟨C, ⟨_, hCK⟩, hqC⟩
      exact hCK hqC
  have hK_disj : (I : Set (Finset Q)).PairwiseDisjoint id := by
    intro C₁ h₁ C₂ h₂ hne
    simp only [I, Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    exact ClusterBalanced.disjoint_of_mem_orbits_ne e h₁.1 h₂.1 hne
  have hK_bal :
      ∑ f ∈ Finset.univ.erase a, β f * ((A.preimage K [f]).card : ℝ) =
        (∑ f ∈ Finset.univ.erase a, β f) * (K.card : ℝ) := by
    have hC_bal : ∀ C ∈ I,
        ∑ f ∈ Finset.univ.erase a, β f * ((A.preimage C [f]).card : ℝ) =
          (∑ f ∈ Finset.univ.erase a, β f) * (C.card : ℝ) := by
      intro C hC
      simp only [I, Finset.mem_filter] at hC
      rcases (ClusterBalanced.mem_orbits_iff e C).mp hC.1 with ⟨r, rfl⟩
      have hCeq :
          ClusterBalanced.orbitFinset e r =
            @Finset.filter Q (fun q => ∃ k : ℕ, (fun x => A.step x a)^[k] r = q)
              (Classical.decPred _) Finset.univ := by
        ext q
        simp [ClusterBalanced.mem_orbitFinset, he]
      rw [hCeq]
      exact hbal r
    have hK_card : (K.card : ℝ) = ∑ C ∈ I, (C.card : ℝ) := by
      rw [hK_eq_biUnion, Finset.card_biUnion hK_disj]
      push_cast
      rfl
    have hK_pre : ∀ f : α, ((A.preimage K [f]).card : ℝ) = ∑ C ∈ I, ((A.preimage C [f]).card : ℝ) := by
      intro f
      have hpre_eq : A.preimage K [f] = I.biUnion (fun C => A.preimage C [f]) := by
        ext q
        simp only [mem_preimage, hK_eq_biUnion, Finset.mem_biUnion, id_eq]
      have hpre_disj : (I : Set (Finset Q)).PairwiseDisjoint (fun C => A.preimage C [f]) := by
        intro C₁ h₁ C₂ h₂ hne
        change Disjoint (A.preimage C₁ [f]) (A.preimage C₂ [f])
        rw [Finset.disjoint_left]
        intro q hq₁ hq₂
        simp only [mem_preimage] at hq₁ hq₂
        exact Finset.disjoint_left.mp (hK_disj h₁ h₂ hne) hq₁ hq₂
      rw [hpre_eq, Finset.card_biUnion hpre_disj]
      push_cast
      rfl
    calc
      ∑ f ∈ Finset.univ.erase a, β f * ((A.preimage K [f]).card : ℝ)
          = ∑ f ∈ Finset.univ.erase a, β f * ∑ C ∈ I, ((A.preimage C [f]).card : ℝ) := by
            refine Finset.sum_congr rfl fun f _ => by rw [hK_pre f]
      _ = ∑ C ∈ I, ∑ f ∈ Finset.univ.erase a, β f * ((A.preimage C [f]).card : ℝ) := by
            simp_rw [Finset.mul_sum]
            exact Finset.sum_comm
      _ = ∑ C ∈ I, (∑ f ∈ Finset.univ.erase a, β f) * (C.card : ℝ) :=
            Finset.sum_congr rfl hC_bal
      _ = (∑ f ∈ Finset.univ.erase a, β f) * ∑ C ∈ I, (C.card : ℝ) := by
            rw [← Finset.mul_sum]
      _ = (∑ f ∈ Finset.univ.erase a, β f) * (K.card : ℝ) := by rw [hK_card]
  have hK_sub : ∀ g : α, K ⊆ A.preimage K [g] := by
    intro g p hp
    rw [mem_preimage, eval_singleton]
    exact hK_step p hp g
  have hK_pre_eq : ∀ g : α, A.preimage K [g] = K := by
    intro g
    by_cases hga : g = a
    · subst hga
      have hcard : (A.preimage K [g]).card = K.card := by
        have h1 : A.preimage K [g] = K.image e.symm := by
          ext q
          simp only [mem_preimage, eval_singleton, Finset.mem_image, he]
          exact ⟨fun h => ⟨e q, h, e.symm_apply_apply q⟩, fun ⟨r, hr, hreq⟩ => by
            rw [← hreq, e.apply_symm_apply]; exact hr⟩
        rw [h1, Finset.card_image_of_injective _ e.symm.injective]
      exact (Finset.eq_of_subset_of_card_le (hK_sub g) hcard.le).symm
    · have hsum_zero :
          ∑ f ∈ Finset.univ.erase a, β f * (((A.preimage K [f]).card : ℝ) - (K.card : ℝ)) = 0 := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        linarith
      have hnonneg : ∀ f ∈ Finset.univ.erase a,
          0 ≤ β f * (((A.preimage K [f]).card : ℝ) - (K.card : ℝ)) := by
        intro f hf
        have hβf : 0 < β f := hβ f (Finset.ne_of_mem_erase hf)
        have hle : (K.card : ℝ) ≤ ((A.preimage K [f]).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (hK_sub f)
        nlinarith
      have hall0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero
      have hg0 := hall0 g (Finset.mem_erase.mpr ⟨hga, Finset.mem_univ g⟩)
      have hβg : 0 < β g := hβ g hga
      have hcard_eq : (A.preimage K [g]).card = K.card := by
        have : ((A.preimage K [g]).card : ℝ) = (K.card : ℝ) := by nlinarith
        exact_mod_cast this
      exact (Finset.eq_of_subset_of_card_le (hK_sub g) hcard_eq.le).symm
  have hK_pre_word : ∀ u : List α, A.preimage K u = K := by
    intro u
    induction u with
    | nil => exact A.preimage_nil K
    | cons g u ih => rw [preimage_cons, ih, hK_pre_eq g]
  have hK_all : ∀ q : Q, q ∈ K := by
    intro q
    have hmem : q ∈ A.preimage K w₀ := by
      rw [mem_preimage, hq₀ q]
      exact hq₀K
    rwa [hK_pre_word w₀] at hmem
  intro p q
  have hqK := hK_all q
  simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hqK
  rcases hqK with ⟨u, hu⟩
  exact ⟨w₀ ++ u, by rw [eval_append, hq₀ p, hu]⟩

end DFA

namespace ClusterBalanced

/-! ### Section 2: Pushforward operator on `Q → ℂ` and zero-sum hyperplane `Z` -/

section DotSet

variable {Q : Type u}

/-- Pairing a vector `v : Q → ℂ` with the indicator of a subset `S : Finset Q`. -/
def dotSet (v : Q → ℂ) (S : Finset Q) : ℂ :=
  ∑ q ∈ S, v q

/-- All-ones vector `[Q]` in `Q → ℂ`. -/
def onesVec : Q → ℂ := fun _ => 1

private lemma dotSet_add (x y : Q → ℂ) (S : Finset Q) :
    dotSet (x + y) S = dotSet x S + dotSet y S :=
  Finset.sum_add_distrib

private lemma dotSet_sub (x y : Q → ℂ) (S : Finset Q) :
    dotSet (x - y) S = dotSet x S - dotSet y S := by
  simp [dotSet, Finset.sum_sub_distrib]

private lemma dotSet_smul (c : ℂ) (x : Q → ℂ) (S : Finset Q) :
    dotSet (c • x) S = c * dotSet x S := by
  simp [dotSet, Finset.mul_sum]

private lemma dotSet_sum {ι : Type*} (t : Finset ι) (f : ι → Q → ℂ) (S : Finset Q) :
    dotSet (∑ i ∈ t, f i) S = ∑ i ∈ t, dotSet (f i) S := by
  simp only [dotSet, Finset.sum_apply]
  exact Finset.sum_comm

private lemma dotSet_ones (S : Finset Q) : dotSet (onesVec (Q := Q)) S = (S.card : ℂ) := by
  simp [dotSet, onesVec]

end DotSet

section LinearSetup

variable {Q : Type u} {α : Type v} [Fintype Q]

/-- Coordinate-sum linear functional `v ↦ ∑ q, v q` on `Q → ℂ`. -/
def sumLin : (Q → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ q : Q, v q
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' c _ := by simp [Finset.mul_sum]

/-- Zero-sum hyperplane `Z = {v ∈ ℂ^Q : ∑ q, v q = 0}`. -/
def zeroSumSub : Submodule ℂ (Q → ℂ) :=
  LinearMap.ker (sumLin (Q := Q))

private lemma sumLin_eq_dotSet_univ (v : Q → ℂ) : sumLin v = dotSet v Finset.univ := rfl

private lemma finrank_zeroSumSub [Nonempty Q] :
    Module.finrank ℂ (zeroSumSub (Q := Q)) = Fintype.card Q - 1 := by
  classical
  have hsurj : Function.Surjective (sumLin (Q := Q)) := by
    intro c
    obtain ⟨q₀⟩ := ‹Nonempty Q›
    refine ⟨Pi.single q₀ c, ?_⟩
    simp [sumLin, Pi.single_apply]
  have hrange : LinearMap.range (sumLin (Q := Q)) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker (sumLin (Q := Q))
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_pi] at hrn
  change _ + Module.finrank ℂ zeroSumSub = _ at hrn
  omega

variable [DecidableEq Q]

/-- Pushforward linear operator on `Q → ℂ` corresponding to right multiplication by `P_w`. -/
def push (A : DFA Q α) (w : List α) : Module.End ℂ (Q → ℂ) where
  toFun v q := ∑ p ∈ Finset.univ.filter (fun p => A.eval p w = q), v p
  map_add' x y := by
    ext q
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    ext q
    simp [Finset.mul_sum]

private lemma push_nil (A : DFA Q α) : push A [] = 1 := by
  refine LinearMap.ext fun v => funext fun q => ?_
  simp only [push, LinearMap.coe_mk, AddHom.coe_mk, one_apply_eq_self]
  rw [Finset.sum_filter, Finset.sum_eq_single q]
  · simp
  · intro p _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma push_append (A : DFA Q α) (u v : List α) :
    push A (u ++ v) = push A v * push A u := by
  refine LinearMap.ext fun x => funext fun r => ?_
  simp only [mul_apply_eq_comp, push, LinearMap.coe_mk, AddHom.coe_mk]
  have h1 :
      ∑ q ∈ Finset.univ.filter (fun q => A.eval q v = r),
        ∑ p ∈ Finset.univ.filter (fun p => A.eval p u = q), x p =
      ∑ p ∈ Finset.univ,
        ∑ q ∈ Finset.univ, if A.eval q v = r ∧ A.eval p u = q then x p else 0 := by
    rw [Finset.sum_filter]
    have hstep :
        ∑ q ∈ Finset.univ,
          (if A.eval q v = r then ∑ p ∈ Finset.univ.filter (fun p => A.eval p u = q), x p else 0) =
        ∑ q ∈ Finset.univ,
          ∑ p ∈ Finset.univ, if A.eval q v = r ∧ A.eval p u = q then x p else 0 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_filter]
      by_cases hqv : A.eval q v = r
      · simp [hqv]
      · simp [hqv]
    rw [hstep, Finset.sum_comm]
  rw [h1, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hinner :
      ∑ q ∈ Finset.univ, (if A.eval q v = r ∧ A.eval p u = q then x p else 0) =
        if A.eval (A.eval p u) v = r then x p else 0 := by
    rw [Finset.sum_eq_single (A.eval p u)]
    · simp
    · intro q _ hne
      simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hinner, DFA.eval_append]

private lemma push_cons (A : DFA Q α) (a : α) (w : List α) :
    push A (a :: w) = push A w * push A [a] := by
  simpa using push_append A [a] w

private lemma push_replicate (A : DFA Q α) (k : ℕ) (a : α) :
    push A (List.replicate k a) = (push A [a]) ^ k := by
  induction k with
  | zero => simp [push_nil]
  | succ k ih =>
    rw [List.replicate_succ, push_cons, ih, pow_succ]

private lemma dotSet_push (A : DFA Q α) (w : List α) (v : Q → ℂ) (S : Finset Q) :
    dotSet (push A w v) S = dotSet v (A.preimage S w) := by
  simp only [dotSet, push, LinearMap.coe_mk, AddHom.coe_mk]
  calc
    ∑ q ∈ S, ∑ p ∈ Finset.univ.filter (fun p => A.eval p w = q), v p
        = ∑ q ∈ S, ∑ p ∈ Finset.univ, if A.eval p w = q then v p else 0 := by
          simp_rw [Finset.sum_filter]
    _ = ∑ p ∈ Finset.univ, ∑ q ∈ S, if A.eval p w = q then v p else 0 := Finset.sum_comm
    _ = ∑ p ∈ Finset.univ, if A.eval p w ∈ S then v p else 0 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases h : A.eval p w ∈ S
          · simp only [h, ↓reduceIte]
            rw [Finset.sum_eq_single (A.eval p w)]
            · simp
            · intro q _ hne; simp [hne.symm]
            · intro hn; exact absurd h hn
          · simp only [h, ↓reduceIte]
            refine Finset.sum_eq_zero fun q hq => ?_
            have hne : A.eval p w ≠ q := fun heq => h (heq ▸ hq)
            simp [hne]
    _ = ∑ p ∈ A.preimage S w, v p := by
          rw [DFA.preimage, Finset.sum_filter]

private lemma sumLin_push (A : DFA Q α) (w : List α) (v : Q → ℂ) :
    sumLin (push A w v) = sumLin v := by
  rw [sumLin_eq_dotSet_univ, dotSet_push, DFA.preimage_univ, ← sumLin_eq_dotSet_univ]

private lemma push_mem_zeroSumSub (A : DFA Q α) (w : List α) {v : Q → ℂ}
    (hv : v ∈ zeroSumSub) : push A w v ∈ zeroSumSub := by
  change sumLin (push A w v) = 0
  rw [sumLin_push]
  exact hv

private lemma push_perm_apply (A : DFA Q α) (a : α) (e : Q ≃ Q)
    (he : ∀ q, A.step q a = e q) (v : Q → ℂ) (q : Q) :
    push A [a] v q = v (e.symm q) := by
  simp only [push, LinearMap.coe_mk, AddHom.coe_mk, DFA.eval_singleton, he]
  rw [Finset.sum_filter, Finset.sum_eq_single (e.symm q)]
  · simp
  · intro p _ hne
    have : e p ≠ q := fun h => hne (by rw [← h, e.symm_apply_apply])
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma push_perm_pow_apply (A : DFA Q α) (a : α) (e : Q ≃ Q)
    (he : ∀ q, A.step q a = e q) (k : ℕ) (v : Q → ℂ) (q : Q) :
    ((push A [a]) ^ k) v q = v ((e.symm)^[k] q) := by
  induction k generalizing q with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, push_perm_apply A a e he, ih, Function.iterate_succ_apply]

private lemma push_perm_ones (A : DFA Q α) (a : α) (e : Q ≃ Q)
    (he : ∀ q, A.step q a = e q) :
    push A [a] onesVec = onesVec := by
  ext q
  rw [push_perm_apply A a e he]
  rfl

private lemma push_perm_pow_ones (A : DFA Q α) (a : α) (e : Q ≃ Q)
    (he : ∀ q, A.step q a = e q) (k : ℕ) :
    ((push A [a]) ^ k) onesVec = onesVec := by
  ext q
  rw [push_perm_pow_apply A a e he]
  rfl

private lemma push_perm_pow_permOrder (A : DFA Q α) (a : α) (e : Q ≃ Q)
    (he : ∀ q, A.step q a = e q) :
    (push A [a]) ^ permOrder e = 1 := by
  refine LinearMap.ext fun v => funext fun q => ?_
  rw [push_perm_pow_apply A a e he, iterate_symm_permOrder, one_apply_eq_self]

end LinearSetup

/-! ### Section 3: Explicit CRT-free Fourier projectors & exact multiplicity matching (Lemma S.1) -/

section Fourier

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- Explicit Fourier spectral projector `E_k = (1/M) ∑_{j < M} (ζ^k)^{-j} T^j`. -/
noncomputable def fourierProj (T : Module.End ℂ (Q → ℂ)) (M : ℕ) (ζ : ℂ) (k : Fin M) :
    Module.End ℂ (Q → ℂ) :=
  ((M : ℂ)⁻¹) • ∑ j : Fin M, ((ζ ^ (k : ℕ))⁻¹ ^ (j : ℕ)) • (T ^ (j : ℕ))

omit [Fintype Q] [DecidableEq Q] in
private lemma fourierProj_mul_T {T : Module.End ℂ (Q → ℂ)} {M : ℕ} {ζ : ℂ}
    (hM : 0 < M) (hTM : T ^ M = 1) (hζ : IsPrimitiveRoot ζ M) (k : Fin M) :
    fourierProj T M ζ k * T = (ζ ^ (k : ℕ)) • fourierProj T M ζ k := by
  have hζkM : (ζ ^ (k : ℕ)) ^ M = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hζk_ne : ζ ^ (k : ℕ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.ne_of_gt hM)] at hζkM
    exact zero_ne_one hζkM
  rw [fourierProj, Algebra.smul_mul_assoc, smul_comm (ζ ^ (k : ℕ))]
  congr 1
  rw [Finset.sum_mul, Finset.smul_sum]
  let shift : Fin M ≃ Fin M :=
    { toFun := fun j => ⟨(j.val + 1) % M, Nat.mod_lt _ hM⟩
      invFun := fun j => ⟨(j.val + M - 1) % M, Nat.mod_lt _ hM⟩
      left_inv := fun j => by
        ext
        dsimp only
        have hj := j.isLt
        by_cases h : j.val + 1 < M
        · rw [Nat.mod_eq_of_lt h, show j.val + 1 + M - 1 = j.val + M by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hj]
        · have h1 : j.val + 1 = M := by omega
          rw [h1, Nat.mod_self, show 0 + M - 1 = j.val by omega, Nat.mod_eq_of_lt hj]
      right_inv := fun j => by
        ext
        dsimp only
        have hj := j.isLt
        by_cases h0 : j.val = 0
        · rw [h0, show 0 + M - 1 = M - 1 by omega]
          have hlt1 : M - 1 < M := by omega
          rw [Nat.mod_eq_of_lt hlt1, show M - 1 + 1 = M by omega, Nat.mod_self]
        · rw [show j.val + M - 1 = (j.val - 1) + M by omega, Nat.add_mod_right]
          have hlt2 : j.val - 1 < M := by omega
          rw [Nat.mod_eq_of_lt hlt2, show j.val - 1 + 1 = j.val by omega, Nat.mod_eq_of_lt hj] }
  rw [← Fintype.sum_equiv shift
    (fun j => ((ζ ^ (k : ℕ))⁻¹ ^ (j : ℕ) • T ^ (j : ℕ)) * T)
    (fun j => (ζ ^ (k : ℕ)) • (((ζ ^ (k : ℕ))⁻¹ ^ (j : ℕ)) • T ^ (j : ℕ)))]
  intro j
  rw [Algebra.smul_mul_assoc, smul_smul, ← pow_succ]
  have hj := j.isLt
  by_cases h : j.val + 1 < M
  · have hs : (shift j).val = j.val + 1 := Nat.mod_eq_of_lt h
    rw [hs]
    congr 1
    rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ hζk_ne, one_mul]
  · have h1 : j.val + 1 = M := by omega
    have hs : (shift j).val = 0 := by simp [shift, h1]
    rw [hs, pow_zero, pow_zero, mul_one, h1, hTM]
    congr 1
    have hinv : (ζ ^ (k : ℕ))⁻¹ ^ M = 1 := by rw [inv_pow, hζkM, inv_one]
    have hmul : (ζ ^ (k : ℕ))⁻¹ ^ j.val * (ζ ^ (k : ℕ))⁻¹ = 1 := by
      rw [← pow_succ, h1, hinv]
    calc
      (ζ ^ (k : ℕ))⁻¹ ^ j.val = (ζ ^ (k : ℕ))⁻¹ ^ j.val * ((ζ ^ (k : ℕ))⁻¹ * ζ ^ (k : ℕ)) := by
        rw [inv_mul_cancel₀ hζk_ne, mul_one]
      _ = ((ζ ^ (k : ℕ))⁻¹ ^ j.val * (ζ ^ (k : ℕ))⁻¹) * ζ ^ (k : ℕ) := by ring
      _ = ζ ^ (k : ℕ) := by rw [hmul, one_mul]

omit [Fintype Q] [DecidableEq Q] in
private lemma fourierProj_mul_T_pow {T : Module.End ℂ (Q → ℂ)} {M : ℕ} {ζ : ℂ}
    (hM : 0 < M) (hTM : T ^ M = 1) (hζ : IsPrimitiveRoot ζ M) (k : Fin M) (h : ℕ) :
    fourierProj T M ζ k * T ^ h = (ζ ^ (k : ℕ)) ^ h • fourierProj T M ζ k := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ, ← mul_assoc, ih, Algebra.smul_mul_assoc, fourierProj_mul_T hM hTM hζ,
      smul_smul, pow_succ]

omit [Fintype Q] [DecidableEq Q] in
private lemma T_mul_fourierProj {T : Module.End ℂ (Q → ℂ)} {M : ℕ} {ζ : ℂ}
    (hM : 0 < M) (hTM : T ^ M = 1) (hζ : IsPrimitiveRoot ζ M) (k : Fin M) :
    T * fourierProj T M ζ k = (ζ ^ (k : ℕ)) • fourierProj T M ζ k := by
  have hcomm : T * fourierProj T M ζ k = fourierProj T M ζ k * T := by
    simp only [fourierProj, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_succ', ← pow_succ]
  rw [hcomm, fourierProj_mul_T hM hTM hζ]

omit [Fintype Q] [DecidableEq Q] in
private lemma T_pow_mul_fourierProj {T : Module.End ℂ (Q → ℂ)} {M : ℕ} {ζ : ℂ}
    (hM : 0 < M) (hTM : T ^ M = 1) (hζ : IsPrimitiveRoot ζ M) (k : Fin M) (h : ℕ) :
    T ^ h * fourierProj T M ζ k = (ζ ^ (k : ℕ)) ^ h • fourierProj T M ζ k := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ', mul_assoc, ih, Algebra.mul_smul_comm, T_mul_fourierProj hM hTM hζ,
      smul_smul, pow_succ', mul_comm]

omit [Fintype Q] [DecidableEq Q] in
private lemma sum_fourierProj {T : Module.End ℂ (Q → ℂ)} {M : ℕ} {ζ : ℂ}
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ M) :
    ∑ k : Fin M, fourierProj T M ζ k = 1 := by
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  simp only [fourierProj, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ j : Fin M,
      ∑ k : Fin M, ((ζ ^ (k : ℕ))⁻¹ ^ (j : ℕ)) • (T ^ (j : ℕ)) =
        (if j.val = 0 then (M : ℂ) else 0) • (T ^ (j : ℕ)) := by
    intro j
    rw [← Finset.sum_smul]
    congr 1
    have hrew : ∀ k : Fin M, (ζ ^ (k : ℕ))⁻¹ ^ (j : ℕ) = ((ζ⁻¹) ^ (j : ℕ)) ^ (k : ℕ) := by
      intro k
      rw [inv_pow, ← pow_mul, mul_comm, pow_mul, ← inv_pow, ← inv_pow]
    simp_rw [hrew]
    rw [Fin.sum_univ_eq_sum_range (fun k => ((ζ⁻¹) ^ (j : ℕ)) ^ k) M]
    by_cases hj0 : j.val = 0
    · simp [hj0]
    · simp only [hj0, ↓reduceIte]
      have hne1 : (ζ⁻¹) ^ (j : ℕ) ≠ 1 := by
        intro heq
        have h1 : ζ ^ (j : ℕ) = 1 := by
          have := congrArg Inv.inv heq
          simpa [inv_pow] using this
        have hdvd : M ∣ j.val := hζ.dvd_of_pow_eq_one j.val h1
        have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hdvd
        omega
      rw [geom_sum_eq hne1]
      have hpowM : ((ζ⁻¹) ^ (j : ℕ)) ^ M = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζ.pow_eq_one, inv_one, one_pow]
      rw [hpowM, sub_self, zero_div]
  simp_rw [hinner]
  rw [Finset.sum_eq_single ⟨0, hM⟩]
  · simp [hMne]
  · intro j _ hne
    have hj0 : j.val ≠ 0 := fun h => hne (Fin.ext h)
    simp [hj0]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype Q] [DecidableEq Q] in
private lemma fourierProj_mul_fourierProj {T : Module.End ℂ (Q → ℂ)} {M : ℕ} {ζ : ℂ}
    (hM : 0 < M) (hTM : T ^ M = 1) (hζ : IsPrimitiveRoot ζ M) (k l : Fin M) :
    fourierProj T M ζ k * fourierProj T M ζ l = if k = l then fourierProj T M ζ k else 0 := by
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  conv_lhs => rhs; unfold fourierProj
  rw [Algebra.mul_smul_comm, Finset.mul_sum]
  have hterm : ∀ j : Fin M,
      fourierProj T M ζ k * (((ζ ^ (l : ℕ))⁻¹ ^ (j : ℕ)) • T ^ (j : ℕ)) =
        ((ζ ^ (k : ℕ) * (ζ ^ (l : ℕ))⁻¹) ^ (j : ℕ)) • fourierProj T M ζ k := by
    intro j
    rw [Algebra.mul_smul_comm, fourierProj_mul_T_pow hM hTM hζ, smul_smul, mul_pow, mul_comm]
  simp_rw [hterm, ← Finset.sum_smul, smul_smul]
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ (k : ℕ) * (ζ ^ (l : ℕ))⁻¹) ^ j) M]
  by_cases hkl : k = l
  · subst hkl
    have hne0 : ζ ^ (k : ℕ) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (Nat.ne_of_gt hM))
    simp [mul_inv_cancel₀ hne0, hMne]
  · simp only [hkl, ↓reduceIte]
    have hne1 : ζ ^ (k : ℕ) * (ζ ^ (l : ℕ))⁻¹ ≠ 1 := by
      intro heq
      have hne0 : ζ ^ (l : ℕ) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (Nat.ne_of_gt hM))
      have hpow_eq : ζ ^ (k : ℕ) = ζ ^ (l : ℕ) := by
        calc
          ζ ^ (k : ℕ) = (ζ ^ (k : ℕ) * (ζ ^ (l : ℕ))⁻¹) * ζ ^ (l : ℕ) := by
            rw [mul_assoc, inv_mul_cancel₀ hne0, mul_one]
          _ = ζ ^ (l : ℕ) := by rw [heq, one_mul]
      have hk_eq := hζ.injOn_pow (Finset.mem_coe.mpr (Finset.mem_range.mpr k.isLt))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr l.isLt)) hpow_eq
      exact hkl (Fin.ext hk_eq)
    rw [geom_sum_eq hne1]
    have hpowM : (ζ ^ (k : ℕ) * (ζ ^ (l : ℕ))⁻¹) ^ M = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, mul_comm (k : ℕ), pow_mul, hζ.pow_eq_one, one_pow,
        ← pow_mul, mul_comm (l : ℕ), pow_mul, hζ.pow_eq_one, one_pow, inv_one, mul_one]
    rw [hpowM, sub_self, zero_div, mul_zero, zero_smul]

omit [Fintype Q] [DecidableEq Q] in
private lemma fourierProj_mem_invariant {T : Module.End ℂ (Q → ℂ)} {M : ℕ} {ζ : ℂ}
    {W : Submodule ℂ (Q → ℂ)} (hW : ∀ v ∈ W, T v ∈ W) (k : Fin M) {v : Q → ℂ} (hv : v ∈ W) :
    fourierProj T M ζ k v ∈ W := by
  have hpow : ∀ j : ℕ, (T ^ j) v ∈ W := by
    intro j
    induction j with
    | zero => simpa using hv
    | succ j ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact hW _ ih
  simp only [fourierProj, LinearMap.smul_apply, LinearMap.sum_apply]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => ?_)
  exact Submodule.smul_mem _ _ (hpow j.val)

/-! ### Exact eigenspace dimensions via disjoint cycle eigenvectors -/

/-- Multiplicity `ν(k)` = number of cycles `C` with `(ζ^k)^{|C|} = 1`. -/
noncomputable def eigMult (e : Q ≃ Q) (ζ : ℂ) (k : Fin (permOrder e)) : ℕ := by
  classical
  exact ((orbits e).filter (fun C => (ζ ^ (k : ℕ)) ^ C.card = 1)).card

/-- Zero-sum eigenspace multiplicity `d_k = ν(k)` for `k ≠ 0`, and `c - 1` for `k = 0`. -/
noncomputable def zEigMult (e : Q ≃ Q) (ζ : ℂ) (k : Fin (permOrder e)) : ℕ :=
  if k.val = 0 then (orbits e).card - 1 else eigMult e ζ k

private lemma sum_eigMult [Nonempty Q] (e : Q ≃ Q) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (permOrder e)) :
    ∑ k : Fin (permOrder e), eigMult e ζ k = Fintype.card Q := by
  classical
  set M := permOrder e
  have hM : 0 < M := permOrder_pos e
  calc
    ∑ k : Fin M, eigMult e ζ k
        = ∑ k : Fin M, ∑ C ∈ orbits e, if (ζ ^ (k : ℕ)) ^ C.card = 1 then 1 else 0 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [eigMult, Finset.card_filter]
    _ = ∑ C ∈ orbits e, ∑ k : Fin M, if (ζ ^ (k : ℕ)) ^ C.card = 1 then 1 else 0 :=
          Finset.sum_comm
    _ = ∑ C ∈ orbits e, C.card := by
          refine Finset.sum_congr rfl fun C hC => ?_
          rw [← Finset.card_filter]
          have hCpos : 0 < C.card := card_pos_of_mem_orbits e hC
          have hdvd : C.card ∣ M := dvd_permOrder e hC
          set step := M / C.card
          have hstep_mul : C.card * step = M := Nat.mul_div_cancel' hdvd
          have hstep_pos : 0 < step := Nat.div_pos (Nat.le_of_dvd hM hdvd) hCpos
          let emb : Fin C.card → Fin M := fun t =>
            ⟨t.val * step, by
              calc
                t.val * step < C.card * step := Nat.mul_lt_mul_of_pos_right t.isLt hstep_pos
                _ = M := hstep_mul⟩
          have hemb_inj : Function.Injective emb := by
            intro t₁ t₂ h
            have hval : t₁.val * step = t₂.val * step := congrArg Fin.val h
            exact Fin.ext (Nat.eq_of_mul_eq_mul_right hstep_pos hval)
          have hfilt_eq :
              Finset.univ.filter (fun k : Fin M => (ζ ^ (k : ℕ)) ^ C.card = 1) =
                Finset.univ.image emb := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · intro hpow
              rw [← pow_mul] at hpow
              have hdvdM : M ∣ k.val * C.card := hζ.dvd_of_pow_eq_one _ hpow
              have hdvd' : step * C.card ∣ k.val * C.card := by
                rwa [mul_comm step C.card, hstep_mul]
              have hstep_dvd : step ∣ k.val :=
                (Nat.mul_dvd_mul_iff_right hCpos).mp hdvd'
              rcases hstep_dvd with ⟨t, ht⟩
              have ht_lt : t < C.card := by
                have hklt : k.val < M := k.isLt
                rw [ht, ← hstep_mul, mul_comm C.card step] at hklt
                exact Nat.lt_of_mul_lt_mul_left hklt
              exact ⟨⟨t, ht_lt⟩, Fin.ext (by simp [emb, ht, mul_comm])⟩
            · rintro ⟨t, rfl⟩
              simp only [emb, ← pow_mul]
              rw [mul_assoc, mul_comm step C.card, hstep_mul, mul_comm t.val M, pow_mul,
                hζ.pow_eq_one, one_pow]
          rw [hfilt_eq, Finset.card_image_of_injective _ hemb_inj, Finset.card_univ,
            Fintype.card_fin]
    _ = Fintype.card Q := sum_card_orbits e

/-- Helper: index of `q ∈ C` along the orbit of a basepoint `q₀ ∈ C`. -/
private noncomputable def orbitIdx (e : Q ≃ Q) (q₀ : Q) (q : Q) (hq : q ∈ orbitFinset e q₀) :
    Fin (cycleLen e q₀) := by
  classical
  have hmem : q ∈ Finset.univ.image (fun i : Fin (cycleLen e q₀) => e^[i.val] q₀) := by
    rwa [← orbitFinset_eq_image_fin e q₀]
  exact (Finset.mem_image.mp hmem).choose

private lemma orbitIdx_spec (e : Q ≃ Q) (q₀ q : Q) (hq : q ∈ orbitFinset e q₀) :
    e^[(orbitIdx e q₀ q hq).val] q₀ = q := by
  classical
  have hmem : q ∈ Finset.univ.image (fun i : Fin (cycleLen e q₀) => e^[i.val] q₀) := by
    rwa [← orbitFinset_eq_image_fin e q₀]
  exact (Finset.mem_image.mp hmem).choose_spec.2

/-- Explicit eigenvector supported on cycle `C` for eigenvalue `ζ^k` (when `(ζ^k)^{|C|} = 1`). -/
noncomputable def cycleEigVec (e : Q ≃ Q) (ζ : ℂ) (C : Finset Q) (hC : C ∈ orbits e)
    (k : Fin (permOrder e)) : Q → ℂ := by
  classical
  let q₀ : Q := (Finset.card_pos.mp (card_pos_of_mem_orbits e hC)).choose
  have hq₀ : q₀ ∈ C := (Finset.card_pos.mp (card_pos_of_mem_orbits e hC)).choose_spec
  have hCeq : orbitFinset e q₀ = C := by
    rcases (mem_orbits_iff e C).mp hC with ⟨r, rfl⟩
    exact orbitFinset_eq_of_mem e hq₀
  exact fun q =>
    if hq : q ∈ C then
      (ζ ^ (k : ℕ))⁻¹ ^ (orbitIdx e q₀ q (hCeq.symm ▸ hq)).val
    else 0

private lemma push_cycleEigVec {α : Type v} (A : DFA Q α) (a : α) (e : Q ≃ Q)
    (he : ∀ q, A.step q a = e q) {ζ : ℂ} (hM : 0 < permOrder e)
    (hζ : IsPrimitiveRoot ζ (permOrder e))
    {C : Finset Q} (hC : C ∈ orbits e) {k : Fin (permOrder e)}
    (hpow : (ζ ^ (k : ℕ)) ^ C.card = 1) :
    push A [a] (cycleEigVec e ζ C hC k) = (ζ ^ (k : ℕ)) • cycleEigVec e ζ C hC k := by
  classical
  let q₀ : Q := (Finset.card_pos.mp (card_pos_of_mem_orbits e hC)).choose
  have hq₀ : q₀ ∈ C := (Finset.card_pos.mp (card_pos_of_mem_orbits e hC)).choose_spec
  have hCeq : orbitFinset e q₀ = C := by
    rcases (mem_orbits_iff e C).mp hC with ⟨r, rfl⟩
    exact orbitFinset_eq_of_mem e hq₀
  have hm_eq : cycleLen e q₀ = C.card := by
    rw [← card_orbitFinset, hCeq]
  have hζk_ne : ζ ^ (k : ℕ) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (Nat.ne_of_gt hM))
  ext q
  rw [push_perm_apply A a e he, Pi.smul_apply, smul_eq_mul]
  by_cases hq : q ∈ C
  · have hqs : e.symm q ∈ C := by
      rw [← hCeq] at hq ⊢
      exact orbitFinset_symm_step_mem e hq
    simp only [cycleEigVec, hq, hqs, ↓reduceDIte]
    set i₁ : Fin (cycleLen e q₀) := orbitIdx e q₀ (e.symm q) (hCeq.symm ▸ hqs)
    set i₂ : Fin (cycleLen e q₀) := orbitIdx e q₀ q (hCeq.symm ▸ hq)
    have hi₁ : e^[i₁.val] q₀ = e.symm q := orbitIdx_spec e q₀ (e.symm q) (hCeq.symm ▸ hqs)
    have hi₂ : e^[i₂.val] q₀ = q := orbitIdx_spec e q₀ q (hCeq.symm ▸ hq)
    have hstep : e^[i₁.val + 1] q₀ = e^[i₂.val] q₀ := by
      rw [Function.iterate_succ_apply', hi₁, e.apply_symm_apply, hi₂]
    by_cases hlt : i₁.val + 1 < cycleLen e q₀
    · have hi_eq : i₁.val + 1 = i₂.val := by
        have h := iterate_cycleLen_inj e q₀ (a₁ := ⟨i₁.val + 1, hlt⟩) (a₂ := i₂) hstep
        exact congrArg Fin.val h
      rw [← hi_eq, pow_succ', ← mul_assoc, mul_inv_cancel₀ hζk_ne, one_mul]
    · have htop : i₁.val + 1 = cycleLen e q₀ := by omega
      rw [htop, iterate_cycleLen] at hstep
      have hi₂_zero : i₂.val = 0 := by
        have h := iterate_cycleLen_inj e q₀ (a₁ := ⟨0, cycleLen_pos e q₀⟩) (a₂ := i₂) hstep
        exact (congrArg Fin.val h).symm
      rw [hi₂_zero, pow_zero, mul_one]
      have hinv_m : (ζ ^ (k : ℕ))⁻¹ ^ cycleLen e q₀ = 1 := by
        rw [inv_pow, hm_eq, hpow, inv_one]
      calc
        (ζ ^ (k : ℕ))⁻¹ ^ i₁.val
            = (ζ ^ (k : ℕ))⁻¹ ^ i₁.val * ((ζ ^ (k : ℕ))⁻¹ * ζ ^ (k : ℕ)) := by
              rw [inv_mul_cancel₀ hζk_ne, mul_one]
        _ = ((ζ ^ (k : ℕ))⁻¹ ^ (i₁.val + 1)) * ζ ^ (k : ℕ) := by rw [pow_succ]; ring
        _ = ζ ^ (k : ℕ) := by rw [htop, hinv_m, one_mul]
  · have hqs : e.symm q ∉ C := by
      intro hmem
      apply hq
      rw [← hCeq] at hmem ⊢
      have := orbitFinset_step_mem e hmem
      rwa [e.apply_symm_apply] at this
    simp [cycleEigVec, hq, hqs]

private lemma cycleEigVec_support_and_ne {e : Q ≃ Q} {ζ : ℂ}
    {C : Finset Q} (hC : C ∈ orbits e) (k : Fin (permOrder e)) :
    (∀ q, q ∉ C → cycleEigVec e ζ C hC k q = 0) ∧
    (∃ q ∈ C, cycleEigVec e ζ C hC k q ≠ 0) := by
  classical
  constructor
  · intro q hq
    simp [cycleEigVec, hq]
  · let q₀ : Q := (Finset.card_pos.mp (card_pos_of_mem_orbits e hC)).choose
    have hq₀ : q₀ ∈ C := (Finset.card_pos.mp (card_pos_of_mem_orbits e hC)).choose_spec
    have hCeq : orbitFinset e q₀ = C := by
      rcases (mem_orbits_iff e C).mp hC with ⟨r, rfl⟩
      exact orbitFinset_eq_of_mem e hq₀
    refine ⟨q₀, hq₀, ?_⟩
    simp only [cycleEigVec, hq₀, ↓reduceDIte]
    set i : Fin (cycleLen e q₀) := orbitIdx e q₀ q₀ (hCeq.symm ▸ hq₀)
    have hi : e^[i.val] q₀ = q₀ := orbitIdx_spec e q₀ q₀ (hCeq.symm ▸ hq₀)
    have hi0 : i.val = 0 := by
      have h := iterate_cycleLen_inj e q₀ (a₁ := i) (a₂ := ⟨0, cycleLen_pos e q₀⟩) hi
      exact congrArg Fin.val h
    rw [hi0, pow_zero]
    exact one_ne_zero

omit [DecidableEq Q] in
/-- Elementary sum-of-finranks identity for independent submodules indexed by a finite set. -/
private lemma sum_finrank_eq_finrank_biSup {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (V : ι → Submodule ℂ (Q → ℂ)) (hind : iSupIndep V) :
    ∑ i ∈ s, Module.finrank ℂ (V i) = Module.finrank ℂ (⨆ i ∈ s, V i : Submodule ℂ (Q → ℂ)) := by
  induction s using Finset.induction_on with
  | empty =>
    have hbot : (⨆ i ∈ (∅ : Finset ι), V i : Submodule ℂ (Q → ℂ)) = ⊥ := by simp
    rw [Finset.sum_empty, hbot, finrank_bot]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.iSup_insert]
    have hdisj : Disjoint (V a) (⨆ i ∈ s, V i) := by
      have h1 : Disjoint (V a) (⨆ i ≠ a, V i) := (iSupIndep_def.mp hind) a
      refine Disjoint.mono_right ?_ h1
      refine iSup₂_le fun i hi => ?_
      have hne : i ≠ a := fun h => ha (h ▸ hi)
      exact le_iSup₂_of_le i hne le_rfl
    have hinf : (V a ⊓ ⨆ i ∈ s, V i : Submodule ℂ (Q → ℂ)) = ⊥ :=
      disjoint_iff.mp hdisj
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq (V a) (⨆ i ∈ s, V i)
    rw [hinf, finrank_bot, add_zero] at hmod
    rw [ih, hmod]

/-- **Lemma S.1(3)**: Exact dimensions of every eigenspace `range (E_k)` and every zero-sum
eigenspace `range (E_k) ⊓ zeroSumSub`. -/
private lemma finrank_fourier_and_zeroSum {α : Type v} [Nonempty Q]
    (A : DFA Q α) (a : α) (e : Q ≃ Q) (he : ∀ q, A.step q a = e q)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (permOrder e)) :
    let T := push A [a]
    let M := permOrder e
    (∀ k : Fin M, Module.finrank ℂ (LinearMap.range (fourierProj T M ζ k)) = eigMult e ζ k) ∧
    (∀ k : Fin M,
      Module.finrank ℂ ((LinearMap.range (fourierProj T M ζ k) ⊓ zeroSumSub : Submodule ℂ (Q → ℂ))) =
        zEigMult e ζ k) := by
  classical
  intro T M
  have hM : 0 < M := permOrder_pos e
  have hTM : T ^ M = 1 := push_perm_pow_permOrder A a e he
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  -- Step 1: Lower bound `eigMult e ζ k ≤ finrank (range (E k))` via `cycleEigVec`.
  have hlb : ∀ k : Fin M,
      eigMult e ζ k ≤ Module.finrank ℂ (LinearMap.range (fourierProj T M ζ k)) := by
    intro k
    let S : Finset (Finset Q) := (orbits e).filter (fun C => (ζ ^ (k : ℕ)) ^ C.card = 1)
    let f : S → LinearMap.range (fourierProj T M ζ k) := fun ⟨C, hCS⟩ =>
      ⟨cycleEigVec e ζ C (Finset.mem_filter.mp hCS).1 k, by
        refine ⟨cycleEigVec e ζ C (Finset.mem_filter.mp hCS).1 k, ?_⟩
        have hC := (Finset.mem_filter.mp hCS).1
        have hpow := (Finset.mem_filter.mp hCS).2
        have hT : T (cycleEigVec e ζ C hC k) = (ζ ^ (k : ℕ)) • cycleEigVec e ζ C hC k :=
          push_cycleEigVec A a e he hM hζ hC hpow
        have hTpow : ∀ j : ℕ, (T ^ j) (cycleEigVec e ζ C hC k) =
            ((ζ ^ (k : ℕ)) ^ j) • cycleEigVec e ζ C hC k := by
          intro j
          induction j with
          | zero => simp
          | succ j ih =>
            rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hT, smul_smul, pow_succ', mul_comm]
        have hζk_ne : ζ ^ (k : ℕ) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (Nat.ne_of_gt hM))
        have hsum :
            (∑ j : Fin M, ((ζ ^ (k : ℕ))⁻¹ ^ (j : ℕ)) • (T ^ (j : ℕ)) (cycleEigVec e ζ C hC k)) =
              (M : ℂ) • cycleEigVec e ζ C hC k := by
          calc
            ∑ j : Fin M, ((ζ ^ (k : ℕ))⁻¹ ^ (j : ℕ)) • (T ^ (j : ℕ)) (cycleEigVec e ζ C hC k)
                = ∑ j : Fin M, ((ζ ^ (k : ℕ))⁻¹ ^ (j : ℕ) * (ζ ^ (k : ℕ)) ^ (j : ℕ)) •
                    cycleEigVec e ζ C hC k := by
                  refine Finset.sum_congr rfl fun j _ => by rw [hTpow, smul_smul]
            _ = ∑ _j : Fin M, cycleEigVec e ζ C hC k := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [← mul_pow, inv_mul_cancel₀ hζk_ne, one_pow, one_smul]
            _ = (M : ℂ) • cycleEigVec e ζ C hC k := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
        simp only [fourierProj, LinearMap.smul_apply, LinearMap.sum_apply]
        rw [hsum, smul_smul, inv_mul_cancel₀ hMne, one_smul]⟩
    have hli : LinearIndependent ℂ f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg ⟨C, hCS⟩
      have hC := (Finset.mem_filter.mp hCS).1
      obtain ⟨q, hqC, hq_ne⟩ := (cycleEigVec_support_and_ne hC k).2
      have hval := congrFun (congrArg Subtype.val hg) q
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Submodule.coe_zero, Pi.zero_apply] at hval
      rw [Finset.sum_eq_single ⟨C, hCS⟩] at hval
      · exact (mul_eq_zero.mp hval).resolve_right hq_ne
      · intro ⟨C', hC'S⟩ _ hne
        have hC' := (Finset.mem_filter.mp hC'S).1
        have hCne : C' ≠ C := fun heq => hne (Subtype.ext heq)
        have hdisj := disjoint_of_mem_orbits_ne e hC' hC hCne
        have hqnot : q ∉ C' := Finset.disjoint_right.mp hdisj hqC
        change g ⟨C', hC'S⟩ * cycleEigVec e ζ C' hC' k q = 0
        rw [(cycleEigVec_support_and_ne hC' k).1 q hqnot, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_coe] at hle
    simpa [S, eigMult] using hle
  -- Step 2: Independence of `range (E k)` gives `∑ k, finrank (range (E k)) ≤ card Q`.
  have hindep : iSupIndep (fun k : Fin M => LinearMap.range (fourierProj T M ζ k)) := by
    rw [iSupIndep_def]
    intro k
    rw [Submodule.disjoint_def]
    intro v hvk hv_rest
    rcases hvk with ⟨x, rfl⟩
    have hEk_self : fourierProj T M ζ k (fourierProj T M ζ k x) = fourierProj T M ζ k x := by
      have := congrArg (fun f => f x) (fourierProj_mul_fourierProj hM hTM hζ k k)
      simpa using this
    have hEk_zero : ∀ w ∈ (⨆ l ≠ k, LinearMap.range (fourierProj T M ζ l)),
        fourierProj T M ζ k w = 0 := by
      intro w hw
      have hle : (⨆ l ≠ k, LinearMap.range (fourierProj T M ζ l)) ≤
          LinearMap.ker (fourierProj T M ζ k) := by
        rw [iSup₂_le_iff]
        intro l hlk
        rintro _ ⟨y, rfl⟩
        change fourierProj T M ζ k (fourierProj T M ζ l y) = 0
        have := congrArg (fun f => f y) (fourierProj_mul_fourierProj hM hTM hζ k l)
        simpa [hlk.symm] using this
      exact hle hw
    rw [← hEk_self]
    exact hEk_zero _ hv_rest
  have hsum_le :
      ∑ k : Fin M, Module.finrank ℂ (LinearMap.range (fourierProj T M ζ k)) ≤ Fintype.card Q := by
    have hsum_eq :=
      sum_finrank_eq_finrank_biSup Finset.univ
        (fun k : Fin M => LinearMap.range (fourierProj T M ζ k)) hindep
    rw [hsum_eq]
    have hle := Submodule.finrank_le
      (⨆ k ∈ (Finset.univ : Finset (Fin M)), LinearMap.range (fourierProj T M ζ k))
    simpa [Module.finrank_pi] using hle
  -- Step 3: Tight equality for every `k : Fin M`!
  have heq_all : ∀ k : Fin M,
      Module.finrank ℂ (LinearMap.range (fourierProj T M ζ k)) = eigMult e ζ k := by
    have hsum1 : ∑ k : Fin M, eigMult e ζ k = Fintype.card Q := sum_eigMult e hζ
    have hsum2 : ∑ k : Fin M, eigMult e ζ k ≤
        ∑ k : Fin M, Module.finrank ℂ (LinearMap.range (fourierProj T M ζ k)) :=
      Finset.sum_le_sum fun k _ => hlb k
    have hsum_eq :
        ∑ k : Fin M, eigMult e ζ k =
          ∑ k : Fin M, Module.finrank ℂ (LinearMap.range (fourierProj T M ζ k)) :=
      le_antisymm hsum2 (hsum_le.trans hsum1.ge)
    have hall := (Finset.sum_eq_sum_iff_of_le (fun k _ => hlb k)).mp hsum_eq
    intro k
    exact (hall k (Finset.mem_univ k)).symm
  refine ⟨heq_all, ?_⟩
  -- Step 4: Zero-sum intersection dimension `d_k`.
  intro k
  by_cases hk0 : k.val = 0
  · simp only [zEigMult, hk0, ↓reduceIte]
    have hν0 : eigMult e ζ k = (orbits e).card := by
      simp [eigMult, hk0]
    let fZ : LinearMap.range (fourierProj T M ζ k) →ₗ[ℂ] ℂ :=
      sumLin.domRestrict (LinearMap.range (fourierProj T M ζ k))
    have hones_mem : onesVec (Q := Q) ∈ LinearMap.range (fourierProj T M ζ k) := by
      refine ⟨onesVec, ?_⟩
      simp only [fourierProj, hk0, pow_zero, inv_one, one_pow, one_smul,
        LinearMap.smul_apply, LinearMap.sum_apply]
      ext q
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      have h1 : ∀ j : Fin M, ((T ^ (j : ℕ)) onesVec) q = 1 := fun j => by
        rw [push_perm_pow_ones A a e he]; rfl
      simp [h1, hMne, onesVec]
    have hsurj : Function.Surjective fZ := by
      intro c
      have hcard_ne : (Fintype.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      refine ⟨(c / (Fintype.card Q : ℂ)) • ⟨onesVec, hones_mem⟩, ?_⟩
      change sumLin ((c / (Fintype.card Q : ℂ)) • onesVec) = c
      rw [map_smul, sumLin_eq_dotSet_univ, dotSet_ones, Finset.card_univ, smul_eq_mul,
        div_mul_cancel₀ _ hcard_ne]
    have hrange : LinearMap.range fZ = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have hrn := LinearMap.finrank_range_add_finrank_ker fZ
    rw [hrange, finrank_top, Module.finrank_self, heq_all k, hν0] at hrn
    have hker_eq : Module.finrank ℂ (LinearMap.ker fZ) =
        Module.finrank ℂ ((LinearMap.range (fourierProj T M ζ k) ⊓ zeroSumSub : Submodule ℂ (Q → ℂ))) := by
      let eKer : LinearMap.ker fZ ≃ₗ[ℂ]
          ↥((LinearMap.range (fourierProj T M ζ k) ⊓ zeroSumSub : Submodule ℂ (Q → ℂ))) :=
        { toFun := fun ⟨⟨v, hv1⟩, hv2⟩ => ⟨v, ⟨hv1, hv2⟩⟩
          invFun := fun ⟨v, ⟨hv1, hv2⟩⟩ => ⟨⟨v, hv1⟩, hv2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact eKer.finrank_eq
    omega
  · simp only [zEigMult, hk0, ↓reduceIte]
    have hleZ : LinearMap.range (fourierProj T M ζ k) ≤ zeroSumSub := by
      rintro _ ⟨v, rfl⟩
      change sumLin (fourierProj T M ζ k v) = 0
      have hTv : T (fourierProj T M ζ k v) = (ζ ^ (k : ℕ)) • fourierProj T M ζ k v := by
        have := congrArg (fun f => f v) (T_mul_fourierProj hM hTM hζ k)
        simpa using this
      have hsum_eq : sumLin (fourierProj T M ζ k v) =
          (ζ ^ (k : ℕ)) * sumLin (fourierProj T M ζ k v) := by
        calc
          sumLin (fourierProj T M ζ k v)
              = sumLin (T (fourierProj T M ζ k v)) := (sumLin_push A [a] _).symm
          _ = (ζ ^ (k : ℕ)) * sumLin (fourierProj T M ζ k v) := by
              rw [hTv, map_smul, smul_eq_mul]
      have hne1 : ζ ^ (k : ℕ) ≠ 1 := by
        intro h1
        have hdvd := hζ.dvd_of_pow_eq_one k.val h1
        have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd
        have := k.isLt
        omega
      have h0 : (1 - ζ ^ (k : ℕ)) * sumLin (fourierProj T M ζ k v) = 0 := by
        linear_combination hsum_eq
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne1.symm)
    rw [inf_eq_left.mpr hleZ, heq_all k]

/-- If `dotSet v C = 0` for every cycle `C` of `e`, then `fourierProj T M ζ 0 v = 0`. -/
private lemma fourierProj_zero_eq_zero_of_dotSet_cycles {α : Type v} [Nonempty Q]
    (A : DFA Q α) (a : α) (e : Q ≃ Q) (he : ∀ q, A.step q a = e q)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (permOrder e)) {v : Q → ℂ}
    (hC0 : ∀ C ∈ orbits e, dotSet v C = 0) :
    fourierProj (push A [a]) (permOrder e) ζ ⟨0, permOrder_pos e⟩ v = 0 := by
  let T := push A [a]
  let M := permOrder e
  have hM : 0 < M := permOrder_pos e
  have hTM : T ^ M = 1 := push_perm_pow_permOrder A a e he
  let w : Q → ℂ := fourierProj T M ζ ⟨0, hM⟩ v
  have hTw : T w = w := by
    have := congrArg (fun f => f v) (T_mul_fourierProj hM hTM hζ ⟨0, hM⟩)
    simpa [w] using this
  have hw_const : ∀ q (k : ℕ), w (e^[k] q) = w q := by
    intro q k
    induction k with
    | zero => rfl
    | succ k ih =>
      have h1 : w (e.symm (e^[k + 1] q)) = w (e^[k + 1] q) := by
        have := congrFun hTw (e^[k + 1] q)
        rwa [push_perm_apply A a e he] at this
      have h2 : e.symm (e^[k + 1] q) = e^[k] q := by
        rw [Function.iterate_succ_apply', e.symm_apply_apply]
      rw [h2] at h1
      rw [← h1, ih]
  have hdot_T : ∀ (j : ℕ) {C : Finset Q}, C ∈ orbits e → dotSet ((T ^ j) v) C = dotSet v C := by
    intro j C hC
    rw [← push_replicate, dotSet_push]
    congr 1
    ext q
    simp only [DFA.mem_preimage, DFA.eval_replicate]
    have hfn : (fun x => A.step x a) = e := funext he
    rw [hfn]
    rcases (mem_orbits_iff e C).mp hC with ⟨r, rfl⟩
    constructor
    · intro hmem
      have hback : ∀ n (x : Q), x ∈ orbitFinset e r → (e.symm)^[n] x ∈ orbitFinset e r := by
        intro n
        induction n with
        | zero => intro x hx; exact hx
        | succ n ih =>
          intro x hx
          rw [Function.iterate_succ_apply']
          exact orbitFinset_symm_step_mem e (ih x hx)
      have h := hback j (e^[j] q) hmem
      rwa [symm_iterate_cancel] at h
    · intro hq
      induction j with
      | zero => exact hq
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact orbitFinset_step_mem e ih
  ext q
  let C := orbitFinset e q
  have hC : C ∈ orbits e := (mem_orbits_iff e _).mpr ⟨q, rfl⟩
  have hdot_w : dotSet w C = 0 := by
    change dotSet (fourierProj T M ζ ⟨0, hM⟩ v) C = 0
    simp only [fourierProj, pow_zero, inv_one, one_pow, one_smul,
      LinearMap.smul_apply, LinearMap.sum_apply]
    rw [dotSet_smul, dotSet_sum]
    have hsum0 : ∑ j : Fin M, dotSet ((T ^ (j : ℕ)) v) C = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hdot_T j.val hC, hC0 C hC]
    rw [hsum0, mul_zero]
  have hconst_sum : dotSet w C = (C.card : ℂ) * w q := by
    rw [dotSet]
    have hall : ∀ p ∈ C, w p = w q := by
      intro p hp
      rw [mem_orbitFinset] at hp
      rcases hp with ⟨k, rfl⟩
      exact hw_const q k
    rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul]
  have hCne : (C.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (card_pos_of_mem_orbits e hC))
  rw [hconst_sum] at hdot_w
  exact (mul_eq_zero.mp hdot_w).resolve_left hCne

end Fourier

/-! ### Section 4: Characteristic polynomial `χ_Z`, reciprocal factorization, and Lemma S.4 -/

section PolyTools

open Polynomial

private lemma coeff_finset_sum {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Polynomial R) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

/-- Degree-`d` reciprocal polynomial `∑_{j ≤ d} p.coeff (d - j) * X^j`. -/
noncomputable def polyRev (d : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (d + 1), C (p.coeff (d - j)) * X ^ j

private lemma coeff_polyRev (d : ℕ) (p : Polynomial ℂ) (j : ℕ) :
    (polyRev d p).coeff j = if j ≤ d then p.coeff (d - j) else 0 := by
  rw [polyRev, coeff_finset_sum]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hj : j ≤ d
  · simp only [hj, ↓reduceIte]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · simp only [hj, ↓reduceIte]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi_lt := Finset.mem_range.mp hi
    have hne : j ≠ i := by omega
    simp [hne]

private lemma coeff_polyRev_eq_zero_of_gt (d : ℕ) (p : Polynomial ℂ) {k : ℕ} (hk : d < k) :
    (polyRev d p).coeff k = 0 := by
  rw [coeff_polyRev]
  have hnot : ¬ k ≤ d := by omega
  simp [hnot]

private lemma polyRev_mul {d₁ d₂ : ℕ} {p q : Polynomial ℂ}
    (hp : ∀ k, d₁ < k → p.coeff k = 0) (hq : ∀ k, d₂ < k → q.coeff k = 0) :
    polyRev d₁ p * polyRev d₂ q = polyRev (d₁ + d₂) (p * q) := by
  ext k
  rw [coeff_mul, coeff_polyRev]
  by_cases hk : k ≤ d₁ + d₂
  · simp only [hk, ↓reduceIte, coeff_mul]
    let A := (Finset.antidiagonal k).filter (fun x => x.1 ≤ d₁ ∧ x.2 ≤ d₂)
    let B := (Finset.antidiagonal (d₁ + d₂ - k)).filter (fun y => y.1 ≤ d₁ ∧ y.2 ≤ d₂)
    have hL :
        ∑ x ∈ Finset.antidiagonal k, (polyRev d₁ p).coeff x.1 * (polyRev d₂ q).coeff x.2 =
          ∑ x ∈ A, p.coeff (d₁ - x.1) * q.coeff (d₂ - x.2) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal k)
        (fun x => x.1 ≤ d₁ ∧ x.2 ≤ d₂)]
      have hzero :
          ∑ x ∈ (Finset.antidiagonal k).filter (fun x => ¬ (x.1 ≤ d₁ ∧ x.2 ≤ d₂)),
            (polyRev d₁ p).coeff x.1 * (polyRev d₂ q).coeff x.2 = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hnot := (Finset.mem_filter.mp hx).2
        by_cases h1 : x.1 ≤ d₁
        · have h2 : ¬ x.2 ≤ d₂ := fun h2 => hnot ⟨h1, h2⟩
          simp [coeff_polyRev, h2]
        · simp [coeff_polyRev, h1]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hcond := (Finset.mem_filter.mp hx).2
      simp [coeff_polyRev, hcond.1, hcond.2]
    have hR :
        ∑ y ∈ Finset.antidiagonal (d₁ + d₂ - k), p.coeff y.1 * q.coeff y.2 =
          ∑ y ∈ B, p.coeff y.1 * q.coeff y.2 := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal (d₁ + d₂ - k))
        (fun y => y.1 ≤ d₁ ∧ y.2 ≤ d₂)]
      have hzero :
          ∑ y ∈ (Finset.antidiagonal (d₁ + d₂ - k)).filter (fun y => ¬ (y.1 ≤ d₁ ∧ y.2 ≤ d₂)),
            p.coeff y.1 * q.coeff y.2 = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        have hnot := (Finset.mem_filter.mp hy).2
        by_cases h1 : y.1 ≤ d₁
        · have h2 : d₂ < y.2 := by omega
          rw [hq y.2 h2, mul_zero]
        · have h1' : d₁ < y.1 := by omega
          rw [hp y.1 h1', zero_mul]
      rw [hzero, add_zero]
    rw [hL, hR]
    refine Finset.sum_nbij (fun x => (d₁ - x.1, d₂ - x.2)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [A, B, Finset.mem_filter, Finset.mem_antidiagonal] at hx ⊢
      omega
    · intro x hx y hy heq
      simp only [A, Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal] at hx hy
      have h1 : d₁ - x.1 = d₁ - y.1 := congrArg Prod.fst heq
      have h2 : d₂ - x.2 = d₂ - y.2 := congrArg Prod.snd heq
      exact Prod.ext (by omega) (by omega)
    · intro y hy
      simp only [A, B, Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal] at hy ⊢
      refine ⟨(d₁ - y.1, d₂ - y.2), ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal]
        omega
      · dsimp only
        exact Prod.ext (by omega) (by omega)
    · intro x _
      rfl
  · simp only [hk, ↓reduceIte]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hsum : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
    by_cases h1 : x.1 ≤ d₁
    · have h2 : ¬ x.2 ≤ d₂ := by omega
      simp [coeff_polyRev, h2]
    · simp [coeff_polyRev, h1]

private lemma coeff_mul_eq_zero_of_gt {d₁ d₂ : ℕ} {p q : Polynomial ℂ}
    (hp : ∀ k, d₁ < k → p.coeff k = 0) (hq : ∀ k, d₂ < k → q.coeff k = 0) :
    ∀ k, d₁ + d₂ < k → (p * q).coeff k = 0 := by
  intro k hk
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hsum : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
  by_cases h1 : d₁ < x.1
  · rw [hp x.1 h1, zero_mul]
  · have h2 : d₂ < x.2 := by omega
    rw [hq x.2 h2, mul_zero]

private lemma polyRev_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (d : ι → ℕ) (f : ι → Polynomial ℂ)
    (hf : ∀ i ∈ s, ∀ k, d i < k → (f i).coeff k = 0) :
    polyRev (∑ i ∈ s, d i) (∏ i ∈ s, f i) = ∏ i ∈ s, polyRev (d i) (f i) ∧
    (∀ k, (∑ i ∈ s, d i) < k → (∏ i ∈ s, f i).coeff k = 0) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · ext k
      simp [coeff_polyRev, coeff_one]
    · intro k hk
      simp only [Finset.sum_empty] at hk
      rw [Finset.prod_empty, coeff_one]
      have hne : k ≠ 0 := by omega
      simp [hne]
  | insert a s ha ih =>
    have hf_s : ∀ i ∈ s, ∀ k, d i < k → (f i).coeff k = 0 :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hf_a : ∀ k, d a < k → (f a).coeff k = 0 := hf a (Finset.mem_insert_self a s)
    obtain ⟨ih_rev, ih_deg⟩ := ih hf_s
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    refine ⟨?_, coeff_mul_eq_zero_of_gt hf_a ih_deg⟩
    rw [← polyRev_mul hf_a ih_deg, ih_rev]

private lemma polyRev_X_sub_C (c : ℂ) :
    polyRev 1 (X - C c) = 1 - C c * X := by
  ext k
  rw [coeff_polyRev]
  rcases k with _ | _ | k
  · simp [coeff_X, coeff_C]
  · simp [coeff_one, coeff_X, coeff_C]
  · have hnot : ¬ k + 2 ≤ 1 := by omega
    simp [hnot, coeff_one]

private lemma polyRev_X_pow_sub_one {m : ℕ} (hm : 0 < m) :
    polyRev m (X ^ m - 1 : Polynomial ℂ) = 1 - X ^ m := by
  ext k
  rw [coeff_polyRev, coeff_sub, coeff_one, coeff_X_pow]
  by_cases hk : k ≤ m
  · simp only [hk, ↓reduceIte, coeff_sub, coeff_X_pow, coeff_one]
    by_cases hk0 : k = 0
    · have hm0 : m ≠ 0 := by omega
      have hm0' : 0 ≠ m := by omega
      simp [hk0, hm0, hm0']
    · by_cases hkm : k = m
      · have h0m : m ≠ 0 := by omega
        have h0m' : 0 ≠ m := by omega
        simp [hkm, h0m, h0m']
      · have h1 : m - k ≠ m := by omega
        have h2 : m - k ≠ 0 := by omega
        simp [hk0, hkm, h1, h2]
  · simp only [hk, ↓reduceIte]
    rw [coeff_sub, coeff_one, coeff_X_pow]
    split_ifs <;> first | omega | ring

private lemma polyRev_geomSum {m : ℕ} (hm : 0 < m) :
    polyRev (m - 1) (∑ j ∈ Finset.range m, (X ^ j : Polynomial ℂ)) =
      ∑ j ∈ Finset.range m, (X ^ j : Polynomial ℂ) := by
  ext k
  rw [coeff_polyRev, coeff_finset_sum, coeff_finset_sum]
  simp_rw [coeff_X_pow]
  by_cases hk : k ≤ m - 1
  · simp only [hk, ↓reduceIte]
    have h1 : (∑ j ∈ Finset.range m, if m - 1 - k = j then (1 : ℂ) else 0) = 1 := by
      rw [Finset.sum_eq_single (m - 1 - k)]
      · simp
      · intro j _ hne; simp [hne.symm]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    have h2 : (∑ j ∈ Finset.range m, if k = j then (1 : ℂ) else 0) = 1 := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hne; simp [hne.symm]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [h1, h2]
  · simp only [hk, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj_lt := Finset.mem_range.mp hj
    have hne : k ≠ j := by omega
    simp [hne]

/-- `1 - X^m = ∏_{t : Fin m} (1 - ω^t * X)` for any primitive `m`-th root of unity `ω`. -/
private lemma one_sub_X_pow_eq_prod {m : ℕ} (hm : 0 < m) {ω : ℂ} (hω : IsPrimitiveRoot ω m) :
    (1 - X ^ m : Polynomial ℂ) = ∏ t : Fin m, (1 - C (ω ^ t.val) * X) := by
  let P : Polynomial ℂ := X ^ m - 1
  have hP_monic : P.Monic := monic_X_pow_sub_C 1 (Nat.ne_of_gt hm)
  have hP_ne : P ≠ 0 := hP_monic.ne_zero
  have hP_deg : P.natDegree = m := by
    have h1 : P = X ^ m - C (1 : ℂ) := by simp [P]
    rw [h1]
    exact natDegree_X_pow_sub_C (n := m) (a := (1 : ℂ))
  let f : Fin m → ℂ := fun t => ω ^ t.val
  have hf_inj : Function.Injective f := by
    intro t₁ t₂ heq
    exact Fin.ext (hω.injOn_pow (Finset.mem_coe.mpr (Finset.mem_range.mpr t₁.isLt))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr t₂.isLt)) heq)
  let S : Finset ℂ := Finset.univ.image f
  have hS_card : S.card = m := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  have hS_le : S.val ≤ P.roots := by
    rw [Multiset.le_iff_count]
    intro a
    by_cases ha : a ∈ S
    · have hcnt1 : Multiset.count a S.val = 1 :=
        Multiset.count_eq_one_of_mem S.nodup ha
      rw [hcnt1]
      have ha_root : a ∈ P.roots := by
        rw [mem_roots hP_ne]
        rcases Finset.mem_image.mp ha with ⟨t, _, rfl⟩
        simp only [P, f, IsRoot.def, eval_sub, eval_pow, eval_X, eval_one]
        rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self]
      exact Multiset.one_le_count_iff_mem.mpr ha_root
    · have hcnt0 : Multiset.count a S.val = 0 := Multiset.count_eq_zero.mpr ha
      rw [hcnt0]
      exact Nat.zero_le _
  have hroots_eq : P.roots = S.val := by
    refine (Multiset.eq_of_le_of_card_le hS_le ?_).symm
    have hle := card_roots' P
    rw [hP_deg] at hle
    exact hle.trans (by simp [hS_card])
  have hprod_X : ∏ t : Fin m, (X - C (ω ^ t.val)) = P := by
    have hcard_roots : P.roots.card = P.natDegree := by
      rw [hroots_eq, hP_deg]
      simp [hS_card]
    have hfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP_monic hcard_roots
    rw [hroots_eq] at hfac
    change (S.val.map (fun a => X - C a)).prod = P at hfac
    rw [← hfac]
    have himg : ∏ a ∈ S, (X - C a) = ∏ t : Fin m, (X - C (f t)) :=
      Finset.prod_image (f := fun a => X - C a) (g := f) (fun x _ y _ h => hf_inj h)
    exact himg.symm
  have hrev_prod := (polyRev_prod (Finset.univ : Finset (Fin m)) (fun _ => 1)
    (fun t => X - C (ω ^ t.val)) (fun t _ k hk => by
      rw [coeff_sub, coeff_X, coeff_C]
      have h0 : k ≠ 0 := by omega
      have h1 : 1 ≠ k := by omega
      simp [h0, h1])).1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hrev_prod
  rw [hprod_X, polyRev_X_pow_sub_one hm] at hrev_prod
  rw [hrev_prod]
  refine Finset.prod_congr rfl fun t _ => polyRev_X_sub_C _

/-- Coefficient-wise congruence for polynomial multiplication up to degree `D`. -/
private lemma coeff_mul_congr_of_le {D : ℕ} {p₁ p₂ q₁ q₂ : Polynomial ℂ}
    (hp : ∀ i ≤ D, p₁.coeff i = p₂.coeff i)
    (hq : ∀ i ≤ D, q₁.coeff i = q₂.coeff i) :
    ∀ j ≤ D, (p₁ * q₁).coeff j = (p₂ * q₂).coeff j := by
  intro j hj
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hsum : x.1 + x.2 = j := Finset.mem_antidiagonal.mp hx
  rw [hp x.1 (by omega), hq x.2 (by omega)]

/-- Finite set of `m`-tuples of natural numbers summing to `s`. -/
def tuplesWithSum (m s : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset (fun _ : Fin m => Finset.range (s + 1))).filter (fun hs => ∑ i, hs i = s)

private lemma mem_tuplesWithSum (m s : ℕ) (hs : Fin m → ℕ) :
    hs ∈ tuplesWithSum m s ↔ ∑ i, hs i = s := by
  simp only [tuplesWithSum, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    and_iff_right_iff_imp]
  intro hsum i
  have hle : hs i ≤ ∑ j, hs j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (hs j)) (Finset.mem_univ i)
  omega

/-- Complete homogeneous symmetric polynomial `h_s(xs)` as a finite sum over `tuplesWithSum`. -/
def hSum (m s : ℕ) (xs : Fin m → ℂ) : ℂ :=
  ∑ hs ∈ tuplesWithSum m s, ∏ i : Fin m, (xs i) ^ (hs i)

private lemma hSum_zero (s : ℕ) (xs : Fin 0 → ℂ) :
    hSum 0 s xs = if s = 0 then 1 else 0 := by
  unfold hSum
  by_cases hs : s = 0
  · subst hs
    have hmem : (Fin.elim0 : Fin 0 → ℕ) ∈ tuplesWithSum 0 0 := by
      rw [mem_tuplesWithSum]; simp
    rw [Finset.sum_eq_single Fin.elim0]
    · simp
    · intro f _ hne
      exact absurd (Subsingleton.elim f Fin.elim0) hne
    · intro h; exact absurd hmem h
  · simp only [hs, ↓reduceIte]
    refine Finset.sum_eq_zero fun f hf => ?_
    rw [mem_tuplesWithSum] at hf
    simp at hf
    exact absurd hf.symm hs

private lemma hSum_succ (m s : ℕ) (xs : Fin (m + 1) → ℂ) :
    hSum (m + 1) s xs =
      ∑ a ∈ Finset.range (s + 1), (xs 0) ^ a * hSum m (s - a) (fun i => xs i.succ) := by
  unfold hSum
  have hmaps : ∀ hs ∈ tuplesWithSum (m + 1) s, hs 0 ∈ Finset.range (s + 1) := by
    intro hs hhs
    rw [Finset.mem_range]
    have hsum : ∑ i, hs i = s := (mem_tuplesWithSum (m + 1) s hs).mp hhs
    have hle : hs 0 ≤ ∑ i, hs i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (hs i)) (Finset.mem_univ (0 : Fin (m + 1)))
    omega
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun hs : Fin (m + 1) → ℕ => hs 0)
    (t := Finset.range (s + 1)) hmaps]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha_le : a ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [Finset.mul_sum]
  refine Finset.sum_nbij (fun hs => fun i : Fin m => hs i.succ) ?_ ?_ ?_ ?_
  · intro hs hhs
    simp only [Finset.mem_filter, mem_tuplesWithSum] at hhs ⊢
    rw [Fin.sum_univ_succ, hhs.2] at hhs
    omega
  · intro hs₁ h₁ hs₂ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    funext i
    refine Fin.cases ?_ ?_ i
    · exact h₁.2.trans h₂.2.symm
    · intro j; exact congrFun heq j
  · intro t ht
    simp only [Finset.mem_coe, mem_tuplesWithSum] at ht
    refine ⟨Fin.cons a t, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, mem_tuplesWithSum]
      refine ⟨?_, by simp⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      omega
    · funext j; simp
  · intro hs hhs
    have h0 : hs 0 = a := (Finset.mem_filter.mp hhs).2
    rw [Fin.prod_univ_succ, h0]

/-- Truncated generating polynomial `H_D(X) = ∑_{s ≤ D} h_s(xs) X^s`. -/
noncomputable def HPoly (m D : ℕ) (xs : Fin m → ℂ) : Polynomial ℂ :=
  ∑ s ∈ Finset.range (D + 1), C (hSum m s xs) * X ^ s

private lemma coeff_HPoly (m D : ℕ) (xs : Fin m → ℂ) (s : ℕ) :
    (HPoly m D xs).coeff s = if s ≤ D then hSum m s xs else 0 := by
  rw [HPoly, coeff_finset_sum]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hs : s ≤ D
  · simp only [hs, ↓reduceIte]
    rw [Finset.sum_eq_single s]
    · simp
    · intro i _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · simp only [hs, ↓reduceIte]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi_lt := Finset.mem_range.mp hi
    have hne : s ≠ i := by omega
    simp [hne]

/-- Zero-PowerSeries finite polynomial identity:
`(∏ i, (1 - xs i * X)) * HPoly m D xs ≡ 1 (mod X^{D+1})`. -/
private lemma coeff_prod_one_sub_mul_HPoly (m D : ℕ) (xs : Fin m → ℂ) :
    ∀ j ≤ D, ((∏ i : Fin m, (1 - C (xs i) * X)) * HPoly m D xs).coeff j =
      if j = 0 then 1 else 0 := by
  induction m with
  | zero =>
    intro j hj
    rw [Fin.prod_univ_zero, one_mul, coeff_HPoly]
    simp only [hj, ↓reduceIte, hSum_zero]
  | succ m ih =>
    let G : Polynomial ℂ := ∑ a ∈ Finset.range (D + 1), C ((xs 0) ^ a) * X ^ a
    have hG_coeff : ∀ a ≤ D, G.coeff a = (xs 0) ^ a := by
      intro a ha
      rw [show G = ∑ i ∈ Finset.range (D + 1), C ((xs 0) ^ i) * X ^ i from rfl, coeff_finset_sum]
      simp_rw [coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single a]
      · simp
      · intro i _ hne; simp [hne.symm]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    have hH_split : ∀ s ≤ D,
        (HPoly (m + 1) D xs).coeff s = (G * HPoly m D (fun i => xs i.succ)).coeff s := by
      intro s hs
      rw [coeff_HPoly]
      simp only [hs, ↓reduceIte]
      rw [hSum_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => G.coeff a * (HPoly m D (fun i => xs i.succ)).coeff b)]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha_le : a ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have hsa_le : s - a ≤ D := by omega
      rw [hG_coeff a (ha_le.trans hs), coeff_HPoly]
      simp only [hsa_le, ↓reduceIte]
    have h1G : ∀ j ≤ D, ((1 - C (xs 0) * X) * G).coeff j = (1 : Polynomial ℂ).coeff j := by
      intro j hj
      have hgeom : (1 - C (xs 0) * X) * G = 1 - C ((xs 0) ^ (D + 1)) * X ^ (D + 1) := by
        have hG_pow : G = ∑ a ∈ Finset.range (D + 1), (C (xs 0) * X) ^ a := by
          refine Finset.sum_congr rfl fun a _ => by rw [mul_pow, map_pow]
        rw [hG_pow]
        have h := mul_geom_sum (C (xs 0) * X) (D + 1)
        -- `(C (xs 0) * X - 1) * ∑ = (C (xs 0) * X)^(D+1) - 1`, negate both sides!
        have hneg : (1 - C (xs 0) * X) * ∑ a ∈ Finset.range (D + 1), (C (xs 0) * X) ^ a =
            1 - (C (xs 0) * X) ^ (D + 1) := by
          calc
            (1 - C (xs 0) * X) * ∑ a ∈ Finset.range (D + 1), (C (xs 0) * X) ^ a
                = - ((C (xs 0) * X - 1) * ∑ a ∈ Finset.range (D + 1), (C (xs 0) * X) ^ a) := by
                  ring
            _ = - ((C (xs 0) * X) ^ (D + 1) - 1) := by rw [h]
            _ = 1 - (C (xs 0) * X) ^ (D + 1) := by ring
        rw [hneg, mul_pow, map_pow]
      rw [hgeom, coeff_sub, coeff_C_mul_X_pow]
      have hne : j ≠ D + 1 := by omega
      simp [hne]
    intro j hj
    rw [Fin.prod_univ_succ]
    have hstep1 :
        (((1 - C (xs 0) * X) * ∏ i : Fin m, (1 - C (xs i.succ) * X)) * HPoly (m + 1) D xs).coeff j =
        (((1 - C (xs 0) * X) * ∏ i : Fin m, (1 - C (xs i.succ) * X)) *
          (G * HPoly m D (fun i => xs i.succ))).coeff j :=
      coeff_mul_congr_of_le (fun _ _ => rfl) hH_split j hj
    rw [hstep1]
    have hrearr :
        ((1 - C (xs 0) * X) * ∏ i : Fin m, (1 - C (xs i.succ) * X)) *
          (G * HPoly m D (fun i => xs i.succ)) =
        ((1 - C (xs 0) * X) * G) *
          ((∏ i : Fin m, (1 - C (xs i.succ) * X)) * HPoly m D (fun i => xs i.succ)) := by
      ring
    rw [hrearr]
    have hih1 : ∀ i ≤ D,
        ((∏ k : Fin m, (1 - C (xs k.succ) * X)) * HPoly m D (fun k => xs k.succ)).coeff i =
          (1 : Polynomial ℂ).coeff i := by
      intro i hi
      rw [ih (fun k => xs k.succ) i hi, coeff_one]
    rw [coeff_mul_congr_of_le h1G hih1 j hj, one_mul, coeff_one]

/-! ### Characteristic polynomial `χ_Z` of the zero-sum hyperplane for a permutation `e` -/

section ChiZ

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

omit [Fintype Q] in
/-- Top-coefficient `+1` lemma for `∏_{C ∈ S} (X^{|C|} - 1)` when all `|C| ≥ m₁`. -/
private lemma prod_X_pow_sub_one_coeffs {m₁ : ℕ} (hm₁ : 0 < m₁) (S : Finset (Finset Q))
    (hge : ∀ C ∈ S, m₁ ≤ C.card) :
    let P : Polynomial ℤ := ∏ C ∈ S, (X ^ C.card - 1)
    let N : ℕ := ∑ C ∈ S, C.card
    P.coeff N = 1 ∧
    (∀ k, N < k → P.coeff k = 0) ∧
    (∀ k, k < N → N < k + m₁ → P.coeff k = 0) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simp, fun k hk => ?_, fun k hk => by simp at hk⟩
    simp only [Finset.sum_empty] at hk
    rw [Finset.prod_empty, coeff_one]
    have hne : k ≠ 0 := by omega
    simp [hne]
  | insert C S hCS ih =>
    have hge_S : ∀ C' ∈ S, m₁ ≤ C'.card := fun C' hC' => hge C' (Finset.mem_insert_of_mem hC')
    have hge_C : m₁ ≤ C.card := hge C (Finset.mem_insert_self C S)
    obtain ⟨ih_top, ih_gt, ih_gap⟩ := ih hge_S
    set Qs : Polynomial ℤ := ∏ C' ∈ S, (X ^ C'.card - 1)
    set Ns : ℕ := ∑ C' ∈ S, C'.card
    have hP : (∏ C' ∈ insert C S, (X ^ C'.card - 1 : Polynomial ℤ)) =
        X ^ C.card * Qs - Qs := by
      rw [Finset.prod_insert hCS, sub_mul, one_mul]
    have hN : ∑ C' ∈ insert C S, C'.card = C.card + Ns := Finset.sum_insert hCS
    have hcoeff : ∀ k : ℕ, (X ^ C.card * Qs - Qs).coeff k =
        (if C.card ≤ k then Qs.coeff (k - C.card) else 0) - Qs.coeff k := by
      intro k
      rw [coeff_sub, coeff_X_pow_mul']
    rw [hP, hN]
    refine ⟨?_, ?_, ?_⟩
    · rw [hcoeff]
      have hle : C.card ≤ C.card + Ns := by omega
      simp only [hle, ↓reduceIte]
      rw [show C.card + Ns - C.card = Ns by omega, ih_top,
        ih_gt (C.card + Ns) (by omega), sub_zero]
    · intro k hk
      rw [hcoeff, ih_gt k (by omega), sub_zero]
      split_ifs with hle
      · exact ih_gt (k - C.card) (by omega)
      · rfl
    · intro k hlt hgap
      rw [hcoeff]
      have h2 : Qs.coeff k = 0 := ih_gt k (by omega)
      rw [h2, sub_zero]
      split_ifs with hle
      · exact ih_gap (k - C.card) (by omega) (by omega)
      · rfl

/-- Integer polynomial `χ_Z(t) = (∑_{j < m₁} t^j) * ∏_{C ∈ rest} (t^{|C|} - 1)`. -/
noncomputable def chiZ (m₁ : ℕ) (rest : Finset (Finset Q)) : Polynomial ℤ :=
  (∑ j ∈ Finset.range m₁, X ^ j) * ∏ C ∈ rest, (X ^ C.card - 1)

/-- Reciprocal complex polynomial `χ_Z^{rev}(x) = (∑_{j < m₁} x^j) * ∏_{C ∈ rest} (1 - x^{|C|})`. -/
noncomputable def chiZRev (m₁ : ℕ) (rest : Finset (Finset Q)) : Polynomial ℂ :=
  (∑ j ∈ Finset.range m₁, X ^ j) * ∏ C ∈ rest, (1 - X ^ C.card)

/-- **Lemma S.1(4)**: Top `m₁` coefficients of `χ_Z` equal `+1`, degree ≤ `n - 1`,
`χ_Z^{rev}` reverses coefficients of `χ_Z`, and `χ_Z^{rev} = ∏_k (1 - ζ^k X)^{d_k}`. -/
private lemma chiZ_properties [Nonempty Q] (e : Q ≃ Q) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (permOrder e))
    {C_min : Finset Q} (hCmin : C_min ∈ orbits e)
    (hmin : ∀ C ∈ orbits e, C_min.card ≤ C.card) :
    let m₁ := C_min.card
    let rest := (orbits e).erase C_min
    let n := Fintype.card Q
    (∀ d, n - m₁ ≤ d → d < n → (chiZ m₁ rest).coeff d = 1) ∧
    (∀ d, n ≤ d → (chiZ m₁ rest).coeff d = 0) ∧
    (∀ j < n, (chiZRev m₁ rest).coeff j = ((chiZ m₁ rest).coeff (n - 1 - j) : ℂ)) ∧
    chiZRev m₁ rest = ∏ k : Fin (permOrder e), (1 - C (ζ ^ (k : ℕ)) * X) ^ zEigMult e ζ k := by
  classical
  intro m₁ rest n
  have hm₁ : 0 < m₁ := card_pos_of_mem_orbits e hCmin
  have hM : 0 < permOrder e := permOrder_pos e
  have hrest_ge : ∀ C ∈ rest, m₁ ≤ C.card :=
    fun C hC => hmin C (Finset.mem_of_mem_erase hC)
  have hrest_sum : ∑ C ∈ rest, C.card = n - m₁ := by
    have hadd : m₁ + ∑ C ∈ rest, C.card = ∑ C ∈ orbits e, C.card :=
      Finset.add_sum_erase (orbits e) Finset.card hCmin
    rw [sum_card_orbits] at hadd
    omega
  have hm₁_le_n : m₁ ≤ n := by
    have hadd : m₁ + ∑ C ∈ rest, C.card = ∑ C ∈ orbits e, C.card :=
      Finset.add_sum_erase (orbits e) Finset.card hCmin
    rw [sum_card_orbits] at hadd
    omega
  obtain ⟨hQ_top, hQ_gt, hQ_gap⟩ := prod_X_pow_sub_one_coeffs hm₁ rest hrest_ge
  set Qs : Polynomial ℤ := ∏ C ∈ rest, (X ^ C.card - 1)
  have hchi_coeff : ∀ d : ℕ, (chiZ m₁ rest).coeff d =
      ∑ j ∈ Finset.range m₁, if j ≤ d then Qs.coeff (d - j) else 0 := by
    intro d
    rw [chiZ, Finset.sum_mul, coeff_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_X_pow_mul']
  have htop1 : ∀ d, n - m₁ ≤ d → d < n → (chiZ m₁ rest).coeff d = 1 := by
    intro d hd1 hd2
    rw [hchi_coeff d, Finset.sum_eq_single (d - (n - m₁))]
    · have hle : d - (n - m₁) ≤ d := by omega
      simp only [hle, ↓reduceIte]
      rw [show d - (d - (n - m₁)) = n - m₁ by omega, ← hrest_sum]
      exact hQ_top
    · intro j hj hne
      have hj_lt := Finset.mem_range.mp hj
      split_ifs with hjd
      · by_cases hlt : j < d - (n - m₁)
        · exact hQ_gt (d - j) (by omega)
        · exact hQ_gap (d - j) (by omega) (by omega)
      · rfl
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hgt0 : ∀ d, n ≤ d → (chiZ m₁ rest).coeff d = 0 := by
    intro d hd
    rw [hchi_coeff d]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj_lt := Finset.mem_range.mp hj
    split_ifs with hjd
    · exact hQ_gt (d - j) (by omega)
    · rfl
  have hrev_eq : chiZRev m₁ rest = polyRev (n - 1) ((chiZ m₁ rest).map (Int.castRingHom ℂ)) := by
    have hmap : (chiZ m₁ rest).map (Int.castRingHom ℂ) =
        (∑ j ∈ Finset.range m₁, (X ^ j : Polynomial ℂ)) *
          ∏ C ∈ rest, (X ^ C.card - 1 : Polynomial ℂ) := by
      simp [chiZ, Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_prod]
    rw [hmap]
    have hdeg1 : ∀ k, m₁ - 1 < k → (∑ j ∈ Finset.range m₁, (X ^ j : Polynomial ℂ)).coeff k = 0 := by
      intro k hk
      rw [coeff_finset_sum]
      simp_rw [coeff_X_pow]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_lt := Finset.mem_range.mp hj
      have hne : k ≠ j := by omega
      simp [hne]
    have hprod_rev := polyRev_prod rest Finset.card (fun C => (X ^ C.card - 1 : Polynomial ℂ))
      (fun C _ k hk => by
        rw [coeff_sub, coeff_X_pow, coeff_one]
        have h1 : k ≠ C.card := by omega
        have h2 : k ≠ 0 := by omega
        simp [h1, h2])
    have hsum_eq : (m₁ - 1) + ∑ C ∈ rest, C.card = n - 1 := by omega
    rw [← hsum_eq, ← polyRev_mul hdeg1 hprod_rev.2, polyRev_geomSum hm₁, hprod_rev.1, chiZRev]
    congr 1
    refine Finset.prod_congr rfl fun C hC => ?_
    exact (polyRev_X_pow_sub_one (card_pos_of_mem_orbits e (Finset.mem_of_mem_erase hC))).symm
  have hrev_coeff : ∀ j < n,
      (chiZRev m₁ rest).coeff j = ((chiZ m₁ rest).coeff (n - 1 - j) : ℂ) := by
    intro j hj
    have hj_le : j ≤ n - 1 := by omega
    rw [hrev_eq, coeff_polyRev]
    simp only [hj_le, ↓reduceIte, coeff_map]
    rfl
  have hfac : chiZRev m₁ rest =
      ∏ k : Fin (permOrder e), (1 - C (ζ ^ (k : ℕ)) * X) ^ zEigMult e ζ k := by
    have hne : (1 - X : Polynomial ℂ) ≠ 0 := by
      intro h0
      have h := congrArg (fun p : Polynomial ℂ => p.coeff 0) h0
      simp at h
    apply mul_left_cancel₀ hne
    have hLHS : (1 - X : Polynomial ℂ) * chiZRev m₁ rest =
        ∏ C ∈ orbits e, (1 - X ^ C.card : Polynomial ℂ) := by
      rw [chiZRev, ← mul_assoc]
      have hgeom : (1 - X : Polynomial ℂ) * ∑ j ∈ Finset.range m₁, (X ^ j : Polynomial ℂ) =
          (1 - X ^ m₁ : Polynomial ℂ) := by
        have h := mul_geom_sum (X : Polynomial ℂ) m₁
        calc
          (1 - X : Polynomial ℂ) * ∑ j ∈ Finset.range m₁, (X ^ j : Polynomial ℂ)
              = - ((X - 1 : Polynomial ℂ) * ∑ j ∈ Finset.range m₁, (X ^ j : Polynomial ℂ)) := by
                ring
          _ = - ((X ^ m₁ - 1 : Polynomial ℂ)) := by rw [h]
          _ = (1 - X ^ m₁ : Polynomial ℂ) := by ring
      rw [hgeom]
      exact Finset.mul_prod_erase (orbits e) (fun C => (1 - X ^ C.card : Polynomial ℂ)) hCmin
    have hcyc : ∀ Cy ∈ orbits e,
        (1 - X ^ Cy.card : Polynomial ℂ) =
          ∏ k ∈ Finset.univ.filter (fun k : Fin (permOrder e) => (ζ ^ (k : ℕ)) ^ Cy.card = 1),
            (1 - C (ζ ^ (k : ℕ)) * X) := by
      intro Cy hC
      have hCpos : 0 < Cy.card := card_pos_of_mem_orbits e hC
      have hdvd : Cy.card ∣ permOrder e := dvd_permOrder e hC
      set step := permOrder e / Cy.card
      have hstep_mul : Cy.card * step = permOrder e := Nat.mul_div_cancel' hdvd
      have hstep_pos : 0 < step := Nat.div_pos (Nat.le_of_dvd hM hdvd) hCpos
      have hω : IsPrimitiveRoot (ζ ^ step) Cy.card := by
        rw [IsPrimitiveRoot.iff_def]
        refine ⟨?_, ?_⟩
        · rw [← pow_mul, mul_comm step Cy.card, hstep_mul, hζ.pow_eq_one]
        · intro l hl
          rw [← pow_mul] at hl
          have hdvdM := hζ.dvd_of_pow_eq_one _ hl
          have hdvd' : step * Cy.card ∣ step * l := by
            rwa [mul_comm step Cy.card, hstep_mul]
          exact (Nat.mul_dvd_mul_iff_left hstep_pos).mp hdvd'
      rw [one_sub_X_pow_eq_prod hCpos hω]
      let emb : Fin Cy.card → Fin (permOrder e) := fun t =>
        ⟨t.val * step, by
          calc
            t.val * step < Cy.card * step := Nat.mul_lt_mul_of_pos_right t.isLt hstep_pos
            _ = permOrder e := hstep_mul⟩
      have hemb_inj : Function.Injective emb := by
        intro t₁ t₂ h
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right hstep_pos (congrArg Fin.val h))
      have hfilt :
          Finset.univ.filter (fun k : Fin (permOrder e) => (ζ ^ (k : ℕ)) ^ Cy.card = 1) =
            Finset.univ.image emb := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hpow
          rw [← pow_mul] at hpow
          have hdvdM : permOrder e ∣ k.val * Cy.card := hζ.dvd_of_pow_eq_one _ hpow
          have hdvd' : step * Cy.card ∣ k.val * Cy.card := by
            rwa [mul_comm step Cy.card, hstep_mul]
          rcases (Nat.mul_dvd_mul_iff_right hCpos).mp hdvd' with ⟨t, ht⟩
          have ht_lt : t < Cy.card := by
            have hklt : k.val < permOrder e := k.isLt
            rw [ht, ← hstep_mul, mul_comm Cy.card step] at hklt
            exact Nat.lt_of_mul_lt_mul_left hklt
          exact ⟨⟨t, ht_lt⟩, Fin.ext (by simp [emb, ht, mul_comm])⟩
        · rintro ⟨t, rfl⟩
          simp only [emb, ← pow_mul]
          rw [mul_assoc, mul_comm step Cy.card, hstep_mul, mul_comm t.val (permOrder e), pow_mul,
            hζ.pow_eq_one, one_pow]
      rw [hfilt, Finset.prod_image (fun x _ y _ h => hemb_inj h)]
      refine Finset.prod_congr rfl fun t _ => ?_
      simp only [← pow_mul, mul_comm step t.val]
      rfl
    have hprod_all :
        ∏ Cy ∈ orbits e, (1 - X ^ Cy.card : Polynomial ℂ) =
          ∏ k : Fin (permOrder e), (1 - C (ζ ^ (k : ℕ)) * X) ^ eigMult e ζ k := by
      calc
        ∏ Cy ∈ orbits e, (1 - X ^ Cy.card : Polynomial ℂ)
            = ∏ Cy ∈ orbits e,
                ∏ k : Fin (permOrder e),
                  if (ζ ^ (k : ℕ)) ^ Cy.card = 1 then (1 - C (ζ ^ (k : ℕ)) * X) else 1 := by
              refine Finset.prod_congr rfl fun Cy hC => ?_
              rw [hcyc Cy hC, Finset.prod_filter]
        _ = ∏ k : Fin (permOrder e),
              ∏ Cy ∈ orbits e,
                if (ζ ^ (k : ℕ)) ^ Cy.card = 1 then (1 - C (ζ ^ (k : ℕ)) * X) else 1 :=
              Finset.prod_comm
        _ = ∏ k : Fin (permOrder e), (1 - C (ζ ^ (k : ℕ)) * X) ^ eigMult e ζ k := by
              refine Finset.prod_congr rfl fun k _ => ?_
              rw [← Finset.prod_filter, Finset.prod_const, eigMult]
    rw [hLHS, hprod_all]
    have h0_mem : (⟨0, hM⟩ : Fin (permOrder e)) ∈ Finset.univ := Finset.mem_univ _
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k : Fin (permOrder e) => (1 - C (ζ ^ (k : ℕ)) * X) ^ eigMult e ζ k) h0_mem]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k : Fin (permOrder e) => (1 - C (ζ ^ (k : ℕ)) * X) ^ zEigMult e ζ k) h0_mem]
    rw [← mul_assoc]
    congr 1
    · have hcpos : 1 ≤ (orbits e).card := (orbits_nonempty e).card_pos
      have hν0 : eigMult e ζ ⟨0, hM⟩ = (orbits e).card := by simp [eigMult]
      have hd0 : zEigMult e ζ ⟨0, hM⟩ = (orbits e).card - 1 := by simp [zEigMult]
      simp only [pow_zero, map_one, one_mul, hν0, hd0]
      rw [← pow_succ', Nat.sub_add_cancel hcpos]
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hk0 : k.val ≠ 0 := fun h => (Finset.ne_of_mem_erase hk) (Fin.ext h)
      simp [zEigMult, hk0]
  exact ⟨htop1, hgt0, hrev_coeff, hfac⟩

/-- **Lemma S.4 (Confluent Divided-Difference Vanishing — zero `PowerSeries`)**:
If every `k : Fin M` appears at most `zEigMult e ζ k` times in `α : Fin (r + 1) → Fin M`,
then `∑_{s < n - r} chiZ.coeff (r + s) * hSum (r + 1) s (ζ^α) = 0`. -/
private lemma confluent_divDiff_eq_zero [Nonempty Q] (e : Q ≃ Q) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (permOrder e))
    {C_min : Finset Q} (hCmin : C_min ∈ orbits e)
    (hmin : ∀ C ∈ orbits e, C_min.card ≤ C.card)
    {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ Fintype.card Q)
    (α : Fin (r + 1) → Fin (permOrder e))
    (hmult : ∀ k : Fin (permOrder e), (Finset.univ.filter (fun i => α i = k)).card ≤ zEigMult e ζ k) :
    ∑ s ∈ Finset.range (Fintype.card Q - r),
      ((chiZ C_min.card ((orbits e).erase C_min)).coeff (r + s) : ℂ) *
        hSum (r + 1) s (fun i => ζ ^ (α i).val) = 0 := by
  classical
  let D : ℕ := Fintype.card Q - 1 - r
  have hD_pos : 1 ≤ D := by omega
  have hM : 0 < permOrder e := permOrder_pos e
  obtain ⟨_, _, hrev_coeff, hfac⟩ := chiZ_properties e hζ hCmin hmin
  let cnt : Fin (permOrder e) → ℕ :=
    fun k => (Finset.univ.filter (fun i : Fin (r + 1) => α i = k)).card
  let R : Polynomial ℂ :=
    ∏ k : Fin (permOrder e), (1 - C (ζ ^ (k : ℕ)) * X) ^ (zEigMult e ζ k - cnt k)
  have hsplit : chiZRev C_min.card ((orbits e).erase C_min) =
      (∏ i : Fin (r + 1), (1 - C (ζ ^ (α i).val) * X)) * R := by
    rw [hfac]
    have hprod_α :
        ∏ i : Fin (r + 1), (1 - C (ζ ^ (α i).val) * X) =
          ∏ k : Fin (permOrder e), (1 - C (ζ ^ (k : ℕ)) * X) ^ cnt k := by
      rw [← Finset.prod_fiberwise_of_maps_to (g := α) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hcongr :
          ∏ i ∈ Finset.univ.filter (fun i => α i = k), (1 - C (ζ ^ (α i).val) * X) =
            ∏ _i ∈ Finset.univ.filter (fun i => α i = k), (1 - C (ζ ^ (k : ℕ)) * X) := by
        refine Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
      rw [hcongr, Finset.prod_const]
    rw [hprod_α, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add, Nat.add_sub_of_le (hmult k)]
  have hsum_zEig : ∑ k : Fin (permOrder e), zEigMult e ζ k = Fintype.card Q - 1 := by
    have h1 : ∑ k : Fin (permOrder e), eigMult e ζ k = Fintype.card Q := sum_eigMult e hζ
    have h0_mem : (⟨0, hM⟩ : Fin (permOrder e)) ∈ Finset.univ := Finset.mem_univ _
    have hcpos : 1 ≤ (orbits e).card := (orbits_nonempty e).card_pos
    have hν0 : eigMult e ζ ⟨0, hM⟩ = (orbits e).card := by simp [eigMult]
    have hd0 : zEigMult e ζ ⟨0, hM⟩ = (orbits e).card - 1 := by simp [zEigMult]
    have hrest :
        ∑ k ∈ Finset.univ.erase ⟨0, hM⟩, zEigMult e ζ k =
          ∑ k ∈ Finset.univ.erase ⟨0, hM⟩, eigMult e ζ k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk0 : k.val ≠ 0 := fun h => (Finset.ne_of_mem_erase hk) (Fin.ext h)
      simp [zEigMult, hk0]
    have hs1 := Finset.add_sum_erase Finset.univ (eigMult e ζ) h0_mem
    have hs2 := Finset.add_sum_erase Finset.univ (zEigMult e ζ) h0_mem
    rw [h1, hν0] at hs1
    rw [hd0, hrest] at hs2
    omega
  have hsum_cnt : ∑ k : Fin (permOrder e), cnt k = r + 1 := by
    have h := Finset.sum_card_fiberwise_eq_card_filter (s := (Finset.univ : Finset (Fin (r + 1))))
      (t := (Finset.univ : Finset (Fin (permOrder e)))) (g := α)
    simpa [cnt] using h
  have hR_deg : R.natDegree < D := by
    have hdeg_le : R.natDegree ≤ ∑ k : Fin (permOrder e), (zEigMult e ζ k - cnt k) := by
      calc
        R.natDegree ≤ ∑ k : Fin (permOrder e),
            ((1 - C (ζ ^ (k : ℕ)) * X) ^ (zEigMult e ζ k - cnt k)).natDegree :=
          natDegree_prod_le _ _
        _ ≤ ∑ k : Fin (permOrder e),
            (zEigMult e ζ k - cnt k) * (1 - C (ζ ^ (k : ℕ)) * X).natDegree :=
          Finset.sum_le_sum
            (f := fun k : Fin (permOrder e) =>
              ((1 - C (ζ ^ (k : ℕ)) * X) ^ (zEigMult e ζ k - cnt k)).natDegree)
            fun k _ => natDegree_pow_le (p := 1 - C (ζ ^ (k : ℕ)) * X) (n := zEigMult e ζ k - cnt k)
        _ ≤ ∑ k : Fin (permOrder e), (zEigMult e ζ k - cnt k) * 1 := by
          refine Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ ?_
          have h1 : (1 - C (ζ ^ (k : ℕ)) * X).natDegree ≤ max (1 : Polynomial ℂ).natDegree
              (C (ζ ^ (k : ℕ)) * X).natDegree := natDegree_sub_le _ _
          have h2 : (C (ζ ^ (k : ℕ)) * X).natDegree ≤ 1 := by
            calc
              (C (ζ ^ (k : ℕ)) * X).natDegree ≤ (C (ζ ^ (k : ℕ))).natDegree + X.natDegree :=
                natDegree_mul_le
              _ = 0 + 1 := by simp
              _ = 1 := by omega
          simp only [natDegree_one] at h1
          omega
        _ = ∑ k : Fin (permOrder e), (zEigMult e ζ k - cnt k) := by simp
    have hsum_sub : ∑ k : Fin (permOrder e), (zEigMult e ζ k - cnt k) +
        ∑ k : Fin (permOrder e), cnt k = ∑ k : Fin (permOrder e), zEigMult e ζ k := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (hmult k)
    omega
  have hR_D : R.coeff D = 0 := coeff_eq_zero_of_natDegree_lt hR_deg
  have hzero : (chiZRev C_min.card ((orbits e).erase C_min) *
      HPoly (r + 1) D (fun i => ζ ^ (α i).val)).coeff D = 0 := by
    have hrearr :
        chiZRev C_min.card ((orbits e).erase C_min) * HPoly (r + 1) D (fun i => ζ ^ (α i).val) =
          R * ((∏ i : Fin (r + 1), (1 - C (ζ ^ (α i).val) * X)) *
            HPoly (r + 1) D (fun i => ζ ^ (α i).val)) := by
      rw [hsplit]
      ring
    rw [hrearr]
    have h1 : ∀ j ≤ D,
        ((∏ i : Fin (r + 1), (1 - C (ζ ^ (α i).val) * X)) *
          HPoly (r + 1) D (fun i => ζ ^ (α i).val)).coeff j = (1 : Polynomial ℂ).coeff j := by
      intro j hj
      rw [coeff_prod_one_sub_mul_HPoly (r + 1) D _ j hj, coeff_one]
    rw [coeff_mul_congr_of_le (fun _ _ => rfl) h1 D (le_refl D), mul_one, hR_D]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => (chiZRev C_min.card ((orbits e).erase C_min)).coeff j *
      (HPoly (r + 1) D (fun i => ζ ^ (α i).val)).coeff k)] at hzero
  have hD_succ : D + 1 = Fintype.card Q - r := by omega
  rw [← hzero, ← hD_succ]
  refine Finset.sum_nbij (fun s => D - s) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_range] at hs ⊢
    omega
  · intro s₁ h₁ s₂ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_range] at h₁ h₂
    dsimp only at heq
    omega
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_range] at hj ⊢
    exact ⟨D - j, by simp only [Finset.mem_coe, Finset.mem_range]; omega, by dsimp only; omega⟩
  · intro s hs
    have hs_lt := Finset.mem_range.mp hs
    rw [hrev_coeff (D - s) (by omega), coeff_HPoly]
    have hle : D - (D - s) ≤ D := by omega
    simp only [hle, ↓reduceIte]
    have hidx1 : Fintype.card Q - 1 - (D - s) = r + s := by omega
    have hidx2 : D - (D - s) = s := by omega
    rw [hidx1, hidx2]

end ChiZ

end PolyTools

/-! ### Section 5: Control-filtered subspaces, Lemma S.3, and Lemma S.6 -/

section ControlFiltration

variable {Q : Type u} {α : Type v}

/-- Number of control letters (letters distinct from `a`) in a word `w`. -/
def countControls [DecidableEq α] (a : α) (w : List α) : ℕ :=
  (w.filter (fun x => decide (x ≠ a))).length

private lemma countControls_nil [DecidableEq α] (a : α) : countControls a [] = 0 := rfl

private lemma countControls_append [DecidableEq α] (a : α) (u v : List α) :
    countControls a (u ++ v) = countControls a u + countControls a v := by
  simp [countControls, List.filter_append]

private lemma countControls_cons_eq [DecidableEq α] (a : α) (w : List α) :
    countControls a (a :: w) = countControls a w := by
  simp [countControls]

private lemma countControls_cons_ne [DecidableEq α] {a g : α} (h : g ≠ a) (w : List α) :
    countControls a (g :: w) = countControls a w + 1 := by
  simp [countControls, h]

private lemma countControls_replicate [DecidableEq α] (a : α) (k : ℕ) :
    countControls a (List.replicate k a) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, countControls_cons_eq, ih]

private lemma word_eq_replicate_of_countControls_zero [DecidableEq α] (a : α) :
    ∀ w : List α, countControls a w = 0 → w = List.replicate w.length a := by
  intro w
  induction w with
  | nil => intro _; rfl
  | cons x u ih =>
    intro h0
    by_cases hxa : x = a
    · subst hxa
      rw [countControls_cons_eq] at h0
      rw [List.length_cons, List.replicate_succ, ← ih h0]
    · rw [countControls_cons_ne hxa] at h0
      omega

private lemma word_split_first_control [DecidableEq α] (a : α) :
    ∀ w : List α, 0 < countControls a w →
      ∃ (h : ℕ) (g : α) (z : List α),
        g ≠ a ∧ countControls a z + 1 = countControls a w ∧
        w = List.replicate h a ++ (g :: z) := by
  intro w
  induction w with
  | nil => intro h; simp [countControls] at h
  | cons x u ih =>
    intro hpos
    by_cases hxa : x = a
    · subst hxa
      rw [countControls_cons_eq] at hpos ⊢
      obtain ⟨h, g, z, hg, hcnt, hu⟩ := ih hpos
      exact ⟨h + 1, g, z, hg, hcnt, by rw [hu, List.replicate_succ, List.cons_append]⟩
    · refine ⟨0, x, u, hxa, ?_, by simp⟩
      rw [countControls_cons_ne hxa]

private lemma word_split_last_control [DecidableEq α] (a : α) :
    ∀ (w : List α) (k : ℕ), countControls a w = k + 1 →
      ∃ (w' : List α) (g : α) (h : ℕ),
        g ≠ a ∧ countControls a w' = k ∧ w = w' ++ [g] ++ List.replicate h a := by
  intro w
  induction w with
  | nil => intro k h; simp [countControls] at h
  | cons x u ih =>
    intro k hcnt
    by_cases hu0 : countControls a u = 0
    · have hxa : x ≠ a := by
        intro heq; subst heq; rw [countControls_cons_eq] at hcnt; omega
      rw [countControls_cons_ne hxa, hu0] at hcnt
      have hk0 : k = 0 := by omega
      subst hk0
      refine ⟨[], x, u.length, hxa, rfl, ?_⟩
      simp only [List.nil_append, List.singleton_append]
      exact congrArg (x :: ·) (word_eq_replicate_of_countControls_zero a u hu0)
    · have hu_pos : 1 ≤ countControls a u := Nat.pos_of_ne_zero hu0
      by_cases hxa : x = a
      · rw [hxa, countControls_cons_eq] at hcnt
        obtain ⟨w', g, h, hg, hw'cnt, hu⟩ := ih k hcnt
        refine ⟨a :: w', g, h, hg, ?_, ?_⟩
        · rw [countControls_cons_eq, hw'cnt]
        · rw [hxa, hu]; simp
      · rw [countControls_cons_ne hxa] at hcnt
        have hk_pos : 1 ≤ k := by omega
        obtain ⟨w', g, h, hg, hw'cnt, hu⟩ := ih (k - 1) (by omega)
        refine ⟨x :: w', g, h, hg, ?_, ?_⟩
        · rw [countControls_cons_ne hxa, hw'cnt]; omega
        · rw [hu]; simp

/-- Block word `a^{h_0} g_0 a^{h_1} ... g_{r-1} a^{h_r}`. -/
def wordOfBlock (a : α) : ∀ {r : ℕ}, (Fin r → α) → (Fin (r + 1) → ℕ) → List α
  | 0, _, hs => List.replicate (hs 0) a
  | r + 1, gs, hs =>
    wordOfBlock a (fun i => gs i.castSucc) (fun i => hs i.castSucc) ++
      [gs (Fin.last r)] ++ List.replicate (hs (Fin.last (r + 1))) a

private lemma length_wordOfBlock (a : α) :
    ∀ {r : ℕ} (gs : Fin r → α) (hs : Fin (r + 1) → ℕ),
      (wordOfBlock a gs hs).length = r + ∑ i : Fin (r + 1), hs i
  | 0, _, hs => by simp [wordOfBlock]
  | r + 1, gs, hs => by
    simp only [wordOfBlock, List.length_append, List.length_singleton, List.length_replicate,
      length_wordOfBlock, Fin.sum_univ_castSucc]
    omega

private lemma countControls_wordOfBlock [DecidableEq α] (a : α) :
    ∀ {r : ℕ} (gs : Fin r → α) (hs : Fin (r + 1) → ℕ),
      (∀ i, gs i ≠ a) → countControls a (wordOfBlock a gs hs) = r
  | 0, _, hs, _ => by simp [wordOfBlock, countControls_replicate]
  | r + 1, gs, hs, hgs => by
    simp only [wordOfBlock, countControls_append, countControls_replicate, add_zero]
    rw [countControls_wordOfBlock a (fun i => gs i.castSucc) (fun i => hs i.castSucc)
      (fun i => hgs i.castSucc)]
    have hlast : countControls a [gs (Fin.last r)] = 1 := by
      rw [countControls_cons_ne (hgs (Fin.last r)), countControls_nil]
    rw [hlast]

section Subspaces

variable [Fintype Q] [DecidableEq Q] [DecidableEq α]

/-- Single-control difference vector `u_f = [Q](P_f - I)`. -/
def uVec (A : DFA Q α) (f : α) : Q → ℂ :=
  push A [f] onesVec - onesVec

omit [DecidableEq α] in
private lemma uVec_mem_zeroSumSub (A : DFA Q α) (f : α) : uVec A f ∈ zeroSumSub := by
  change sumLin (push A [f] onesVec - onesVec) = 0
  rw [map_sub, sumLin_push, sub_self]

omit [DecidableEq α] in
private lemma dotSet_push_uVec (A : DFA Q α) (f : α) (w : List α) (S : Finset Q) :
    dotSet (push A w (uVec A f)) S =
      ((A.preimage S (f :: w)).card : ℂ) - ((A.preimage S w).card : ℂ) := by
  rw [uVec, map_sub, dotSet_sub, ← mul_apply_eq_comp, ← push_cons, dotSet_push, dotSet_push,
    dotSet_ones, dotSet_ones]

/-- Control-filtered subspace `L_r = span { push A w (uVec A f) : f ≠ a, countControls a w ≤ r }`. -/
def ctrlSub (A : DFA Q α) (a : α) (r : ℕ) : Submodule ℂ (Q → ℂ) :=
  Submodule.span ℂ
    { v | ∃ (f : α) (w : List α), f ≠ a ∧ countControls a w ≤ r ∧ v = push A w (uVec A f) }

private lemma ctrlSub_mono (A : DFA Q α) (a : α) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    ctrlSub A a r₁ ≤ ctrlSub A a r₂ := by
  apply Submodule.span_mono
  rintro v ⟨f, w, hf, hcnt, rfl⟩
  exact ⟨f, w, hf, hcnt.trans h, rfl⟩

private lemma ctrlSub_le_zeroSumSub (A : DFA Q α) (a : α) (r : ℕ) :
    ctrlSub A a r ≤ zeroSumSub := by
  rw [ctrlSub, Submodule.span_le]
  rintro v ⟨f, w, _, _, rfl⟩
  exact push_mem_zeroSumSub A w (uVec_mem_zeroSumSub A f)

private lemma push_uVec_mem_ctrlSub (A : DFA Q α) (a : α) {f : α} (hf : f ≠ a)
    {w : List α} {r : ℕ} (hw : countControls a w ≤ r) :
    push A w (uVec A f) ∈ ctrlSub A a r :=
  Submodule.subset_span ⟨f, w, hf, hw, rfl⟩

private lemma push_perm_mem_ctrlSub (A : DFA Q α) (a : α) (r : ℕ) {v : Q → ℂ}
    (hv : v ∈ ctrlSub A a r) : push A [a] v ∈ ctrlSub A a r := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨f, w, hf, hcnt, rfl⟩
    rw [← mul_apply_eq_comp, ← push_append]
    refine push_uVec_mem_ctrlSub A a hf ?_
    rw [countControls_append, countControls_cons_eq, countControls_nil, add_zero]
    exact hcnt
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx

private lemma push_perm_pow_mem_ctrlSub (A : DFA Q α) (a : α) (r k : ℕ) {v : Q → ℂ}
    (hv : v ∈ ctrlSub A a r) : ((push A [a]) ^ k) v ∈ ctrlSub A a r := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact push_perm_mem_ctrlSub A a r ih

private lemma push_control_mem_ctrlSub (A : DFA Q α) (a : α) (r : ℕ) {g : α} (hg : g ≠ a)
    {v : Q → ℂ} (hv : v ∈ ctrlSub A a r) : push A [g] v ∈ ctrlSub A a (r + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨f, w, hf, hcnt, rfl⟩
    rw [← mul_apply_eq_comp, ← push_append]
    refine push_uVec_mem_ctrlSub A a hf ?_
    rw [countControls_append, countControls_cons_ne hg, countControls_nil]
    omega
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx

private lemma fourierProj_mem_ctrlSub (A : DFA Q α) (a : α) (M : ℕ) (ζ : ℂ) (k : Fin M)
    (r : ℕ) {v : Q → ℂ} (hv : v ∈ ctrlSub A a r) :
    fourierProj (push A [a]) M ζ k v ∈ ctrlSub A a r :=
  fourierProj_mem_invariant (fun _ => push_perm_mem_ctrlSub A a r) k hv

/-- Weighted control mixture `u_mix = ∑_{f ≠ a} β_f u_f`. -/
def uMix [Fintype α] (A : DFA Q α) (a : α) (β : α → ℝ) : Q → ℂ :=
  ∑ f ∈ Finset.univ.erase a, (β f : ℂ) • uVec A f

private lemma uMix_mem_ctrlSub_zero [Fintype α] (A : DFA Q α) (a : α) (β : α → ℝ) :
    uMix A a β ∈ ctrlSub A a 0 := by
  refine Submodule.sum_mem _ fun f hf => Submodule.smul_mem _ _ ?_
  have hfne : f ≠ a := Finset.ne_of_mem_erase hf
  simpa [push_nil] using push_uVec_mem_ctrlSub A a hfne (w := []) (r := 0) (by simp [countControls])

private lemma uMix_mem_zeroSumSub [Fintype α] (A : DFA Q α) (a : α) (β : α → ℝ) :
    uMix A a β ∈ zeroSumSub :=
  ctrlSub_le_zeroSumSub A a 0 (uMix_mem_ctrlSub_zero A a β)

private lemma fourierProj_zero_uMix [Nonempty Q] [Fintype α] (A : DFA Q α) (a : α)
    (e : Q ≃ Q) (he : ∀ q, A.step q a = e q) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (permOrder e))
    (β : α → ℝ)
    (hbal : ∀ q₀ : Q,
      let C : Finset Q :=
        @Finset.filter Q (fun q => ∃ k : ℕ, (fun x => A.step x a)^[k] q₀ = q)
          (Classical.decPred _) Finset.univ
      ∑ f ∈ Finset.univ.erase a, β f * ((A.preimage C [f]).card : ℝ) =
        (∑ f ∈ Finset.univ.erase a, β f) * (C.card : ℝ)) :
    fourierProj (push A [a]) (permOrder e) ζ ⟨0, permOrder_pos e⟩ (uMix A a β) = 0 := by
  refine fourierProj_zero_eq_zero_of_dotSet_cycles A a e he hζ fun C hC => ?_
  rcases (mem_orbits_iff e C).mp hC with ⟨q₀, rfl⟩
  have hCeq :
      orbitFinset e q₀ =
        @Finset.filter Q (fun q => ∃ k : ℕ, (fun x => A.step x a)^[k] q₀ = q)
          (Classical.decPred _) Finset.univ := by
    ext q
    simp [mem_orbitFinset, he]
  have hq := hbal q₀
  dsimp only at hq
  rw [← hCeq] at hq
  rw [uMix, dotSet_sum]
  have hterm : ∀ f ∈ Finset.univ.erase a,
      dotSet ((β f : ℂ) • uVec A f) (orbitFinset e q₀) =
        ((β f * (((A.preimage (orbitFinset e q₀) [f]).card : ℝ) - ((orbitFinset e q₀).card : ℝ)) : ℝ) : ℂ) := by
    intro f _
    rw [dotSet_smul, uVec, dotSet_sub, dotSet_push, dotSet_ones, dotSet_ones]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum]
  have hreal0 :
      ∑ f ∈ Finset.univ.erase a,
        β f * (((A.preimage (orbitFinset e q₀) [f]).card : ℝ) - ((orbitFinset e q₀).card : ℝ)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    linarith
  rw [hreal0, Complex.ofReal_zero]

/-! ### Spectral chain expansion and Lemma S.3 (Higher-Multiplicity Control Deletion) -/

/-- Spectral chain `E_{α_r} P_{g_{r-1}} ... P_{g_0} E_{α_0} v`. -/
noncomputable def spectralChain (T : Module.End ℂ (Q → ℂ)) (M : ℕ) (ζ : ℂ) (A : DFA Q α) :
    ∀ {r : ℕ}, (Fin r → α) → (Fin (r + 1) → Fin M) → (Q → ℂ) → (Q → ℂ)
  | 0, _, αs, v => fourierProj T M ζ (αs 0) v
  | r + 1, gs, αs, v =>
    fourierProj T M ζ (αs (Fin.last (r + 1)))
      (push A [gs (Fin.last r)]
        (spectralChain T M ζ A (fun i => gs i.castSucc) (fun i => αs i.castSucc) v))

omit [DecidableEq α] in
/-- Spectral expansion of `push A (wordOfBlock a gs hs) v` over all projector tuples `αs`. -/
private lemma push_wordOfBlock_eq_sum_spectralChain (A : DFA Q α) (a : α)
    {M : ℕ} {ζ : ℂ} (hM : 0 < M) (hTM : (push A [a]) ^ M = 1) (hζ : IsPrimitiveRoot ζ M) :
    ∀ {r : ℕ} (gs : Fin r → α) (hs : Fin (r + 1) → ℕ) (v : Q → ℂ),
      push A (wordOfBlock a gs hs) v =
        ∑ αs : Fin (r + 1) → Fin M,
          (∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ (hs i)) •
            spectralChain (push A [a]) M ζ A gs αs v := by
  intro r
  induction r with
  | zero =>
    intro gs hs v
    simp only [wordOfBlock, push_replicate]
    let T := push A [a]
    have h1 : (T ^ hs 0) v = (T ^ hs 0 * ∑ k : Fin M, fourierProj T M ζ k) v := by
      rw [sum_fourierProj hM hζ, mul_one]
    rw [h1, Finset.mul_sum, LinearMap.sum_apply]
    let e0 : Fin M ≃ (Fin 1 → Fin M) :=
      { toFun := fun k _ => k
        invFun := fun f => f 0
        left_inv := fun _ => rfl
        right_inv := fun f => funext fun i => by rw [Fin.eq_zero i] }
    rw [← Fintype.sum_equiv e0
      (fun k => (T ^ hs 0 * fourierProj T M ζ k) v)
      (fun αs => (∏ i : Fin 1, (ζ ^ (αs i).val) ^ (hs i)) • spectralChain T M ζ A gs αs v)]
    intro k
    rw [T_pow_mul_fourierProj hM hTM hζ]
    simp [e0, spectralChain, T]
  | succ r ih =>
    intro gs hs v
    let T := push A [a]
    simp only [wordOfBlock, push_append, push_replicate, mul_apply_eq_comp]
    rw [ih (fun i => gs i.castSucc) (fun i => hs i.castSucc) v]
    rw [map_sum, map_sum]
    have hstep : ∀ αs' : Fin (r + 1) → Fin M,
        (T ^ hs (Fin.last (r + 1))) (push A [gs (Fin.last r)]
          ((∏ i : Fin (r + 1), (ζ ^ (αs' i).val) ^ hs i.castSucc) •
            spectralChain T M ζ A (fun i => gs i.castSucc) αs' v)) =
        ∑ k : Fin M,
          ((∏ i : Fin (r + 1), (ζ ^ (αs' i).val) ^ hs i.castSucc) *
            (ζ ^ k.val) ^ hs (Fin.last (r + 1))) •
          fourierProj T M ζ k (push A [gs (Fin.last r)]
            (spectralChain T M ζ A (fun i => gs i.castSucc) αs' v)) := by
      intro αs'
      rw [map_smul, map_smul]
      set x := push A [gs (Fin.last r)] (spectralChain T M ζ A (fun i => gs i.castSucc) αs' v)
      have h1 : (T ^ hs (Fin.last (r + 1))) x =
          (T ^ hs (Fin.last (r + 1)) * ∑ k : Fin M, fourierProj T M ζ k) x := by
        rw [sum_fourierProj hM hζ, mul_one]
      rw [h1, Finset.mul_sum, LinearMap.sum_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [T_pow_mul_fourierProj hM hTM hζ, LinearMap.smul_apply, smul_smul]
    rw [Finset.sum_congr rfl fun αs' _ => hstep αs']
    rw [← Fintype.sum_prod_type']
    let eSnoc : ((Fin (r + 1) → Fin M) × Fin M) ≃ (Fin (r + 2) → Fin M) :=
      { toFun := fun p => Fin.snoc p.1 p.2
        invFun := fun f => (fun i => f i.castSucc, f (Fin.last (r + 1)))
        left_inv := fun ⟨αs', k⟩ => by
          apply Prod.ext
          · funext i; simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last]
        right_inv := fun f => by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · simp [Fin.snoc_last]
          · intro j; simp [Fin.snoc_castSucc] }
    rw [Fintype.sum_equiv eSnoc
      (fun p => ((∏ i : Fin (r + 1), (ζ ^ (p.1 i).val) ^ hs i.castSucc) *
          (ζ ^ p.2.val) ^ hs (Fin.last (r + 1))) •
        fourierProj T M ζ p.2 (push A [gs (Fin.last r)]
          (spectralChain T M ζ A (fun i => gs i.castSucc) p.1 v)))
      (fun αs => (∏ i : Fin (r + 2), (ζ ^ (αs i).val) ^ hs i) •
        spectralChain T M ζ A gs αs v)]
    intro ⟨αs', k⟩
    simp only [eSnoc, Equiv.coe_fn_mk, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      spectralChain]

/-- Prefix vector along a spectral chain up to index `p : Fin (r + 1)`. -/
private noncomputable def chainPrefix (T : Module.End ℂ (Q → ℂ)) (M : ℕ) (ζ : ℂ) (A : DFA Q α)
    {r : ℕ} (gs : Fin r → α) (αs : Fin (r + 1) → Fin M) (v : Q → ℂ) :
    (p : ℕ) → p ≤ r → (Q → ℂ)
  | 0, _ => fourierProj T M ζ (αs ⟨0, Nat.zero_lt_succ r⟩) v
  | p + 1, hp =>
    fourierProj T M ζ (αs ⟨p + 1, Nat.lt_succ_of_le hp⟩)
      (push A [gs ⟨p, hp⟩] (chainPrefix T M ζ A gs αs v p (Nat.le_of_succ_le hp)))

/-- Suffix operator from position `p` over `k` steps along a spectral chain. -/
private noncomputable def chainSuffixAux (T : Module.End ℂ (Q → ℂ)) (M : ℕ) (ζ : ℂ) (A : DFA Q α)
    {r : ℕ} (gs : Fin r → α) (αs : Fin (r + 1) → Fin M) :
    (p : ℕ) → (k : ℕ) → p + k ≤ r → Module.End ℂ (Q → ℂ)
  | _, 0, _ => 1
  | p, k + 1, hpk =>
    fourierProj T M ζ (αs ⟨p + k + 1, by omega⟩) *
      push A [gs ⟨p + k, by omega⟩] *
      chainSuffixAux T M ζ A gs αs p k (by omega)

omit [DecidableEq α] in
private lemma chainPrefix_eq_spectralChain (T : Module.End ℂ (Q → ℂ)) (M : ℕ) (ζ : ℂ) (A : DFA Q α) :
    ∀ {r : ℕ} (gs : Fin r → α) (αs : Fin (r + 1) → Fin M) (v : Q → ℂ),
      chainPrefix T M ζ A gs αs v r (le_refl r) = spectralChain T M ζ A gs αs v := by
  intro r
  induction r with
  | zero => intro gs αs v; rfl
  | succ r ih =>
    intro gs αs v
    have hpre : ∀ (p : ℕ) (hp : p ≤ r),
        chainPrefix T M ζ A gs αs v p (Nat.le_succ_of_le hp) =
          chainPrefix T M ζ A (fun i => gs i.castSucc) (fun i => αs i.castSucc) v p hp := by
      intro p
      induction p with
      | zero => intro _; rfl
      | succ p ihp =>
        intro hp
        simp only [chainPrefix, ihp (Nat.le_of_succ_le hp)]
        rfl
    simp only [chainPrefix, spectralChain, hpre r (le_refl r), ih]
    rfl

omit [DecidableEq α] in
private lemma chainSuffixAux_apply_prefix (T : Module.End ℂ (Q → ℂ)) (M : ℕ) (ζ : ℂ) (A : DFA Q α)
    {r : ℕ} (gs : Fin r → α) (αs : Fin (r + 1) → Fin M) (v : Q → ℂ)
    (p k : ℕ) (hpk : p + k ≤ r) :
    chainSuffixAux T M ζ A gs αs p k hpk (chainPrefix T M ζ A gs αs v p (by omega)) =
      chainPrefix T M ζ A gs αs v (p + k) hpk := by
  induction k with
  | zero => simp [chainSuffixAux]
  | succ k ih =>
    simp only [chainSuffixAux, mul_apply_eq_comp, ih (by omega)]
    rfl

private lemma chainPrefix_mem_ctrlSub (A : DFA Q α) (a : α) (M : ℕ) (ζ : ℂ)
    {r : ℕ} (gs : Fin r → α) (hgs : ∀ i, gs i ≠ a) (αs : Fin (r + 1) → Fin M)
    {v : Q → ℂ} (hv : v ∈ ctrlSub A a 0) (p : ℕ) (hp : p ≤ r) :
    chainPrefix (push A [a]) M ζ A gs αs v p hp ∈ ctrlSub A a p := by
  induction p with
  | zero =>
    exact fourierProj_mem_ctrlSub A a M ζ _ 0 hv
  | succ p ih =>
    refine fourierProj_mem_ctrlSub A a M ζ _ (p + 1) ?_
    exact push_control_mem_ctrlSub A a p (hgs ⟨p, hp⟩) (ih (Nat.le_of_succ_le hp))

omit [DecidableEq α] in
private lemma chainPrefix_mem_range (T : Module.End ℂ (Q → ℂ)) (M : ℕ) (ζ : ℂ) (A : DFA Q α)
    {r : ℕ} (gs : Fin r → α) (αs : Fin (r + 1) → Fin M) (v : Q → ℂ)
    (p : ℕ) (hp : p ≤ r) :
    chainPrefix T M ζ A gs αs v p hp ∈ LinearMap.range (fourierProj T M ζ (αs ⟨p, by omega⟩)) := by
  cases p with
  | zero => exact ⟨v, rfl⟩
  | succ p => exact ⟨_, rfl⟩

private lemma chainSuffixAux_mem_ctrlSub (A : DFA Q α) (a : α) (M : ℕ) (ζ : ℂ)
    {r : ℕ} (gs : Fin r → α) (hgs : ∀ i, gs i ≠ a) (αs : Fin (r + 1) → Fin M)
    (p k : ℕ) (hpk : p + k ≤ r) :
    ∀ (s : ℕ) {v : Q → ℂ}, v ∈ ctrlSub A a s →
      chainSuffixAux (push A [a]) M ζ A gs αs p k hpk v ∈ ctrlSub A a (s + k) := by
  induction k with
  | zero =>
    intro s v hv
    simpa [chainSuffixAux] using hv
  | succ k ih =>
    intro s v hv
    simp only [chainSuffixAux, mul_apply_eq_comp]
    refine fourierProj_mem_ctrlSub A a M ζ _ (s + (k + 1)) ?_
    rw [show s + (k + 1) = (s + k) + 1 by omega]
    exact push_control_mem_ctrlSub A a (s + k) (hgs ⟨p + k, by omega⟩) (ih (by omega) s hv)

omit [DecidableEq α] in
/-- **Lemma S.3 (Higher-Multiplicity Control Deletion)**:
1. If `αs 0 = 0` and `E 0 v = 0`, then `spectralChain ... v = 0`.
2. If some `k : Fin M` occurs strictly more than `zEigMult e ζ k` times in `αs`, then
   `spectralChain ... v ∈ ctrlSub A a (r - 1)`. -/
private lemma spectralChain_zero_head_eq_zero (T : Module.End ℂ (Q → ℂ)) (M : ℕ) (ζ : ℂ)
    (A : DFA Q α) : ∀ {r : ℕ} (gs : Fin r → α) (αs : Fin (r + 1) → Fin M) {v : Q → ℂ},
      fourierProj T M ζ (αs 0) v = 0 → spectralChain T M ζ A gs αs v = 0
  | 0, _, _, _, hv0 => hv0
  | r + 1, gs, αs, v, hv0 => by
    simp only [spectralChain]
    have h0 : αs (Fin.castSucc (0 : Fin (r + 1))) = αs 0 := congrArg αs Fin.castSucc_zero
    rw [spectralChain_zero_head_eq_zero T M ζ A (fun i => gs i.castSucc) (fun i => αs i.castSucc)
      (by simpa [h0] using hv0), map_zero, map_zero]

private lemma higherMult_controlDeletion [Nonempty Q] (A : DFA Q α) (a : α)
    (e : Q ≃ Q) (he : ∀ q, A.step q a = e q) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (permOrder e))
    {r : ℕ} (hr : 1 ≤ r) (gs : Fin r → α) (hgs : ∀ i, gs i ≠ a)
    (αs : Fin (r + 1) → Fin (permOrder e)) {v : Q → ℂ} (hv : v ∈ ctrlSub A a 0)
    (k : Fin (permOrder e))
    (hgt : zEigMult e ζ k < (Finset.univ.filter (fun i : Fin (r + 1) => αs i = k)).card) :
    spectralChain (push A [a]) (permOrder e) ζ A gs αs v ∈ ctrlSub A a (r - 1) := by
  classical
  let T := push A [a]
  let M := permOrder e
  set S : Finset (Fin (r + 1)) := Finset.univ.filter (fun i => αs i = k)
  let VZk : Submodule ℂ (Q → ℂ) := LinearMap.range (fourierProj T M ζ k) ⊓ zeroSumSub
  have hfinrank : Module.finrank ℂ VZk = zEigMult e ζ k :=
    (finrank_fourier_and_zeroSum A a e he hζ).2 k
  let vec : S → VZk := fun p =>
    ⟨chainPrefix T M ζ A gs αs v p.val.val (Nat.lt_succ_iff.mp p.val.isLt), by
      refine ⟨?_, ?_⟩
      · have hk_eq : αs p.val = k := (Finset.mem_filter.mp p.property).2
        have hmem := chainPrefix_mem_range T M ζ A gs αs v p.val.val (Nat.lt_succ_iff.mp p.val.isLt)
        rwa [Fin.eta, hk_eq] at hmem
      · exact ctrlSub_le_zeroSumSub A a p.val.val
          (chainPrefix_mem_ctrlSub A a M ζ gs hgs αs hv p.val.val (Nat.lt_succ_iff.mp p.val.isLt))⟩
  have hdep : ¬ LinearIndependent ℂ vec := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_coe, hfinrank] at hle
    omega
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  rcases hdep with ⟨c, hsum0, p₀, hp₀_ne⟩
  let Pnz : Finset S := Finset.univ.filter (fun p => c p ≠ 0)
  have hPnz_ne : Pnz.Nonempty := ⟨p₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp₀_ne⟩⟩
  obtain ⟨q, hq_mem, hq_max⟩ := Finset.exists_max_image Pnz (fun p : S => p.val.val) hPnz_ne
  have hcq_ne : c q ≠ 0 := (Finset.mem_filter.mp hq_mem).2
  -- Extract the vector equation `∑ p ∈ Pnz, c p • prefix p = 0`.
  have hsum_Pnz : ∑ p ∈ Pnz, c p • (vec p : Q → ℂ) = 0 := by
    have hval := congrArg Subtype.val hsum0
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Submodule.coe_zero] at hval
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => c p ≠ 0)] at hval
    have hrest : ∑ p ∈ Finset.univ.filter (fun p => ¬ c p ≠ 0), c p • (vec p : Q → ℂ) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have h0 : c p = 0 := not_not.mp (Finset.mem_filter.mp hp).2
      rw [h0, zero_smul]
    rw [hrest, add_zero] at hval
    exact hval
  -- Isolate `vec q`: `vec q = ∑ p ∈ Pnz.erase q, (-(c p / c q)) • vec p`.
  have hvec_q : (vec q : Q → ℂ) =
      ∑ p ∈ Pnz.erase q, (-(c p / c q)) • (vec p : Q → ℂ) := by
    have hadd := Finset.add_sum_erase Pnz (fun p => c p • (vec p : Q → ℂ)) hq_mem
    rw [hsum_Pnz] at hadd
    have hcq_vec : c q • (vec q : Q → ℂ) = - ∑ p ∈ Pnz.erase q, c p • (vec p : Q → ℂ) :=
      eq_neg_of_add_eq_zero_left hadd
    calc
      (vec q : Q → ℂ) = (c q)⁻¹ • (c q • (vec q : Q → ℂ)) := by
        rw [smul_smul, inv_mul_cancel₀ hcq_ne, one_smul]
      _ = (c q)⁻¹ • (- ∑ p ∈ Pnz.erase q, c p • (vec p : Q → ℂ)) := by rw [hcq_vec]
      _ = ∑ p ∈ Pnz.erase q, (-(c p / c q)) • (vec p : Q → ℂ) := by
        rw [smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [smul_smul, ← neg_smul, div_eq_inv_mul]
  -- Apply `chainSuffixAux` from `q.val.val` to `r`!
  have hq_le : q.val.val ≤ r := Nat.lt_succ_iff.mp q.val.isLt
  have hfull :
      spectralChain T M ζ A gs αs v =
        chainSuffixAux T M ζ A gs αs q.val.val (r - q.val.val) (by omega) (vec q : Q → ℂ) := by
    rw [← chainPrefix_eq_spectralChain]
    have h := chainSuffixAux_apply_prefix T M ζ A gs αs v q.val.val (r - q.val.val) (by omega)
    convert h.symm using 2
    omega
  rw [hfull, hvec_q, map_sum]
  refine Submodule.sum_mem _ fun p hp => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  have hp_mem : p ∈ Pnz := Finset.mem_of_mem_erase hp
  have hp_ne : p ≠ q := Finset.ne_of_mem_erase hp
  have hp_le_q : p.val.val ≤ q.val.val := hq_max p hp_mem
  have hp_lt_q : p.val.val < q.val.val := by
    refine lt_of_le_of_ne hp_le_q ?_
    intro heq
    exact hp_ne (Subtype.ext (Fin.ext heq))
  have hp_in : (vec p : Q → ℂ) ∈ ctrlSub A a p.val.val :=
    chainPrefix_mem_ctrlSub A a M ζ gs hgs αs hv p.val.val (Nat.lt_succ_iff.mp p.val.isLt)
  have hmem_sum := chainSuffixAux_mem_ctrlSub A a M ζ gs hgs αs q.val.val (r - q.val.val)
    (by omega) p.val.val hp_in
  exact ctrlSub_mono A a (by omega) hmem_sum

/-! ### Lemma S.6: Ascending-chain block generation and stabilization (zero `charpoly`!) -/

omit [DecidableEq Q] [DecidableEq α] in
/-- 10-line `charpoly`-free cyclic orbit bound modulo an invariant subspace `U ≤ W`. -/
private lemma iterate_mem_sup_span_lt_finrank_sub (T : Module.End ℂ (Q → ℂ))
    {U W : Submodule ℂ (Q → ℂ)} (hUW : U ≤ W)
    (hU : ∀ x ∈ U, T x ∈ U) (hW : ∀ x ∈ W, T x ∈ W) {v : Q → ℂ} (hv : v ∈ W) :
    ∀ k : ℕ, (T ^ k) v ∈ U ⊔ Submodule.span ℂ
      { x | ∃ j : ℕ, j < Module.finrank ℂ W - Module.finrank ℂ U ∧ x = (T ^ j) v } := by
  let s := Module.finrank ℂ W - Module.finrank ℂ U
  let F : ℕ → Submodule ℂ (Q → ℂ) := fun m =>
    U ⊔ Submodule.span ℂ { x | ∃ j : ℕ, j < m ∧ x = (T ^ j) v }
  have hpow_W : ∀ k : ℕ, (T ^ k) v ∈ W := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih => rw [pow_succ', mul_apply_eq_comp]; exact hW _ ih
  have hF_le_W : ∀ m : ℕ, F m ≤ W := by
    intro m
    refine sup_le hUW ?_
    rw [Submodule.span_le]
    rintro x ⟨j, _, rfl⟩
    exact hpow_W j
  have hF_mono : ∀ {m₁ m₂ : ℕ}, m₁ ≤ m₂ → F m₁ ≤ F m₂ := by
    intro m₁ m₂ hm
    refine sup_le_sup_left (Submodule.span_mono ?_) U
    rintro x ⟨j, hj, rfl⟩
    exact ⟨j, lt_of_lt_of_le hj hm, rfl⟩
  by_cases hcol : ∃ m < s, F (m + 1) ≤ F m
  · rcases hcol with ⟨m, hm, hle⟩
    have hFm_inv : ∀ x ∈ F m, T x ∈ F m := by
      intro x hx
      rw [Submodule.mem_sup] at hx
      rcases hx with ⟨u, hu, y, hy, rfl⟩
      rw [map_add]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (hU u hu)) ?_
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨j, hj, rfl⟩
        rw [← mul_apply_eq_comp, ← pow_succ']
        exact hle (Submodule.mem_sup_right (Submodule.subset_span ⟨j + 1, by omega, rfl⟩))
      · simp
      · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
      · intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ c ha
    have hv_Fm : v ∈ F m :=
      hle (Submodule.mem_sup_right (Submodule.subset_span ⟨0, Nat.zero_lt_succ m, by simp⟩))
    intro k
    have hk_Fm : (T ^ k) v ∈ F m := by
      induction k with
      | zero => simpa using hv_Fm
      | succ k ih => rw [pow_succ', mul_apply_eq_comp]; exact hFm_inv _ ih
    exact hF_mono (le_of_lt hm) hk_Fm
  · push Not at hcol
    have hstrict : ∀ m < s, F m < F (m + 1) := fun m hm =>
      lt_of_le_of_ne (hF_mono (Nat.le_succ m)) (fun heq => hcol m hm heq.ge)
    have hgrow : ∀ m ≤ s, Module.finrank ℂ U + m ≤ Module.finrank ℂ (F m) := by
      intro m
      induction m with
      | zero =>
        intro _
        have hF0 : F 0 = U := by
          simp [F]
        rw [hF0, add_zero]
      | succ m ih =>
        intro hm
        have hlt := Submodule.finrank_lt_finrank_of_lt (hstrict m (by omega))
        have ihm := ih (by omega)
        omega
    have hFs_eq_W : F s = W := by
      refine Submodule.eq_of_le_of_finrank_eq (hF_le_W s) ?_
      have h1 := hgrow s (le_refl s)
      have h2 := Submodule.finrank_mono (hF_le_W s)
      have hUW_fin : Module.finrank ℂ U ≤ Module.finrank ℂ W := Submodule.finrank_mono hUW
      omega
    intro k
    rw [show U ⊔ Submodule.span ℂ
      { x | ∃ j : ℕ, j < Module.finrank ℂ W - Module.finrank ℂ U ∧ x = (T ^ j) v } = F s from rfl,
      hFs_eq_W]
    exact hpow_W k

/-- **Lemma S.6(1a)**: For a synchronizing DFA on `n ≥ 2` states with permutation letter `a`,
`1 ≤ finrank (ctrlSub A a 0)`. -/
private lemma ctrlSub_zero_finrank_pos (A : DFA Q α) (a : α)
    (e : Q ≃ Q) (he : ∀ q, A.step q a = e q)
    (hSync : A.IsSynchronizing) (hcard : 2 ≤ Fintype.card Q) :
    1 ≤ Module.finrank ℂ (ctrlSub A a 0) := by
  by_contra h0
  have hfin0 : Module.finrank ℂ (ctrlSub A a 0) = 0 := by omega
  have hbot : ctrlSub A a 0 = ⊥ := Submodule.finrank_eq_zero.mp hfin0
  have hpush_one : ∀ g : α, push A [g] onesVec = onesVec := by
    intro g
    by_cases hga : g = a
    · subst hga; exact push_perm_ones A g e he
    · have hmem : uVec A g ∈ ctrlSub A a 0 := by
        simpa [push_nil] using push_uVec_mem_ctrlSub A a hga (w := []) (r := 0) (by simp [countControls])
      rw [hbot, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
  have hpush_word : ∀ w : List α, push A w onesVec = onesVec := by
    intro w
    induction w with
    | nil => simp [push_nil]
    | cons g u ih => rw [push_cons, mul_apply_eq_comp, hpush_one g, ih]
  rcases hSync with ⟨w, q₀, hq₀⟩
  have hpre : A.preimage {q₀} w = Finset.univ := by
    ext q; simp [hq₀ q]
  have hdot : dotSet (push A w onesVec) {q₀} = dotSet onesVec {q₀} := by rw [hpush_word w]
  rw [dotSet_push, hpre, dotSet_ones, dotSet_ones, Finset.card_univ, Finset.card_singleton] at hdot
  have hcard1 : Fintype.card Q = 1 := by exact_mod_cast hdot
  omega

/-- **Lemma S.6(1b) (Stabilization)**: For `n ≥ 2`, `ctrlSub A a r ≤ ctrlSub A a (n - 2)` for all `r`. -/
private lemma ctrlSub_stabilize [Nonempty Q] (A : DFA Q α) (a : α)
    (e : Q ≃ Q) (he : ∀ q, A.step q a = e q)
    (hSync : A.IsSynchronizing) (hcard : 2 ≤ Fintype.card Q) :
    ∀ r : ℕ, ctrlSub A a r ≤ ctrlSub A a (Fintype.card Q - 2) := by
  have h0_pos : 1 ≤ Module.finrank ℂ (ctrlSub A a 0) :=
    ctrlSub_zero_finrank_pos A a e he hSync hcard
  have hclosed_of_eq : ∀ k : ℕ, ctrlSub A a (k + 1) ≤ ctrlSub A a k →
      ∀ r : ℕ, ctrlSub A a r ≤ ctrlSub A a k := by
    intro k hkeq r
    have hinv_all : ∀ g : α, ∀ v ∈ ctrlSub A a k, push A [g] v ∈ ctrlSub A a k := by
      intro g v hv
      by_cases hga : g = a
      · subst hga; exact push_perm_mem_ctrlSub A g k hv
      · exact hkeq (push_control_mem_ctrlSub A a k hga hv)
    have hinv_word : ∀ w : List α, ∀ v ∈ ctrlSub A a k, push A w v ∈ ctrlSub A a k := by
      intro w
      induction w with
      | nil => intro v hv; simpa [push_nil] using hv
      | cons g u ih =>
        intro v hv
        rw [push_cons, mul_apply_eq_comp]
        exact ih _ (hinv_all g v hv)
    rw [ctrlSub, Submodule.span_le]
    rintro v ⟨f, w, hf, _, rfl⟩
    have hu : uVec A f ∈ ctrlSub A a k :=
      ctrlSub_mono A a (Nat.zero_le k) (by
        simpa [push_nil] using push_uVec_mem_ctrlSub A a hf (w := []) (r := 0) (by simp [countControls]))
    exact hinv_word w _ hu
  by_cases hcol : ∃ k < Fintype.card Q - 2, ctrlSub A a (k + 1) ≤ ctrlSub A a k
  · rcases hcol with ⟨k, hk, hkeq⟩
    intro r
    exact (hclosed_of_eq k hkeq r).trans (ctrlSub_mono A a (le_of_lt hk))
  · push Not at hcol
    have hstrict : ∀ k < Fintype.card Q - 2, ctrlSub A a k < ctrlSub A a (k + 1) := fun k hk =>
      lt_of_le_of_ne (ctrlSub_mono A a (Nat.le_succ k)) (fun heq => hcol k hk heq.ge)
    have hgrow : ∀ k ≤ Fintype.card Q - 2, k + 1 ≤ Module.finrank ℂ (ctrlSub A a k) := by
      intro k
      induction k with
      | zero => intro _; exact h0_pos
      | succ k ih =>
        intro hk
        have hlt := Submodule.finrank_lt_finrank_of_lt (hstrict k (by omega))
        have ihk := ih (by omega)
        omega
    have htop : ctrlSub A a (Fintype.card Q - 2) = zeroSumSub := by
      refine Submodule.eq_of_le_of_finrank_eq (ctrlSub_le_zeroSumSub A a _) ?_
      have h1 := hgrow (Fintype.card Q - 2) (le_refl _)
      have h2 := Submodule.finrank_mono (ctrlSub_le_zeroSumSub A a (Fintype.card Q - 2))
      have hZ : Module.finrank ℂ (zeroSumSub (Q := Q)) = Fintype.card Q - 1 := finrank_zeroSumSub
      omega
    intro r
    rw [htop]
    exact ctrlSub_le_zeroSumSub A a r

/-- **Lemma S.6(2) (Block-Word Generation)**:
Whenever `1 ≤ finrank (L 0)` and `finrank (L 0) < finrank (L 1) < ... < finrank (L r)`,
for every `k ≤ r`, `L k` is generated modulo `L (k - 1)` (or `⊥` at `k = 0`) by `k`-control
block words `wordOfBlock a gs hs` with `(∑ i, hs i) + k + 1 ≤ finrank (L k)`. -/
private lemma ctrlSub_block_gen (A : DFA Q α) (a : α) :
    ∀ k : ℕ, 1 ≤ Module.finrank ℂ (ctrlSub A a 0) →
      (∀ j < k, Module.finrank ℂ (ctrlSub A a j) < Module.finrank ℂ (ctrlSub A a (j + 1))) →
      ctrlSub A a k ≤
        (if k = 0 then ⊥ else ctrlSub A a (k - 1)) ⊔
          Submodule.span ℂ
            { v | ∃ (f : α) (gs : Fin k → α) (hs : Fin (k + 1) → ℕ),
              f ≠ a ∧ (∀ i, gs i ≠ a) ∧
              (∑ i, hs i) + k + 1 ≤ Module.finrank ℂ (ctrlSub A a k) ∧
              v = push A (wordOfBlock a gs hs) (uVec A f) } := by
  intro k
  induction k with
  | zero =>
    intro h0 _
    simp only [↓reduceIte, bot_sup_eq]
    rw [ctrlSub, Submodule.span_le]
    rintro v ⟨f, w, hf, hcnt, rfl⟩
    have hw0 : countControls a w = 0 := Nat.le_zero.mp hcnt
    have hw_rep : w = List.replicate w.length a := word_eq_replicate_of_countControls_zero a w hw0
    rw [hw_rep, push_replicate]
    have hu_mem : uVec A f ∈ ctrlSub A a 0 := by
      simpa [push_nil] using push_uVec_mem_ctrlSub A a hf (w := []) (r := 0) (by simp [countControls])
    have hcyc := iterate_mem_sup_span_lt_finrank_sub (push A [a])
      (U := ⊥) (W := ctrlSub A a 0) bot_le (fun _ hx => by rw [(Submodule.mem_bot ℂ).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ hx => push_perm_mem_ctrlSub A a 0 hx) hu_mem w.length
    simp only [finrank_bot, Nat.sub_zero, bot_sup_eq] at hcyc
    refine (Submodule.span_mono ?_) hcyc
    rintro x ⟨j, hj, rfl⟩
    refine ⟨f, Fin.elim0, fun _ => j, hf, fun i => Fin.elim0 i, ?_, ?_⟩
    · exact hj
    · simp [wordOfBlock, push_replicate]
  | succ k ih =>
    intro h0 hstrict
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    have hih := ih h0 (fun j hj => hstrict j (Nat.lt_succ_of_lt hj))
    let G : Submodule ℂ (Q → ℂ) :=
      Submodule.span ℂ
        { v | ∃ (f : α) (gs : Fin (k + 1) → α) (hs : Fin (k + 2) → ℕ),
          f ≠ a ∧ (∀ i, gs i ≠ a) ∧
          (∑ i, hs i) + (k + 1) + 1 ≤ Module.finrank ℂ (ctrlSub A a (k + 1)) ∧
          v = push A (wordOfBlock a gs hs) (uVec A f) }
    change ctrlSub A a (k + 1) ≤ ctrlSub A a k ⊔ G
    rw [ctrlSub, Submodule.span_le]
    rintro v ⟨f, w, hf, hcnt, rfl⟩
    by_cases hle : countControls a w ≤ k
    · exact Submodule.mem_sup_left (push_uVec_mem_ctrlSub A a hf hle)
    · have hcnt_eq : countControls a w = k + 1 := by omega
      obtain ⟨w', g, h, hg, hw'cnt, hw_eq⟩ := word_split_last_control a w k hcnt_eq
      rw [hw_eq, push_append, push_append, push_replicate, mul_apply_eq_comp, mul_apply_eq_comp]
      have hw'_in : push A w' (uVec A f) ∈ ctrlSub A a k :=
        push_uVec_mem_ctrlSub A a hf hw'cnt.le
      have hw'_split := hih hw'_in
      rw [Submodule.mem_sup] at hw'_split
      rcases hw'_split with ⟨u_prev, hu_prev, y_gen, hy_gen, hdecomp⟩
      rw [← hdecomp, map_add, map_add]
      refine Submodule.add_mem _ ?_ ?_
      · -- `u_prev` comes from `L (k - 1)` (or `⊥`), so `T^h (P_g u_prev) ∈ L k`.
        refine Submodule.mem_sup_left ?_
        by_cases hk0 : k = 0
        · subst hk0
          simp only [↓reduceIte, Submodule.mem_bot] at hu_prev
          rw [hu_prev, map_zero, map_zero]
          exact Submodule.zero_mem _
        · simp only [hk0, ↓reduceIte] at hu_prev
          have hpg : push A [g] u_prev ∈ ctrlSub A a k := by
            have := push_control_mem_ctrlSub A a (k - 1) hg hu_prev
            rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)] at this
          exact push_perm_pow_mem_ctrlSub A a k h hpg
      · -- `y_gen` is a linear combination of `k`-control block generators!
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hy_gen
        · rintro _ ⟨f', gs', hs', hf', hgs', hsum', rfl⟩
          have hsrc_mem : push A [g] (push A (wordOfBlock a gs' hs') (uVec A f')) ∈
              ctrlSub A a (k + 1) := by
            refine push_control_mem_ctrlSub A a k hg ?_
            exact push_uVec_mem_ctrlSub A a hf' (by rw [countControls_wordOfBlock a gs' hs' hgs'])
          have hcyc := iterate_mem_sup_span_lt_finrank_sub (push A [a])
            (ctrlSub_mono A a (Nat.le_succ k))
            (fun _ => push_perm_mem_ctrlSub A a k)
            (fun _ => push_perm_mem_ctrlSub A a (k + 1))
            hsrc_mem h
          refine (sup_le_sup_left (Submodule.span_mono ?_) (ctrlSub A a k)) hcyc
          rintro x ⟨j, hj, rfl⟩
          let gs : Fin (k + 1) → α := Fin.snoc gs' g
          let hs : Fin (k + 2) → ℕ := Fin.snoc hs' j
          refine ⟨f', gs, hs, hf', ?_, ?_, ?_⟩
          · intro i
            refine Fin.lastCases ?_ ?_ i
            · simpa [gs] using hg
            · intro i'; simpa [gs] using hgs' i'
          · have hsum_hs : ∑ i : Fin (k + 2), hs i = (∑ i : Fin (k + 1), hs' i) + j := by
              rw [Fin.sum_univ_castSucc]
              simp [hs]
            have hj' : j < Module.finrank ℂ (ctrlSub A a (k + 1)) - Module.finrank ℂ (ctrlSub A a k) := hj
            have hdk_lt : Module.finrank ℂ (ctrlSub A a k) <
                Module.finrank ℂ (ctrlSub A a (k + 1)) := hstrict k (Nat.lt_succ_self k)
            omega
          · have hgs_cast : (fun i : Fin k => gs i.castSucc) = gs' := funext fun i => by simp [gs]
            have hhs_cast : (fun i : Fin (k + 1) => hs i.castSucc) = hs' :=
              funext fun i => by simp [hs]
            simp only [wordOfBlock, hgs_cast, hhs_cast, gs, hs, Fin.snoc_last,
              push_append, push_replicate, mul_apply_eq_comp]
        · simp
        · intro x₁ x₂ _ _ hx₁ hx₂
          rw [map_add, map_add]
          exact Submodule.add_mem _ hx₁ hx₂
        · intro c x _ hx
          rw [map_smul, map_smul]
          exact Submodule.smul_mem _ c hx

end Subspaces

end ControlFiltration

/-! ### Section 6: Positive annihilating polynomial, Proposition S.5, and Theorems B & C -/

section SpectralDescent

variable {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]

open Polynomial

/-- Geometric sum polynomial `1 + X + ... + X^{m - 1}` over `ℕ`. -/
noncomputable def geomSumNat (m : ℕ) : Polynomial ℕ :=
  ∑ j ∈ Finset.range m, X ^ j

private lemma coeff_geomSumNat (m k : ℕ) :
    (geomSumNat m).coeff k = if k < m then 1 else 0 := by
  rw [geomSumNat, coeff_finset_sum]
  simp_rw [coeff_X_pow]
  by_cases hk : k < m
  · simp only [hk, ↓reduceIte]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_range.mpr hk) h
  · simp only [hk, ↓reduceIte]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj_lt := Finset.mem_range.mp hj
    have hne : k ≠ j := by omega
    simp [hne]

/-- Gap-free positivity is preserved by multiplication of `ℕ`-polynomials. -/
private lemma gapFree_mul {p q : Polynomial ℕ} {d₁ d₂ : ℕ}
    (hp1 : ∀ k ≤ d₁, 1 ≤ p.coeff k) (hp0 : ∀ k, d₁ < k → p.coeff k = 0)
    (hq1 : ∀ k ≤ d₂, 1 ≤ q.coeff k) (hq0 : ∀ k, d₂ < k → q.coeff k = 0) :
    (∀ k ≤ d₁ + d₂, 1 ≤ (p * q).coeff k) ∧ (∀ k, d₁ + d₂ < k → (p * q).coeff k = 0) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    rw [coeff_mul]
    let a := min k d₁
    let b := k - a
    have hab : (a, b) ∈ Finset.antidiagonal k := by
      rw [Finset.mem_antidiagonal]
      omega
    have ha_le : a ≤ d₁ := min_le_right k d₁
    have hb_le : b ≤ d₂ := by omega
    have hterm : 1 ≤ p.coeff a * q.coeff b :=
      Nat.mul_pos (hp1 a ha_le) (hq1 b hb_le)
    exact hterm.trans (Finset.single_le_sum (f := fun x : ℕ × ℕ => p.coeff x.1 * q.coeff x.2)
      (fun _ _ => Nat.zero_le _) hab)
  · intro k hk
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hsum : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
    by_cases h1 : d₁ < x.1
    · rw [hp0 x.1 h1, zero_mul]
    · rw [hq0 x.2 (by omega), mul_zero]

/-- Product of geometric sums over all distinct cycle lengths of `e`. -/
noncomputable def posProdPoly (e : Q ≃ Q) : Polynomial ℕ :=
  ∏ m ∈ (orbits e).image Finset.card, geomSumNat m

/-- Degree of `posProdPoly e`: `∑_{m ∈ distinct cycle lengths} (m - 1)`. -/
noncomputable def posProdDeg (e : Q ≃ Q) : ℕ :=
  ∑ m ∈ (orbits e).image Finset.card, (m - 1)

private lemma posProdPoly_props [Nonempty Q] (e : Q ≃ Q) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (permOrder e)) :
    (∀ s ≤ posProdDeg e, 1 ≤ (posProdPoly e).coeff s) ∧
    (∀ s, posProdDeg e < s → (posProdPoly e).coeff s = 0) ∧
    posProdDeg e ≤ Fintype.card Q - (orbits e).card ∧
    (∀ k : Fin (permOrder e), k.val ≠ 0 → 0 < zEigMult e ζ k →
      eval (ζ ^ (k : ℕ)) ((posProdPoly e).map (Nat.castRingHom ℂ)) = 0) := by
  have hpos_gen : ∀ S : Finset ℕ, (∀ m ∈ S, 1 ≤ m) →
      (∀ s ≤ ∑ m ∈ S, (m - 1), 1 ≤ (∏ m ∈ S, geomSumNat m).coeff s) ∧
      (∀ s, (∑ m ∈ S, (m - 1)) < s → (∏ m ∈ S, geomSumNat m).coeff s = 0) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun s hs => ?_, fun s hs => ?_⟩
      · simp only [Finset.sum_empty, Nat.le_zero] at hs
        subst hs; simp
      · simp only [Finset.sum_empty] at hs
        rw [Finset.prod_empty, coeff_one]
        split_ifs <;> omega
    | insert m S hm ih =>
      intro hge
      have hm1 : 1 ≤ m := hge m (Finset.mem_insert_self m S)
      obtain ⟨ih1, ih0⟩ := ih (fun x hx => hge x (Finset.mem_insert_of_mem hx))
      rw [Finset.sum_insert hm, Finset.prod_insert hm]
      refine gapFree_mul ?_ ?_ ih1 ih0
      · intro k hk
        rw [coeff_geomSumNat]
        have hlt : k < m := by omega
        simp [hlt]
      · intro k hk
        rw [coeff_geomSumNat]
        have hnot : ¬ k < m := by omega
        simp [hnot]
  have hge1 : ∀ m ∈ (orbits e).image Finset.card, 1 ≤ m := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨C, hC, rfl⟩
    exact card_pos_of_mem_orbits e hC
  obtain ⟨h1, h0⟩ := hpos_gen ((orbits e).image Finset.card) hge1
  have hdeg_le : posProdDeg e ≤ Fintype.card Q - (orbits e).card := by
    have himg_le : ∀ s : Finset (Finset Q),
        ∑ m ∈ s.image Finset.card, (m - 1) ≤ ∑ C ∈ s, (C.card - 1) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert C t hCt ih =>
        rw [Finset.image_insert, Finset.sum_insert hCt]
        by_cases hmem : C.card ∈ t.image Finset.card
        · rw [Finset.insert_eq_of_mem hmem]
          omega
        · rw [Finset.sum_insert hmem]
          omega
    have hsum_le : posProdDeg e ≤ ∑ C ∈ orbits e, (C.card - 1) := himg_le (orbits e)
    have hsum_orb : (∑ C ∈ orbits e, (C.card - 1)) + (orbits e).card = Fintype.card Q := by
      calc
        (∑ C ∈ orbits e, (C.card - 1)) + (orbits e).card
            = ∑ C ∈ orbits e, ((C.card - 1) + 1) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
        _ = ∑ C ∈ orbits e, C.card := by
              refine Finset.sum_congr rfl fun C hC => Nat.sub_add_cancel (card_pos_of_mem_orbits e hC)
        _ = Fintype.card Q := sum_card_orbits e
    omega
  have hroot : ∀ k : Fin (permOrder e), k.val ≠ 0 → 0 < zEigMult e ζ k →
      eval (ζ ^ (k : ℕ)) ((posProdPoly e).map (Nat.castRingHom ℂ)) = 0 := by
    intro k hk0 hdz
    have hνpos : 0 < eigMult e ζ k := by simpa [zEigMult, hk0] using hdz
    unfold eigMult at hνpos
    obtain ⟨C, hC_filt⟩ := Finset.card_pos.mp hνpos
    have hC : C ∈ orbits e := (Finset.mem_filter.mp hC_filt).1
    have hpow : (ζ ^ (k : ℕ)) ^ C.card = 1 := (Finset.mem_filter.mp hC_filt).2
    have hmem : C.card ∈ (orbits e).image Finset.card := Finset.mem_image_of_mem Finset.card hC
    rw [posProdPoly, Polynomial.map_prod, eval_prod]
    refine Finset.prod_eq_zero hmem ?_
    have hne1 : ζ ^ (k : ℕ) ≠ 1 := by
      intro h1
      have hdvd := hζ.dvd_of_pow_eq_one k.val h1
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd
      have := k.isLt
      omega
    have heval : eval (ζ ^ (k : ℕ)) ((geomSumNat C.card).map (Nat.castRingHom ℂ)) =
        ∑ j ∈ Finset.range C.card, (ζ ^ (k : ℕ)) ^ j := by
      rw [geomSumNat, Polynomial.map_sum]
      change evalRingHom (ζ ^ (k : ℕ)) (∑ j ∈ Finset.range C.card, (X ^ j : Polynomial ℕ).map (Nat.castRingHom ℂ)) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => by simp
    rw [heval, geom_sum_eq hne1, hpow, sub_self, zero_div]
  exact ⟨h1, h0, hdeg_le, hroot⟩

/-! ### Lemma S.2: Annihilation of `uMix` and finite-power spanning via `P_pos` -/

/-- **Lemma S.2(a)**: `∑_{s ≤ d} P_pos.coeff s • (T ^ s) uMix = 0`. -/
private lemma posPoly_annihilate_uMix [Nonempty Q] [DecidableEq α] [Fintype α]
    (A : DFA Q α) (a : α) (e : Q ≃ Q) (he : ∀ q, A.step q a = e q)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (permOrder e))
    {P_pos : Polynomial ℕ} {d : ℕ}
    (hP0 : ∀ s, d < s → P_pos.coeff s = 0)
    (hProot : ∀ k : Fin (permOrder e), k.val ≠ 0 → 0 < zEigMult e ζ k →
      eval (ζ ^ (k : ℕ)) (P_pos.map (Nat.castRingHom ℂ)) = 0)
    {v : Q → ℂ} (hv0 : fourierProj (push A [a]) (permOrder e) ζ ⟨0, permOrder_pos e⟩ v = 0) :
    ∑ s ∈ Finset.range (d + 1), ((P_pos.coeff s : ℕ) : ℂ) • (((push A [a]) ^ s) v) = 0 := by
  let T := push A [a]
  let M := permOrder e
  have hM : 0 < M := permOrder_pos e
  have hTM : T ^ M = 1 := push_perm_pow_permOrder A a e he
  let Op : Module.End ℂ (Q → ℂ) :=
    ∑ s ∈ Finset.range (d + 1), ((P_pos.coeff s : ℕ) : ℂ) • (T ^ s)
  have hLHS : ∑ s ∈ Finset.range (d + 1), ((P_pos.coeff s : ℕ) : ℂ) • ((T ^ s) v) = Op v := by
    simp [Op, LinearMap.sum_apply]
  rw [hLHS]
  have hsplit : Op v = ((∑ k : Fin M, fourierProj T M ζ k) * Op) v := by
    rw [sum_fourierProj hM hζ, one_mul]
  rw [hsplit, Finset.sum_mul, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  -- Compute `E_k * Op = (eval (ζ^k) P_pos) • E_k`.
  have hEkOp : fourierProj T M ζ k * Op =
      eval (ζ ^ (k : ℕ)) (P_pos.map (Nat.castRingHom ℂ)) • fourierProj T M ζ k := by
    rw [Finset.mul_sum]
    have hterm : ∀ s ∈ Finset.range (d + 1),
        fourierProj T M ζ k * (((P_pos.coeff s : ℕ) : ℂ) • (T ^ s)) =
          (((P_pos.coeff s : ℕ) : ℂ) * (ζ ^ (k : ℕ)) ^ s) • fourierProj T M ζ k := by
      intro s _
      rw [Algebra.mul_smul_comm, fourierProj_mul_T_pow hM hTM hζ, smul_smul]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul]
    congr 1
    rw [eval_eq_sum_range' (n := d + 1)]
    · refine Finset.sum_congr rfl fun s _ => by simp [coeff_map]
    · by_cases hzero : P_pos.map (Nat.castRingHom ℂ) = 0
      · rw [hzero, natDegree_zero]; omega
      · exact Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun s hs => by
          rw [coeff_map, hP0 s hs, map_zero])
  rw [hEkOp, LinearMap.smul_apply]
  by_cases hk0 : k.val = 0
  · have hk_eq : k = ⟨0, hM⟩ := Fin.ext hk0
    rw [hk_eq, hv0, smul_zero]
  · by_cases hdz : 0 < zEigMult e ζ k
    · rw [hProot k hk0 hdz, zero_smul]
    · have hν0 : eigMult e ζ k = 0 := by
        have h0 : zEigMult e ζ k = 0 := by omega
        simpa [zEigMult, hk0] using h0
      have hfin0 : Module.finrank ℂ (LinearMap.range (fourierProj T M ζ k)) = 0 := by
        rw [(finrank_fourier_and_zeroSum A a e he hζ).1 k, hν0]
      have hbot : LinearMap.range (fourierProj T M ζ k) = ⊥ := Submodule.finrank_eq_zero.mp hfin0
      have hEk_v : fourierProj T M ζ k v = 0 := by
        have : fourierProj T M ζ k v ∈ LinearMap.range (fourierProj T M ζ k) := ⟨v, rfl⟩
        rwa [hbot, Submodule.mem_bot] at this
      rw [hEk_v, smul_zero]

/-- **Lemma S.2(b)**: If `dotSet ((T^s) v) S = 0` for all `0 ≤ s ≤ d`, then
`dotSet ((T^k) v) S = 0` for ALL `k : ℕ`. -/
private lemma dotSet_pow_eq_zero_of_le_posPoly_deg [Nonempty Q]
    (A : DFA Q α) (a : α) (e : Q ≃ Q) (he : ∀ q, A.step q a = e q)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (permOrder e))
    {P_pos : Polynomial ℕ} {d : ℕ}
    (hP1 : ∀ s ≤ d, 1 ≤ P_pos.coeff s)
    (hP0 : ∀ s, d < s → P_pos.coeff s = 0)
    (hProot : ∀ k : Fin (permOrder e), k.val ≠ 0 → 0 < zEigMult e ζ k →
      eval (ζ ^ (k : ℕ)) (P_pos.map (Nat.castRingHom ℂ)) = 0)
    (v : Q → ℂ) (S : Finset Q)
    (hinit : ∀ s ≤ d, dotSet (((push A [a]) ^ s) v) S = 0) :
    ∀ k : ℕ, dotSet (((push A [a]) ^ k) v) S = 0 := by
  let T := push A [a]
  let M := permOrder e
  have hM : 0 < M := permOrder_pos e
  have hTM : T ^ M = 1 := push_perm_pow_permOrder A a e he
  let P_c : Polynomial ℂ := P_pos.map (Nat.castRingHom ℂ)
  let Q_ann : Polynomial ℂ := (X - 1) * P_c
  have hQ_gt : ∀ j, d + 1 < j → Q_ann.coeff j = 0 := by
    intro j hj
    have : Q_ann = X ^ 1 * P_c - P_c := by simp [Q_ann]; ring
    rw [this, coeff_sub, coeff_X_pow_mul']
    have hP_gt : ∀ s, d < s → P_c.coeff s = 0 := fun s hs => by
      simp [P_c, hP0 s hs]
    rw [hP_gt j (by omega), sub_zero]
    split_ifs with hj1
    · exact hP_gt (j - 1) (by omega)
    · rfl
  have hQ_top : Q_ann.coeff (d + 1) = (P_pos.coeff d : ℂ) := by
    have : Q_ann = X ^ 1 * P_c - P_c := by simp [Q_ann]; ring
    rw [this, coeff_sub, coeff_X_pow_mul']
    have h1 : 1 ≤ d + 1 := by omega
    simp only [h1, ↓reduceIte, Nat.add_sub_cancel]
    have hd1 : P_c.coeff (d + 1) = 0 := by simp [P_c, hP0 (d + 1) (by omega)]
    rw [hd1, sub_zero]
    simp [P_c]
  have hQ_top_ne : Q_ann.coeff (d + 1) ≠ 0 := by
    rw [hQ_top]
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hP1 d (le_refl d)))
  -- Operator `∑_{j ≤ d + 1} Q_ann.coeff j • T^j = 0` on ALL of `Q → ℂ`!
  let AnnOp : Module.End ℂ (Q → ℂ) := ∑ j ∈ Finset.range (d + 2), Q_ann.coeff j • (T ^ j)
  have hAnn_zero : AnnOp = 0 := by
    have hsplit : AnnOp = (∑ k : Fin M, fourierProj T M ζ k) * AnnOp := by
      rw [sum_fourierProj hM hζ, one_mul]
    rw [hsplit, Finset.sum_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hEkAnn : fourierProj T M ζ k * AnnOp =
        eval (ζ ^ (k : ℕ)) Q_ann • fourierProj T M ζ k := by
      rw [Finset.mul_sum]
      have hterm : ∀ j ∈ Finset.range (d + 2),
          fourierProj T M ζ k * (Q_ann.coeff j • (T ^ j)) =
            (Q_ann.coeff j * (ζ ^ (k : ℕ)) ^ j) • fourierProj T M ζ k := by
        intro j _
        rw [Algebra.mul_smul_comm, fourierProj_mul_T_pow hM hTM hζ, smul_smul]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul]
      congr 1
      rw [eval_eq_sum_range' (n := d + 2)]
      by_cases h0 : Q_ann = 0
      · rw [h0, natDegree_zero]; omega
      · exact Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr hQ_gt)
    rw [hEkAnn]
    by_cases hk0 : k.val = 0
    · have hev : eval (ζ ^ (k : ℕ)) Q_ann = 0 := by
        simp [Q_ann, hk0]
      rw [hev, zero_smul]
    · by_cases hdz : 0 < zEigMult e ζ k
      · have hev : eval (ζ ^ (k : ℕ)) Q_ann = 0 := by
          simp [Q_ann, P_c, hProot k hk0 hdz]
        rw [hev, zero_smul]
      · have hν0 : eigMult e ζ k = 0 := by
          have h0 : zEigMult e ζ k = 0 := by omega
          simpa [zEigMult, hk0] using h0
        have hfin0 : Module.finrank ℂ (LinearMap.range (fourierProj T M ζ k)) = 0 := by
          rw [(finrank_fourier_and_zeroSum A a e he hζ).1 k, hν0]
        have hbot : LinearMap.range (fourierProj T M ζ k) = ⊥ := Submodule.finrank_eq_zero.mp hfin0
        have hEk0 : fourierProj T M ζ k = 0 := by
          refine LinearMap.ext fun x => ?_
          have : fourierProj T M ζ k x ∈ LinearMap.range (fourierProj T M ζ k) := ⟨x, rfl⟩
          rwa [hbot, Submodule.mem_bot] at this
        rw [hEk0, smul_zero]
  -- Strong induction on `k` using `AnnOp = 0`.
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k ≤ d
    · exact hinit k hk
    · let m := k - (d + 1)
      have hm_add : m + (d + 1) = k := by omega
      have h0 : dotSet ((T ^ m * AnnOp) v) S = 0 := by rw [hAnn_zero, mul_zero]; simp [dotSet]
      have hexp : (T ^ m * AnnOp) v =
          ∑ j ∈ Finset.range (d + 2), Q_ann.coeff j • ((T ^ (m + j)) v) := by
        simp only [AnnOp, Finset.mul_sum, LinearMap.sum_apply, Algebra.mul_smul_comm,
          LinearMap.smul_apply, ← pow_add]
      rw [hexp, dotSet_sum, Finset.sum_range_succ] at h0
      have hinit_sum :
          ∑ j ∈ Finset.range (d + 1), dotSet (Q_ann.coeff j • ((T ^ (m + j)) v)) S = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj_lt := Finset.mem_range.mp hj
        rw [dotSet_smul, ih (m + j) (by omega), mul_zero]
      rw [hinit_sum, zero_add, hm_add, dotSet_smul] at h0
      exact (mul_eq_zero.mp h0).resolve_left hQ_top_ne

/-! ### Proposition S.5: Asymmetric Block-Shifted Positive Polynomial & Exact Descent -/

/-- The asymmetric block-shifted integer weight `c_r(hs)` from Proposition S.5. -/
noncomputable def annularCoeff (chiZ_p : Polynomial ℤ) (P_pos : Polynomial ℕ)
    (n m₁ d C₀ r : ℕ) (hs : Fin (r + 1) → ℕ) : ℤ :=
  let τ : ℕ := ∑ i : Fin (r + 1), hs i
  let a_val : ℤ := if τ + r < n then chiZ_p.coeff (τ + r) else 0
  let S_P : ℕ := d + 1
  let q : ℕ := hs 0 / S_P
  let s : ℕ := hs 0 % S_P
  let tail : ℕ := ∑ i : Fin r, hs i.succ
  let b_val : ℤ := if q * S_P + tail + m₁ + r < n then (C₀ : ℤ) * (P_pos.coeff s : ℤ) else 0
  a_val + b_val

/-- **Proposition S.5 (Positivity, Coverage, Length Bound, and Exact Descent)**:
For `1 ≤ r ≤ n - 2`, `c_r(hs)` is nonnegative everywhere, `≥ 1` on `∑ hs + r < n`, supported
inside `1 + r + ∑ hs ≤ max n (n + d - m₁)`, and `Ω_r^{mix} ∈ ctrlSub A a (r - 1)`. -/
private lemma annularDescent_props [Nonempty Q] [DecidableEq α] [Fintype α]
    (A : DFA Q α) (a : α) (e : Q ≃ Q) (he : ∀ q, A.step q a = e q)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (permOrder e))
    {C_min : Finset Q} (hCmin : C_min ∈ orbits e)
    (hmin : ∀ C ∈ orbits e, C_min.card ≤ C.card)
    {P_pos : Polynomial ℕ} {d : ℕ}
    (hP1 : ∀ s ≤ d, 1 ≤ P_pos.coeff s)
    (hP0 : ∀ s, d < s → P_pos.coeff s = 0)
    (hProot : ∀ k : Fin (permOrder e), k.val ≠ 0 → 0 < zEigMult e ζ k →
      eval (ζ ^ (k : ℕ)) (P_pos.map (Nat.castRingHom ℂ)) = 0)
    {v : Q → ℂ} (hv_mem : v ∈ ctrlSub A a 0)
    (hv0 : fourierProj (push A [a]) (permOrder e) ζ ⟨0, permOrder_pos e⟩ v = 0)
    {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ Fintype.card Q)
    (gs : Fin r → α) (hgs : ∀ i, gs i ≠ a) :
    let n := Fintype.card Q
    let m₁ := C_min.card
    let chiZ_p := chiZ m₁ ((orbits e).erase C_min)
    let C₀ := 1 + (Finset.range n).sup (fun k => (chiZ_p.coeff k).natAbs)
    let L := max n (n + d - m₁)
    let box : Finset (Fin (r + 1) → ℕ) :=
      Fintype.piFinset (fun _ : Fin (r + 1) => Finset.range (L + 1))
    let c_r := annularCoeff chiZ_p P_pos n m₁ d C₀ r
    (∀ hs, 0 ≤ c_r hs) ∧
    (∀ hs, (∑ i, hs i) + r < n → 1 ≤ c_r hs) ∧
    (∀ hs, c_r hs ≠ 0 → 1 + r + ∑ i, hs i ≤ L) ∧
    (∑ hs ∈ box, (c_r hs : ℂ) • push A (wordOfBlock a gs hs) v) ∈ ctrlSub A a (r - 1) := by
  classical
  intro n m₁ chiZ_p C₀ L box c_r
  have hm₁_pos : 0 < m₁ := card_pos_of_mem_orbits e hCmin
  have hm₁_le_n : m₁ ≤ n := by
    have hadd : m₁ + ∑ C ∈ (orbits e).erase C_min, C.card = ∑ C ∈ orbits e, C.card :=
      Finset.add_sum_erase (orbits e) Finset.card hCmin
    rw [sum_card_orbits] at hadd
    omega
  obtain ⟨htop1, _, _, _⟩ := chiZ_properties e hζ hCmin hmin
  -- Bound on `|chiZ_p.coeff k|` for `k < n`:
  have hC0_bound : ∀ k < n, -(C₀ : ℤ) + 1 ≤ chiZ_p.coeff k := by
    intro k hk
    have hle : (chiZ_p.coeff k).natAbs ≤ (Finset.range n).sup (fun j => (chiZ_p.coeff j).natAbs) :=
      Finset.le_sup (f := fun j => (chiZ_p.coeff j).natAbs) (Finset.mem_range.mpr hk)
    have hleC : (chiZ_p.coeff k).natAbs + 1 ≤ C₀ := by omega
    omega
  -- Part 1 & Part 2: Positivity and coverage.
  have hcov : ∀ hs : Fin (r + 1) → ℕ, (∑ i, hs i) + r < n → 1 ≤ c_r hs := by
    intro hs hlt
    simp only [c_r, annularCoeff, hlt, ↓reduceIte]
    have hb_nn : 0 ≤ (if hs 0 / (d + 1) * (d + 1) + (∑ i : Fin r, hs i.succ) + m₁ + r < n then
        (C₀ : ℤ) * (P_pos.coeff (hs 0 % (d + 1)) : ℤ) else 0) := by
      split_ifs <;> positivity
    by_cases htop : n - m₁ ≤ (∑ i, hs i) + r
    · have h1 : chiZ_p.coeff ((∑ i, hs i) + r) = 1 := htop1 _ htop hlt
      rw [h1]
      linarith
    · have hsum_split : ∑ i : Fin (r + 1), hs i = hs 0 + ∑ i : Fin r, hs i.succ :=
        Fin.sum_univ_succ hs
      have hdiv : hs 0 / (d + 1) * (d + 1) + hs 0 % (d + 1) = hs 0 := by
        rw [mul_comm]; exact Nat.div_add_mod (hs 0) (d + 1)
      have hcond : hs 0 / (d + 1) * (d + 1) + (∑ i : Fin r, hs i.succ) + m₁ + r < n := by omega
      simp only [hcond, ↓reduceIte]
      have hs_le : hs 0 % (d + 1) ≤ d := Nat.lt_succ_iff.mp (Nat.mod_lt (hs 0) (Nat.succ_pos d))
      have hp1 : (1 : ℤ) ≤ (P_pos.coeff (hs 0 % (d + 1)) : ℤ) := by
        exact_mod_cast hP1 _ hs_le
      have hC0_pos : (1 : ℤ) ≤ (C₀ : ℤ) := by exact_mod_cast (show 1 ≤ C₀ by omega)
      have hb_ge : (C₀ : ℤ) ≤ (C₀ : ℤ) * (P_pos.coeff (hs 0 % (d + 1)) : ℤ) := by nlinarith
      have ha_ge := hC0_bound ((∑ i, hs i) + r) hlt
      linarith
  have hnn : ∀ hs : Fin (r + 1) → ℕ, 0 ≤ c_r hs := by
    intro hs
    by_cases hlt : (∑ i, hs i) + r < n
    · linarith [hcov hs hlt]
    · simp only [c_r, annularCoeff, hlt, ↓reduceIte, zero_add]
      split_ifs <;> positivity
  -- Part 3: Length bound.
  have hlen : ∀ hs : Fin (r + 1) → ℕ, c_r hs ≠ 0 → 1 + r + ∑ i, hs i ≤ L := by
    intro hs hne
    simp only [c_r, annularCoeff] at hne
    by_cases h1 : (∑ i, hs i) + r < n
    · exact (show 1 + r + ∑ i, hs i ≤ n by omega).trans (le_max_left _ _)
    · simp only [h1, ↓reduceIte, zero_add] at hne
      by_cases h2 : hs 0 / (d + 1) * (d + 1) + (∑ i : Fin r, hs i.succ) + m₁ + r < n
      · have hsum_split : ∑ i : Fin (r + 1), hs i = hs 0 + ∑ i : Fin r, hs i.succ :=
          Fin.sum_univ_succ hs
        have hdiv : hs 0 / (d + 1) * (d + 1) + hs 0 % (d + 1) = hs 0 := by
          rw [mul_comm]; exact Nat.div_add_mod (hs 0) (d + 1)
        have hmod : hs 0 % (d + 1) ≤ d := Nat.lt_succ_iff.mp (Nat.mod_lt (hs 0) (Nat.succ_pos d))
        exact (show 1 + r + ∑ i, hs i ≤ n + d - m₁ by omega).trans (le_max_right _ _)
      · simp only [h2, ↓reduceIte] at hne
        exact absurd rfl hne
  -- Part 4: Exact descent `Ω_r^{mix} ∈ ctrlSub A a (r - 1)`.
  have hdesc : (∑ hs ∈ box, (c_r hs : ℂ) • push A (wordOfBlock a gs hs) v) ∈ ctrlSub A a (r - 1) := by
    have hM : 0 < permOrder e := permOrder_pos e
    have hTM : (push A [a]) ^ permOrder e = 1 := push_perm_pow_permOrder A a e he
    have hexp :
        ∑ hs ∈ box, (c_r hs : ℂ) • push A (wordOfBlock a gs hs) v =
          ∑ αs : Fin (r + 1) → Fin (permOrder e),
            (∑ hs ∈ box, (c_r hs : ℂ) * ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i) •
              spectralChain (push A [a]) (permOrder e) ζ A gs αs v := by
      calc
        ∑ hs ∈ box, (c_r hs : ℂ) • push A (wordOfBlock a gs hs) v
            = ∑ hs ∈ box, ∑ αs : Fin (r + 1) → Fin (permOrder e),
                ((c_r hs : ℂ) * ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i) •
                  spectralChain (push A [a]) (permOrder e) ζ A gs αs v := by
              refine Finset.sum_congr rfl fun hs _ => ?_
              rw [push_wordOfBlock_eq_sum_spectralChain A a hM hTM hζ gs hs v, Finset.smul_sum]
              refine Finset.sum_congr rfl fun αs _ => by rw [smul_smul]
        _ = ∑ αs : Fin (r + 1) → Fin (permOrder e), ∑ hs ∈ box,
              ((c_r hs : ℂ) * ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i) •
                spectralChain (push A [a]) (permOrder e) ζ A gs αs v := Finset.sum_comm
        _ = _ := by
              refine Finset.sum_congr rfl fun αs _ => by rw [← Finset.sum_smul]
    rw [hexp]
    refine Submodule.sum_mem _ fun αs _ => ?_
    by_cases hhead0 : (αs 0).val = 0
    · have hα0 : αs 0 = ⟨0, hM⟩ := Fin.ext hhead0
      rw [spectralChain_zero_head_eq_zero _ _ _ A gs αs (by rw [hα0]; exact hv0), smul_zero]
      exact Submodule.zero_mem _
    · by_cases hmult : ∀ k : Fin (permOrder e),
          (Finset.univ.filter (fun i : Fin (r + 1) => αs i = k)).card ≤ zEigMult e ζ k
      · -- Both parts of the scalar sum vanish identically!
        have hscalar0 :
            ∑ hs ∈ box, (c_r hs : ℂ) * ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i = 0 := by
          -- Split `c_r hs = a_val + b_val`.
          have hsplit_sum :
              ∑ hs ∈ box, (c_r hs : ℂ) * ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i =
                (∑ hs ∈ box,
                  ((if (∑ i, hs i) + r < n then chiZ_p.coeff ((∑ i, hs i) + r) else 0 : ℤ) : ℂ) *
                    ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i) +
                (∑ hs ∈ box,
                  ((if hs 0 / (d + 1) * (d + 1) + (∑ i : Fin r, hs i.succ) + m₁ + r < n then
                      (C₀ : ℤ) * (P_pos.coeff (hs 0 % (d + 1)) : ℤ) else 0 : ℤ) : ℂ) *
                    ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun hs _ => ?_
            simp only [c_r, annularCoeff, Int.cast_add, add_mul]
          rw [hsplit_sum]
          -- Part A: Equals the confluent divided difference `= 0` by Lemma S.4!
          have hPartA :
              ∑ hs ∈ box,
                ((if (∑ i, hs i) + r < n then chiZ_p.coeff ((∑ i, hs i) + r) else 0 : ℤ) : ℂ) *
                  ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i = 0 := by
            have hfilt :
                ∑ hs ∈ box,
                  ((if (∑ i, hs i) + r < n then chiZ_p.coeff ((∑ i, hs i) + r) else 0 : ℤ) : ℂ) *
                    ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i =
                ∑ hs ∈ box.filter (fun hs => (∑ i, hs i) + r < n),
                  (chiZ_p.coeff ((∑ i, hs i) + r) : ℂ) *
                    ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun hs _ => by split_ifs <;> simp
            rw [hfilt]
            have hmaps : ∀ hs ∈ box.filter (fun hs => (∑ i, hs i) + r < n),
                (∑ i, hs i) ∈ Finset.range (n - r) := by
              intro hs hhs
              have hlt := (Finset.mem_filter.mp hhs).2
              rw [Finset.mem_range]; omega
            rw [← Finset.sum_fiberwise_of_maps_to (g := fun hs : Fin (r + 1) → ℕ => ∑ i, hs i)
              (t := Finset.range (n - r)) hmaps]
            have hfiber : ∀ s ∈ Finset.range (n - r),
                ∑ hs ∈ (box.filter (fun hs => (∑ i, hs i) + r < n)).filter (fun hs => ∑ i, hs i = s),
                  (chiZ_p.coeff ((∑ i, hs i) + r) : ℂ) *
                    ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i =
                (chiZ_p.coeff (r + s) : ℂ) * hSum (r + 1) s (fun i => ζ ^ (αs i).val) := by
              intro s hs_mem
              have hs_lt : s < n - r := Finset.mem_range.mp hs_mem
              have hset_eq :
                  (box.filter (fun hs => (∑ i, hs i) + r < n)).filter (fun hs => ∑ i, hs i = s) =
                    tuplesWithSum (r + 1) s := by
                ext f
                simp only [Finset.mem_filter, mem_tuplesWithSum, box, Fintype.mem_piFinset,
                  Finset.mem_range]
                constructor
                · intro h; exact h.2
                · intro hsum
                  refine ⟨⟨fun i => ?_, by omega⟩, hsum⟩
                  have hle : f i ≤ ∑ j, f j :=
                    Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i)
                  have hnL : n ≤ L := le_max_left _ _
                  omega
              rw [hset_eq, hSum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun f hf => ?_
              rw [(mem_tuplesWithSum (r + 1) s f).mp hf, add_comm s r]
            rw [Finset.sum_congr rfl hfiber]
            exact confluent_divDiff_eq_zero e hζ hCmin hmin hr1 hr2 αs hmult
          -- Part B: Factors out `eval (ζ^(αs 0)) P_pos = 0`!
          have hPartB :
              ∑ hs ∈ box,
                ((if hs 0 / (d + 1) * (d + 1) + (∑ i : Fin r, hs i.succ) + m₁ + r < n then
                    (C₀ : ℤ) * (P_pos.coeff (hs 0 % (d + 1)) : ℤ) else 0 : ℤ) : ℂ) *
                  ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i = 0 := by
            -- Group by `(hs 0 / (d + 1), fun i : Fin r => hs i.succ)`!
            let key : (Fin (r + 1) → ℕ) → ℕ × (Fin r → ℕ) :=
              fun hs => (hs 0 / (d + 1), fun i => hs i.succ)
            let Bfilt := box.filter (fun hs =>
              hs 0 / (d + 1) * (d + 1) + (∑ i : Fin r, hs i.succ) + m₁ + r < n)
            have hfilt :
                ∑ hs ∈ box,
                  ((if hs 0 / (d + 1) * (d + 1) + (∑ i : Fin r, hs i.succ) + m₁ + r < n then
                      (C₀ : ℤ) * (P_pos.coeff (hs 0 % (d + 1)) : ℤ) else 0 : ℤ) : ℂ) *
                    ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i =
                ∑ hs ∈ Bfilt,
                  ((C₀ : ℂ) * (P_pos.coeff (hs 0 % (d + 1)) : ℂ)) *
                    ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun hs _ => by
                split_ifs <;> simp
            rw [hfilt]
            rw [← Finset.sum_fiberwise_of_maps_to (g := key) (t := Bfilt.image key)
              (fun hs hhs => Finset.mem_image_of_mem key hhs)]
            refine Finset.sum_eq_zero fun p hp => ?_
            rcases Finset.mem_image.mp hp with ⟨hs₀, hhs₀, rfl⟩
            have hcond0 : hs₀ 0 / (d + 1) * (d + 1) + (∑ i : Fin r, hs₀ i.succ) + m₁ + r < n :=
              (Finset.mem_filter.mp hhs₀).2
            set q := hs₀ 0 / (d + 1)
            set tail := fun i : Fin r => hs₀ i.succ
            -- Every `s ∈ range (d + 1)` gives a unique member `Fin.cons (q * (d + 1) + s) tail` of the fiber!
            have hbij :
                ∑ hs ∈ Bfilt.filter (fun hs => key hs = (q, tail)),
                  ((C₀ : ℂ) * (P_pos.coeff (hs 0 % (d + 1)) : ℂ)) *
                    ∏ i : Fin (r + 1), (ζ ^ (αs i).val) ^ hs i =
                ∑ s ∈ Finset.range (d + 1),
                  ((C₀ : ℂ) * (P_pos.coeff s : ℂ)) *
                    ((ζ ^ (αs 0).val) ^ (q * (d + 1) + s) *
                      ∏ i : Fin r, (ζ ^ (αs i.succ).val) ^ tail i) := by
              refine Finset.sum_nbij (fun hs => hs 0 % (d + 1)) ?_ ?_ ?_ ?_
              · intro hs _
                exact Finset.mem_range.mpr (Nat.mod_lt _ (Nat.succ_pos d))
              · intro hs₁ h₁ hs₂ h₂ heq
                simp only [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
                have hk₁ : hs₁ 0 / (d + 1) = q ∧ (fun i => hs₁ i.succ) = tail :=
                  Prod.mk.inj h₁.2
                have hk₂ : hs₂ 0 / (d + 1) = q ∧ (fun i => hs₂ i.succ) = tail :=
                  Prod.mk.inj h₂.2
                funext i
                refine Fin.cases ?_ ?_ i
                · have hd₁ := Nat.div_add_mod (hs₁ 0) (d + 1)
                  have hd₂ := Nat.div_add_mod (hs₂ 0) (d + 1)
                  dsimp only at heq
                  rw [hk₁.1] at hd₁; rw [hk₂.1] at hd₂
                  omega
                · intro j; exact congrFun (hk₁.2.trans hk₂.2.symm) j
              · intro s hs_mem
                have hs_lt : s < d + 1 := Finset.mem_range.mp hs_mem
                let f : Fin (r + 1) → ℕ := Fin.cons (q * (d + 1) + s) tail
                have hf_div : f 0 / (d + 1) = q := by
                  simp only [f, Fin.cons_zero]
                  rw [mul_comm, Nat.mul_add_div (Nat.succ_pos d), Nat.div_eq_of_lt hs_lt, add_zero]
                have hf_mod : f 0 % (d + 1) = s := by
                  simp only [f, Fin.cons_zero]
                  rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hs_lt]
                have hf_tail : (fun i : Fin r => f i.succ) = tail := funext fun i => by simp [f]
                refine ⟨f, ?_, hf_mod⟩
                simp only [Finset.mem_coe, Finset.mem_filter, Bfilt, box, Fintype.mem_piFinset,
                  Finset.mem_range]
                refine ⟨⟨fun i => ?_, ?_⟩, Prod.ext hf_div hf_tail⟩
                · refine Fin.cases ?_ ?_ i
                  · simp only [f, Fin.cons_zero]
                    have hleL : n + d - m₁ ≤ L := le_max_right _ _
                    omega
                  · intro j
                    simp only [f, Fin.cons_succ]
                    have hle : tail j ≤ Finset.univ.sum tail :=
                      Finset.single_le_sum (f := tail)
                        (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
                    have hcond' : q * (d + 1) + Finset.univ.sum tail + m₁ + r < n := hcond0
                    have hnL : n ≤ L := le_max_left _ _
                    omega
                · rw [hf_div, hf_tail]; exact hcond0
              · intro hs hhs
                have hk : hs 0 / (d + 1) = q ∧ (fun i => hs i.succ) = tail :=
                  Prod.mk.inj (Finset.mem_filter.mp hhs).2
                have h0_eq : q * (d + 1) + hs 0 % (d + 1) = hs 0 := by
                  rw [← hk.1, mul_comm]; exact Nat.div_add_mod (hs 0) (d + 1)
                rw [Fin.prod_univ_succ, h0_eq]
                congr 2
                refine Finset.prod_congr rfl fun i _ => by rw [← congrFun hk.2 i]
            rw [hbij]
            have hfactor :
                ∑ s ∈ Finset.range (d + 1),
                  ((C₀ : ℂ) * (P_pos.coeff s : ℂ)) *
                    ((ζ ^ (αs 0).val) ^ (q * (d + 1) + s) *
                      ∏ i : Fin r, (ζ ^ (αs i.succ).val) ^ tail i) =
                ((C₀ : ℂ) * (ζ ^ (αs 0).val) ^ (q * (d + 1)) *
                    ∏ i : Fin r, (ζ ^ (αs i.succ).val) ^ tail i) *
                  eval (ζ ^ (αs 0).val) (P_pos.map (Nat.castRingHom ℂ)) := by
              rw [eval_eq_sum_range' (n := d + 1)]
              · rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun s _ => ?_
                simp only [coeff_map, eq_natCast, pow_add]
                ring
              · by_cases hzero : P_pos.map (Nat.castRingHom ℂ) = 0
                · rw [hzero, natDegree_zero]; omega
                · exact Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun s hs => by
                    rw [coeff_map, hP0 s hs, map_zero])
            rw [hfactor]
            have hdz_pos : 0 < zEigMult e ζ (αs 0) := by
              have h1 : 1 ≤ (Finset.univ.filter (fun i : Fin (r + 1) => αs i = αs 0)).card :=
                Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
              exact lt_of_lt_of_le (by omega) (hmult (αs 0))
            rw [hProot (αs 0) hhead0 hdz_pos, mul_zero]
          rw [hPartA, hPartB, add_zero]
        rw [hscalar0, zero_smul]
        exact Submodule.zero_mem _
      · push Not at hmult
        rcases hmult with ⟨k, hgt⟩
        refine Submodule.smul_mem _ _ ?_
        exact higherMult_controlDeletion A a e he hζ hr1 gs hgs αs hv_mem k hgt
  exact ⟨hnn, hcov, hlen, hdesc⟩

/-! ### Theorem S.7(1): Master short-extending-word theorem for cluster-balanced permutation DFAs -/

/-- **Master Short-Extending-Word Theorem**: For any synchronizing cluster-balanced permutation
DFA with a positive gap-free annihilating polynomial `P_pos` of degree `d ≤ n - 1`, every
nonempty proper subset `S` admits an extending word of length at most `max n (n + d - m₁)`. -/
private lemma exists_extending_word_of_posPoly [Nonempty Q] [DecidableEq α] [Fintype α]
    (A : DFA Q α) (a : α) (hCB : A.IsClusterBalanced a) (hSync : A.IsSynchronizing)
    (e : Q ≃ Q) (he : ∀ q, A.step q a = e q)
    {C_min : Finset Q} (hCmin : C_min ∈ orbits e)
    (hmin : ∀ C ∈ orbits e, C_min.card ≤ C.card)
    {P_pos : Polynomial ℕ} {d : ℕ}
    (hd_le : d ≤ Fintype.card Q - 1)
    (hP1 : ∀ s ≤ d, 1 ≤ P_pos.coeff s)
    (hP0 : ∀ s, d < s → P_pos.coeff s = 0)
    (hProot : ∀ k : Fin (permOrder e), k.val ≠ 0 →
      0 < zEigMult e (Complex.exp (2 * Real.pi * Complex.I / (permOrder e : ℂ))) k →
      eval ((Complex.exp (2 * Real.pi * Complex.I / (permOrder e : ℂ))) ^ (k : ℕ))
        (P_pos.map (Nat.castRingHom ℂ)) = 0)
    {S : Finset Q} (hS_ne : S.Nonempty) (hS_lt : S.card < Fintype.card Q) :
    ∃ w : List α,
      w.length ≤ max (Fintype.card Q) (Fintype.card Q + d - C_min.card) ∧
      S.card < (A.preimage S w).card := by
  classical
  set n := Fintype.card Q
  set m₁ := C_min.card
  set L := max n (n + d - m₁)
  have hn2 : 2 ≤ n := by
    have hpos := hS_ne.card_pos
    omega
  rcases hCB with ⟨_, β, hβ, hbal⟩
  let M := permOrder e
  have hM : 0 < M := permOrder_pos e
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (M : ℂ))
  have hζ : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M (Nat.ne_of_gt hM)
  by_contra hno
  push Not at hno
  -- `hno : ∀ w, w.length ≤ L → (A.preimage S w).card ≤ S.card`
  -- Leftmost-control deletion helper: if `L (r - 1) ⊥ S`, then every word with `≤ r` controls preserves `|S w⁻¹|`.
  have hleft_del : ∀ r : ℕ,
      (∀ v ∈ ctrlSub A a r, dotSet v S = 0) →
      ∀ w : List α, countControls a w ≤ r + 1 → (A.preimage S w).card = S.card := by
    intro r horth w
    have hcard_eq_of_zero : ∀ k : ℕ, (A.preimage S (List.replicate k a)).card = S.card := by
      intro k
      have h1 : dotSet (push A (List.replicate k a) onesVec) S = dotSet onesVec S := by
        rw [push_replicate, push_perm_pow_ones A a e he]
      rw [dotSet_push, dotSet_ones, dotSet_ones] at h1
      exact_mod_cast h1
    induction hcnt : countControls a w generalizing w with
    | zero =>
      intro _
      rw [word_eq_replicate_of_countControls_zero a w hcnt]
      exact hcard_eq_of_zero w.length
    | succ c ih =>
      intro hle
      obtain ⟨h, g, z, hg, hz_cnt, hw_eq⟩ := word_split_first_control a w (by omega)
      have hz_eq : countControls a z = c := by omega
      have hdiff : ((A.preimage S w).card : ℂ) - ((A.preimage S z).card : ℂ) =
          dotSet (push A z (uVec A g)) S := by
        have h1 : dotSet (push A w onesVec) S = dotSet (push A (g :: z) onesVec) S := by
          rw [hw_eq, push_append, push_replicate, mul_apply_eq_comp, push_perm_pow_ones A a e he]
        rw [dotSet_push, dotSet_push, dotSet_ones, dotSet_ones] at h1
        rw [h1, dotSet_push_uVec]
      have hz_in : push A z (uVec A g) ∈ ctrlSub A a r :=
        push_uVec_mem_ctrlSub A a hg (by omega)
      rw [horth _ hz_in] at hdiff
      have heq_z : (A.preimage S w).card = (A.preimage S z).card := by
        exact_mod_cast sub_eq_zero.mp hdiff
      rw [heq_z, ih z hz_eq (by omega)]
  -- Helper: `uMix` satisfies `E_0 uMix = 0`.
  have huMix0 : fourierProj (push A [a]) M ζ ⟨0, hM⟩ (uMix A a β) = 0 :=
    fourierProj_zero_uMix A a e he hζ β hbal
  have huMix_mem : uMix A a β ∈ ctrlSub A a 0 := uMix_mem_ctrlSub_zero A a β
  -- Main induction: `∀ r ≤ n - 2, ∀ v ∈ ctrlSub A a r, dotSet v S = 0`.
  have horth_all : ∀ r ≤ n - 2, ∀ v ∈ ctrlSub A a r, dotSet v S = 0 := by
    intro r
    induction r with
    | zero =>
      intro _
      -- Base case `r = 0`: `uMix P_pos(T) = 0`!
      have hann := posPoly_annihilate_uMix A a e he hζ hP0 hProot huMix0
      have hdot0 : dotSet (∑ s ∈ Finset.range (d + 1),
          ((P_pos.coeff s : ℕ) : ℂ) • (((push A [a]) ^ s) (uMix A a β))) S = 0 := by
        rw [hann]; simp [dotSet]
      -- Expand `uMix = ∑_{f ≠ a} β_f u_f` and take `.re`!
      have hre0 :
          ∑ f ∈ Finset.univ.erase a, ∑ s ∈ Finset.range (d + 1),
            β f * (P_pos.coeff s : ℝ) *
              (((A.preimage S (f :: List.replicate s a)).card : ℝ) - (S.card : ℝ)) = 0 := by
        have hcomp :
            dotSet (∑ s ∈ Finset.range (d + 1),
              ((P_pos.coeff s : ℕ) : ℂ) • (((push A [a]) ^ s) (uMix A a β))) S =
            ((∑ f ∈ Finset.univ.erase a, ∑ s ∈ Finset.range (d + 1),
              β f * (P_pos.coeff s : ℝ) *
                (((A.preimage S (f :: List.replicate s a)).card : ℝ) - (S.card : ℝ)) : ℝ) : ℂ) := by
          rw [dotSet_sum]
          have hstep : ∀ s ∈ Finset.range (d + 1),
              dotSet (((P_pos.coeff s : ℕ) : ℂ) • (((push A [a]) ^ s) (uMix A a β))) S =
                ∑ f ∈ Finset.univ.erase a,
                  ((β f * (P_pos.coeff s : ℝ) *
                    (((A.preimage S (f :: List.replicate s a)).card : ℝ) - (S.card : ℝ)) : ℝ) : ℂ) := by
            intro s _
            rw [dotSet_smul, uMix, map_sum, dotSet_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [map_smul, dotSet_smul, ← push_replicate, dotSet_push_uVec]
            have hrep_card : (A.preimage S (List.replicate s a)).card = S.card := by
              have h1 : dotSet (push A (List.replicate s a) onesVec) S = dotSet onesVec S := by
                rw [push_replicate, push_perm_pow_ones A a e he]
              rw [dotSet_push, dotSet_ones, dotSet_ones] at h1
              exact_mod_cast h1
            rw [hrep_card]
            push_cast
            ring
          rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
          simp [Complex.ofReal_sum]
        rw [hcomp] at hdot0
        exact Complex.ofReal_eq_zero.mp hdot0
      -- Every term is `≤ 0` (since `|f a^s| = 1 + s ≤ 1 + d ≤ n ≤ L`), so every term vanishes!
      have hnonpos_outer : ∀ f ∈ Finset.univ.erase a,
          ∑ s ∈ Finset.range (d + 1),
            β f * (P_pos.coeff s : ℝ) *
              (((A.preimage S (f :: List.replicate s a)).card : ℝ) - (S.card : ℝ)) ≤ 0 := by
        intro f hf
        refine Finset.sum_nonpos fun s hs => ?_
        have hs_le : s ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
        have hlen_le : (f :: List.replicate s a).length ≤ L := by
          simp only [List.length_cons, List.length_replicate]
          have : s + 1 ≤ n := by omega
          exact this.trans (le_max_left _ _)
        have hle_card : ((A.preimage S (f :: List.replicate s a)).card : ℝ) ≤ (S.card : ℝ) := by
          exact_mod_cast hno _ hlen_le
        have hβpos : 0 ≤ β f := (hβ f (Finset.ne_of_mem_erase hf)).le
        have hppos : (0 : ℝ) ≤ (P_pos.coeff s : ℝ) := Nat.cast_nonneg _
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hβpos hppos) (by linarith)
      have hall_f := (Finset.sum_eq_zero_iff_of_nonpos hnonpos_outer).mp hre0
      -- Extract `dotSet ((T^s) (uVec A f)) S = 0` for all `f ≠ a` and `s ≤ d`.
      have hbase_le : ∀ f : α, f ≠ a → ∀ s ≤ d, dotSet (((push A [a]) ^ s) (uVec A f)) S = 0 := by
        intro f hf s hs
        have hf_mem : f ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hf, Finset.mem_univ f⟩
        have hsum_f0 := hall_f f hf_mem
        have hnonpos_s : ∀ j ∈ Finset.range (d + 1),
            β f * (P_pos.coeff j : ℝ) *
              (((A.preimage S (f :: List.replicate j a)).card : ℝ) - (S.card : ℝ)) ≤ 0 := by
          intro j hj
          have hj_le : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hlen_le : (f :: List.replicate j a).length ≤ L := by
            simp only [List.length_cons, List.length_replicate]
            exact (show j + 1 ≤ n by omega).trans (le_max_left _ _)
          have hle_card : ((A.preimage S (f :: List.replicate j a)).card : ℝ) ≤ (S.card : ℝ) := by
            exact_mod_cast hno _ hlen_le
          have hβpos : 0 ≤ β f := (hβ f hf).le
          have hppos : (0 : ℝ) ≤ (P_pos.coeff j : ℝ) := Nat.cast_nonneg _
          exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hβpos hppos) (by linarith)
        have hs0 := (Finset.sum_eq_zero_iff_of_nonpos hnonpos_s).mp hsum_f0 s
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hs))
        have hβpos : 0 < β f := hβ f hf
        have hppos : (0 : ℝ) < (P_pos.coeff s : ℝ) := by exact_mod_cast hP1 s hs
        have hdiff0 : ((A.preimage S (f :: List.replicate s a)).card : ℝ) - (S.card : ℝ) = 0 :=
          (mul_eq_zero.mp hs0).resolve_left (ne_of_gt (mul_pos hβpos hppos))
        have hrep_card : (A.preimage S (List.replicate s a)).card = S.card := by
          have h1 : dotSet (push A (List.replicate s a) onesVec) S = dotSet onesVec S := by
            rw [push_replicate, push_perm_pow_ones A a e he]
          rw [dotSet_push, dotSet_ones, dotSet_ones] at h1
          exact_mod_cast h1
        rw [← push_replicate, dotSet_push_uVec, hrep_card]
        exact_mod_cast hdiff0
      -- Extend to ALL `k : ℕ` by Lemma S.2(b), hence all of `ctrlSub A a 0`!
      have hbase_all : ∀ f : α, f ≠ a → ∀ k : ℕ, dotSet (((push A [a]) ^ k) (uVec A f)) S = 0 :=
        fun f hf => dotSet_pow_eq_zero_of_le_posPoly_deg A a e he hζ hP1 hP0 hProot (uVec A f) S
          (hbase_le f hf)
      intro v hv
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨f, w, hf, hcnt, rfl⟩
        rw [word_eq_replicate_of_countControls_zero a w (Nat.le_zero.mp hcnt), push_replicate]
        exact hbase_all f hf w.length
      · simp [dotSet]
      · intro x y _ _ hx hy; rw [dotSet_add, hx, hy, add_zero]
      · intro c x _ hx; rw [dotSet_smul, hx, mul_zero]
    | succ r ih =>
      intro hr_le
      have hih : ∀ v ∈ ctrlSub A a r, dotSet v S = 0 := ih (by omega)
      -- If `ctrlSub A a (r + 1) ≤ ctrlSub A a r`, we're immediately done!
      by_cases hcol : ∃ j < r + 1, Module.finrank ℂ (ctrlSub A a j) = Module.finrank ℂ (ctrlSub A a (j + 1))
      · rcases hcol with ⟨j, hj, heq⟩
        have hsub_eq : ctrlSub A a (j + 1) = ctrlSub A a j :=
          (Submodule.eq_of_le_of_finrank_eq (ctrlSub_mono A a (Nat.le_succ j)) heq).symm
        -- Closed under all letters ⇒ `ctrlSub A a (r + 1) ≤ ctrlSub A a j ≤ ctrlSub A a r`!
        have hinv_all : ∀ g : α, ∀ v ∈ ctrlSub A a j, push A [g] v ∈ ctrlSub A a j := by
          intro g v hv
          by_cases hga : g = a
          · subst hga; exact push_perm_mem_ctrlSub A g j hv
          · rw [← hsub_eq]; exact push_control_mem_ctrlSub A a j hga hv
        have hinv_word : ∀ w : List α, ∀ v ∈ ctrlSub A a j, push A w v ∈ ctrlSub A a j := by
          intro w
          induction w with
          | nil => intro v hv; simpa [push_nil] using hv
          | cons g u ihw =>
            intro v hv; rw [push_cons, mul_apply_eq_comp]; exact ihw _ (hinv_all g v hv)
        intro v hv
        have hv_j : v ∈ ctrlSub A a j := by
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
          · rintro _ ⟨f, w, hf, _, rfl⟩
            exact hinv_word w _ (ctrlSub_mono A a (Nat.zero_le j) (by
              simpa [push_nil] using push_uVec_mem_ctrlSub A a hf (w := []) (r := 0) (by simp [countControls])))
          · exact Submodule.zero_mem _
          · intro x y _ _ hx hy; exact Submodule.add_mem _ hx hy
          · intro c x _ hx; exact Submodule.smul_mem _ c hx
        exact hih v (ctrlSub_mono A a (by omega) hv_j)
      · push Not at hcol
        have hstrict : ∀ j < r + 1,
            Module.finrank ℂ (ctrlSub A a j) < Module.finrank ℂ (ctrlSub A a (j + 1)) := by
          intro j hj
          exact lt_of_le_of_ne (Submodule.finrank_mono (ctrlSub_mono A a (Nat.le_succ j))) (hcol j hj)
        have h0_pos : 1 ≤ Module.finrank ℂ (ctrlSub A a 0) :=
          ctrlSub_zero_finrank_pos A a e he hSync hn2
        -- Step A: Show every `(r + 1)`-control block generator with `∑ hs + (r + 1) < n` has `dotSet · S = 0`!
        have hblock0 : ∀ (f : α) (gs : Fin (r + 1) → α) (hs : Fin (r + 2) → ℕ),
            f ≠ a → (∀ i, gs i ≠ a) → (∑ i, hs i) + (r + 1) < n →
            dotSet (push A (wordOfBlock a gs hs) (uVec A f)) S = 0 := by
          intro f gs hs hf hgs hsum_lt
          obtain ⟨hnn, hcov, hlen_supp, hdesc⟩ :=
            annularDescent_props A a e he hζ hCmin hmin hP1 hP0 hProot huMix_mem huMix0
              (r := r + 1) (by omega) (by omega) gs hgs
          let chiZ_p := chiZ m₁ ((orbits e).erase C_min)
          let C₀ := 1 + (Finset.range n).sup (fun k => (chiZ_p.coeff k).natAbs)
          let box : Finset (Fin (r + 2) → ℕ) :=
            Fintype.piFinset (fun _ : Fin (r + 2) => Finset.range (L + 1))
          let c_r := annularCoeff chiZ_p P_pos n m₁ d C₀ (r + 1)
          have hdesc' : (∑ h' ∈ box, (c_r h' : ℂ) • push A (wordOfBlock a gs h') (uMix A a β)) ∈
              ctrlSub A a r := hdesc
          have hdot0 : dotSet (∑ h' ∈ box, (c_r h' : ℂ) • push A (wordOfBlock a gs h') (uMix A a β)) S = 0 :=
            hih _ hdesc'
          -- Leftmost-control deletion gives `(A.preimage S (wordOfBlock a gs h')).card = S.card`!
          have hwb_card : ∀ h' : Fin (r + 2) → ℕ,
              (A.preimage S (wordOfBlock a gs h')).card = S.card := fun h' =>
            hleft_del r hih (wordOfBlock a gs h') (by rw [countControls_wordOfBlock a gs h' hgs])
          -- Expand as a real sum `= 0`!
          have hre0 :
              ∑ f' ∈ Finset.univ.erase a, ∑ h' ∈ box,
                β f' * (c_r h' : ℝ) *
                  (((A.preimage S (f' :: wordOfBlock a gs h')).card : ℝ) - (S.card : ℝ)) = 0 := by
            have hcomp :
                dotSet (∑ h' ∈ box, (c_r h' : ℂ) • push A (wordOfBlock a gs h') (uMix A a β)) S =
                ((∑ f' ∈ Finset.univ.erase a, ∑ h' ∈ box,
                  β f' * (c_r h' : ℝ) *
                    (((A.preimage S (f' :: wordOfBlock a gs h')).card : ℝ) - (S.card : ℝ)) : ℝ) : ℂ) := by
              rw [dotSet_sum]
              have hstep : ∀ h' ∈ box,
                  dotSet ((c_r h' : ℂ) • push A (wordOfBlock a gs h') (uMix A a β)) S =
                    ∑ f' ∈ Finset.univ.erase a,
                      ((β f' * (c_r h' : ℝ) *
                        (((A.preimage S (f' :: wordOfBlock a gs h')).card : ℝ) - (S.card : ℝ)) : ℝ) : ℂ) := by
                intro h' _
                rw [dotSet_smul, uMix, map_sum, dotSet_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun f' _ => ?_
                rw [map_smul, dotSet_smul, dotSet_push_uVec, hwb_card h']
                push_cast
                ring
              rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
              simp [Complex.ofReal_sum]
            rw [hcomp] at hdot0
            exact Complex.ofReal_eq_zero.mp hdot0
          have hterm_nonpos : ∀ f' ∈ Finset.univ.erase a, ∀ h' ∈ box,
              β f' * (c_r h' : ℝ) *
                (((A.preimage S (f' :: wordOfBlock a gs h')).card : ℝ) - (S.card : ℝ)) ≤ 0 := by
            intro f' hf' h' _
            by_cases hc0 : c_r h' = 0
            · simp [hc0]
            · have hlen_le : (f' :: wordOfBlock a gs h').length ≤ L := by
                rw [List.length_cons, length_wordOfBlock]
                have := hlen_supp h' hc0
                omega
              have hle_card : ((A.preimage S (f' :: wordOfBlock a gs h')).card : ℝ) ≤ (S.card : ℝ) := by
                exact_mod_cast hno _ hlen_le
              have hβpos : 0 ≤ β f' := (hβ f' (Finset.ne_of_mem_erase hf')).le
              have hc_nn : (0 : ℝ) ≤ (c_r h' : ℝ) := by exact_mod_cast hnn h'
              exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hβpos hc_nn) (by linarith)
          have hall_f' := (Finset.sum_eq_zero_iff_of_nonpos (fun f' hf' =>
            Finset.sum_nonpos (hterm_nonpos f' hf'))).mp hre0
          have hf_mem : f ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hf, Finset.mem_univ f⟩
          have hall_h' := (Finset.sum_eq_zero_iff_of_nonpos (hterm_nonpos f hf_mem)).mp
            (hall_f' f hf_mem)
          have hhs_box : hs ∈ box := by
            simp only [box, Fintype.mem_piFinset, Finset.mem_range]
            intro i
            have hle : hs i ≤ ∑ j, hs j :=
              Finset.single_le_sum (fun j _ => Nat.zero_le (hs j)) (Finset.mem_univ i)
            have hnL : n ≤ L := le_max_left _ _
            omega
          have hhs0 := hall_h' hs hhs_box
          have hβpos : 0 < β f := hβ f hf
          have hcpos : (0 : ℝ) < (c_r hs : ℝ) := by
            have h1 : (1 : ℤ) ≤ c_r hs := hcov hs hsum_lt
            exact_mod_cast (show (0 : ℤ) < c_r hs by omega)
          have hdiff0 : ((A.preimage S (f :: wordOfBlock a gs hs)).card : ℝ) - (S.card : ℝ) = 0 :=
            (mul_eq_zero.mp hhs0).resolve_left (ne_of_gt (mul_pos hβpos hcpos))
          rw [dotSet_push_uVec, hwb_card hs]
          exact_mod_cast hdiff0
        -- Step B: Combine with Lemma S.6(2) (`ctrlSub_block_gen`)!
        have hgen := ctrlSub_block_gen A a (r + 1) h0_pos hstrict
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel] at hgen
        have hfin_le : Module.finrank ℂ (ctrlSub A a (r + 1)) ≤ n - 1 := by
          have := Submodule.finrank_mono (ctrlSub_le_zeroSumSub A a (r + 1))
          rwa [finrank_zeroSumSub] at this
        intro v hv
        have hv_split := hgen hv
        rw [Submodule.mem_sup] at hv_split
        rcases hv_split with ⟨u, hu, y, hy, rfl⟩
        rw [dotSet_add, hih u hu, zero_add]
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨f, gs, hs, hf, hgs, hsum, rfl⟩
          have hsum_lt : (∑ i : Fin (r + 2), hs i) + (r + 1) < n := by
            have hsum' : (∑ i : Fin (r + 2), hs i) + (r + 1) + 1 ≤
                Module.finrank ℂ (ctrlSub A a (r + 1)) := hsum
            omega
          exact hblock0 f gs hs hf hgs hsum_lt
        · simp [dotSet]
        · intro x₁ x₂ _ _ hx₁ hx₂; rw [dotSet_add, hx₁, hx₂, add_zero]
        · intro c x _ hx; rw [dotSet_smul, hx, mul_zero]
  -- Stabilization at `n - 2`: `ctrlSub A a r ⊥ S` for ALL `r`!
  have hstab := ctrlSub_stabilize A a e he hSync hn2
  have horth_any : ∀ (r : ℕ) (v : Q → ℂ), v ∈ ctrlSub A a r → dotSet v S = 0 :=
    fun r v hv => horth_all (n - 2) (le_refl _) v (hstab r hv)
  -- Contradiction from `hSync`!
  rcases hSync with ⟨w_sync, q₀, hq₀⟩
  have hw_eq : (A.preimage S w_sync).card = S.card :=
    hleft_del (countControls a w_sync) (horth_any (countControls a w_sync)) w_sync (Nat.le_succ _)
  by_cases hqS : q₀ ∈ S
  · have hpre : A.preimage S w_sync = Finset.univ := by ext q; simp [hq₀ q, hqS]
    rw [hpre, Finset.card_univ] at hw_eq
    omega
  · have hpre : A.preimage S w_sync = ∅ := by ext q; simp [hq₀ q, hqS]
    rw [hpre, Finset.card_empty] at hw_eq
    have hpos := hS_ne.card_pos
    omega

/-! ### Chain assembly helpers -/

/-- If a synchronizing DFA has at least 2 states, some letter merges at least two states. -/
private lemma exists_letter_card_preimage_ge_two
    (A : DFA Q α) (hSync : A.IsSynchronizing) (hcard : 2 ≤ Fintype.card Q) :
    ∃ (q₀ : Q) (a₀ : α), 2 ≤ (A.preimage {q₀} [a₀]).card := by
  rcases hSync with ⟨w, q_sync, hq_sync⟩
  have hnot_inj : ¬ Function.Injective (fun q => A.eval q w) := by
    intro hinj
    obtain ⟨p₁, p₂, hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Q)
    exact hne (hinj ((hq_sync p₁).trans (hq_sync p₂).symm))
  have hex_letter : ∃ a₀ : α, ¬ Function.Injective (fun q => A.step q a₀) := by
    by_contra hall
    push Not at hall
    have hinj_all : ∀ u : List α, Function.Injective (fun q => A.eval q u) := by
      intro u
      induction u with
      | nil => exact Function.injective_id
      | cons x u ih =>
        have hcomp :
            (fun q => A.eval q (x :: u)) = (fun q => A.eval q u) ∘ (fun q => A.step q x) := rfl
        rw [hcomp]
        exact ih.comp (hall x)
    exact hnot_inj (hinj_all w)
  rcases hex_letter with ⟨a₀, hna₀⟩
  simp only [Function.Injective, not_forall] at hna₀
  rcases hna₀ with ⟨p₁, p₂, heq, hne⟩
  refine ⟨A.step p₁ a₀, a₀, ?_⟩
  have hsub : ({p₁, p₂} : Finset Q) ⊆ A.preimage {A.step p₁ a₀} [a₀] := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [DFA.mem_preimage, DFA.eval_singleton, Finset.mem_singleton]
    rcases hx with rfl | rfl
    · rfl
    · exact heq.symm
  have hpair : ({p₁, p₂} : Finset Q).card = 2 := Finset.card_pair hne
  rw [← hpair]
  exact Finset.card_le_card hsub

/-- Iterating an `L`-extending property expands any nonempty subset `S` to `Finset.univ` in
at most `(n - |S|) * L` steps. -/
private lemma exists_preimage_eq_univ_of_extending
    (A : DFA Q α) (L : ℕ)
    (hext : ∀ S : Finset Q, S.Nonempty → S.card < Fintype.card Q →
      ∃ w : List α, w.length ≤ L ∧ S.card < (A.preimage S w).card) :
    ∀ (d : ℕ) (S : Finset Q), S.Nonempty → Fintype.card Q - S.card ≤ d →
      ∃ w : List α, A.preimage S w = Finset.univ ∧ w.length ≤ d * L := by
  intro d
  induction d with
  | zero =>
    intro S _ hle
    have hcard_le : S.card ≤ Fintype.card Q := Finset.card_le_univ S
    have hcard_eq : S.card = Fintype.card Q := by omega
    exact ⟨[], by rw [DFA.preimage_nil, Finset.eq_univ_of_card S hcard_eq], by simp⟩
  | succ d ih =>
    intro S hS_ne hle
    by_cases hfull : S.card = Fintype.card Q
    · exact ⟨[], by rw [DFA.preimage_nil, Finset.eq_univ_of_card S hfull], Nat.zero_le _⟩
    · have hlt : S.card < Fintype.card Q :=
        lt_of_le_of_ne (Finset.card_le_univ S) hfull
      obtain ⟨u, hu_len, hu_gt⟩ := hext S hS_ne hlt
      set S' : Finset Q := A.preimage S u
      have hS'_ne : S'.Nonempty := by
        have hpos := hS_ne.card_pos
        exact Finset.card_pos.mp (by omega)
      obtain ⟨v, hv_univ, hv_len⟩ := ih S' hS'_ne (by omega)
      refine ⟨v ++ u, by rw [DFA.preimage_append]; exact hv_univ, ?_⟩
      rw [List.length_append]
      calc
        v.length + u.length ≤ d * L + L := Nat.add_le_add hv_len hu_len
        _ = (d + 1) * L := by ring

end SpectralDescent

end ClusterBalanced

/-! ### Main Public Theorems (Theorems B & C) -/

/-- **Theorem B (General Cluster-Balanced Permutation Spectral Descent)**:
Every synchronizing cluster-balanced permutation DFA on `n ≥ 1` states with arbitrary cycle
lengths (`m₁` = minimum cycle length, `c` = number of cycles) admits a synchronizing word of
length at most `1 + (n - 2) * max n (2 * n - m₁ - c)` (for `n ≥ 2`). -/
theorem clusterBalanced_reset_bound {Q : Type u} [Fintype Q] [Nonempty Q] [DecidableEq Q]
    {α : Type v} [Fintype α] [DecidableEq α] (A : DFA Q α) (a : α)
    (hCB : A.IsClusterBalanced a) (hSync : A.IsSynchronizing) :
    let e : Q ≃ Q := Equiv.ofBijective (fun q => A.step q a) hCB.1
    let c : ℕ := (ClusterBalanced.orbits e).card
    ∃ m₁ : ℕ, (∃ C ∈ ClusterBalanced.orbits e, C.card = m₁) ∧
      (∀ C ∈ ClusterBalanced.orbits e, m₁ ≤ C.card) ∧
      ∃ w : List α, A.IsSyncWord w ∧
        w.length ≤ 1 + (Fintype.card Q - 2) * max (Fintype.card Q) (2 * Fintype.card Q - m₁ - c) := by
  classical
  intro e c
  obtain ⟨C_min, hCmin, hmin⟩ :=
    Finset.exists_min_image (ClusterBalanced.orbits e) Finset.card (ClusterBalanced.orbits_nonempty e)
  refine ⟨C_min.card, ⟨C_min, hCmin, rfl⟩, hmin, ?_⟩
  by_cases h1 : Fintype.card Q ≤ 1
  · obtain ⟨q₀⟩ := ‹Nonempty Q›
    have hsub : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp h1
    exact ⟨[], ⟨q₀, fun _ => Subsingleton.elim _ _⟩, by simp⟩
  · have h2 : 2 ≤ Fintype.card Q := by omega
    have hM : 0 < ClusterBalanced.permOrder e := ClusterBalanced.permOrder_pos e
    have hζ : IsPrimitiveRoot
        (Complex.exp (2 * Real.pi * Complex.I / (ClusterBalanced.permOrder e : ℂ)))
        (ClusterBalanced.permOrder e) :=
      Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hM)
    obtain ⟨hP1, hP0, hdeg_le, hProot⟩ := ClusterBalanced.posProdPoly_props e hζ
    have hcpos : 1 ≤ c := (ClusterBalanced.orbits_nonempty e).card_pos
    have hc_le_n : c ≤ Fintype.card Q := by
      calc
        c = ∑ _C ∈ ClusterBalanced.orbits e, 1 := by simp [c]
        _ ≤ ∑ C ∈ ClusterBalanced.orbits e, C.card :=
          Finset.sum_le_sum fun C hC => ClusterBalanced.card_pos_of_mem_orbits e hC
        _ = Fintype.card Q := ClusterBalanced.sum_card_orbits e
    have hCmin_le : C_min.card ≤ Fintype.card Q := Finset.card_le_univ C_min
    have hdeg_le' : ClusterBalanced.posProdDeg e ≤ Fintype.card Q - c := hdeg_le
    have hd_le_n1 : ClusterBalanced.posProdDeg e ≤ Fintype.card Q - 1 := by omega
    have hL_le : max (Fintype.card Q) (Fintype.card Q + ClusterBalanced.posProdDeg e - C_min.card) ≤
        max (Fintype.card Q) (2 * Fintype.card Q - C_min.card - c) :=
      max_le_max_left _ (by omega)
    have hext : ∀ S : Finset Q, S.Nonempty → S.card < Fintype.card Q →
        ∃ w : List α,
          w.length ≤ max (Fintype.card Q) (2 * Fintype.card Q - C_min.card - c) ∧
          S.card < (A.preimage S w).card := by
      intro S hSne hSlt
      obtain ⟨w, hlen, hgt⟩ := ClusterBalanced.exists_extending_word_of_posPoly A a hCB hSync e
        (fun _ => rfl) hCmin hmin hd_le_n1 hP1 hP0 hProot hSne hSlt
      exact ⟨w, hlen.trans hL_le, hgt⟩
    obtain ⟨q₀, a₀, hge2⟩ := ClusterBalanced.exists_letter_card_preimage_ge_two A hSync h2
    set S₀ : Finset Q := A.preimage {q₀} [a₀]
    have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨w, hw_univ, hw_len⟩ :=
      ClusterBalanced.exists_preimage_eq_univ_of_extending A _ hext
        (Fintype.card Q - 2) S₀ hS₀_ne (by omega)
    refine ⟨w ++ [a₀], ?_, ?_⟩
    · rw [DFA.isSyncWord_iff_exists_preimage_eq_univ]
      exact ⟨q₀, by rw [DFA.preimage_append]; exact hw_univ⟩
    · rw [List.length_append, List.length_singleton]
      omega

/-- **Theorem B (Clean Quadratic Corollary)**: Every synchronizing cluster-balanced permutation
DFA on `n ≥ 1` states admits a synchronizing word of length at most `2 * (n - 1) ^ 2`
(strictly `< 2 * n ^ 2`). -/
theorem clusterBalanced_quadratic_bound {Q : Type u} [Fintype Q] [Nonempty Q] [DecidableEq Q]
    {α : Type v} [Fintype α] [DecidableEq α] (A : DFA Q α) (a : α)
    (hCB : A.IsClusterBalanced a) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 2 * (Fintype.card Q - 1) ^ 2 ∧ w.length < 2 * Fintype.card Q ^ 2 := by
  by_cases h1 : Fintype.card Q ≤ 1
  · obtain ⟨q₀⟩ := ‹Nonempty Q›
    have hsub : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp h1
    have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos
    refine ⟨[], ⟨q₀, fun _ => Subsingleton.elim _ _⟩, by simp, ?_⟩
    simp only [List.length_nil]
    nlinarith
  · have h2 : 2 ≤ Fintype.card Q := by omega
    obtain ⟨m₁, ⟨C, hC, rfl⟩, _, w, hw, hlen⟩ := clusterBalanced_reset_bound A a hCB hSync
    set e : Q ≃ Q := Equiv.ofBijective (fun q => A.step q a) hCB.1
    have hm1 : 1 ≤ C.card := ClusterBalanced.card_pos_of_mem_orbits e hC
    have hc1 : 1 ≤ (ClusterBalanced.orbits e).card := (ClusterBalanced.orbits_nonempty e).card_pos
    have hmax_le : max (Fintype.card Q) (2 * Fintype.card Q - C.card - (ClusterBalanced.orbits e).card) ≤
        2 * Fintype.card Q - 2 := by
      apply max_le <;> omega
    have hbound1 : w.length ≤ 1 + (Fintype.card Q - 2) * (2 * Fintype.card Q - 2) :=
      hlen.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hmax_le) 1)
    have hbound2 : 1 + (Fintype.card Q - 2) * (2 * Fintype.card Q - 2) ≤ 2 * (Fintype.card Q - 1) ^ 2 := by
      set k := Fintype.card Q - 2
      have hn : Fintype.card Q = k + 2 := by omega
      have hn1 : Fintype.card Q - 1 = k + 1 := by omega
      have h2n2 : 2 * Fintype.card Q - 2 = 2 * k + 2 := by omega
      rw [hn1, h2n2, sq]
      nlinarith
    have hbound3 : 2 * (Fintype.card Q - 1) ^ 2 < 2 * Fintype.card Q ^ 2 := by
      have hlt : Fintype.card Q - 1 < Fintype.card Q := by omega
      have hsq : (Fintype.card Q - 1) ^ 2 < Fintype.card Q ^ 2 :=
        Nat.pow_lt_pow_left hlt (by omega)
      omega
    exact ⟨w, hw, hbound1.trans hbound2, lt_of_le_of_lt (hbound1.trans hbound2) hbound3⟩

/-- **Theorem C (Exact Černý Conjecture for Cluster-Balanced Equal-Cycle Permutation DFAs)**:
Every synchronizing cluster-balanced DFA with a permutation letter `a` whose cycles all have
equal length `m` (`n = c * m`, arbitrary `c ≥ 1`) admits a synchronizing word of length at
most `(n - 1) ^ 2` — unifying Dubuc (`c = 1`) and pseudo-Eulerian (`c = n`). -/
theorem clusterBalanced_equalCycle_cerny {Q : Type u} [Fintype Q] [Nonempty Q] [DecidableEq Q]
    {α : Type v} [Fintype α] [DecidableEq α] (A : DFA Q α) (a : α) (m : ℕ)
    (hCB : A.IsClusterBalanced a) (hEq : A.IsEqualCyclePerm a m) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  by_cases h1 : Fintype.card Q ≤ 1
  · obtain ⟨q₀⟩ := ‹Nonempty Q›
    have hsub : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp h1
    exact ⟨[], ⟨q₀, fun _ => Subsingleton.elim _ _⟩, by simp⟩
  · have h2 : 2 ≤ Fintype.card Q := by omega
    let e : Q ≃ Q := Equiv.ofBijective (fun q => A.step q a) hCB.1
    obtain ⟨C_min, hCmin, hmin⟩ :=
      Finset.exists_min_image (ClusterBalanced.orbits e) Finset.card (ClusterBalanced.orbits_nonempty e)
    have hM : 0 < ClusterBalanced.permOrder e := ClusterBalanced.permOrder_pos e
    have hζ : IsPrimitiveRoot
        (Complex.exp (2 * Real.pi * Complex.I / (ClusterBalanced.permOrder e : ℂ)))
        (ClusterBalanced.permOrder e) :=
      Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hM)
    obtain ⟨hP1, hP0, hdeg_le, hProot⟩ := ClusterBalanced.posProdPoly_props e hζ
    have hcpos : 1 ≤ (ClusterBalanced.orbits e).card := (ClusterBalanced.orbits_nonempty e).card_pos
    have hd_le_n1 : ClusterBalanced.posProdDeg e ≤ Fintype.card Q - 1 := by omega
    -- Equal cycles ⇒ every cycle has card `m`, so `(orbits e).image Finset.card = {m}`, `d = m - 1`, `C_min.card = m`!
    have himg : (ClusterBalanced.orbits e).image Finset.card = {m} := by
      ext k
      simp only [Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨C, hC, rfl⟩
        exact ClusterBalanced.card_orbit_eq_of_isEqualCyclePerm A a m hEq e (fun _ => rfl) hC
      · intro hk
        rw [hk]
        exact ⟨C_min, hCmin,
          ClusterBalanced.card_orbit_eq_of_isEqualCyclePerm A a m hEq e (fun _ => rfl) hCmin⟩
    have hdeg_eq : ClusterBalanced.posProdDeg e = m - 1 := by
      simp [ClusterBalanced.posProdDeg, himg]
    have hCmin_eq : C_min.card = m :=
      ClusterBalanced.card_orbit_eq_of_isEqualCyclePerm A a m hEq e (fun _ => rfl) hCmin
    have hL_eq : max (Fintype.card Q) (Fintype.card Q + ClusterBalanced.posProdDeg e - C_min.card) =
        Fintype.card Q := by
      rw [hdeg_eq, hCmin_eq]
      exact max_eq_left (by omega)
    have hext : ∀ S : Finset Q, S.Nonempty → S.card < Fintype.card Q →
        ∃ w : List α, w.length ≤ Fintype.card Q ∧ S.card < (A.preimage S w).card := by
      intro S hSne hSlt
      obtain ⟨w, hlen, hgt⟩ := ClusterBalanced.exists_extending_word_of_posPoly A a hCB hSync e
        (fun _ => rfl) hCmin hmin hd_le_n1 hP1 hP0 hProot hSne hSlt
      rw [hL_eq] at hlen
      exact ⟨w, hlen, hgt⟩
    obtain ⟨q₀, a₀, hge2⟩ := ClusterBalanced.exists_letter_card_preimage_ge_two A hSync h2
    set S₀ : Finset Q := A.preimage {q₀} [a₀]
    have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨w, hw_univ, hw_len⟩ :=
      ClusterBalanced.exists_preimage_eq_univ_of_extending A (Fintype.card Q) hext
        (Fintype.card Q - 2) S₀ hS₀_ne (by omega)
    refine ⟨w ++ [a₀], ?_, ?_⟩
    · rw [DFA.isSyncWord_iff_exists_preimage_eq_univ]
      exact ⟨q₀, by rw [DFA.preimage_append]; exact hw_univ⟩
    · rw [List.length_append, List.length_singleton]
      have hsq : (Fintype.card Q - 2) * Fintype.card Q + 1 = (Fintype.card Q - 1) ^ 2 := by
        set k := Fintype.card Q - 2
        have hn : Fintype.card Q = k + 2 := by omega
        have hn1 : Fintype.card Q - 1 = k + 1 := by omega
        rw [hn1, hn, sq]
        ring
      omega

/-- Equal-cycle short `1`-extensibility (`|w| ≤ n`) as a standalone corollary of Theorem C. -/
theorem clusterBalanced_equalCycle_exists_extending_word {Q : Type u} [Fintype Q] [Nonempty Q]
    [DecidableEq Q] {α : Type v} [Fintype α] [DecidableEq α] (A : DFA Q α) (a : α) (m : ℕ)
    (hCB : A.IsClusterBalanced a) (hEq : A.IsEqualCyclePerm a m) (hSync : A.IsSynchronizing)
    {S : Finset Q} (hS_ne : S.Nonempty) (hS_lt : S.card < Fintype.card Q) :
    ∃ w : List α, w.length ≤ Fintype.card Q ∧ S.card < (A.preimage S w).card := by
  classical
  let e : Q ≃ Q := Equiv.ofBijective (fun q => A.step q a) hCB.1
  obtain ⟨C_min, hCmin, hmin⟩ :=
    Finset.exists_min_image (ClusterBalanced.orbits e) Finset.card (ClusterBalanced.orbits_nonempty e)
  have hM : 0 < ClusterBalanced.permOrder e := ClusterBalanced.permOrder_pos e
  have hζ : IsPrimitiveRoot
      (Complex.exp (2 * Real.pi * Complex.I / (ClusterBalanced.permOrder e : ℂ)))
      (ClusterBalanced.permOrder e) :=
    Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hM)
  obtain ⟨hP1, hP0, hdeg_le, hProot⟩ := ClusterBalanced.posProdPoly_props e hζ
  have hcpos : 1 ≤ (ClusterBalanced.orbits e).card := (ClusterBalanced.orbits_nonempty e).card_pos
  have hd_le_n1 : ClusterBalanced.posProdDeg e ≤ Fintype.card Q - 1 := by omega
  have himg : (ClusterBalanced.orbits e).image Finset.card = {m} := by
    ext k
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨C, hC, rfl⟩
      exact ClusterBalanced.card_orbit_eq_of_isEqualCyclePerm A a m hEq e (fun _ => rfl) hC
    · intro hk
      rw [hk]
      exact ⟨C_min, hCmin,
        ClusterBalanced.card_orbit_eq_of_isEqualCyclePerm A a m hEq e (fun _ => rfl) hCmin⟩
  have hdeg_eq : ClusterBalanced.posProdDeg e = m - 1 := by
    simp [ClusterBalanced.posProdDeg, himg]
  have hCmin_eq : C_min.card = m :=
    ClusterBalanced.card_orbit_eq_of_isEqualCyclePerm A a m hEq e (fun _ => rfl) hCmin
  have hL_eq : max (Fintype.card Q) (Fintype.card Q + ClusterBalanced.posProdDeg e - C_min.card) =
      Fintype.card Q := by
    rw [hdeg_eq, hCmin_eq]
    exact max_eq_left (by omega)
  obtain ⟨w, hlen, hgt⟩ := ClusterBalanced.exists_extending_word_of_posPoly A a hCB hSync e
    (fun _ => rfl) hCmin hmin hd_le_n1 hP1 hP0 hProot hS_ne hS_lt
  rw [hL_eq] at hlen
  exact ⟨w, hlen, hgt⟩

end Cerny


