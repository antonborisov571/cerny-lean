import Cerny.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Černý's Conjecture for One-Cluster Automata via Annular Spectral Descent

Formalization of Yinfeng Zhu's July 2026 theorem (`arXiv:2607.19675`):
every synchronizing one-cluster automaton on `n ≥ 1` states with cycle length `m` and level `ℓ`
admits a synchronizing word of length at most `(m - 1) * (n - 1) + m * ℓ ≤ (n - 1) ^ 2`.

## Main Theorems

* `Cerny.oneCluster_short_relative_extension`: Zhu's Theorem 2.3 (Short Relative Extension).
* `Cerny.oneCluster_reset_bound`: Sharp reset bound `(m - 1) * (n - 1) + m * ℓ`.
* `Cerny.oneCluster_cerny`: Černý's Conjecture `(n - 1) ^ 2` for all synchronizing one-cluster DFAs.
* `Cerny.oneCluster_resetThreshold_le`: Equivalent statement using `DFA.resetThreshold`.
* `Cerny.oneCluster_circular_cerny`: Immediate corollary for circular automata (Dubuc 1998).
-/

open scoped BigOperators Matrix Polynomial

namespace Cerny

namespace OneCluster

noncomputable section

open Classical

universe u v

/-! ### Section 1: One-Cluster Combinatorics, Controls, and Block Words -/

/-- Witness data for a one-cluster automaton with respect to letter `a`, cycle `C`, and level `ℓ`. -/
structure Data {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q] (A : DFA Q α) where
  a : α
  C : Finset Q
  ℓ : ℕ
  hC_ne : C.Nonempty
  hC_inv : ∀ q ∈ C, A.step q a ∈ C
  hC_trans : ∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q
  hℓ : ∀ q : Q, (fun x => A.step x a)^[ℓ] q ∈ C

namespace Data

variable {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q] {A : DFA Q α} (D : Data A)

/-- The action of the one-cluster letter `a`. -/
def stepA (q : Q) : Q := A.step q D.a

/-- Total number of states `n = |Q|`. -/
def n (_ : Data A) : ℕ := Fintype.card Q

/-- Cycle length `m = |C|`. -/
def m : ℕ := D.C.card

/-- Number of non-cycle states `t = n - m`. -/
def t : ℕ := D.n - D.m

lemma m_pos : 0 < D.m := Finset.card_pos.mpr D.hC_ne

lemma m_le_n : D.m ≤ D.n := Finset.card_le_univ D.C

lemma m_add_t : D.m + D.t = D.n := by
  unfold t
  have := D.m_le_n
  omega

lemma t_eq_zero_of_l_eq_zero (h : D.ℓ = 0) : D.t = 0 := by
  have hall : D.C = Finset.univ := by
    ext q
    simp only [Finset.mem_univ, iff_true]
    simpa [h] using D.hℓ q
  unfold t m n
  rw [hall, Finset.card_univ, Nat.sub_self]

lemma iterate_mem_C {q : Q} (hq : q ∈ D.C) (k : ℕ) : D.stepA^[k] q ∈ D.C := by
  induction k with
  | zero => exact hq
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact D.hC_inv _ ih

lemma iterate_mem_C_of_ge (q : Q) {k : ℕ} (hk : D.ℓ ≤ k) : D.stepA^[k] q ∈ D.C := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm, Function.iterate_add_apply]
  exact D.iterate_mem_C (D.hℓ q) d

/-- The restriction of `stepA` to the cycle `C`. -/
def stepAC : D.C → D.C := fun x => ⟨D.stepA x.1, D.hC_inv x.1 x.2⟩

lemma stepAC_iterate_val (k : ℕ) (x : D.C) : (D.stepAC^[k] x).1 = D.stepA^[k] x.1 := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    rfl

lemma stepAC_surjective : Function.Surjective D.stepAC := by
  intro ⟨q, hq⟩
  obtain ⟨k, hk⟩ := D.hC_trans (D.stepA q) (D.hC_inv q hq) q hq
  refine ⟨⟨D.stepA^[k] q, D.iterate_mem_C hq k⟩, ?_⟩
  apply Subtype.ext
  change D.stepA (D.stepA^[k] q) = q
  rw [← Function.iterate_succ_apply' D.stepA k q, Function.iterate_succ_apply]
  exact hk

lemma stepAC_bijective : Function.Bijective D.stepAC :=
  ⟨Finite.injective_iff_surjective.mpr D.stepAC_surjective, D.stepAC_surjective⟩

lemma stepAC_injective : Function.Injective D.stepAC :=
  D.stepAC_bijective.1

lemma stepA_injOn_C : Set.InjOn D.stepA D.C := by
  intro p hp q hq hpq
  have : D.stepAC ⟨p, hp⟩ = D.stepAC ⟨q, hq⟩ := Subtype.ext hpq
  exact congrArg Subtype.val (D.stepAC_injective this)

lemma stepAC_iterate_bijective (k : ℕ) : Function.Bijective (D.stepAC^[k]) :=
  D.stepAC_bijective.iterate k

lemma exists_lt_m_iterate_eq {p q : Q} (hp : p ∈ D.C) (hq : q ∈ D.C) :
    ∃ k < D.m, D.stepA^[k] p = q := by
  have hex : ∃ k : ℕ, D.stepA^[k] p = q := D.hC_trans p hp q hq
  let k := Nat.find hex
  have hk : D.stepA^[k] p = q := Nat.find_spec hex
  refine ⟨k, ?_, hk⟩
  by_contra hge
  push Not at hge
  have hlt : Fintype.card D.C < Fintype.card (Fin (D.m + 1)) := by
    rw [Fintype.card_coe, Fintype.card_fin]
    exact Nat.lt_succ_self D.m
  obtain ⟨i, j, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun r : Fin (D.m + 1) => D.stepAC^[r.val] ⟨p, hp⟩) hlt
  wlog hlt_ij : i.val < j.val generalizing i j
  · exact this j i hij.symm heq.symm (by omega)
  have hsub : D.stepAC^[j.val - i.val] ⟨p, hp⟩ = ⟨p, hp⟩ := by
    have h1 : D.stepAC^[i.val] (D.stepAC^[j.val - i.val] ⟨p, hp⟩) = D.stepAC^[i.val] ⟨p, hp⟩ := by
      rw [← Function.iterate_add_apply]
      have : i.val + (j.val - i.val) = j.val := by omega
      rw [this]
      exact heq.symm
    exact (D.stepAC_iterate_bijective i.val).1 h1
  have hk' : D.stepA^[k - (j.val - i.val)] p = q := by
    have h2 : D.stepAC^[k - (j.val - i.val)] ⟨p, hp⟩ = D.stepAC^[k] ⟨p, hp⟩ := by
      calc D.stepAC^[k - (j.val - i.val)] ⟨p, hp⟩
          = D.stepAC^[k - (j.val - i.val)] (D.stepAC^[j.val - i.val] ⟨p, hp⟩) := by rw [hsub]
        _ = D.stepAC^[k - (j.val - i.val) + (j.val - i.val)] ⟨p, hp⟩ := by
            rw [← Function.iterate_add_apply]
        _ = D.stepAC^[k] ⟨p, hp⟩ := by
            congr 1
            omega
    have hval := congrArg Subtype.val h2
    rw [D.stepAC_iterate_val, D.stepAC_iterate_val] at hval
    exact hval.trans hk
  exact Nat.find_min hex (m := k - (j.val - i.val)) (by omega) hk'

/-- For any basepoint `c ∈ C`, `j ↦ stepA^[j] c` is a bijection `Fin m ≃ C`. -/
def cycleEquiv (c : Q) (hc : c ∈ D.C) : Fin D.m ≃ D.C := by
  have hsurj : Function.Surjective (fun j : Fin D.m =>
      (⟨D.stepA^[j.val] c, D.iterate_mem_C hc j.val⟩ : D.C)) := by
    intro ⟨q, hq⟩
    obtain ⟨k, hkm, hk⟩ := D.exists_lt_m_iterate_eq hc hq
    exact ⟨⟨k, hkm⟩, Subtype.ext hk⟩
  have hcard : Fintype.card (Fin D.m) = Fintype.card D.C := by
    rw [Fintype.card_fin, Fintype.card_coe]
    rfl
  have hbij : Function.Bijective (fun j : Fin D.m =>
      (⟨D.stepA^[j.val] c, D.iterate_mem_C hc j.val⟩ : D.C)) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcard⟩
  exact Equiv.ofBijective _ hbij

lemma cycleEquiv_apply (c : Q) (hc : c ∈ D.C) (j : Fin D.m) :
    (D.cycleEquiv c hc j).1 = D.stepA^[j.val] c :=
  rfl

lemma iterate_m_eq_self {c : Q} (hc : c ∈ D.C) : D.stepA^[D.m] c = c := by
  obtain ⟨j, hj⟩ := (D.cycleEquiv c hc).surjective ⟨D.stepA^[D.m] c, D.iterate_mem_C hc D.m⟩
  have hval : D.stepA^[j.val] c = D.stepA^[D.m] c := congrArg Subtype.val hj
  by_cases hj0 : j.val = 0
  · rw [hj0] at hval
    exact hval.symm
  · exfalso
    have hsub : D.stepAC^[D.m - j.val] ⟨c, hc⟩ = ⟨c, hc⟩ := by
      apply (D.stepAC_iterate_bijective j.val).1
      rw [← Function.iterate_add_apply]
      have : j.val + (D.m - j.val) = D.m := by omega
      rw [this]
      apply Subtype.ext
      rw [D.stepAC_iterate_val, D.stepAC_iterate_val]
      exact hval.symm
    have hlt : D.m - j.val < D.m := by omega
    have hinj := (D.cycleEquiv c hc).injective (a₁ := ⟨D.m - j.val, hlt⟩) (a₂ := ⟨0, D.m_pos⟩)
    have heq : D.cycleEquiv c hc ⟨D.m - j.val, hlt⟩ = D.cycleEquiv c hc ⟨0, D.m_pos⟩ := by
      apply Subtype.ext
      simp only [cycleEquiv_apply, Function.iterate_zero, id_eq]
      have := congrArg Subtype.val hsub
      rw [D.stepAC_iterate_val] at this
      exact this
    have := congrArg Fin.val (hinj heq)
    simp at this
    omega

lemma iterate_add_m_eq (q : Q) {k : ℕ} (hk : D.ℓ ≤ k) :
    D.stepA^[k + D.m] q = D.stepA^[k] q := by
  rw [add_comm, Function.iterate_add_apply]
  exact D.iterate_m_eq_self (D.iterate_mem_C_of_ge q hk)

lemma iterate_add_mul_m_eq (q : Q) {k : ℕ} (hk : D.ℓ ≤ k) (r : ℕ) :
    D.stepA^[k + r * D.m] q = D.stepA^[k] q := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.succ_mul, ← add_assoc, D.iterate_add_m_eq q (by omega), ih]

lemma iterate_m_mul_l_eq_self {c : Q} (hc : c ∈ D.C) : D.stepA^[D.m * D.ℓ] c = c := by
  have h : ∀ l : ℕ, D.stepA^[D.m * l] c = c := by
    intro l
    induction l with
    | zero => simp
    | succ l ih =>
      rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih]
      exact D.iterate_m_eq_self hc
  exact h D.ℓ

/-- Chosen basepoint `c₀ ∈ C`. -/
def c₀ : Q := D.hC_ne.choose

lemma c₀_mem : D.c₀ ∈ D.C := D.hC_ne.choose_spec

end Data

/-- Existence of a `Data` with minimal level `ℓ` satisfying `|C| + ℓ ≤ |Q|` from `A.IsOneCluster`. -/
lemma exists_data_of_isOneCluster {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} (h1C : A.IsOneCluster) :
    ∃ D : Data A, D.m + D.ℓ ≤ D.n := by
  rcases h1C with ⟨a, Cset, hCne, hCinv, hCtrans, hCreach⟩
  let C : Finset Q := Cset.toFinset
  have hCmem : ∀ q, q ∈ C ↔ q ∈ Cset := fun q => Set.mem_toFinset
  have hC_ne : C.Nonempty := by
    rcases hCne with ⟨q, hq⟩
    exact ⟨q, (hCmem q).mpr hq⟩
  have hC_inv : ∀ q ∈ C, A.step q a ∈ C := fun q hq =>
    (hCmem _).mpr (hCinv q ((hCmem q).mp hq))
  have hC_iter : ∀ q ∈ C, ∀ k : ℕ, (fun x => A.step x a)^[k] q ∈ C := by
    intro q hq k
    induction k with
    | zero => exact hq
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hC_inv _ ih
  have hex_all : ∃ K : ℕ, ∀ q : Q, (fun x => A.step x a)^[K] q ∈ C := by
    let g : Q → ℕ := fun q => Nat.find (hCreach q)
    let K : ℕ := Finset.univ.sup g
    refine ⟨K, fun q => ?_⟩
    have hle : g q ≤ K := Finset.le_sup (f := g) (Finset.mem_univ q)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, add_comm, Function.iterate_add_apply]
    exact hC_iter _ ((hCmem _).mpr (Nat.find_spec (hCreach q))) d
  let ℓ := Nat.find hex_all
  have hℓ : ∀ q : Q, (fun x => A.step x a)^[ℓ] q ∈ C := Nat.find_spec hex_all
  refine ⟨⟨a, C, ℓ, hC_ne, hC_inv,
    fun p hp q hq => hCtrans p ((hCmem p).mp hp) q ((hCmem q).mp hq), hℓ⟩, ?_⟩
  change C.card + ℓ ≤ Fintype.card Q
  by_cases hℓ0 : ℓ = 0
  · rw [hℓ0, add_zero]
    exact Finset.card_le_univ C
  · have hlt : ℓ - 1 < ℓ := by omega
    have hnot := Nat.find_min hex_all hlt
    push Not at hnot
    rcases hnot with ⟨q, hq⟩
    let f : Q → Q := fun x => A.step x a
    have hnotC : ∀ i : Fin ℓ, f^[i.val] q ∉ C := by
      intro i hi
      apply hq
      have : ℓ - 1 = (ℓ - 1 - i.val) + i.val := by omega
      rw [show (fun x => A.step x a)^[ℓ - 1] q = f^[ℓ - 1] q from rfl, this,
        Function.iterate_add_apply]
      exact hC_iter _ hi _
    have hinj : Function.Injective (fun i : Fin ℓ =>
        (⟨f^[i.val] q, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotC i⟩⟩ :
          (Finset.univ \ C : Finset Q))) := by
      intro i j hij
      have hval : f^[i.val] q = f^[j.val] q := congrArg Subtype.val hij
      clear hij
      by_contra hne
      have hne_val : i.val ≠ j.val := fun h => hne (Fin.ext h)
      wlog hlt_ij : i.val < j.val generalizing i j
      · exact this (i := j) (j := i) hval.symm (Ne.symm hne) (Ne.symm hne_val) (by omega)
      let d := j.val - i.val
      have hd_pos : 0 < d := by omega
      have hper : ∀ k : ℕ, f^[i.val + k * d] q = f^[i.val] q := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Nat.succ_mul, ← add_assoc, add_comm (i.val + k * d) d,
            Function.iterate_add_apply, ih, ← Function.iterate_add_apply]
          have : d + i.val = j.val := by omega
          rw [this]
          exact hval.symm
      have hmem : f^[i.val + ℓ * d] q ∈ C := by
        have hle : ℓ ≤ i.val + ℓ * d := by
          have : 1 ≤ d := hd_pos
          nlinarith
        obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
        rw [hr, add_comm, Function.iterate_add_apply]
        exact hC_iter _ (hℓ q) r
      rw [hper ℓ] at hmem
      exact hnotC i hmem
    have hcard := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at hcard
    have hsdiff : (Finset.univ \ C).card = Fintype.card Q - C.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have hCle : C.card ≤ Fintype.card Q := Finset.card_le_univ C
    omega

/-! ### Controls and Block Words -/

section Controls

variable {α : Type v}

/-- Number of control letters (letters `≠ a`) in a word `w`. -/
def controls (a : α) (w : List α) : ℕ :=
  w.countP (fun b => decide (b ≠ a))

@[simp]
lemma controls_nil (a : α) : controls a [] = 0 := by
  simp [controls]

lemma controls_cons (a b : α) (w : List α) :
    controls a (b :: w) = (if b = a then 0 else 1) + controls a w := by
  simp only [controls, List.countP_cons]
  by_cases h : b = a
  · simp [h]
  · simp [h, add_comm]

lemma controls_cons_self (a : α) (w : List α) :
    controls a (a :: w) = controls a w := by
  simp [controls_cons]

lemma controls_cons_ne {a b : α} (h : b ≠ a) (w : List α) :
    controls a (b :: w) = controls a w + 1 := by
  simp [controls_cons, h, add_comm]

@[simp]
lemma controls_append (a : α) (u v : List α) :
    controls a (u ++ v) = controls a u + controls a v := by
  simp [controls, List.countP_append]

@[simp]
lemma controls_replicate_self (a : α) (k : ℕ) :
    controls a (List.replicate k a) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, controls_cons_self, ih]

lemma controls_le_length (a : α) (w : List α) : controls a w ≤ w.length :=
  List.countP_le_length

lemma eq_replicate_of_controls_zero {a : α} {w : List α} (h : controls a w = 0) :
    w = List.replicate w.length a := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [controls_cons] at h
    by_cases hba : b = a
    · subst b
      simp only [ite_true, zero_add] at h
      rw [List.length_cons, List.replicate_succ]
      congr 1
      exact ih h
    · simp only [hba, ite_false] at h
      omega

/-- Every word with `controls a w = r + 1` splits at its last control letter `g ≠ a`. -/
lemma exists_split_last_control {a : α} {w : List α} {r : ℕ} (h : controls a w = r + 1) :
    ∃ (u : List α) (g : α) (j : ℕ),
      g ≠ a ∧ controls a u = r ∧ w = u ++ [g] ++ List.replicate j a := by
  induction w using List.reverseRecOn with
  | nil => simp at h
  | append_singleton w b ih =>
    rw [controls_append, controls_cons, controls_nil, add_zero] at h
    by_cases hba : b = a
    · subst b
      simp only [ite_true, add_zero] at h
      obtain ⟨u, g, j, hga, hcu, rfl⟩ := ih h
      refine ⟨u, g, j + 1, hga, hcu, ?_⟩
      simp [List.replicate_succ', List.append_assoc]
    · simp only [hba, ite_false] at h
      refine ⟨w, b, 0, hba, by omega, by simp⟩

/-- Block word `a^(h 0) g 0 a^(h 1) ... g (r-1) a^(h r)`. -/
def blockWord (a : α) : ∀ {r : ℕ}, (Fin r → α) → (Fin (r + 1) → ℕ) → List α
  | 0, _, h => List.replicate (h 0) a
  | _ + 1, g, h =>
    List.replicate (h 0) a ++ [g 0] ++ blockWord a (fun i => g i.succ) (fun i => h i.succ)

lemma blockWord_length (a : α) : ∀ {r : ℕ} (g : Fin r → α) (h : Fin (r + 1) → ℕ),
    (blockWord a g h).length = r + ∑ i : Fin (r + 1), h i
  | 0, _, h => by simp [blockWord]
  | r + 1, g, h => by
    simp only [blockWord, List.length_append, List.length_replicate, List.length_singleton,
      blockWord_length a (fun i => g i.succ) (fun i => h i.succ), Fin.sum_univ_succ]
    omega

lemma blockWord_controls (a : α) : ∀ {r : ℕ} (g : Fin r → α) (_ : ∀ i, g i ≠ a)
    (h : Fin (r + 1) → ℕ), controls a (blockWord a g h) = r
  | 0, _, _, h => by simp [blockWord]
  | r + 1, g, hg, h => by
    simp only [blockWord, controls_append, controls_replicate_self, zero_add]
    rw [controls_cons_ne (hg 0), controls_nil, zero_add,
      blockWord_controls a (fun i => g i.succ) (fun i => hg i.succ) (fun i => h i.succ)]
    omega

lemma blockWord_append_replicate (a : α) : ∀ {r : ℕ} (g : Fin r → α) (h : Fin (r + 1) → ℕ) (k : ℕ),
    blockWord a g h ++ List.replicate k a =
      blockWord a g (Function.update h (Fin.last r) (h (Fin.last r) + k))
  | 0, _, h, k => by
    simp only [blockWord, Fin.last_zero, Function.update_self, ← List.replicate_add]
  | r + 1, g, h, k => by
    simp only [blockWord, List.append_assoc]
    have h0 : Function.update h (Fin.last (r + 1)) (h (Fin.last (r + 1)) + k) 0 = h 0 := by
      apply Function.update_of_ne
      exact (Fin.succ_ne_zero (Fin.last r)).symm
    have hsucc : (fun i : Fin (r + 1) =>
        Function.update h (Fin.last (r + 1)) (h (Fin.last (r + 1)) + k) i.succ) =
        Function.update (fun i : Fin (r + 1) => h i.succ) (Fin.last r)
          (h (Fin.last r).succ + k) := by
      funext i
      by_cases hi : i = Fin.last r
      · subst hi
        simp [Fin.succ_last]
      · have hne : i.succ ≠ Fin.last (r + 1) := by
          intro heq
          apply hi
          exact Fin.succ_injective _ (heq.trans (Fin.succ_last r).symm)
        simp [Function.update_of_ne hne, Function.update_of_ne hi]
    rw [h0, hsucc, ← blockWord_append_replicate a (fun i => g i.succ) (fun i => h i.succ) k]

/-- Every word `w` with `controls a w = r` can be written as a `blockWord`. -/
lemma exists_blockWord (a : α) (w : List α) :
    ∃ (g : Fin (controls a w) → α) (h : Fin (controls a w + 1) → ℕ),
      (∀ i, g i ≠ a) ∧ w = blockWord a g h := by
  induction w with
  | nil =>
    rw [controls_nil]
    refine ⟨Fin.elim0, fun _ => 0, fun i => i.elim0, ?_⟩
    simp [blockWord]
  | cons b w ih =>
    obtain ⟨g, h, hg, hw⟩ := ih
    by_cases hba : b = a
    · subst b
      have hctrl : controls a (a :: w) = controls a w := controls_cons_self a w
      generalize hctrl_eq : controls a w = r at g h hg hw hctrl
      rw [hctrl]
      refine ⟨g, fun i => if i = 0 then h 0 + 1 else h i, hg, ?_⟩
      cases r with
      | zero =>
        simp only [blockWord, ite_true] at hw ⊢
        rw [hw, List.replicate_succ]
      | succ r =>
        simp only [blockWord, ite_true, Fin.succ_ne_zero, ite_false] at hw ⊢
        rw [hw, List.replicate_succ, List.cons_append, List.cons_append]
    · have hctrl : controls a (b :: w) = controls a w + 1 := controls_cons_ne hba w
      generalize hctrl_eq : controls a w = r at g h hg hw hctrl
      rw [hctrl]
      refine ⟨Fin.cases b g, Fin.cases 0 h, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · exact hba
        · exact hg
      · simp only [blockWord, Fin.cases_zero, Fin.cases_succ, List.replicate_zero, List.nil_append,
          List.singleton_append]
        rw [hw]

end Controls

/-! ### Section 2: Matrix Representation, Fitting Decomposition, and Explicit Spectral Projectors -/

/-- Row-stochastic transition matrix `P_w` over `ℂ`: `(P_w) p q = 1` iff `A.eval p w = q`. -/
def transMat {Q : Type u} {α : Type v} [DecidableEq Q] (A : DFA Q α) (w : List α) : Matrix Q Q ℂ :=
  fun p q => if A.eval p w = q then 1 else 0

lemma transMat_nil {Q : Type u} {α : Type v} [DecidableEq Q] (A : DFA Q α) :
    transMat A [] = 1 := by
  ext p q
  simp only [transMat, DFA.eval_nil, Matrix.one_apply]
  by_cases h : p = q <;> simp [h]

lemma transMat_append {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (u v : List α) :
    transMat A (u ++ v) = transMat A u * transMat A v := by
  ext p q
  simp only [transMat, DFA.eval_append, Matrix.mul_apply]
  rw [Finset.sum_eq_single (A.eval p u)]
  · simp
  · intro r _ hr
    simp [Ne.symm hr]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma transMat_cons {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (b : α) (w : List α) :
    transMat A (b :: w) = transMat A [b] * transMat A w := by
  simpa using transMat_append A [b] w

/-- Indicator vector `[S]` in `Q → ℂ`. -/
def indVec {Q : Type u} [DecidableEq Q] (S : Finset Q) : Q → ℂ :=
  fun q => if q ∈ S then 1 else 0

lemma vecMul_transMat_apply {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (v : Q → ℂ) (w : List α) (q : Q) :
    (v ᵥ* transMat A w) q = ∑ p : Q, if A.eval p w = q then v p else 0 := by
  simp only [Matrix.vecMul, dotProduct, transMat, mul_ite, mul_one, mul_zero]

lemma single_vecMul_transMat {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (p : Q) (w : List α) :
    (Pi.single p (1 : ℂ)) ᵥ* transMat A w = Pi.single (A.eval p w) 1 := by
  ext q
  rw [vecMul_transMat_apply, Pi.single_apply]
  rw [Finset.sum_eq_single p]
  · simp [eq_comm]
  · intro r _ hr
    simp [Pi.single_eq_of_ne hr]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma sum_vecMul_transMat {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (v : Q → ℂ) (w : List α) :
    ∑ q : Q, (v ᵥ* transMat A w) q = ∑ p : Q, v p := by
  simp only [vecMul_transMat_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single (A.eval p w)]
  · simp
  · intro q _ hq
    simp [Ne.symm hq]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Zero-sum row subspace `Z = {v | ∑ q, v q = 0}`. -/
def Zsub {Q : Type u} [Fintype Q] : Submodule ℂ (Q → ℂ) :=
  LinearMap.ker (LinearMap.lsum ℂ (fun _ : Q => ℂ) ℂ (fun _ => LinearMap.id))

lemma mem_Zsub_iff {Q : Type u} [Fintype Q] (v : Q → ℂ) :
    v ∈ Zsub (Q := Q) ↔ ∑ q : Q, v q = 0 := by
  simp [Zsub]

lemma vecMul_transMat_mem_Zsub {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} {v : Q → ℂ} (hv : v ∈ Zsub) (w : List α) :
    v ᵥ* transMat A w ∈ Zsub := by
  rw [mem_Zsub_iff] at hv ⊢
  rw [sum_vecMul_transMat]
  exact hv

/-- Right-multiplication by a matrix `M` as a linear endomorphism of `Q → ℂ`. -/
def vecMulEnd {Q : Type u} [Fintype Q] (M : Matrix Q Q ℂ) : Module.End ℂ (Q → ℂ) :=
  Matrix.vecMulLinear M

@[simp]
lemma vecMulEnd_apply {Q : Type u} [Fintype Q] (M : Matrix Q Q ℂ) (v : Q → ℂ) :
    vecMulEnd M v = v ᵥ* M :=
  rfl

namespace Data

variable {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q] {A : DFA Q α} (D : Data A)

/-- Transition matrix of the one-cluster letter `a`. -/
def Tmat : Matrix Q Q ℂ := transMat A [D.a]

lemma transMat_replicate (k : ℕ) : transMat A (List.replicate k D.a) = D.Tmat ^ k := by
  induction k with
  | zero => simp [transMat_nil]
  | succ k ih =>
    rw [List.replicate_succ, transMat_cons, ih, pow_succ', Tmat]

lemma Tmat_pow_apply (k : ℕ) (p q : Q) :
    (D.Tmat ^ k) p q = if D.stepA^[k] p = q then 1 else 0 := by
  rw [← D.transMat_replicate, transMat, DFA.eval_replicate]
  rfl

lemma single_vecMul_Tmat_pow (p : Q) (k : ℕ) :
    (Pi.single p (1 : ℂ)) ᵥ* (D.Tmat ^ k) = Pi.single (D.stepA^[k] p) 1 := by
  rw [← D.transMat_replicate, single_vecMul_transMat, DFA.eval_replicate]
  rfl

lemma vecMul_Tmat_pow_mem_Zsub {v : Q → ℂ} (hv : v ∈ Zsub) (k : ℕ) :
    v ᵥ* (D.Tmat ^ k) ∈ Zsub := by
  rw [← D.transMat_replicate]
  exact vecMul_transMat_mem_Zsub hv _

lemma Tmat_pow_add_m {k : ℕ} (hk : D.ℓ ≤ k) :
    D.Tmat ^ (k + D.m) = D.Tmat ^ k := by
  ext p q
  rw [D.Tmat_pow_apply, D.Tmat_pow_apply, D.iterate_add_m_eq p hk]

lemma Tmat_pow_add_mul_m {k : ℕ} (hk : D.ℓ ≤ k) (r : ℕ) :
    D.Tmat ^ (k + r * D.m) = D.Tmat ^ k := by
  ext p q
  rw [D.Tmat_pow_apply, D.Tmat_pow_apply, D.iterate_add_mul_m_eq p hk r]

lemma Tmat_pow_m_mul_l_mul_l : D.Tmat ^ (D.m * D.ℓ) * D.Tmat ^ D.ℓ = D.Tmat ^ D.ℓ := by
  rw [← pow_add, add_comm]
  have h := D.Tmat_pow_add_mul_m (k := D.ℓ) le_rfl D.ℓ
  rwa [mul_comm] at h

lemma Tmat_pow_l_mul_m_mul_l : D.Tmat ^ D.ℓ * D.Tmat ^ (D.m * D.ℓ) = D.Tmat ^ D.ℓ := by
  rw [← pow_add]
  have h := D.Tmat_pow_add_mul_m (k := D.ℓ) le_rfl D.ℓ
  rwa [mul_comm] at h

lemma Tmat_pow_m_mul_l_idem :
    D.Tmat ^ (D.m * D.ℓ) * D.Tmat ^ (D.m * D.ℓ) = D.Tmat ^ (D.m * D.ℓ) := by
  have hle : D.ℓ ≤ D.m * D.ℓ := Nat.le_mul_of_pos_left D.ℓ D.m_pos
  rw [← pow_add]
  have h := D.Tmat_pow_add_mul_m (k := D.m * D.ℓ) hle D.ℓ
  rwa [mul_comm D.ℓ D.m] at h

lemma indVec_C_vecMul_Tmat : indVec D.C ᵥ* D.Tmat = indVec D.C := by
  ext q
  rw [Tmat, vecMul_transMat_apply]
  change (∑ p : Q, if D.stepA p = q then indVec D.C p else 0) = indVec D.C q
  simp only [indVec]
  by_cases hq : q ∈ D.C
  · simp only [hq, ite_true]
    obtain ⟨⟨p, hp⟩, hpq⟩ := D.stepAC_surjective ⟨q, hq⟩
    have hpq' : D.stepA p = q := congrArg Subtype.val hpq
    rw [Finset.sum_eq_single p]
    · simp [hpq', hp]
    · intro r _ hr
      split_ifs with h1 h2
      · exfalso
        exact hr (D.stepA_injOn_C h2 hp (h1.trans hpq'.symm))
      · rfl
      · rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [hq, ite_false]
    refine Finset.sum_eq_zero fun p _ => ?_
    split_ifs with h1 h2
    · exfalso
      exact hq (h1 ▸ D.hC_inv p h2)
    · rfl
    · rfl

lemma indVec_C_vecMul_Tmat_pow (k : ℕ) : indVec D.C ᵥ* (D.Tmat ^ k) = indVec D.C := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.vecMul_vecMul, ih, D.indVec_C_vecMul_Tmat]

/-- Counting pairing identity: `[C] P_w [S]ᵀ = |S w⁻¹ ∩ C|`. -/
lemma dotProduct_indVec_C_transMat (S : Finset Q) (w : List α) :
    dotProduct (indVec D.C ᵥ* transMat A w) (indVec S) =
      (((A.preimage S w) ∩ D.C).card : ℂ) := by
  simp only [dotProduct, vecMul_transMat_apply, indVec]
  have h1 : (∑ q : Q, (∑ p : Q, if A.eval p w = q then if p ∈ D.C then (1 : ℂ) else 0 else 0) *
      if q ∈ S then 1 else 0) =
      ∑ p : Q, ∑ q : Q, (if A.eval p w = q then if p ∈ D.C then (1 : ℂ) else 0 else 0) *
        if q ∈ S then 1 else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
  rw [h1]
  have h2 : (∑ p : Q, ∑ q : Q, (if A.eval p w = q then if p ∈ D.C then (1 : ℂ) else 0 else 0) *
      if q ∈ S then 1 else 0) =
      ∑ p ∈ D.C, if A.eval p w ∈ S then (1 : ℂ) else 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ D.C)]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.sum_eq_single (A.eval p w)]
      · simp [hp]
      · intro q _ hq
        simp [Ne.symm hq]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro p _ hp
      refine Finset.sum_eq_zero fun q _ => ?_
      simp [hp]
  rw [h2, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext p
  simp [and_comm]

/-- Sum of `m` consecutive powers starting at any `k ≥ ℓ` equals the rank-1 matrix `1 [C]`. -/
lemma sum_Tmat_pow_range_apply {k : ℕ} (hk : D.ℓ ≤ k) (p q : Q) :
    (∑ j ∈ Finset.range D.m, D.Tmat ^ (k + j)) p q = if q ∈ D.C then 1 else 0 := by
  simp only [Matrix.sum_apply, D.Tmat_pow_apply]
  have hmem : D.stepA^[k] p ∈ D.C := D.iterate_mem_C_of_ge p hk
  have hsum : (∑ j ∈ Finset.range D.m, if D.stepA^[k + j] p = q then (1 : ℂ) else 0) =
      ∑ j : Fin D.m, if (D.cycleEquiv (D.stepA^[k] p) hmem j).1 = q then (1 : ℂ) else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => if D.stepA^[k + j] p = q then (1 : ℂ) else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Data.cycleEquiv_apply, add_comm k j.val, Function.iterate_add_apply]
  rw [hsum]
  by_cases hq : q ∈ D.C
  · simp only [hq, ite_true]
    let j₀ := (D.cycleEquiv (D.stepA^[k] p) hmem).symm ⟨q, hq⟩
    rw [Finset.sum_eq_single j₀]
    · simp [j₀]
    · intro j _ hj
      have hne : (D.cycleEquiv (D.stepA^[k] p) hmem j).1 ≠ q := by
        intro heq
        apply hj
        apply (D.cycleEquiv (D.stepA^[k] p) hmem).injective
        apply Subtype.ext
        simpa [j₀] using heq
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [hq, ite_false]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hne : (D.cycleEquiv (D.stepA^[k] p) hmem j).1 ≠ q := fun heq =>
      hq (heq ▸ (D.cycleEquiv (D.stepA^[k] p) hmem j).2)
    simp [hne]

/-- Cycle-averaging matrix `B = ∑_{j < m} T^(ℓ + j)`. -/
def Bmat : Matrix Q Q ℂ := ∑ j ∈ Finset.range D.m, D.Tmat ^ (D.ℓ + j)

lemma Bmat_apply (p q : Q) : D.Bmat p q = if q ∈ D.C then 1 else 0 :=
  D.sum_Tmat_pow_range_apply le_rfl p q

lemma vecMul_Bmat_eq_zero {v : Q → ℂ} (hv : v ∈ Zsub) : v ᵥ* D.Bmat = 0 := by
  ext q
  simp only [Matrix.vecMul, dotProduct, D.Bmat_apply, Pi.zero_apply]
  rw [mem_Zsub_iff] at hv
  by_cases hq : q ∈ D.C
  · simp [hq, hv]
  · simp [hq]

/-- Primitive `m`-th root of unity `ζ = exp(2πi / m)`. -/
def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / D.m)

lemma isPrimitiveRoot_zeta : IsPrimitiveRoot D.zeta D.m :=
  Complex.isPrimitiveRoot_exp D.m (Nat.ne_of_gt D.m_pos)

/-- The `k`-th `m`-th root of unity `λ_k = ζ^k`. -/
def lam (k : Fin D.m) : ℂ := D.zeta ^ k.val

lemma lam_zero : D.lam ⟨0, D.m_pos⟩ = 1 := by simp [lam]

lemma lam_pow_m (k : Fin D.m) : D.lam k ^ D.m = 1 := by
  rw [lam, ← pow_mul, mul_comm, pow_mul, D.isPrimitiveRoot_zeta.pow_eq_one, one_pow]

lemma lam_ne_zero (k : Fin D.m) : D.lam k ≠ 0 :=
  pow_ne_zero k.val (D.isPrimitiveRoot_zeta.ne_zero (Nat.ne_of_gt D.m_pos))

lemma lam_injective : Function.Injective D.lam := by
  intro i j hij
  exact Fin.ext (D.isPrimitiveRoot_zeta.injOn_pow
    (Finset.mem_coe.mpr (Finset.mem_range.mpr i.isLt))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr j.isLt)) hij)

lemma lam_ne_one_of_ne_zero {k : Fin D.m} (hk : k.val ≠ 0) : D.lam k ≠ 1 := by
  intro h
  have := D.lam_injective (h.trans D.lam_zero.symm)
  exact hk (congrArg Fin.val this)

lemma sum_lam_pow (k : Fin D.m) :
    ∑ j : Fin D.m, D.lam k ^ j.val = if k.val = 0 then (D.m : ℂ) else 0 := by
  by_cases hk : k.val = 0
  · simp only [hk, ite_true]
    have hlam : D.lam k = 1 := by simp [lam, hk]
    simp [hlam]
  · simp only [hk, ite_false]
    rw [Fin.sum_univ_eq_sum_range (fun j => D.lam k ^ j),
      geom_sum_eq (D.lam_ne_one_of_ne_zero hk), D.lam_pow_m, sub_self, zero_div]

lemma sum_inv_lam_pow (k : Fin D.m) :
    ∑ j : Fin D.m, (D.lam k)⁻¹ ^ j.val = if k.val = 0 then (D.m : ℂ) else 0 := by
  by_cases hk : k.val = 0
  · simp only [hk, ite_true]
    have hlam : D.lam k = 1 := by simp [lam, hk]
    simp [hlam]
  · simp only [hk, ite_false]
    have hne : (D.lam k)⁻¹ ≠ 1 := fun h =>
      D.lam_ne_one_of_ne_zero hk (inv_eq_one.mp h)
    have hpow : (D.lam k)⁻¹ ^ D.m = 1 := by
      rw [inv_pow, D.lam_pow_m, inv_one]
    rw [Fin.sum_univ_eq_sum_range (fun j => (D.lam k)⁻¹ ^ j),
      geom_sum_eq hne, hpow, sub_self, zero_div]

/-- Explicit Fitting & spectral projectors (CRT-free!). -/
def E_R : Matrix Q Q ℂ := D.Tmat ^ (D.m * D.ℓ)

def E_N : Matrix Q Q ℂ := 1 - D.E_R

def E_eig (k : Fin D.m) : Matrix Q Q ℂ :=
  ((D.m : ℂ)⁻¹) • ∑ j : Fin D.m, ((D.lam k)⁻¹ ^ j.val) • D.Tmat ^ (D.m * D.ℓ + j.val)

/-- Explicit polynomial witnesses for `E_R`, `E_N`, `E_eig k`. -/
def poly_ER : ℂ[X] := Polynomial.X ^ (D.m * D.ℓ)

def poly_EN : ℂ[X] := 1 - Polynomial.X ^ (D.m * D.ℓ)

def poly_Eeig (k : Fin D.m) : ℂ[X] :=
  Polynomial.C ((D.m : ℂ)⁻¹) *
    ∑ j : Fin D.m, Polynomial.C ((D.lam k)⁻¹ ^ j.val) * Polynomial.X ^ (D.m * D.ℓ + j.val)

lemma aeval_poly_ER : Polynomial.aeval D.Tmat D.poly_ER = D.E_R := by
  simp [poly_ER, E_R]

lemma aeval_poly_EN : Polynomial.aeval D.Tmat D.poly_EN = D.E_N := by
  simp [poly_EN, E_N, E_R]

lemma aeval_poly_Eeig (k : Fin D.m) : Polynomial.aeval D.Tmat (D.poly_Eeig k) = D.E_eig k := by
  simp [poly_Eeig, E_eig, map_mul, map_sum, Polynomial.aeval_C, Polynomial.aeval_X_pow,
    Algebra.smul_def]

lemma E_R_idem : D.E_R * D.E_R = D.E_R := D.Tmat_pow_m_mul_l_idem

lemma E_N_mul_Tmat_pow_l : D.E_N * D.Tmat ^ D.ℓ = 0 := by
  rw [E_N, sub_mul, one_mul, E_R, D.Tmat_pow_m_mul_l_mul_l, sub_self]

lemma Tmat_pow_comm_E_N (j : ℕ) : D.Tmat ^ j * D.E_N = D.E_N * D.Tmat ^ j := by
  rw [E_N, mul_sub, sub_mul, mul_one, one_mul, E_R, ← pow_add, ← pow_add, add_comm]

lemma E_N_mul_E_R : D.E_N * D.E_R = 0 := by
  rw [E_N, sub_mul, one_mul, D.E_R_idem, sub_self]

lemma E_R_mul_E_N : D.E_R * D.E_N = 0 := by
  rw [E_N, mul_sub, mul_one, D.E_R_idem, sub_self]

lemma E_N_idem : D.E_N * D.E_N = D.E_N := by
  rw [E_N, sub_mul, one_mul, mul_sub, mul_one, D.E_R_idem, sub_self, sub_zero]

lemma E_R_mul_Tmat_pow_add (j : ℕ) :
    D.E_R * D.Tmat ^ (D.m * D.ℓ + j) = D.Tmat ^ (D.m * D.ℓ + j) := by
  rw [pow_add, ← mul_assoc, E_R, D.Tmat_pow_m_mul_l_idem]

lemma E_N_mul_E_eig (k : Fin D.m) : D.E_N * D.E_eig k = 0 := by
  rw [E_eig, Matrix.mul_smul, Finset.mul_sum]
  have hterm : ∀ j : Fin D.m,
      D.E_N * (((D.lam k)⁻¹ ^ j.val) • D.Tmat ^ (D.m * D.ℓ + j.val)) = 0 := by
    intro j
    rw [Matrix.mul_smul, ← D.E_R_mul_Tmat_pow_add j.val, ← mul_assoc, D.E_N_mul_E_R,
      zero_mul, smul_zero]
  rw [Finset.sum_eq_zero (fun j _ => hterm j), smul_zero]

lemma E_eig_mul_E_N (k : Fin D.m) : D.E_eig k * D.E_N = 0 := by
  rw [E_eig, Matrix.smul_mul, Finset.sum_mul]
  have hterm : ∀ j : Fin D.m,
      (((D.lam k)⁻¹ ^ j.val) • D.Tmat ^ (D.m * D.ℓ + j.val)) * D.E_N = 0 := by
    intro j
    rw [Matrix.smul_mul, pow_add, mul_assoc, D.Tmat_pow_comm_E_N, ← mul_assoc, ← E_R,
      D.E_R_mul_E_N, zero_mul, smul_zero]
  rw [Finset.sum_eq_zero (fun j _ => hterm j), smul_zero]

lemma sum_E_eig_eq_E_R : ∑ k : Fin D.m, D.E_eig k = D.E_R := by
  simp only [E_eig, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ j : Fin D.m,
      (∑ k : Fin D.m, ((D.lam k)⁻¹ ^ j.val) • D.Tmat ^ (D.m * D.ℓ + j.val)) =
        (if j.val = 0 then (D.m : ℂ) else 0) • D.Tmat ^ (D.m * D.ℓ + j.val) := by
    intro j
    rw [← Finset.sum_smul]
    congr 1
    have heq : (∑ k : Fin D.m, (D.lam k)⁻¹ ^ j.val) = ∑ k : Fin D.m, (D.lam j)⁻¹ ^ k.val := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lam, inv_pow, ← pow_mul, mul_comm]
    rw [heq, D.sum_inv_lam_pow]
  simp_rw [hterm]
  rw [Finset.sum_eq_single ⟨0, D.m_pos⟩]
  · simp only [ite_true, add_zero, smul_smul]
    have hm : (D.m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.m_pos)
    rw [inv_mul_cancel₀ hm, one_smul, E_R]
  · intro j _ hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp [hj0]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma E_N_add_sum_E_eig : D.E_N + ∑ k : Fin D.m, D.E_eig k = 1 := by
  rw [D.sum_E_eig_eq_E_R, E_N, sub_add_cancel]

lemma E_eig_mul_Tmat (k : Fin D.m) : D.E_eig k * D.Tmat = D.lam k • D.E_eig k := by
  have hm : 0 < D.m := D.m_pos
  have hle : D.ℓ ≤ D.m * D.ℓ := Nat.le_mul_of_pos_left D.ℓ hm
  have hcomm : D.E_eig k * D.Tmat =
      ((D.m : ℂ)⁻¹) • ∑ j : Fin D.m, ((D.lam k)⁻¹ ^ j.val) • D.Tmat ^ (D.m * D.ℓ + (j.val + 1)) := by
    rw [E_eig, Matrix.smul_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mul, ← pow_succ, add_assoc]
  rw [hcomm, E_eig, smul_comm]
  congr 1
  rw [Finset.smul_sum]
  let σ : Fin D.m ≃ Fin D.m :=
    { toFun := fun j => ⟨(j.val + 1) % D.m, Nat.mod_lt _ hm⟩
      invFun := fun j => ⟨(j.val + (D.m - 1)) % D.m, Nat.mod_lt _ hm⟩
      left_inv := fun j => by
        ext
        simp only [Nat.mod_add_mod]
        have hj := j.isLt
        have : j.val + 1 + (D.m - 1) = j.val + D.m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
      right_inv := fun j => by
        ext
        simp only [Nat.mod_add_mod]
        have hj := j.isLt
        have : j.val + (D.m - 1) + 1 = j.val + D.m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj] }
  refine Fintype.sum_equiv σ
    (fun j : Fin D.m => ((D.lam k)⁻¹ ^ j.val) • D.Tmat ^ (D.m * D.ℓ + (j.val + 1)))
    (fun j : Fin D.m => D.lam k • (((D.lam k)⁻¹ ^ j.val) • D.Tmat ^ (D.m * D.ℓ + j.val)))
    fun j => ?_
  rw [smul_smul]
  have hlam_ne : D.lam k ≠ 0 := D.lam_ne_zero k
  by_cases hlast : j.val + 1 < D.m
  · have hσ : (σ j).val = j.val + 1 := Nat.mod_eq_of_lt hlast
    rw [hσ, pow_succ', ← mul_assoc, mul_inv_cancel₀ hlam_ne, one_mul]
  · have hj_eq : j.val + 1 = D.m := by have := j.isLt; omega
    have hσ : (σ j).val = 0 := by change (j.val + 1) % D.m = 0; rw [hj_eq, Nat.mod_self]
    rw [hσ, hj_eq, D.Tmat_pow_add_m hle, add_zero, pow_zero, mul_one]
    congr 1
    have hpow : D.lam k ^ j.val * D.lam k = 1 := by
      rw [← pow_succ, hj_eq, D.lam_pow_m]
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_right hpow

lemma Tmat_mul_E_eig (k : Fin D.m) : D.Tmat * D.E_eig k = D.lam k • D.E_eig k := by
  have hcomm : D.Tmat * D.E_eig k = D.E_eig k * D.Tmat := by
    rw [E_eig, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← pow_succ', ← pow_succ]
  rw [hcomm, D.E_eig_mul_Tmat]

lemma E_eig_mul_Tmat_pow (k : Fin D.m) (h : ℕ) :
    D.E_eig k * D.Tmat ^ h = (D.lam k ^ h) • D.E_eig k := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ, ← mul_assoc, ih, Matrix.smul_mul, D.E_eig_mul_Tmat, smul_smul, pow_succ]

lemma Tmat_pow_mul_E_eig (k : Fin D.m) (h : ℕ) :
    D.Tmat ^ h * D.E_eig k = (D.lam k ^ h) • D.E_eig k := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ', mul_assoc, ih, Matrix.mul_smul, D.Tmat_mul_E_eig, smul_smul, pow_succ', mul_comm]

lemma E_eig_mul_E_eig (k₁ k₂ : Fin D.m) :
    D.E_eig k₁ * D.E_eig k₂ = if k₁ = k₂ then D.E_eig k₁ else 0 := by
  nth_rw 2 [E_eig]
  rw [Matrix.mul_smul, Finset.mul_sum]
  have hterm : ∀ j : Fin D.m,
      D.E_eig k₁ * (((D.lam k₂)⁻¹ ^ j.val) • D.Tmat ^ (D.m * D.ℓ + j.val)) =
        ((D.lam k₁ * (D.lam k₂)⁻¹) ^ j.val) • D.E_eig k₁ := by
    intro j
    rw [Matrix.mul_smul, D.E_eig_mul_Tmat_pow, smul_smul, pow_add, pow_mul,
      D.lam_pow_m, one_pow, one_mul, mul_pow, mul_comm]
  simp_rw [hterm, ← Finset.sum_smul, smul_smul]
  by_cases heq : k₁ = k₂
  · subst heq
    simp only [ite_true, mul_inv_cancel₀ (D.lam_ne_zero k₁), one_pow, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.m_pos)), one_smul]
  · simp only [heq, ite_false]
    have hne : D.lam k₁ * (D.lam k₂)⁻¹ ≠ 1 := by
      intro h
      apply heq
      apply D.lam_injective
      calc D.lam k₁ = (D.lam k₁ * (D.lam k₂)⁻¹) * D.lam k₂ := by
            rw [mul_assoc, inv_mul_cancel₀ (D.lam_ne_zero k₂), mul_one]
        _ = D.lam k₂ := by rw [h, one_mul]
    have hpow : (D.lam k₁ * (D.lam k₂)⁻¹) ^ D.m = 1 := by
      rw [mul_pow, inv_pow, D.lam_pow_m, D.lam_pow_m, inv_one, mul_one]
    have hsum : (∑ j : Fin D.m, (D.lam k₁ * (D.lam k₂)⁻¹) ^ j.val) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (D.lam k₁ * (D.lam k₂)⁻¹) ^ j),
        geom_sum_eq hne, hpow, sub_self, zero_div]
    rw [hsum, mul_zero, zero_smul]

lemma E_eig_zero_eq : D.E_eig ⟨0, D.m_pos⟩ = ((D.m : ℂ)⁻¹) • D.Bmat := by
  ext p q
  simp only [E_eig, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, D.lam_zero, inv_one,
    one_pow, one_smul, D.Bmat_apply]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j => (D.Tmat ^ (D.m * D.ℓ + j)) p q)]
  have := D.sum_Tmat_pow_range_apply (k := D.m * D.ℓ) (Nat.le_mul_of_pos_left D.ℓ D.m_pos) p q
  simpa [Matrix.sum_apply] using this

lemma vecMul_E_eig_zero_eq_zero {v : Q → ℂ} (hv : v ∈ Zsub) :
    v ᵥ* D.E_eig ⟨0, D.m_pos⟩ = 0 := by
  rw [D.E_eig_zero_eq, Matrix.vecMul_smul, D.vecMul_Bmat_eq_zero hv, smul_zero]

lemma vecMul_E_eig_mem_Zsub {k : Fin D.m} (hk : k.val ≠ 0) (v : Q → ℂ) :
    v ᵥ* D.E_eig k ∈ Zsub := by
  rw [mem_Zsub_iff]
  have h1 : ∑ q : Q, ((v ᵥ* D.E_eig k) ᵥ* D.Tmat) q = ∑ q : Q, (v ᵥ* D.E_eig k) q :=
    sum_vecMul_transMat A (v ᵥ* D.E_eig k) [D.a]
  have h2 : (v ᵥ* D.E_eig k) ᵥ* D.Tmat = D.lam k • (v ᵥ* D.E_eig k) := by
    rw [Matrix.vecMul_vecMul, D.E_eig_mul_Tmat, Matrix.vecMul_smul]
  rw [h2] at h1
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h1
  have hsub : (D.lam k - 1) * ∑ q : Q, (v ᵥ* D.E_eig k) q = 0 := by
    rw [sub_mul, one_mul, h1, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr (D.lam_ne_one_of_ne_zero hk))

lemma vecMul_E_R_mem_Zsub {v : Q → ℂ} (hv : v ∈ Zsub) : v ᵥ* D.E_R ∈ Zsub :=
  D.vecMul_Tmat_pow_mem_Zsub hv (D.m * D.ℓ)

lemma vecMul_E_N_mem_Zsub {v : Q → ℂ} (hv : v ∈ Zsub) : v ᵥ* D.E_N ∈ Zsub := by
  rw [E_N, Matrix.vecMul_sub, Matrix.vecMul_one]
  exact Zsub.sub_mem hv (D.vecMul_E_R_mem_Zsub hv)

lemma vecMul_E_eig_mem_Zsub_of_mem {v : Q → ℂ} (hv : v ∈ Zsub) (k : Fin D.m) :
    v ᵥ* D.E_eig k ∈ Zsub := by
  by_cases hk : k.val = 0
  · have : k = ⟨0, D.m_pos⟩ := Fin.ext hk
    rw [this, D.vecMul_E_eig_zero_eq_zero hv]
    exact Zsub.zero_mem
  · exact D.vecMul_E_eig_mem_Zsub hk v

/-! #### Fitting Subspaces `N` and `R`, Dimensions, and 1D Eigenspaces -/

/-- Nilpotent Fitting summand `N = ker(T^ℓ)`. -/
def Nsub : Submodule ℂ (Q → ℂ) := LinearMap.ker (vecMulEnd (D.Tmat ^ D.ℓ))

/-- Cycle (semisimple) Fitting summand `R = im(E_R)`. -/
def Rsub : Submodule ℂ (Q → ℂ) := LinearMap.range (vecMulEnd D.E_R)

lemma mem_Nsub_iff (v : Q → ℂ) : v ∈ D.Nsub ↔ v ᵥ* D.Tmat ^ D.ℓ = 0 :=
  Iff.rfl

lemma mem_Nsub_iff_vecMul_E_R (v : Q → ℂ) : v ∈ D.Nsub ↔ v ᵥ* D.E_R = 0 := by
  rw [mem_Nsub_iff]
  constructor
  · intro h
    have hle : D.ℓ ≤ D.m * D.ℓ := Nat.le_mul_of_pos_left D.ℓ D.m_pos
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [E_R, hd, pow_add, ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]
  · intro h
    rw [← D.Tmat_pow_m_mul_l_mul_l, ← Matrix.vecMul_vecMul, ← E_R, h, Matrix.zero_vecMul]

lemma mem_Nsub_iff_vecMul_E_N (v : Q → ℂ) : v ∈ D.Nsub ↔ v ᵥ* D.E_N = v := by
  rw [mem_Nsub_iff_vecMul_E_R, E_N, Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_self]

lemma vecMul_E_N_mem_Nsub (v : Q → ℂ) : v ᵥ* D.E_N ∈ D.Nsub := by
  rw [mem_Nsub_iff_vecMul_E_N, Matrix.vecMul_vecMul, D.E_N_idem]

lemma vecMul_Tmat_mem_Nsub {v : Q → ℂ} (hv : v ∈ D.Nsub) : v ᵥ* D.Tmat ∈ D.Nsub := by
  rw [mem_Nsub_iff] at hv ⊢
  rw [Matrix.vecMul_vecMul, ← pow_succ', pow_succ, ← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]

lemma mem_Rsub_iff_vecMul_E_R (v : Q → ℂ) : v ∈ D.Rsub ↔ v ᵥ* D.E_R = v := by
  constructor
  · rintro ⟨w, rfl⟩
    change (w ᵥ* D.E_R) ᵥ* D.E_R = w ᵥ* D.E_R
    rw [Matrix.vecMul_vecMul, D.E_R_idem]
  · intro h
    exact ⟨v, h⟩

lemma vecMul_E_R_mem_Rsub (v : Q → ℂ) : v ᵥ* D.E_R ∈ D.Rsub :=
  ⟨v, rfl⟩

lemma vecMul_Tmat_mem_Rsub {v : Q → ℂ} (hv : v ∈ D.Rsub) : v ᵥ* D.Tmat ∈ D.Rsub := by
  rw [mem_Rsub_iff_vecMul_E_R] at hv ⊢
  rw [Matrix.vecMul_vecMul, E_R, ← pow_succ', pow_succ, ← E_R, ← Matrix.vecMul_vecMul, hv]

lemma vecMul_E_eig_mem_Rsub (v : Q → ℂ) (k : Fin D.m) : v ᵥ* D.E_eig k ∈ D.Rsub := by
  rw [mem_Rsub_iff_vecMul_E_R, Matrix.vecMul_vecMul]
  have h1 : D.E_eig k * D.E_R = D.E_eig k := by
    have : D.E_eig k * (D.E_N + D.E_R) = D.E_eig k := by rw [E_N, sub_add_cancel, mul_one]
    rw [mul_add, D.E_eig_mul_E_N, zero_add] at this
    exact this
  rw [h1]

lemma mem_Rsub_iff_support_C (v : Q → ℂ) : v ∈ D.Rsub ↔ ∀ q : Q, q ∉ D.C → v q = 0 := by
  rw [mem_Rsub_iff_vecMul_E_R]
  constructor
  · intro hv q hq
    rw [← hv, E_R, ← D.transMat_replicate, vecMul_transMat_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    have hmem : A.eval p (List.replicate (D.m * D.ℓ) D.a) ∈ D.C := by
      rw [DFA.eval_replicate]
      exact D.iterate_mem_C_of_ge p (Nat.le_mul_of_pos_left D.ℓ D.m_pos)
    have hne : A.eval p (List.replicate (D.m * D.ℓ) D.a) ≠ q := fun heq => hq (heq ▸ hmem)
    simp [hne]
  · intro hsupp
    ext q
    rw [E_R, ← D.transMat_replicate, vecMul_transMat_apply]
    have hterm : ∀ p : Q,
        (if A.eval p (List.replicate (D.m * D.ℓ) D.a) = q then v p else 0) =
          if p = q then v p else 0 := by
      intro p
      by_cases hp : p ∈ D.C
      · rw [DFA.eval_replicate]
        change (if D.stepA^[D.m * D.ℓ] p = q then v p else 0) = _
        rw [D.iterate_m_mul_l_eq_self hp]
      · simp [hsupp p hp]
    simp_rw [hterm]
    rw [Finset.sum_eq_single q]
    · simp
    · intro p _ hp; simp [hp]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma mem_Rsub_iff_range_Tmat_pow_l (v : Q → ℂ) :
    v ∈ D.Rsub ↔ ∃ w : Q → ℂ, w ᵥ* D.Tmat ^ D.ℓ = v := by
  constructor
  · intro hv
    rw [mem_Rsub_iff_vecMul_E_R] at hv
    have hle : D.ℓ ≤ D.m * D.ℓ := Nat.le_mul_of_pos_left D.ℓ D.m_pos
    refine ⟨v ᵥ* D.Tmat ^ (D.m * D.ℓ - D.ℓ), ?_⟩
    rw [Matrix.vecMul_vecMul, ← pow_add, Nat.sub_add_cancel hle, ← E_R, hv]
  · rintro ⟨w, rfl⟩
    rw [mem_Rsub_iff_vecMul_E_R, Matrix.vecMul_vecMul, E_R, D.Tmat_pow_l_mul_m_mul_l]

lemma Nsub_le_Zsub : D.Nsub ≤ Zsub := by
  intro v hv
  rw [mem_Nsub_iff] at hv
  rw [mem_Zsub_iff]
  have h := sum_vecMul_transMat A v (List.replicate D.ℓ D.a)
  rw [D.transMat_replicate, hv] at h
  simp only [Pi.zero_apply, Finset.sum_const_zero] at h
  exact h.symm

lemma Nsub_inf_Rsub : D.Nsub ⊓ D.Rsub = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rcases hv with ⟨hN, hR⟩
  change v ∈ D.Nsub at hN
  change v ∈ D.Rsub at hR
  rw [mem_Nsub_iff_vecMul_E_R] at hN
  rw [mem_Rsub_iff_vecMul_E_R] at hR
  rw [Submodule.mem_bot, ← hR, hN]

lemma Nsub_sup_Rsub : D.Nsub ⊔ D.Rsub = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have h : v = v ᵥ* D.E_N + v ᵥ* D.E_R := by
    rw [← Matrix.vecMul_add, E_N, sub_add_cancel, Matrix.vecMul_one]
  rw [h]
  exact Submodule.add_mem_sup (D.vecMul_E_N_mem_Nsub v) (D.vecMul_E_R_mem_Rsub v)

lemma finrank_Rsub : Module.finrank ℂ D.Rsub = D.m := by
  let e : D.Rsub ≃ₗ[ℂ] (D.C → ℂ) :=
    { toFun := fun v c => v.1 c.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f => ⟨fun q => if h : q ∈ D.C then f ⟨q, h⟩ else 0, by
        rw [mem_Rsub_iff_support_C]
        intro q hq
        simp [hq]⟩
      left_inv := fun ⟨v, hv⟩ => by
        ext q
        by_cases hq : q ∈ D.C
        · simp [hq]
        · simp [hq, (D.mem_Rsub_iff_support_C v).mp hv q hq]
      right_inv := fun f => by
        ext ⟨q, hq⟩
        simp [hq] }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  rfl

lemma finrank_Nsub : Module.finrank ℂ D.Nsub = D.t := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq D.Nsub D.Rsub
  rw [D.Nsub_sup_Rsub, D.Nsub_inf_Rsub, finrank_top, finrank_bot, add_zero,
    Module.finrank_fintype_fun_eq_card, D.finrank_Rsub] at h
  unfold t n
  omega

/-- Canonical nonzero eigenvector `r_k = e_{c₀} ᵥ* E_k` spanning the 1D eigenspace `V_k`. -/
def rVec (k : Fin D.m) : Q → ℂ := (Pi.single D.c₀ (1 : ℂ)) ᵥ* D.E_eig k

lemma rVec_c₀ (k : Fin D.m) : D.rVec k D.c₀ = (D.m : ℂ)⁻¹ := by
  simp only [rVec, E_eig, Matrix.vecMul_smul, Matrix.vecMul_sum, Pi.smul_apply, Finset.sum_apply,
    D.single_vecMul_Tmat_pow]
  rw [Finset.sum_eq_single ⟨0, D.m_pos⟩]
  · simp [D.iterate_m_mul_l_eq_self D.c₀_mem]
  · intro j _ hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hne : D.stepA^[D.m * D.ℓ + j.val] D.c₀ ≠ D.c₀ := by
      rw [add_comm, Function.iterate_add_apply, D.iterate_m_mul_l_eq_self D.c₀_mem]
      intro heq
      have := (D.cycleEquiv D.c₀ D.c₀_mem).injective (a₁ := j) (a₂ := ⟨0, D.m_pos⟩)
        (Subtype.ext (by simpa [Data.cycleEquiv_apply] using heq))
      exact hj0 (congrArg Fin.val this)
    simp [Pi.single_eq_of_ne hne.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma rVec_ne_zero (k : Fin D.m) : D.rVec k ≠ 0 := by
  intro h
  have hc := congrFun h D.c₀
  rw [D.rVec_c₀, Pi.zero_apply] at hc
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.m_pos)) hc

lemma rVec_vecMul_E_eig (k₁ k₂ : Fin D.m) :
    D.rVec k₁ ᵥ* D.E_eig k₂ = if k₁ = k₂ then D.rVec k₁ else 0 := by
  rw [rVec, Matrix.vecMul_vecMul, D.E_eig_mul_E_eig]
  split_ifs <;> simp

lemma rVec_vecMul_Tmat (k : Fin D.m) : D.rVec k ᵥ* D.Tmat = D.lam k • D.rVec k := by
  rw [rVec, Matrix.vecMul_vecMul, D.E_eig_mul_Tmat, Matrix.vecMul_smul]

lemma rVec_mem_Rsub (k : Fin D.m) : D.rVec k ∈ D.Rsub :=
  D.vecMul_E_eig_mem_Rsub _ k

lemma rVec_mem_Zsub {k : Fin D.m} (hk : k.val ≠ 0) : D.rVec k ∈ Zsub :=
  D.vecMul_E_eig_mem_Zsub hk _

/-- Every vector in `im(E_k)` is a scalar multiple of `rVec k` (`dim V_k = 1`). -/
lemma exists_smul_rVec (k : Fin D.m) (v : Q → ℂ) :
    ∃ c : ℂ, v ᵥ* D.E_eig k = c • D.rVec k := by
  have hsingle : ∀ p : Q, ∃ c : ℂ, (Pi.single p (1 : ℂ)) ᵥ* D.E_eig k = c • D.rVec k := by
    intro p
    have hmem : D.stepA^[D.m * D.ℓ] p ∈ D.C :=
      D.iterate_mem_C_of_ge p (Nat.le_mul_of_pos_left D.ℓ D.m_pos)
    let j := (D.cycleEquiv D.c₀ D.c₀_mem).symm ⟨D.stepA^[D.m * D.ℓ] p, hmem⟩
    have hj : D.stepA^[j.val] D.c₀ = D.stepA^[D.m * D.ℓ] p := by
      exact congrArg Subtype.val ((D.cycleEquiv D.c₀ D.c₀_mem).apply_symm_apply
        ⟨D.stepA^[D.m * D.ℓ] p, hmem⟩)
    refine ⟨D.lam k ^ j.val, ?_⟩
    have hER : D.E_R * D.E_eig k = D.E_eig k := by
      have : (D.E_N + D.E_R) * D.E_eig k = D.E_eig k := by rw [E_N, sub_add_cancel, one_mul]
      rw [add_mul, D.E_N_mul_E_eig, zero_add] at this
      exact this
    calc (Pi.single p (1 : ℂ)) ᵥ* D.E_eig k
        = (Pi.single p (1 : ℂ)) ᵥ* (D.E_R * D.E_eig k) := by rw [hER]
      _ = ((Pi.single p (1 : ℂ)) ᵥ* D.Tmat ^ (D.m * D.ℓ)) ᵥ* D.E_eig k := by
          rw [E_R, Matrix.vecMul_vecMul]
      _ = (Pi.single (D.stepA^[D.m * D.ℓ] p) (1 : ℂ)) ᵥ* D.E_eig k := by
          rw [D.single_vecMul_Tmat_pow]
      _ = (Pi.single (D.stepA^[j.val] D.c₀) (1 : ℂ)) ᵥ* D.E_eig k := by rw [hj]
      _ = ((Pi.single D.c₀ (1 : ℂ)) ᵥ* D.Tmat ^ j.val) ᵥ* D.E_eig k := by
          rw [D.single_vecMul_Tmat_pow]
      _ = (Pi.single D.c₀ (1 : ℂ)) ᵥ* (D.Tmat ^ j.val * D.E_eig k) := by
          rw [Matrix.vecMul_vecMul]
      _ = (D.lam k ^ j.val) • D.rVec k := by
          rw [D.Tmat_pow_mul_E_eig, Matrix.vecMul_smul, rVec]
  choose cf hcf using hsingle
  refine ⟨∑ p : Q, v p * cf p, ?_⟩
  have hv : v = ∑ p : Q, v p • Pi.single p (1 : ℂ) := by
    ext q
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [Matrix.sum_vecMul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.smul_vecMul, hcf p, smul_smul]

/-- **1D Collapse**: because `dim V_k = 1`, `E_k * M * E_k = η • E_k` for every matrix `M`. -/
lemma E_eig_mul_mul_E_eig (k : Fin D.m) (M : Matrix Q Q ℂ) :
    ∃ η : ℂ, D.E_eig k * M * D.E_eig k = η • D.E_eig k := by
  obtain ⟨η, hη⟩ := D.exists_smul_rVec k (D.rVec k ᵥ* M)
  refine ⟨η, ?_⟩
  ext p q
  have hrow : (Pi.single p (1 : ℂ)) ᵥ* (D.E_eig k * M * D.E_eig k) =
      (Pi.single p (1 : ℂ)) ᵥ* (η • D.E_eig k) := by
    obtain ⟨c, hc⟩ := D.exists_smul_rVec k (Pi.single p (1 : ℂ))
    calc (Pi.single p (1 : ℂ)) ᵥ* (D.E_eig k * M * D.E_eig k)
        = (((Pi.single p (1 : ℂ)) ᵥ* D.E_eig k) ᵥ* M) ᵥ* D.E_eig k := by
            rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
      _ = c • ((D.rVec k ᵥ* M) ᵥ* D.E_eig k) := by
            rw [hc, Matrix.smul_vecMul, Matrix.smul_vecMul]
      _ = c • (η • D.rVec k) := by rw [hη]
      _ = η • (c • D.rVec k) := smul_comm c η (D.rVec k)
      _ = (Pi.single p (1 : ℂ)) ᵥ* (η • D.E_eig k) := by
            rw [← hc, Matrix.vecMul_smul]
  have := congrFun hrow q
  simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using this

lemma rVec_linearIndependent : LinearIndependent ℂ D.rVec := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have h := congrArg (fun v => v ᵥ* D.E_eig k) hc
  rw [Matrix.zero_vecMul, Matrix.sum_vecMul] at h
  simp only [Matrix.smul_vecMul, D.rVec_vecMul_E_eig] at h
  rw [Finset.sum_eq_single k] at h
  · simp only [ite_true] at h
    exact (smul_eq_zero.mp h).resolve_right (D.rVec_ne_zero k)
  · intro j _ hj
    simp [hj]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

lemma finrank_Rsub_inf_Zsub : Module.finrank ℂ (D.Rsub ⊓ Zsub : Submodule ℂ (Q → ℂ)) = D.m - 1 := by
  let I : Finset (Fin D.m) := Finset.univ.filter (fun k : Fin D.m => k.val ≠ 0)
  have hIcard : I.card = D.m - 1 := by
    have : I = Finset.univ.erase ⟨0, D.m_pos⟩ := by
      ext k
      simp [I, Fin.ext_iff]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  let RZ : Submodule ℂ (Q → ℂ) := D.Rsub ⊓ Zsub
  let f : I → RZ := fun k =>
    ⟨D.rVec k.1, D.rVec_mem_Rsub k.1, D.rVec_mem_Zsub (Finset.mem_filter.mp k.2).2⟩
  have hli : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have hval : ∑ i : I, c i • D.rVec i.1 = 0 := by
      have := congrArg Subtype.val hc
      simpa [f] using this
    let c' : Fin D.m → ℂ := fun j => if hj : j ∈ I then c ⟨j, hj⟩ else 0
    have hc' : ∑ j : Fin D.m, c' j • D.rVec j = 0 := by
      rw [← Finset.sum_subset (Finset.subset_univ I)]
      · rw [← Finset.sum_coe_sort I (fun j => c' j • D.rVec j)]
        refine (Finset.sum_congr rfl fun i _ => ?_).trans hval
        simp [c', i.2]
      · intro j _ hj; simp [c', hj]
    have h0 := Fintype.linearIndependent_iff.mp D.rVec_linearIndependent c' hc' k.1
    simpa [c', k.2] using h0
  have hspan : Submodule.span ℂ (Set.range f) = ⊤ := by
    rw [eq_top_iff]
    intro ⟨v, hvR, hvZ⟩ _
    have hdecomp : v = ∑ k : Fin D.m, v ᵥ* D.E_eig k := by
      rw [← Matrix.vecMul_sum, D.sum_E_eig_eq_E_R, (D.mem_Rsub_iff_vecMul_E_R v).mp hvR]
    have hsumI : v = ∑ k : I, v ᵥ* D.E_eig k.1 := by
      conv_lhs => rw [hdecomp]
      rw [Finset.sum_coe_sort I (fun k => v ᵥ* D.E_eig k)]
      symm
      refine Finset.sum_subset (Finset.subset_univ I) fun k _ hk => ?_
      have hk0 : k.val = 0 := by
        by_contra hne
        exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      have : k = ⟨0, D.m_pos⟩ := Fin.ext hk0
      rw [this, D.vecMul_E_eig_zero_eq_zero hvZ]
    choose coef hcoef using fun k : I => D.exists_smul_rVec k.1 v
    have hEq : (⟨v, hvR, hvZ⟩ : RZ) = ∑ k : I, coef k • f k := by
      ext q
      rw [Submodule.coe_sum]
      simp only [Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, f]
      conv_lhs => rw [hsumI]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact congrFun (hcoef k) q
    rw [hEq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b := Module.Basis.mk hli (le_of_eq hspan.symm)
  change Module.finrank ℂ RZ = D.m - 1
  rw [Module.finrank_eq_card_basis b, Fintype.card_coe, hIcard]

/-! ### Section 3: Control-Filtered Subspaces & Two Filtered Generation Bounds -/

/-- Fundamental difference row `u_f = [C] (P_f - I)`. -/
def uRow (f : α) : Q → ℂ := indVec D.C ᵥ* (transMat A [f] - 1)

lemma uRow_mem_Zsub (f : α) : D.uRow f ∈ Zsub := by
  rw [mem_Zsub_iff, uRow, Matrix.vecMul_sub, Matrix.vecMul_one]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_vecMul_transMat, sub_self]

lemma uRow_vecMul_transMat (f : α) (w : List α) :
    D.uRow f ᵥ* transMat A w = indVec D.C ᵥ* transMat A (f :: w) - indVec D.C ᵥ* transMat A w := by
  rw [uRow, Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.sub_vecMul, Matrix.vecMul_vecMul,
    ← transMat_cons]

lemma dotProduct_uRow_transMat (f : α) (S : Finset Q) (w : List α) :
    dotProduct (D.uRow f ᵥ* transMat A w) (indVec S) =
      (((A.preimage S (f :: w)) ∩ D.C).card : ℂ) - (((A.preimage S w) ∩ D.C).card : ℂ) := by
  rw [D.uRow_vecMul_transMat, sub_dotProduct, D.dotProduct_indVec_C_transMat,
    D.dotProduct_indVec_C_transMat]

/-- Control-filtered subspace `L_r(f) = span { u_f P_w : controls(w) ≤ r }`. -/
def Lsub (f : α) (r : ℕ) : Submodule ℂ (Q → ℂ) :=
  Submodule.span ℂ {v | ∃ w : List α, controls D.a w ≤ r ∧ v = D.uRow f ᵥ* transMat A w}

/-- Semisimple (cycle) filtered subspace `M_r(f) = L_r(f) T^ℓ`. -/
def Msub (f : α) (r : ℕ) : Submodule ℂ (Q → ℂ) :=
  (D.Lsub f r).map (vecMulEnd (D.Tmat ^ D.ℓ))

/-- Nilpotent filtered subspace `N_r(f) = L_r(f) ∩ N`. -/
def Nfilt (f : α) (r : ℕ) : Submodule ℂ (Q → ℂ) :=
  D.Lsub f r ⊓ D.Nsub

def dDim (f : α) (r : ℕ) : ℕ := Module.finrank ℂ (D.Msub f r)

def kDim (f : α) (r : ℕ) : ℕ := Module.finrank ℂ (D.Nfilt f r)

def kappa (r : ℕ) : ℕ := min D.t (D.ℓ * r)

lemma uRow_vecMul_mem_Lsub (f : α) {r : ℕ} {w : List α} (hw : controls D.a w ≤ r) :
    D.uRow f ᵥ* transMat A w ∈ D.Lsub f r :=
  Submodule.subset_span ⟨w, hw, rfl⟩

lemma uRow_mem_Lsub (f : α) (r : ℕ) : D.uRow f ∈ D.Lsub f r := by
  have h := D.uRow_vecMul_mem_Lsub f (r := r) (w := []) (by simp)
  rwa [transMat_nil, Matrix.vecMul_one] at h

lemma Lsub_mono (f : α) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : D.Lsub f r₁ ≤ D.Lsub f r₂ := by
  refine Submodule.span_mono ?_
  rintro v ⟨w, hw, rfl⟩
  exact ⟨w, hw.trans h, rfl⟩

lemma Msub_mono (f : α) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : D.Msub f r₁ ≤ D.Msub f r₂ :=
  Submodule.map_mono (D.Lsub_mono f h)

lemma Nfilt_mono (f : α) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : D.Nfilt f r₁ ≤ D.Nfilt f r₂ :=
  inf_le_inf_right D.Nsub (D.Lsub_mono f h)

lemma dDim_mono (f : α) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : D.dDim f r₁ ≤ D.dDim f r₂ :=
  Submodule.finrank_mono (D.Msub_mono f h)

lemma kDim_mono (f : α) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : D.kDim f r₁ ≤ D.kDim f r₂ :=
  Submodule.finrank_mono (D.Nfilt_mono f h)

lemma Lsub_le_Zsub (f : α) (r : ℕ) : D.Lsub f r ≤ Zsub := by
  rw [Lsub, Submodule.span_le]
  rintro v ⟨w, _, rfl⟩
  exact vecMul_transMat_mem_Zsub (D.uRow_mem_Zsub f) w

lemma vecMul_Tmat_mem_Lsub {f : α} {r : ℕ} {v : Q → ℂ} (hv : v ∈ D.Lsub f r) :
    v ᵥ* D.Tmat ∈ D.Lsub f r := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨w, hw, rfl⟩
    rw [Matrix.vecMul_vecMul, Tmat, ← transMat_append]
    exact D.uRow_vecMul_mem_Lsub f (by simp [controls_cons_self, hw])
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_vecMul]; exact (D.Lsub f r).add_mem hx hy
  | smul c x _ hx => rw [Matrix.smul_vecMul]; exact (D.Lsub f r).smul_mem c hx

lemma vecMul_Tmat_pow_mem_of_T_inv {W : Submodule ℂ (Q → ℂ)}
    (hW : ∀ v ∈ W, v ᵥ* D.Tmat ∈ W) {v : Q → ℂ} (hv : v ∈ W) (k : ℕ) :
    v ᵥ* D.Tmat ^ k ∈ W := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ, ← Matrix.vecMul_vecMul]
    exact hW _ ih

lemma vecMul_aeval_mem_of_T_inv {W : Submodule ℂ (Q → ℂ)}
    (hW : ∀ v ∈ W, v ᵥ* D.Tmat ∈ W) {v : Q → ℂ} (hv : v ∈ W) (p : ℂ[X]) :
    v ᵥ* Polynomial.aeval D.Tmat p ∈ W := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Matrix.vecMul_add]
    exact W.add_mem hp hq
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul,
      Matrix.vecMul_smul]
    exact W.smul_mem c (D.vecMul_Tmat_pow_mem_of_T_inv hW hv k)

lemma vecMul_aeval_mem_Lsub {f : α} {r : ℕ} {v : Q → ℂ} (hv : v ∈ D.Lsub f r) (p : ℂ[X]) :
    v ᵥ* Polynomial.aeval D.Tmat p ∈ D.Lsub f r :=
  D.vecMul_aeval_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_Lsub hw) hv p

lemma vecMul_E_R_mem_Lsub {f : α} {r : ℕ} {v : Q → ℂ} (hv : v ∈ D.Lsub f r) :
    v ᵥ* D.E_R ∈ D.Lsub f r := by
  rw [← D.aeval_poly_ER]
  exact D.vecMul_aeval_mem_Lsub hv D.poly_ER

lemma vecMul_E_N_mem_Lsub {f : α} {r : ℕ} {v : Q → ℂ} (hv : v ∈ D.Lsub f r) :
    v ᵥ* D.E_N ∈ D.Lsub f r := by
  rw [← D.aeval_poly_EN]
  exact D.vecMul_aeval_mem_Lsub hv D.poly_EN

lemma vecMul_E_eig_mem_Lsub {f : α} {r : ℕ} {v : Q → ℂ} (hv : v ∈ D.Lsub f r) (k : Fin D.m) :
    v ᵥ* D.E_eig k ∈ D.Lsub f r := by
  rw [← D.aeval_poly_Eeig k]
  exact D.vecMul_aeval_mem_Lsub hv (D.poly_Eeig k)

lemma vecMul_transMat_step_mem_Lsub {f : α} {r : ℕ} {v : Q → ℂ} (hv : v ∈ D.Lsub f r) (g : α) :
    v ᵥ* transMat A [g] ∈ D.Lsub f (r + 1) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨w, hw, rfl⟩
    rw [Matrix.vecMul_vecMul, ← transMat_append]
    refine D.uRow_vecMul_mem_Lsub f ?_
    rw [controls_append, controls_cons, controls_nil, add_zero]
    split_ifs <;> omega
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_vecMul]; exact (D.Lsub f (r + 1)).add_mem hx hy
  | smul c x _ hx => rw [Matrix.smul_vecMul]; exact (D.Lsub f (r + 1)).smul_mem c hx

lemma Msub_eq_Lsub_inf_Rsub (f : α) (r : ℕ) : D.Msub f r = D.Lsub f r ⊓ D.Rsub := by
  apply le_antisymm
  · rintro v ⟨x, hx, rfl⟩
    refine ⟨?_, (D.mem_Rsub_iff_range_Tmat_pow_l _).mpr ⟨x, rfl⟩⟩
    exact D.vecMul_Tmat_pow_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_Lsub hw) hx D.ℓ
  · intro v ⟨hvL, hvR⟩
    change v ∈ D.Lsub f r at hvL
    change v ∈ D.Rsub at hvR
    have hle : D.ℓ ≤ D.m * D.ℓ := Nat.le_mul_of_pos_left D.ℓ D.m_pos
    refine ⟨v ᵥ* D.Tmat ^ (D.m * D.ℓ - D.ℓ),
      D.vecMul_Tmat_pow_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_Lsub hw) hvL _, ?_⟩
    change (v ᵥ* D.Tmat ^ (D.m * D.ℓ - D.ℓ)) ᵥ* D.Tmat ^ D.ℓ = v
    rw [Matrix.vecMul_vecMul, ← pow_add, Nat.sub_add_cancel hle, ← E_R,
      (D.mem_Rsub_iff_vecMul_E_R v).mp hvR]

lemma vecMul_Tmat_mem_Msub {f : α} {r : ℕ} {v : Q → ℂ} (hv : v ∈ D.Msub f r) :
    v ᵥ* D.Tmat ∈ D.Msub f r := by
  rw [D.Msub_eq_Lsub_inf_Rsub] at hv ⊢
  exact ⟨D.vecMul_Tmat_mem_Lsub hv.1, D.vecMul_Tmat_mem_Rsub hv.2⟩

lemma vecMul_E_eig_mem_Msub {f : α} {r : ℕ} {v : Q → ℂ} (hv : v ∈ D.Msub f r) (k : Fin D.m) :
    v ᵥ* D.E_eig k ∈ D.Msub f r := by
  rw [D.Msub_eq_Lsub_inf_Rsub] at hv ⊢
  exact ⟨D.vecMul_E_eig_mem_Lsub hv.1 k, D.vecMul_E_eig_mem_Rsub v k⟩

lemma Nfilt_inf_Msub (f : α) (r : ℕ) : D.Nfilt f r ⊓ D.Msub f r = ⊥ := by
  rw [eq_bot_iff, D.Msub_eq_Lsub_inf_Rsub]
  intro v ⟨hvN, hvM⟩
  have hNR : v ∈ D.Nsub ⊓ D.Rsub := ⟨hvN.2, hvM.2⟩
  rwa [D.Nsub_inf_Rsub] at hNR

lemma Nfilt_sup_Msub (f : α) (r : ℕ) : D.Nfilt f r ⊔ D.Msub f r = D.Lsub f r := by
  apply le_antisymm
  · refine sup_le (inf_le_left) ?_
    rw [D.Msub_eq_Lsub_inf_Rsub]
    exact inf_le_left
  · intro v hv
    have h : v = v ᵥ* D.E_N + v ᵥ* D.E_R := by
      rw [← Matrix.vecMul_add, E_N, sub_add_cancel, Matrix.vecMul_one]
    rw [h]
    refine Submodule.add_mem_sup ⟨D.vecMul_E_N_mem_Lsub hv, D.vecMul_E_N_mem_Nsub v⟩ ?_
    rw [D.Msub_eq_Lsub_inf_Rsub]
    exact ⟨D.vecMul_E_R_mem_Lsub hv, D.vecMul_E_R_mem_Rsub v⟩

lemma finrank_Lsub (f : α) (r : ℕ) :
    Module.finrank ℂ (D.Lsub f r) = D.kDim f r + D.dDim f r := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (D.Nfilt f r) (D.Msub f r)
  rw [D.Nfilt_sup_Msub, D.Nfilt_inf_Msub, finrank_bot, add_zero] at h
  exact h

lemma kDim_le_t (f : α) (r : ℕ) : D.kDim f r ≤ D.t := by
  rw [kDim, ← D.finrank_Nsub]
  exact Submodule.finrank_mono inf_le_right

lemma dDim_le_m_sub_one (f : α) (r : ℕ) : D.dDim f r ≤ D.m - 1 := by
  rw [dDim, ← D.finrank_Rsub_inf_Zsub]
  refine Submodule.finrank_mono ?_
  rw [D.Msub_eq_Lsub_inf_Rsub]
  exact le_inf inf_le_right (inf_le_left.trans (D.Lsub_le_Zsub f r))

/-! #### Monic-Polynomial Span Lemma & `Δ`-Step Quotient Dependence Lemma -/

lemma vecMul_Tmat_pow_mem_of_monic_annihilator
    {W : Submodule ℂ (Q → ℂ)} (hW : ∀ v ∈ W, v ᵥ* D.Tmat ∈ W)
    {x : Q → ℂ} {p : ℂ[X]} (hp : p.Monic) (hpx : x ᵥ* Polynomial.aeval D.Tmat p ∈ W)
    (k : ℕ) :
    x ᵥ* D.Tmat ^ k ∈ W ⊔ Submodule.span ℂ {v | ∃ j < p.natDegree, v = x ᵥ* D.Tmat ^ j} := by
  let S : Submodule ℂ (Q → ℂ) :=
    W ⊔ Submodule.span ℂ {v | ∃ j < p.natDegree, v = x ᵥ* D.Tmat ^ j}
  change x ᵥ* D.Tmat ^ k ∈ S
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hlt : k < p.natDegree
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨k, hlt, rfl⟩)
    · push Not at hlt
      let d := p.natDegree
      have hp_eq : p = Polynomial.X ^ d + ∑ i ∈ Finset.range d,
          Polynomial.C (p.coeff i) * Polynomial.X ^ i := by
        have hsum := Polynomial.as_sum_range_C_mul_X_pow p
        rw [Finset.sum_range_succ, Polynomial.coeff_natDegree, hp.leadingCoeff, map_one, one_mul,
          add_comm] at hsum
        exact hsum
      have haeval : Polynomial.aeval D.Tmat p =
          D.Tmat ^ d + ∑ i ∈ Finset.range d, p.coeff i • D.Tmat ^ i := by
        conv_lhs => rw [hp_eq]
        simp only [map_add, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
          Algebra.smul_def]
      have hdecomp : x ᵥ* D.Tmat ^ k =
          (x ᵥ* Polynomial.aeval D.Tmat p) ᵥ* D.Tmat ^ (k - d) -
            ∑ i ∈ Finset.range d, p.coeff i • (x ᵥ* D.Tmat ^ (i + (k - d))) := by
        rw [haeval, Matrix.vecMul_add, Matrix.add_vecMul, Matrix.vecMul_vecMul, ← pow_add,
          Nat.add_sub_cancel' hlt, Matrix.vecMul_sum, Matrix.sum_vecMul]
        have hterm : ∀ i ∈ Finset.range d,
            (x ᵥ* (p.coeff i • D.Tmat ^ i)) ᵥ* D.Tmat ^ (k - d) =
              p.coeff i • (x ᵥ* D.Tmat ^ (i + (k - d))) := by
          intro i _
          rw [Matrix.vecMul_smul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, ← pow_add]
        rw [Finset.sum_congr rfl hterm, add_sub_cancel_right]
      rw [hdecomp]
      refine S.sub_mem (Submodule.mem_sup_left (D.vecMul_Tmat_pow_mem_of_T_inv hW hpx (k - d))) ?_
      refine S.sum_mem fun i hi => S.smul_mem _ ?_
      have hi' : i < d := Finset.mem_range.mp hi
      exact ih (i + (k - d)) (by omega)

lemma vecMul_Tmat_pow_mem_of_finrank_sub
    {W W' : Submodule ℂ (Q → ℂ)} (hWW' : W ≤ W')
    (hW : ∀ v ∈ W, v ᵥ* D.Tmat ∈ W) (hW' : ∀ v ∈ W', v ᵥ* D.Tmat ∈ W')
    {x : Q → ℂ} (hx : x ∈ W') (k : ℕ) :
    x ᵥ* D.Tmat ^ k ∈
      W ⊔ Submodule.span ℂ
        {v | ∃ j < Module.finrank ℂ W' - Module.finrank ℂ W, v = x ᵥ* D.Tmat ^ j} := by
  let Δ := Module.finrank ℂ W' - Module.finrank ℂ W
  have hle_fr : Module.finrank ℂ W ≤ Module.finrank ℂ W' := Submodule.finrank_mono hWW'
  by_cases hΔ : Δ = 0
  · have hEq : W = W' := Submodule.eq_of_le_of_finrank_eq hWW' (by omega)
    rw [← hEq] at hx
    exact Submodule.mem_sup_left (D.vecMul_Tmat_pow_mem_of_T_inv hW hx k)
  · let Win : Submodule ℂ W' := W.comap W'.subtype
    have hWin_fr : Module.finrank ℂ Win = Module.finrank ℂ W := by
      let e : Win ≃ₗ[ℂ] W :=
        { toFun := fun v => ⟨v.1.1, v.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          invFun := fun v => ⟨⟨v.1, hWW' v.2⟩, v.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact e.finrank_eq
    have hQ_fr : Module.finrank ℂ (W' ⧸ Win) = Δ := by
      have hadd := Submodule.finrank_quotient_add_finrank Win
      rw [hWin_fr] at hadd
      omega
    let u : Fin (Δ + 1) → W' ⧸ Win := fun j =>
      Win.mkQ ⟨x ᵥ* D.Tmat ^ j.val, D.vecMul_Tmat_pow_mem_of_T_inv hW' hx j.val⟩
    have hnot_li : ¬ LinearIndependent ℂ u := by
      intro hli
      have hle := hli.fintype_card_le_finrank
      rw [Fintype.card_fin, hQ_fr] at hle
      omega
    rw [Fintype.not_linearIndependent_iff] at hnot_li
    rcases hnot_li with ⟨c, hc_sum, ⟨j₀, hj₀⟩⟩
    let S : Finset (Fin (Δ + 1)) := Finset.univ.filter (fun j => c j ≠ 0)
    have hSne : S.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀⟩⟩
    let jmax : Fin (Δ + 1) := S.max' hSne
    have hjmax_ne : c jmax ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem S hSne)).2
    have hjmax_gt : ∀ j : Fin (Δ + 1), jmax.val < j.val → c j = 0 := by
      intro j hj
      by_contra hne
      have hle := Finset.le_max' S j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      exact absurd hle (not_le_of_gt hj)
    let cNat : ℕ → ℂ := fun i => if hi : i < Δ + 1 then c ⟨i, hi⟩ else 0
    let p : ℂ[X] :=
      Polynomial.X ^ jmax.val +
        ∑ i ∈ Finset.range jmax.val,
          Polynomial.C ((c jmax)⁻¹ * cNat i) * Polynomial.X ^ i
    have hlt_deg : (∑ i ∈ Finset.range jmax.val,
        Polynomial.C ((c jmax)⁻¹ * cNat i) * Polynomial.X ^ i).degree <
        (Polynomial.X ^ jmax.val : ℂ[X]).degree := by
      rw [Polynomial.degree_X_pow]
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe jmax.val)).mpr fun i hi => ?_
      have hi' : i < jmax.val := Finset.mem_range.mp hi
      exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le i _)
        (WithBot.coe_lt_coe.mpr hi')
    have hp_deg : p.natDegree = jmax.val := by
      rw [Polynomial.natDegree_eq_of_degree_eq_some]
      rw [Polynomial.degree_add_eq_left_of_degree_lt hlt_deg, Polynomial.degree_X_pow]
    have hp_monic : p.Monic :=
      (Polynomial.monic_X_pow jmax.val).add_of_left hlt_deg
    have hpx : x ᵥ* Polynomial.aeval D.Tmat p ∈ W := by
      have hsum_mem : (∑ j : Fin (Δ + 1), c j • (x ᵥ* D.Tmat ^ j.val)) ∈ W := by
        have hmk : Win.mkQ (∑ j : Fin (Δ + 1), c j •
            (⟨x ᵥ* D.Tmat ^ j.val, D.vecMul_Tmat_pow_mem_of_T_inv hW' hx j.val⟩ : W')) = 0 := by
          rw [map_sum]
          simpa only [map_smul] using hc_sum
        have hmem_Win : (∑ j : Fin (Δ + 1), c j •
            (⟨x ᵥ* D.Tmat ^ j.val, D.vecMul_Tmat_pow_mem_of_T_inv hW' hx j.val⟩ : W')) ∈ Win := by
          exact (Submodule.Quotient.mk_eq_zero Win).mp hmk
        change (∑ j : Fin (Δ + 1), c j •
            (⟨x ᵥ* D.Tmat ^ j.val, D.vecMul_Tmat_pow_mem_of_T_inv hW' hx j.val⟩ : W')).1 ∈ W at hmem_Win
        simpa [Submodule.coe_sum] using hmem_Win
      have hEq : x ᵥ* Polynomial.aeval D.Tmat p =
          (c jmax)⁻¹ • ∑ j : Fin (Δ + 1), c j • (x ᵥ* D.Tmat ^ j.val) := by
        simp only [p, map_add, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
          Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul, Matrix.vecMul_add,
          Matrix.vecMul_sum, Matrix.vecMul_smul]
        rw [Finset.smul_sum]
        have hsplit : (∑ j : Fin (Δ + 1), (c jmax)⁻¹ • (c j • (x ᵥ* D.Tmat ^ j.val))) =
            ∑ j ∈ Finset.univ.filter (fun j : Fin (Δ + 1) => j.val ≤ jmax.val),
              (c jmax)⁻¹ • (c j • (x ᵥ* D.Tmat ^ j.val)) := by
          symm
          refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
          have hgt : jmax.val < j.val := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
            exact hj
          simp [hjmax_gt j hgt]
        rw [hsplit]
        have hsum_range : (∑ j ∈ Finset.univ.filter (fun j : Fin (Δ + 1) => j.val ≤ jmax.val),
            (c jmax)⁻¹ • (c j • (x ᵥ* D.Tmat ^ j.val))) =
            ∑ i ∈ Finset.range (jmax.val + 1),
              ((c jmax)⁻¹ * cNat i) • (x ᵥ* D.Tmat ^ i) := by
          refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact Finset.mem_range.mpr (by omega)
          · intro j₁ _ j₂ _ heq; exact Fin.ext heq
          · intro i hi
            have hi' : i ≤ jmax.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hi_lt : i < Δ + 1 := lt_of_le_of_lt hi' jmax.isLt
            exact ⟨⟨i, hi_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩, rfl⟩
          · intro j _
            simp only [cNat, j.isLt, dite_true, smul_smul]
        have hjmax_nat : cNat jmax.val = c jmax := by simp only [cNat, jmax.isLt, dite_true]
        rw [hsum_range, Finset.sum_range_succ, hjmax_nat, inv_mul_cancel₀ hjmax_ne, one_smul,
          add_comm]
        simp_rw [smul_smul]
      rw [hEq]
      exact W.smul_mem _ hsum_mem
    have hmem := D.vecMul_Tmat_pow_mem_of_monic_annihilator hW hp_monic hpx k
    refine (sup_le_sup_left (Submodule.span_mono ?_) W) hmem
    rintro v ⟨j, hj, rfl⟩
    rw [hp_deg] at hj
    have hle_jmax : jmax.val ≤ Δ := Nat.le_of_lt_succ jmax.isLt
    exact ⟨j, lt_of_lt_of_le hj hle_jmax, rfl⟩

/-! #### Spectral Support of `M_r(f)` and Filtered Generation Bounds -/

/-- Spectral support `Λ_r(f) = {k ≠ 0 : r_k ∈ M_r(f)}`. -/
def specSupp (f : α) (r : ℕ) : Finset (Fin D.m) :=
  Finset.univ.filter (fun k : Fin D.m => k.val ≠ 0 ∧ D.rVec k ∈ D.Msub f r)

lemma specSupp_mono (f : α) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    D.specSupp f r₁ ⊆ D.specSupp f r₂ := by
  intro k hk
  simp only [specSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact ⟨hk.1, D.Msub_mono f h hk.2⟩

lemma mem_Msub_decomp_specSupp {f : α} {r : ℕ} {v : Q → ℂ} (hv : v ∈ D.Msub f r) :
    v = ∑ k ∈ D.specSupp f r, v ᵥ* D.E_eig k := by
  have hvR : v ∈ D.Rsub := by rw [D.Msub_eq_Lsub_inf_Rsub] at hv; exact hv.2
  have hvZ : v ∈ Zsub := D.Lsub_le_Zsub f r (by rw [D.Msub_eq_Lsub_inf_Rsub] at hv; exact hv.1)
  have hdecomp : v = ∑ k : Fin D.m, v ᵥ* D.E_eig k := by
    rw [← Matrix.vecMul_sum, D.sum_E_eig_eq_E_R, (D.mem_Rsub_iff_vecMul_E_R v).mp hvR]
  conv_lhs => rw [hdecomp]
  symm
  refine Finset.sum_subset (Finset.subset_univ (D.specSupp f r)) fun k _ hk => ?_
  by_cases hk0 : k.val = 0
  · have : k = ⟨0, D.m_pos⟩ := Fin.ext hk0
    rw [this, D.vecMul_E_eig_zero_eq_zero hvZ]
  · obtain ⟨c, hc⟩ := D.exists_smul_rVec k v
    by_cases hc0 : c = 0
    · rw [hc, hc0, zero_smul]
    · exfalso
      apply hk
      simp only [specSupp, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hk0, ?_⟩
      have hmem : v ᵥ* D.E_eig k ∈ D.Msub f r := D.vecMul_E_eig_mem_Msub hv k
      rw [hc] at hmem
      have : D.rVec k = c⁻¹ • (c • D.rVec k) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact (D.Msub f r).smul_mem _ hmem

lemma dDim_eq_card_specSupp (f : α) (r : ℕ) : D.dDim f r = (D.specSupp f r).card := by
  let S := D.specSupp f r
  let g : S → D.Msub f r := fun k => ⟨D.rVec k.1, (Finset.mem_filter.mp k.2).2.2⟩
  have hli : LinearIndependent ℂ g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have hval : ∑ i : S, c i • D.rVec i.1 = 0 := by
      have := congrArg Subtype.val hc
      simpa [g] using this
    let c' : Fin D.m → ℂ := fun j => if hj : j ∈ S then c ⟨j, hj⟩ else 0
    have hc' : ∑ j : Fin D.m, c' j • D.rVec j = 0 := by
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      · rw [← Finset.sum_coe_sort S (fun j => c' j • D.rVec j)]
        refine (Finset.sum_congr rfl fun i _ => ?_).trans hval
        simp [c', i.2]
      · intro j _ hj; simp [c', hj]
    have h0 := Fintype.linearIndependent_iff.mp D.rVec_linearIndependent c' hc' k.1
    simpa [c', k.2] using h0
  have hspan : Submodule.span ℂ (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    intro ⟨v, hv⟩ _
    have hdec := D.mem_Msub_decomp_specSupp hv
    choose coef hcoef using fun k : S => D.exists_smul_rVec k.1 v
    have hEq : (⟨v, hv⟩ : D.Msub f r) = ∑ k : S, coef k • g k := by
      ext q
      rw [Submodule.coe_sum]
      simp only [Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, g]
      conv_lhs => rw [hdec, ← Finset.sum_coe_sort S (fun k => v ᵥ* D.E_eig k)]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact congrFun (hcoef k) q
    rw [hEq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b := Module.Basis.mk hli (le_of_eq hspan.symm)
  rw [dDim, Module.finrank_eq_card_basis b, Fintype.card_coe]

/-- Minimal spectral polynomial `∏_{k ∈ S} (X - λ_k)`. -/
def specPoly (S : Finset (Fin D.m)) : ℂ[X] :=
  ∏ k ∈ S, (Polynomial.X - Polynomial.C (D.lam k))

lemma specPoly_monic (S : Finset (Fin D.m)) : (D.specPoly S).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C (D.lam k)

lemma specPoly_natDegree (S : Finset (Fin D.m)) : (D.specPoly S).natDegree = S.card := by
  rw [specPoly, Polynomial.natDegree_prod_of_monic _ _ (fun k _ => Polynomial.monic_X_sub_C _)]
  simp

lemma E_eig_mul_aeval_specPoly_eq_zero {S : Finset (Fin D.m)} {k : Fin D.m} (hk : k ∈ S) :
    D.E_eig k * Polynomial.aeval D.Tmat (D.specPoly S) = 0 := by
  rw [specPoly, ← Finset.mul_prod_erase _ _ hk, map_mul, ← mul_assoc]
  have hkill : D.E_eig k * Polynomial.aeval D.Tmat (Polynomial.X - Polynomial.C (D.lam k)) = 0 := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, mul_sub, D.E_eig_mul_Tmat,
      Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one, sub_self]
  rw [hkill, zero_mul]

lemma vecMul_aeval_specPoly_zero_eq_zero {f : α} {v : Q → ℂ} (hv : v ∈ D.Msub f 0) :
    v ᵥ* Polynomial.aeval D.Tmat (D.specPoly (D.specSupp f 0)) = 0 := by
  conv_lhs => rw [D.mem_Msub_decomp_specSupp hv]
  rw [Matrix.sum_vecMul]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Matrix.vecMul_vecMul, D.E_eig_mul_aeval_specPoly_eq_zero hk, Matrix.vecMul_zero]

lemma vecMul_aeval_specPoly_diff_mem_Msub {f : α} {r : ℕ} {v : Q → ℂ} (hv : v ∈ D.Msub f (r + 1)) :
    v ᵥ* Polynomial.aeval D.Tmat (D.specPoly (D.specSupp f (r + 1) \ D.specSupp f r)) ∈
      D.Msub f r := by
  rw [D.mem_Msub_decomp_specSupp hv, Matrix.sum_vecMul]
  refine (D.Msub f r).sum_mem fun k hk => ?_
  by_cases hkr : k ∈ D.specSupp f r
  · have hmem : v ᵥ* D.E_eig k ∈ D.Msub f r := by
      obtain ⟨c, hc⟩ := D.exists_smul_rVec k v
      rw [hc]
      exact (D.Msub f r).smul_mem c (Finset.mem_filter.mp hkr).2.2
    exact D.vecMul_aeval_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_Msub hw) hmem _
  · have hdiff : k ∈ D.specSupp f (r + 1) \ D.specSupp f r := Finset.mem_sdiff.mpr ⟨hk, hkr⟩
    rw [Matrix.vecMul_vecMul, D.E_eig_mul_aeval_specPoly_eq_zero hdiff, Matrix.vecMul_zero]
    exact (D.Msub f r).zero_mem

/-- **Filtered Generation Bound (1) — Total-dimension bound** for `L_r(f)`. -/
lemma Lsub_eq_span_total_dim (f : α) (r : ℕ) :
    D.Lsub f r = Submodule.span ℂ
      {v | ∃ w : List α, controls D.a w ≤ r ∧ w.length + 1 ≤ D.dDim f r + D.kDim f r ∧
        v = D.uRow f ᵥ* transMat A w} := by
  induction r with
  | zero =>
    apply le_antisymm
    · rw [Lsub, Submodule.span_le]
      rintro v ⟨w, hw, rfl⟩
      have hw0 : controls D.a w = 0 := Nat.eq_zero_of_le_zero hw
      rw [eq_replicate_of_controls_zero hw0, D.transMat_replicate]
      have hmem := D.vecMul_Tmat_pow_mem_of_finrank_sub (W := ⊥) (W' := D.Lsub f 0)
        bot_le (by simp) (fun _ h => D.vecMul_Tmat_mem_Lsub h) (D.uRow_mem_Lsub f 0) w.length
      rw [bot_sup_eq, finrank_bot, Nat.sub_zero, D.finrank_Lsub, add_comm] at hmem
      refine Submodule.span_mono ?_ hmem
      rintro x ⟨j, hj, rfl⟩
      refine ⟨List.replicate j D.a, by simp, by simp; omega, ?_⟩
      rw [D.transMat_replicate]
    · refine Submodule.span_mono ?_
      rintro v ⟨w, hw, _, rfl⟩
      exact ⟨w, hw, rfl⟩
  | succ r ih =>
    apply le_antisymm
    · let Tspan : Submodule ℂ (Q → ℂ) := Submodule.span ℂ
        {v | ∃ w : List α, controls D.a w ≤ r + 1 ∧
          w.length + 1 ≤ D.dDim f (r + 1) + D.kDim f (r + 1) ∧
          v = D.uRow f ᵥ* transMat A w}
      have hL_le : D.Lsub f r ≤ Tspan := by
        rw [ih]
        refine Submodule.span_mono ?_
        rintro v ⟨w, hw, hlen, rfl⟩
        have hd : D.dDim f r ≤ D.dDim f (r + 1) := D.dDim_mono f (Nat.le_succ r)
        have hk : D.kDim f r ≤ D.kDim f (r + 1) := D.kDim_mono f (Nat.le_succ r)
        exact ⟨w, by omega, by omega, rfl⟩
      rw [Lsub, Submodule.span_le]
      rintro v ⟨w, hw, rfl⟩
      by_cases hle : controls D.a w ≤ r
      · exact hL_le (D.uRow_vecMul_mem_Lsub f hle)
      · have heq : controls D.a w = r + 1 := by omega
        obtain ⟨u, g, j, hga, hcu, rfl⟩ := exists_split_last_control heq
        have hu_mem : D.uRow f ᵥ* transMat A u ∈ D.Lsub f r :=
          D.uRow_vecMul_mem_Lsub f (le_of_eq hcu)
        rw [ih] at hu_mem
        have hstep : ∀ y, y ∈ Submodule.span ℂ
            {v | ∃ w : List α, controls D.a w ≤ r ∧ w.length + 1 ≤ D.dDim f r + D.kDim f r ∧
              v = D.uRow f ᵥ* transMat A w} →
            y ᵥ* (transMat A [g] * D.Tmat ^ j) ∈ Tspan := by
          intro y hy_mem
          induction hy_mem using Submodule.span_induction with
          | mem y hy =>
            rcases hy with ⟨u', hu'c, hu'len, rfl⟩
            let x := (D.uRow f ᵥ* transMat A u') ᵥ* transMat A [g]
            have hx_mem : x ∈ D.Lsub f (r + 1) :=
              D.vecMul_transMat_step_mem_Lsub (D.uRow_vecMul_mem_Lsub f hu'c) g
            have hpow := D.vecMul_Tmat_pow_mem_of_finrank_sub (W := D.Lsub f r) (W' := D.Lsub f (r + 1))
              (D.Lsub_mono f (Nat.le_succ r))
              (fun _ h => D.vecMul_Tmat_mem_Lsub h)
              (fun _ h => D.vecMul_Tmat_mem_Lsub h) hx_mem j
            have hcomm : (D.uRow f ᵥ* transMat A u') ᵥ* (transMat A [g] * D.Tmat ^ j) =
                x ᵥ* D.Tmat ^ j := by
              simp only [x, Matrix.vecMul_vecMul, mul_assoc]
            rw [hcomm]
            refine (sup_le hL_le ?_) hpow
            rw [Submodule.span_le]
            rintro z ⟨i, hi, rfl⟩
            rw [D.finrank_Lsub, D.finrank_Lsub] at hi
            refine Submodule.subset_span ⟨u' ++ [g] ++ List.replicate i D.a, ?_, ?_, ?_⟩
            · simp only [controls_append, controls_replicate_self, add_zero, controls_cons_ne hga,
                controls_nil, zero_add]
              omega
            · simp only [List.length_append, List.length_singleton, List.length_replicate]
              have hd : D.dDim f r ≤ D.dDim f (r + 1) := D.dDim_mono f (Nat.le_succ r)
              have hk : D.kDim f r ≤ D.kDim f (r + 1) := D.kDim_mono f (Nat.le_succ r)
              omega
            · simp only [x, transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul]
          | zero => simp
          | add x y _ _ hx hy => rw [Matrix.add_vecMul]; exact Tspan.add_mem hx hy
          | smul c x _ hx => rw [Matrix.smul_vecMul]; exact Tspan.smul_mem c hx
        have hres := hstep _ hu_mem
        change D.uRow f ᵥ* transMat A (u ++ [g] ++ List.replicate j D.a) ∈ Tspan
        simpa only [transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul, mul_assoc] using hres
    · refine Submodule.span_mono ?_
      rintro v ⟨w, hw, _, rfl⟩
      exact ⟨w, hw, rfl⟩

/-- **Filtered Generation Bound (2) — Spectral–nilpotent bound** for `L_r(f)` (for `ℓ ≥ 1`). -/
lemma Lsub_eq_span_spectral_nilp (f : α) (r : ℕ) :
    D.Lsub f r = Submodule.span ℂ
      {v | ∃ w : List α, controls D.a w ≤ r ∧ w.length + 1 ≤ D.dDim f r + D.ℓ * r + D.ℓ ∧
        v = D.uRow f ᵥ* transMat A w} := by
  induction r with
  | zero =>
    apply le_antisymm
    · rw [Lsub, Submodule.span_le]
      rintro v ⟨w, hw, rfl⟩
      have hw0 : controls D.a w = 0 := Nat.eq_zero_of_le_zero hw
      rw [eq_replicate_of_controls_zero hw0, D.transMat_replicate]
      let p : ℂ[X] := Polynomial.X ^ D.ℓ * D.specPoly (D.specSupp f 0)
      have hp_monic : p.Monic := (Polynomial.monic_X_pow D.ℓ).mul (D.specPoly_monic _)
      have hp_deg : p.natDegree = D.ℓ + D.dDim f 0 := by
        rw [Polynomial.natDegree_mul' (by
          rw [Polynomial.Monic.leadingCoeff (Polynomial.monic_X_pow D.ℓ),
            Polynomial.Monic.leadingCoeff (D.specPoly_monic _), one_mul]
          exact one_ne_zero), Polynomial.natDegree_X_pow, D.specPoly_natDegree, D.dDim_eq_card_specSupp]
      have hpx : D.uRow f ᵥ* Polynomial.aeval D.Tmat p ∈ (⊥ : Submodule ℂ (Q → ℂ)) := by
        rw [Submodule.mem_bot, map_mul, Polynomial.aeval_X_pow, ← Matrix.vecMul_vecMul]
        exact D.vecMul_aeval_specPoly_zero_eq_zero ⟨D.uRow f, D.uRow_mem_Lsub f 0, rfl⟩
      have hmem := D.vecMul_Tmat_pow_mem_of_monic_annihilator (W := ⊥) (by simp) hp_monic hpx w.length
      rw [bot_sup_eq, hp_deg] at hmem
      refine Submodule.span_mono ?_ hmem
      rintro x ⟨j, hj, rfl⟩
      refine ⟨List.replicate j D.a, by simp, by simp; omega, ?_⟩
      rw [D.transMat_replicate]
    · refine Submodule.span_mono ?_
      rintro v ⟨w, hw, _, rfl⟩
      exact ⟨w, hw, rfl⟩
  | succ r ih =>
    apply le_antisymm
    · let Tspan : Submodule ℂ (Q → ℂ) := Submodule.span ℂ
        {v | ∃ w : List α, controls D.a w ≤ r + 1 ∧
          w.length + 1 ≤ D.dDim f (r + 1) + D.ℓ * (r + 1) + D.ℓ ∧
          v = D.uRow f ᵥ* transMat A w}
      have hL_le : D.Lsub f r ≤ Tspan := by
        rw [ih]
        refine Submodule.span_mono ?_
        rintro v ⟨w, hw, hlen, rfl⟩
        have hd : D.dDim f r ≤ D.dDim f (r + 1) := D.dDim_mono f (Nat.le_succ r)
        refine ⟨w, by omega, ?_, rfl⟩
        rw [Nat.mul_succ]
        omega
      rw [Lsub, Submodule.span_le]
      rintro v ⟨w, hw, rfl⟩
      by_cases hle : controls D.a w ≤ r
      · exact hL_le (D.uRow_vecMul_mem_Lsub f hle)
      · have heq : controls D.a w = r + 1 := by omega
        obtain ⟨u, g, j, hga, hcu, rfl⟩ := exists_split_last_control heq
        have hu_mem : D.uRow f ᵥ* transMat A u ∈ D.Lsub f r :=
          D.uRow_vecMul_mem_Lsub f (le_of_eq hcu)
        rw [ih] at hu_mem
        let ψ := D.specPoly (D.specSupp f (r + 1) \ D.specSupp f r)
        let q : ℂ[X] := Polynomial.X ^ D.ℓ * ψ
        have hq_monic : q.Monic := (Polynomial.monic_X_pow D.ℓ).mul (D.specPoly_monic _)
        have hq_deg : q.natDegree = D.ℓ + (D.dDim f (r + 1) - D.dDim f r) := by
          rw [Polynomial.natDegree_mul' (by
            rw [(Polynomial.monic_X_pow D.ℓ).leadingCoeff, (D.specPoly_monic _).leadingCoeff, one_mul]
            exact one_ne_zero), Polynomial.natDegree_X_pow, D.specPoly_natDegree,
            Finset.card_sdiff_of_subset (D.specSupp_mono f (Nat.le_succ r)),
            D.dDim_eq_card_specSupp, D.dDim_eq_card_specSupp]
        have hstep : ∀ y, y ∈ Submodule.span ℂ
            {v | ∃ w : List α, controls D.a w ≤ r ∧ w.length + 1 ≤ D.dDim f r + D.ℓ * r + D.ℓ ∧
              v = D.uRow f ᵥ* transMat A w} →
            y ᵥ* (transMat A [g] * D.Tmat ^ j) ∈ Tspan := by
          intro y hy_mem
          induction hy_mem using Submodule.span_induction with
          | mem y hy =>
            rcases hy with ⟨u', hu'c, hu'len, rfl⟩
            let x := (D.uRow f ᵥ* transMat A u') ᵥ* transMat A [g]
            have hx_mem : x ∈ D.Lsub f (r + 1) :=
              D.vecMul_transMat_step_mem_Lsub (D.uRow_vecMul_mem_Lsub f hu'c) g
            have hqx : x ᵥ* Polynomial.aeval D.Tmat q ∈ D.Lsub f r := by
              rw [map_mul, Polynomial.aeval_X_pow, ← Matrix.vecMul_vecMul]
              have hM := D.vecMul_aeval_specPoly_diff_mem_Msub (f := f) (r := r) ⟨x, hx_mem, rfl⟩
              rw [D.Msub_eq_Lsub_inf_Rsub] at hM
              exact hM.1
            have hpow := D.vecMul_Tmat_pow_mem_of_monic_annihilator
              (W := D.Lsub f r) (fun _ h => D.vecMul_Tmat_mem_Lsub h) hq_monic hqx j
            have hcomm : (D.uRow f ᵥ* transMat A u') ᵥ* (transMat A [g] * D.Tmat ^ j) =
                x ᵥ* D.Tmat ^ j := by
              simp only [x, Matrix.vecMul_vecMul, mul_assoc]
            rw [hcomm]
            refine (sup_le hL_le ?_) hpow
            rw [Submodule.span_le]
            rintro z ⟨i, hi, rfl⟩
            rw [hq_deg] at hi
            refine Submodule.subset_span ⟨u' ++ [g] ++ List.replicate i D.a, ?_, ?_, ?_⟩
            · simp only [controls_append, controls_replicate_self, add_zero, controls_cons_ne hga,
                controls_nil, zero_add]
              omega
            · simp only [List.length_append, List.length_singleton, List.length_replicate,
                Nat.mul_succ]
              have hd : D.dDim f r ≤ D.dDim f (r + 1) := D.dDim_mono f (Nat.le_succ r)
              omega
            · simp only [x, transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul]
          | zero => simp
          | add x y _ _ hx hy => rw [Matrix.add_vecMul]; exact Tspan.add_mem hx hy
          | smul c x _ hx => rw [Matrix.smul_vecMul]; exact Tspan.smul_mem c hx
        have hres := hstep _ hu_mem
        change D.uRow f ᵥ* transMat A (u ++ [g] ++ List.replicate j D.a) ∈ Tspan
        simpa only [transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul, mul_assoc] using hres
    · refine Submodule.span_mono ?_
      rintro v ⟨w, hw, _, rfl⟩
      exact ⟨w, hw, rfl⟩

/-- **Route 1 generation of `M_r(f)`**: prefixes `u` before `a^ℓ` have `u.length + 1 ≤ d_r + k_r`. -/
lemma Msub_eq_span_route1 (f : α) (r : ℕ) :
    D.Msub f r = Submodule.span ℂ
      {v | ∃ u : List α, controls D.a u ≤ r ∧ u.length + 1 ≤ D.dDim f r + D.kDim f r ∧
        v = D.uRow f ᵥ* transMat A (u ++ List.replicate D.ℓ D.a)} := by
  rw [Msub, D.Lsub_eq_span_total_dim f r, Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, vecMulEnd_apply]
  constructor
  · rintro ⟨x, ⟨u, huc, hulen, rfl⟩, rfl⟩
    refine ⟨u, huc, hulen, ?_⟩
    rw [transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul]
  · rintro ⟨u, huc, hulen, rfl⟩
    refine ⟨D.uRow f ᵥ* transMat A u, ⟨u, huc, hulen, rfl⟩, ?_⟩
    rw [transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul]

/-- **Route 2 generation of `M_r(f)`**: prefixes `u` before `a^ℓ` have `u.length + 1 ≤ d_r + ℓ * r`. -/
lemma Msub_eq_span_route2 (f : α) (r : ℕ) :
    D.Msub f r = Submodule.span ℂ
      {v | ∃ u : List α, controls D.a u ≤ r ∧ u.length + 1 ≤ D.dDim f r + D.ℓ * r ∧
        v = D.uRow f ᵥ* transMat A (u ++ List.replicate D.ℓ D.a)} := by
  induction r with
  | zero =>
    apply le_antisymm
    · let Tspan0 : Submodule ℂ (Q → ℂ) := Submodule.span ℂ
        {v | ∃ u : List α, controls D.a u ≤ 0 ∧ u.length + 1 ≤ D.dDim f 0 + D.ℓ * 0 ∧
          v = D.uRow f ᵥ* transMat A (u ++ List.replicate D.ℓ D.a)}
      rw [Msub, Submodule.map_le_iff_le_comap, Lsub, Submodule.span_le]
      rintro x ⟨w, hw, rfl⟩
      change (D.uRow f ᵥ* transMat A w) ᵥ* D.Tmat ^ D.ℓ ∈ Tspan0
      have hw0 : controls D.a w = 0 := Nat.eq_zero_of_le_zero hw
      rw [eq_replicate_of_controls_zero hw0, D.transMat_replicate, Matrix.vecMul_vecMul,
        ← pow_add, add_comm, pow_add, ← Matrix.vecMul_vecMul]
      let y := D.uRow f ᵥ* D.Tmat ^ D.ℓ
      have hy_mem : y ∈ D.Msub f 0 := ⟨D.uRow f, D.uRow_mem_Lsub f 0, rfl⟩
      have hpy : y ᵥ* Polynomial.aeval D.Tmat (D.specPoly (D.specSupp f 0)) ∈
          (⊥ : Submodule ℂ (Q → ℂ)) := by
        rw [Submodule.mem_bot]
        exact D.vecMul_aeval_specPoly_zero_eq_zero hy_mem
      have hmem := D.vecMul_Tmat_pow_mem_of_monic_annihilator (W := ⊥) (by simp)
        (D.specPoly_monic _) hpy w.length
      rw [bot_sup_eq, D.specPoly_natDegree, ← D.dDim_eq_card_specSupp] at hmem
      refine Submodule.span_mono ?_ hmem
      rintro z ⟨j, hj, rfl⟩
      refine ⟨List.replicate j D.a, by simp, by simp; omega, ?_⟩
      rw [transMat_append, D.transMat_replicate, D.transMat_replicate, Matrix.vecMul_vecMul,
        ← pow_add, add_comm, pow_add, ← Matrix.vecMul_vecMul]
    · rw [Submodule.span_le]
      rintro v ⟨u, huc, _, rfl⟩
      refine ⟨D.uRow f ᵥ* transMat A u, D.uRow_vecMul_mem_Lsub f huc, ?_⟩
      change (D.uRow f ᵥ* transMat A u) ᵥ* D.Tmat ^ D.ℓ = _
      rw [transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul]
  | succ r ih =>
    apply le_antisymm
    · let Tspan : Submodule ℂ (Q → ℂ) := Submodule.span ℂ
        {v | ∃ u : List α, controls D.a u ≤ r + 1 ∧
          u.length + 1 ≤ D.dDim f (r + 1) + D.ℓ * (r + 1) ∧
          v = D.uRow f ᵥ* transMat A (u ++ List.replicate D.ℓ D.a)}
      have hM_le : D.Msub f r ≤ Tspan := by
        rw [ih]
        refine Submodule.span_mono ?_
        rintro v ⟨u, huc, hulen, rfl⟩
        have hd : D.dDim f r ≤ D.dDim f (r + 1) := D.dDim_mono f (Nat.le_succ r)
        refine ⟨u, by omega, ?_, rfl⟩
        rw [Nat.mul_succ]
        omega
      rw [Msub, Submodule.map_le_iff_le_comap, Lsub, Submodule.span_le]
      rintro x ⟨w, hw, rfl⟩
      change (D.uRow f ᵥ* transMat A w) ᵥ* D.Tmat ^ D.ℓ ∈ Tspan
      by_cases hle : controls D.a w ≤ r
      · exact hM_le ⟨D.uRow f ᵥ* transMat A w, D.uRow_vecMul_mem_Lsub f hle, rfl⟩
      · have heq : controls D.a w = r + 1 := by omega
        obtain ⟨u, g, j, hga, hcu, rfl⟩ := exists_split_last_control heq
        have hu_mem : D.uRow f ᵥ* transMat A u ∈ D.Lsub f r :=
          D.uRow_vecMul_mem_Lsub f (le_of_eq hcu)
        rw [D.Lsub_eq_span_spectral_nilp f r] at hu_mem
        let ψ := D.specPoly (D.specSupp f (r + 1) \ D.specSupp f r)
        have hψ_deg : ψ.natDegree = D.dDim f (r + 1) - D.dDim f r := by
          rw [D.specPoly_natDegree, Finset.card_sdiff_of_subset (D.specSupp_mono f (Nat.le_succ r)),
            D.dDim_eq_card_specSupp, D.dDim_eq_card_specSupp]
        have hstep : ∀ y, y ∈ Submodule.span ℂ
            {v | ∃ w : List α, controls D.a w ≤ r ∧ w.length + 1 ≤ D.dDim f r + D.ℓ * r + D.ℓ ∧
              v = D.uRow f ᵥ* transMat A w} →
            y ᵥ* (transMat A [g] * D.Tmat ^ j * D.Tmat ^ D.ℓ) ∈ Tspan := by
          intro y hy_mem
          induction hy_mem using Submodule.span_induction with
          | mem y hy =>
            rcases hy with ⟨u', hu'c, hu'len, rfl⟩
            let z₀ := ((D.uRow f ᵥ* transMat A u') ᵥ* transMat A [g]) ᵥ* D.Tmat ^ D.ℓ
            have hz₀_mem : z₀ ∈ D.Msub f (r + 1) :=
              ⟨(D.uRow f ᵥ* transMat A u') ᵥ* transMat A [g],
                D.vecMul_transMat_step_mem_Lsub (D.uRow_vecMul_mem_Lsub f hu'c) g, rfl⟩
            have hψz : z₀ ᵥ* Polynomial.aeval D.Tmat ψ ∈ D.Msub f r :=
              D.vecMul_aeval_specPoly_diff_mem_Msub hz₀_mem
            have hpow := D.vecMul_Tmat_pow_mem_of_monic_annihilator
              (W := D.Msub f r) (fun _ h => D.vecMul_Tmat_mem_Msub h)
              (D.specPoly_monic _) hψz j
            have hcomm : (D.uRow f ᵥ* transMat A u') ᵥ* (transMat A [g] * D.Tmat ^ j * D.Tmat ^ D.ℓ) =
                z₀ ᵥ* D.Tmat ^ j := by
              simp only [z₀, Matrix.vecMul_vecMul, mul_assoc, ← pow_add, add_comm j D.ℓ]
            rw [hcomm]
            refine (sup_le hM_le ?_) hpow
            rw [Submodule.span_le]
            rintro z ⟨i, hi, rfl⟩
            rw [hψ_deg] at hi
            refine Submodule.subset_span ⟨u' ++ [g] ++ List.replicate i D.a, ?_, ?_, ?_⟩
            · simp only [controls_append, controls_replicate_self, add_zero, controls_cons_ne hga,
                controls_nil, zero_add]
              omega
            · simp only [List.length_append, List.length_singleton, List.length_replicate,
                Nat.mul_succ]
              have hd : D.dDim f r ≤ D.dDim f (r + 1) := D.dDim_mono f (Nat.le_succ r)
              omega
            · simp only [z₀, transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul,
                mul_assoc, ← pow_add, add_comm i D.ℓ]
          | zero => simp
          | add x y _ _ hx hy => rw [Matrix.add_vecMul]; exact Tspan.add_mem hx hy
          | smul c x _ hx => rw [Matrix.smul_vecMul]; exact Tspan.smul_mem c hx
        have hres := hstep _ hu_mem
        simpa only [transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul, mul_assoc] using hres
    · rw [Submodule.span_le]
      rintro v ⟨u, huc, _, rfl⟩
      refine ⟨D.uRow f ᵥ* transMat A u, D.uRow_vecMul_mem_Lsub f huc, ?_⟩
      change (D.uRow f ᵥ* transMat A u) ᵥ* D.Tmat ^ D.ℓ = _
      rw [transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul]

/-- **Combined generation of `M_r(f)`**: prefixes `u` before `a^ℓ` have `u.length + 2 ≤ m + κ_r`. -/
lemma Msub_eq_span_combined (f : α) (r : ℕ) :
    D.Msub f r = Submodule.span ℂ
      {v | ∃ u : List α, controls D.a u ≤ r ∧ u.length + 2 ≤ D.m + D.kappa r ∧
        v = D.uRow f ᵥ* transMat A (u ++ List.replicate D.ℓ D.a)} := by
  have hd : D.dDim f r ≤ D.m - 1 := D.dDim_le_m_sub_one f r
  have hk : D.kDim f r ≤ D.t := D.kDim_le_t f r
  have hm : 1 ≤ D.m := D.m_pos
  apply le_antisymm
  · by_cases hmin : D.t ≤ D.ℓ * r
    · rw [D.Msub_eq_span_route1 f r]
      refine Submodule.span_mono ?_
      rintro v ⟨u, huc, hlen, rfl⟩
      exact ⟨u, huc, by unfold kappa; omega, rfl⟩
    · rw [D.Msub_eq_span_route2 f r]
      refine Submodule.span_mono ?_
      rintro v ⟨u, huc, hlen, rfl⟩
      exact ⟨u, huc, by unfold kappa; omega, rfl⟩
  · rw [Submodule.span_le]
    rintro v ⟨u, huc, _, rfl⟩
    refine ⟨D.uRow f ᵥ* transMat A u, D.uRow_vecMul_mem_Lsub f huc, ?_⟩
    change (D.uRow f ᵥ* transMat A u) ᵥ* D.Tmat ^ D.ℓ = _
    rw [transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul]

/-- **Stabilization**: `M_r(f) ≤ M_{n-2}(f)` for all `r : ℕ` (when `n ≥ 2`). -/
lemma Msub_le_Msub_n_sub_two (f : α) (r : ℕ) : D.Msub f r ≤ D.Msub f (D.n - 2) := by
  rw [D.Msub_eq_span_route1 f r, Submodule.span_le]
  rintro v ⟨u, _, hlen, rfl⟩
  have hd : D.dDim f r ≤ D.m - 1 := D.dDim_le_m_sub_one f r
  have hk : D.kDim f r ≤ D.t := D.kDim_le_t f r
  have hmt : D.m + D.t = D.n := D.m_add_t
  have hctrl : controls D.a u ≤ D.n - 2 := by
    have hcl := controls_le_length D.a u
    have hm := D.m_pos
    omega
  refine ⟨D.uRow f ᵥ* transMat A u, D.uRow_vecMul_mem_Lsub f hctrl, ?_⟩
  change (D.uRow f ᵥ* transMat A u) ᵥ* D.Tmat ^ D.ℓ = _
  rw [transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul]

/-! ### Section 4: Nilpotent Dimension Growth & Finite-Polynomial Annular Coefficient Identity -/

/-- Nilpotent span `H_j = span { x_i T^k : i < j, k < ℓ }`. -/
def nilpSpan {z : ℕ} (x : Fin z → (Q → ℂ)) (j : ℕ) : Submodule ℂ (Q → ℂ) :=
  Submodule.span ℂ {v | ∃ (i : Fin z), i.val < j ∧ ∃ k < D.ℓ, v = x i ᵥ* D.Tmat ^ k}

lemma nilpSpan_zero {z : ℕ} (x : Fin z → (Q → ℂ)) : D.nilpSpan x 0 = ⊥ := by
  rw [nilpSpan, eq_bot_iff, Submodule.span_le]
  rintro v ⟨i, hi, _⟩
  omega

lemma nilpSpan_mono {z : ℕ} (x : Fin z → (Q → ℂ)) {j₁ j₂ : ℕ} (h : j₁ ≤ j₂) :
    D.nilpSpan x j₁ ≤ D.nilpSpan x j₂ := by
  refine Submodule.span_mono ?_
  rintro v ⟨i, hi, k, hk, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi h, k, hk, rfl⟩

lemma nilpSpan_le_Nsub {z : ℕ} {x : Fin z → (Q → ℂ)} (hx : ∀ i, x i ∈ D.Nsub) (j : ℕ) :
    D.nilpSpan x j ≤ D.Nsub := by
  rw [nilpSpan, Submodule.span_le]
  rintro v ⟨i, _, k, _, rfl⟩
  exact D.vecMul_Tmat_pow_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_Nsub hw) (hx i) k

lemma vecMul_Tmat_mem_nilpSpan {z : ℕ} {x : Fin z → (Q → ℂ)} (hx : ∀ i, x i ∈ D.Nsub)
    {j : ℕ} {v : Q → ℂ} (hv : v ∈ D.nilpSpan x j) : v ᵥ* D.Tmat ∈ D.nilpSpan x j := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨i, hi, k, hk, rfl⟩
    rw [Matrix.vecMul_vecMul, ← pow_succ]
    by_cases hlt : k + 1 < D.ℓ
    · exact Submodule.subset_span ⟨i, hi, k + 1, hlt, rfl⟩
    · have heq : k + 1 = D.ℓ := by omega
      rw [heq, (D.mem_Nsub_iff (x i)).mp (hx i)]
      exact (D.nilpSpan x j).zero_mem
  | zero => simp
  | add y w _ _ hy hw => rw [Matrix.add_vecMul]; exact (D.nilpSpan x j).add_mem hy hw
  | smul c y _ hy => rw [Matrix.smul_vecMul]; exact (D.nilpSpan x j).smul_mem c hy

/-- **Lemma 1.8 (Nilpotent Dimension Growth — single step)**: if `x_j T^{ν_j} ∉ H_j`, then
`dim H_{j+1} ≥ dim H_j + (ν_j + 1)`. -/
lemma nilpotent_dim_growth_step {z : ℕ} {x : Fin z → (Q → ℂ)} (hx : ∀ i, x i ∈ D.Nsub)
    {ν : Fin z → ℕ} (hν : ∀ i, ν i < D.ℓ) (j : Fin z)
    (hnot : x j ᵥ* D.Tmat ^ (ν j) ∉ D.nilpSpan x j.val) :
    Module.finrank ℂ (D.nilpSpan x j.val) + (ν j + 1) ≤
      Module.finrank ℂ (D.nilpSpan x (j.val + 1)) := by
  let H := D.nilpSpan x j.val
  let H' := D.nilpSpan x (j.val + 1)
  have hHH' : H ≤ H' := D.nilpSpan_mono x (Nat.le_succ j.val)
  let Hin : Submodule ℂ H' := H.comap H'.subtype
  have hHin_fr : Module.finrank ℂ Hin = Module.finrank ℂ H := by
    let e : Hin ≃ₗ[ℂ] H :=
      { toFun := fun v => ⟨v.1.1, v.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun v => ⟨⟨v.1, hHH' v.2⟩, v.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  have hQ_add := Submodule.finrank_quotient_add_finrank Hin
  rw [hHin_fr] at hQ_add
  have hmemH' : ∀ k : Fin (ν j + 1), x j ᵥ* D.Tmat ^ k.val ∈ H' := fun k =>
    Submodule.subset_span ⟨j, Nat.lt_succ_self j.val, k.val, lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt) (hν j), rfl⟩
  let u : Fin (ν j + 1) → H' ⧸ Hin := fun k => Hin.mkQ ⟨x j ᵥ* D.Tmat ^ k.val, hmemH' k⟩
  have hli : LinearIndependent ℂ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum_mem : (∑ k : Fin (ν j + 1), c k • (x j ᵥ* D.Tmat ^ k.val)) ∈ H := by
      have hmk : Hin.mkQ (∑ k : Fin (ν j + 1), c k •
          (⟨x j ᵥ* D.Tmat ^ k.val, hmemH' k⟩ : H')) = 0 := by
        rw [map_sum]
        simpa only [map_smul] using hc
      have hmem_Hin := (Submodule.Quotient.mk_eq_zero Hin).mp hmk
      change (∑ k : Fin (ν j + 1), c k • (⟨x j ᵥ* D.Tmat ^ k.val, hmemH' k⟩ : H')).1 ∈ H at hmem_Hin
      simpa [Submodule.coe_sum] using hmem_Hin
    by_contra hne_all
    push Not at hne_all
    rcases hne_all with ⟨k_wit, hk_wit⟩
    let S : Finset (Fin (ν j + 1)) := Finset.univ.filter (fun k => c k ≠ 0)
    have hSne : S.Nonempty := ⟨k_wit, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_wit⟩⟩
    let k₀ : Fin (ν j + 1) := S.min' hSne
    have hk₀_ne : c k₀ ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
    have hk₀_lt : ∀ k : Fin (ν j + 1), k.val < k₀.val → c k = 0 := by
      intro k hk
      by_contra hck
      have hle := Finset.min'_le S k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hck⟩)
      exact absurd hle (not_le_of_gt hk)
    let Tset : Finset ℕ := (Finset.range D.ℓ).filter (fun d => x j ᵥ* D.Tmat ^ d ∉ H)
    have hTne : Tset.Nonempty :=
      ⟨ν j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hν j), hnot⟩⟩
    let d : ℕ := Tset.max' hTne
    have hd_mem := Finset.mem_filter.mp (Finset.max'_mem Tset hTne)
    have hd_notH : x j ᵥ* D.Tmat ^ d ∉ H := hd_mem.2
    have hν_le_d : ν j ≤ d := Finset.le_max' Tset (ν j)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hν j), hnot⟩)
    have hk₀_le_d : k₀.val ≤ d := le_trans (Nat.le_of_lt_succ k₀.isLt) hν_le_d
    have hgt_d_mem : ∀ m : ℕ, d < m → x j ᵥ* D.Tmat ^ m ∈ H := by
      intro m hm
      by_cases hml : m < D.ℓ
      · by_contra hnotm
        have hle := Finset.le_max' Tset m
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hml, hnotm⟩)
        omega
      · push Not at hml
        obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hml
        rw [pow_add, ← Matrix.vecMul_vecMul, (D.mem_Nsub_iff (x j)).mp (hx j), Matrix.zero_vecMul]
        exact H.zero_mem
    have hshift_mem : (∑ k : Fin (ν j + 1), c k • (x j ᵥ* D.Tmat ^ k.val)) ᵥ* D.Tmat ^ (d - k₀.val) ∈ H :=
      D.vecMul_Tmat_pow_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_nilpSpan hx hw) hsum_mem (d - k₀.val)
    rw [Matrix.sum_vecMul] at hshift_mem
    have hterm_eq : ∀ k : Fin (ν j + 1),
        (c k • (x j ᵥ* D.Tmat ^ k.val)) ᵥ* D.Tmat ^ (d - k₀.val) =
          c k • (x j ᵥ* D.Tmat ^ (k.val + (d - k₀.val))) := by
      intro k
      rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, ← pow_add]
    simp_rw [hterm_eq] at hshift_mem
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀), Nat.add_sub_cancel' hk₀_le_d] at hshift_mem
    have herase_mem : (∑ k ∈ Finset.univ.erase k₀,
        c k • (x j ᵥ* D.Tmat ^ (k.val + (d - k₀.val)))) ∈ H := by
      refine H.sum_mem fun k hk => ?_
      have hne : k.val ≠ k₀.val := fun heq => (Finset.mem_erase.mp hk).1 (Fin.ext heq)
      by_cases hlt : k.val < k₀.val
      · rw [hk₀_lt k hlt, zero_smul]; exact H.zero_mem
      · exact H.smul_mem (c k) (hgt_d_mem (k.val + (d - k₀.val)) (by omega))
    have hlead_mem : c k₀ • (x j ᵥ* D.Tmat ^ d) ∈ H := by
      have hsub := H.sub_mem hshift_mem herase_mem
      rwa [add_sub_cancel_right] at hsub
    have hfinal : x j ᵥ* D.Tmat ^ d ∈ H := by
      have hsm := H.smul_mem (c k₀)⁻¹ hlead_mem
      rwa [smul_smul, inv_mul_cancel₀ hk₀_ne, one_smul] at hsm
    exact hd_notH hfinal
  have hle_fr := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hle_fr
  change Module.finrank ℂ (↥H' ⧸ Hin) + Module.finrank ℂ (D.nilpSpan x j.val) =
    Module.finrank ℂ (D.nilpSpan x (j.val + 1)) at hQ_add
  omega

/-- **Lemma 1.8 (Nilpotent Dimension Growth — full sum)**: if no `x_j T^{ν_j}` lies in `H_j`,
then `z + ∑ ν_j ≤ t`. -/
lemma nilpotent_dim_growth {z : ℕ} {x : Fin z → (Q → ℂ)} (hx : ∀ i, x i ∈ D.Nsub)
    {ν : Fin z → ℕ} (hν : ∀ i, ν i < D.ℓ)
    (hnot : ∀ j : Fin z, x j ᵥ* D.Tmat ^ (ν j) ∉ D.nilpSpan x j.val) :
    z + ∑ j : Fin z, ν j ≤ D.t := by
  have hbound : ∀ k : ℕ, k ≤ z →
      ∑ j ∈ Finset.univ.filter (fun j : Fin z => j.val < k), (ν j + 1) ≤
        Module.finrank ℂ (D.nilpSpan x k) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk_lt : k < z := by omega
      let jk : Fin z := ⟨k, hk_lt⟩
      have hfilt : Finset.univ.filter (fun j : Fin z => j.val < k + 1) =
          insert jk (Finset.univ.filter (fun j : Fin z => j.val < k)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, jk]
        omega
      have hnotmem : jk ∉ Finset.univ.filter (fun j : Fin z => j.val < k) := by
        simp [jk]
      rw [hfilt, Finset.sum_insert hnotmem]
      have hstep := D.nilpotent_dim_growth_step hx hν jk (hnot jk)
      have hjk_val : jk.val = k := rfl
      rw [hjk_val] at hstep
      have hih := ih (by omega)
      omega
  have htop := hbound z le_rfl
  have hall : Finset.univ.filter (fun j : Fin z => j.val < z) = Finset.univ := by
    ext j; simp
  rw [hall, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] at htop
  have hle_t : Module.finrank ℂ (D.nilpSpan x z) ≤ D.t := by
    rw [← D.finrank_Nsub]
    exact Submodule.finrank_mono (D.nilpSpan_le_Nsub hx z)
  omega

end Data

/-! #### Complete Homogeneous Symmetric Sums & Finite-Polynomial Annular Coefficient Identity -/

/-- Finset of `I`-indexed nonnegative integer tuples summing to `d`. -/
def tupleFinset {ι : Type*} [DecidableEq ι] (I : Finset ι) (d : ℕ) : Finset (I → ℕ) :=
  (Fintype.piFinset (fun _ : I => Finset.range (d + 1))).filter (fun f => ∑ i : I, f i = d)

lemma mem_tupleFinset {ι : Type*} [DecidableEq ι] {I : Finset ι} {d : ℕ} {f : I → ℕ} :
    f ∈ tupleFinset I d ↔ ∑ i : I, f i = d := by
  simp only [tupleFinset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    and_iff_right_iff_imp]
  intro hsum i
  have hle : f i ≤ ∑ j : I, f j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- Complete homogeneous symmetric polynomial `h_d(φ(I)) = ∑_{∑ f = d} ∏_{i ∈ I} (φ i)^(f i)`. -/
def tupleSum {ι : Type*} [DecidableEq ι] (I : Finset ι) (φ : ι → ℂ) (d : ℕ) : ℂ :=
  ∑ f ∈ tupleFinset I d, ∏ i : I, (φ i.1) ^ (f i)

lemma tupleSum_empty {ι : Type*} [DecidableEq ι] (φ : ι → ℂ) (d : ℕ) :
    tupleSum (∅ : Finset ι) φ d = if d = 0 then 1 else 0 := by
  unfold tupleSum
  by_cases hd : d = 0
  · subst hd
    have hcard : tupleFinset (∅ : Finset ι) 0 = {fun i => (Finset.notMem_empty _ i.2).elim} := by
      ext f
      simp only [mem_tupleFinset, Finset.univ_eq_empty, Finset.sum_empty, Finset.mem_singleton,
        true_iff]
      funext i
      exact (Finset.notMem_empty _ i.2).elim
    rw [hcard, Finset.sum_singleton]
    simp
  · have hempty : tupleFinset (∅ : Finset ι) d = ∅ := by
      ext f
      simp only [mem_tupleFinset, Finset.univ_eq_empty, Finset.sum_empty, Finset.notMem_empty,
        iff_false]
      exact Ne.symm hd
    simp [hd, hempty]

lemma tupleSum_zero {ι : Type*} [DecidableEq ι] (I : Finset ι) (φ : ι → ℂ) :
    tupleSum I φ 0 = 1 := by
  unfold tupleSum
  have hsing : tupleFinset I 0 = {fun _ => 0} := by
    ext f
    simp only [mem_tupleFinset, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left,
      Finset.mem_singleton]
    exact ⟨fun h => funext h, fun h i => by rw [h]⟩
  rw [hsing, Finset.sum_singleton]
  simp

lemma tupleSum_insert {ι : Type*} [DecidableEq ι] {x : ι} {I : Finset ι} (hx : x ∉ I)
    (φ : ι → ℂ) (d : ℕ) :
    tupleSum (insert x I) φ d =
      ∑ j ∈ Finset.range (d + 1), (φ x) ^ j * tupleSum I φ (d - j) := by
  unfold tupleSum
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sigma (Finset.range (d + 1)) (fun j => tupleFinset I (d - j))
    (fun p : Σ _ : ℕ, I → ℕ => (φ x) ^ p.1 * ∏ i : I, (φ i.1) ^ (p.2 i))]
  let J : Finset ι := insert x I
  let xmem : J := ⟨x, Finset.mem_insert_self x I⟩
  let emb : I → J := fun i => ⟨i.1, Finset.mem_insert_of_mem i.2⟩
  have hJ_univ : (Finset.univ : Finset J) = insert xmem ((Finset.univ : Finset I).image emb) := by
    ext ⟨y, hy⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_image, true_and, true_iff,
      Subtype.ext_iff, xmem, emb]
    rcases Finset.mem_insert.mp hy with rfl | hyI
    · left; rfl
    · right; exact ⟨⟨y, hyI⟩, rfl⟩
  have hxmem_not : xmem ∉ (Finset.univ : Finset I).image emb := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists, Subtype.ext_iff,
      xmem, emb]
    intro i hi
    exact hx (hi ▸ i.2)
  have hemb_inj : Function.Injective emb :=
    fun i₁ i₂ h => Subtype.ext (congrArg (fun y : J => y.1) h)
  have hsplit_sum : ∀ f : J → ℕ, ∑ i : J, f i = f xmem + ∑ i : I, f (emb i) := by
    intro f
    conv_lhs =>
      rw [hJ_univ, Finset.sum_insert hxmem_not, Finset.sum_image (fun _ _ _ _ h => hemb_inj h)]
  have hsplit_prod : ∀ f : J → ℕ,
      ∏ i : J, (φ i.1) ^ (f i) = (φ x) ^ (f xmem) * ∏ i : I, (φ i.1) ^ (f (emb i)) := by
    intro f
    conv_lhs =>
      rw [hJ_univ, Finset.prod_insert hxmem_not, Finset.prod_image (fun _ _ _ _ h => hemb_inj h)]
  change ∑ f ∈ tupleFinset J d, ∏ i : J, (φ i.1) ^ (f i) = _
  refine Finset.sum_bij
    (fun f _ => (⟨f xmem, fun i : I => f (emb i)⟩ : Σ _ : ℕ, I → ℕ))
    ?_ ?_ ?_ ?_
  · intro f hf
    rw [mem_tupleFinset, hsplit_sum] at hf
    simp only [Finset.mem_sigma, Finset.mem_range, mem_tupleFinset]
    exact ⟨by omega, by omega⟩
  · intro f₁ _ f₂ _ heq
    have h1 : f₁ xmem = f₂ xmem := congrArg Sigma.fst heq
    have h2 : (fun i : I => f₁ (emb i)) = (fun i : I => f₂ (emb i)) :=
      eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    funext ⟨y, hy⟩
    by_cases hyx : y = x
    · subst hyx; exact h1
    · have hyI : y ∈ I := (Finset.mem_insert.mp hy).resolve_left hyx
      exact congrFun h2 ⟨y, hyI⟩
  · rintro ⟨j, g⟩ hmem
    simp only [Finset.mem_sigma, Finset.mem_range, mem_tupleFinset] at hmem
    let f : J → ℕ := fun i =>
      if h : i.1 = x then j else g ⟨i.1, (Finset.mem_insert.mp i.2).resolve_left h⟩
    have hfx : f xmem = j := by simp [f, xmem]
    have hfg : (fun i : I => f (emb i)) = g := by
      funext i
      have hne : i.1 ≠ x := fun h => hx (h ▸ i.2)
      simp [f, emb, hne]
    refine ⟨f, ?_, ?_⟩
    · have hfg' : ∀ i : I, f (emb i) = g i := fun i => congrFun hfg i
      rw [mem_tupleFinset, hsplit_sum, hfx]
      simp_rw [hfg']
      have h1 : j ≤ d := Nat.lt_succ_iff.mp hmem.1
      have h2 : ∑ i : I, g i = d - j := hmem.2
      rw [h2]
      omega
    · exact Sigma.ext hfx (by rw [hfg])
  · intro f _
    exact hsplit_prod f

lemma tupleSum_congr_equiv {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {I : Finset ι} {J : Finset κ} (e : I ≃ J) {φ : ι → ℂ} {ψ : κ → ℂ}
    (hφψ : ∀ i : I, ψ (e i).1 = φ i.1) (d : ℕ) :
    tupleSum I φ d = tupleSum J ψ d := by
  unfold tupleSum
  refine Finset.sum_bij (fun f _ => fun j : J => f (e.symm j)) ?_ ?_ ?_ ?_
  · intro f hf
    rw [mem_tupleFinset] at hf ⊢
    rw [Equiv.sum_comp e.symm f]
    exact hf
  · intro f₁ _ f₂ _ heq
    funext i
    have := congrFun heq (e i)
    simpa using this
  · intro g hg
    refine ⟨fun i : I => g (e i), ?_, ?_⟩
    · rw [mem_tupleFinset] at hg ⊢
      rw [Equiv.sum_comp e g]
      exact hg
    · funext j; simp
  · intro f _
    symm
    refine Fintype.prod_equiv e.symm (fun j : J => (ψ j.1) ^ (f (e.symm j)))
      (fun i : I => (φ i.1) ^ (f i)) fun j => ?_
    have h := hφψ (e.symm j)
    rw [e.apply_symm_apply] at h
    rw [h]

/-- Truncated generating polynomial `H_D(I) = ∑_{d ≤ D} h_d(φ(I)) X^d`. -/
def Hpoly {ι : Type*} [DecidableEq ι] (I : Finset ι) (φ : ι → ℂ) (deg : ℕ) : ℂ[X] :=
  ∑ d ∈ Finset.range (deg + 1), Polynomial.C (tupleSum I φ d) * Polynomial.X ^ d

lemma coeff_Hpoly {ι : Type*} [DecidableEq ι] (I : Finset ι) (φ : ι → ℂ) {deg d : ℕ}
    (hd : d ≤ deg) : (Hpoly I φ deg).coeff d = tupleSum I φ d := by
  rw [Hpoly, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single d]
  · simp
  · intro k _ hk; simp [Ne.symm hk]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

lemma coeff_mul_eq_of_coeff_eq_le {P Q₁ Q₂ : ℂ[X]} {deg : ℕ}
    (hQ : ∀ j ≤ deg, Q₁.coeff j = Q₂.coeff j) {d : ℕ} (hd : d ≤ deg) :
    (P * Q₁).coeff d = (P * Q₂).coeff d := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx2 : x.2 ≤ deg := by
    have := Finset.mem_antidiagonal.mp hx
    omega
  rw [hQ x.2 hx2]

lemma coeff_one_sub_mul_Hpoly_insert {ι : Type*} [DecidableEq ι] {x : ι} {I : Finset ι}
    (hx : x ∉ I) (φ : ι → ℂ) {deg d : ℕ} (hd : d ≤ deg) :
    ((1 - Polynomial.C (φ x) * Polynomial.X) * Hpoly (insert x I) φ deg).coeff d =
      (Hpoly I φ deg).coeff d := by
  rw [sub_mul, one_mul, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul]
  cases d with
  | zero =>
    rw [coeff_Hpoly _ _ hd, coeff_Hpoly _ _ hd, tupleSum_zero, tupleSum_zero,
      Polynomial.coeff_X_mul_zero, mul_zero, sub_zero]
  | succ k =>
    rw [Polynomial.coeff_X_mul, coeff_Hpoly _ _ hd, coeff_Hpoly _ _ (by omega),
      coeff_Hpoly _ _ hd, tupleSum_insert hx, tupleSum_insert hx,
      Finset.sum_range_succ' (fun j => (φ x) ^ j * tupleSum I φ (k + 1 - j)) (k + 1)]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.succ_sub_succ_eq_sub, Finset.mul_sum]
    have hEq : (∑ j ∈ Finset.range (k + 1), (φ x) ^ (j + 1) * tupleSum I φ (k - j)) =
        ∑ j ∈ Finset.range (k + 1), φ x * ((φ x) ^ j * tupleSum I φ (k - j)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ', mul_assoc]
    rw [hEq, add_sub_cancel_left]

lemma coeff_prod_one_sub_mul_Hpoly {ι : Type*} [DecidableEq ι] (I : Finset ι) (φ : ι → ℂ)
    (deg : ℕ) :
    ∀ d ≤ deg,
      ((∏ x ∈ I, (1 - Polynomial.C (φ x) * Polynomial.X)) * Hpoly I φ deg).coeff d =
        (1 : ℂ[X]).coeff d := by
  induction I using Finset.induction_on with
  | empty =>
    intro d hd
    rw [Finset.prod_empty, one_mul, coeff_Hpoly _ _ hd, tupleSum_empty, Polynomial.coeff_one]
  | @insert x I hx ih =>
    intro d hd
    rw [Finset.prod_insert hx, mul_comm (1 - Polynomial.C (φ x) * Polynomial.X), mul_assoc]
    have hstep := coeff_mul_eq_of_coeff_eq_le
      (P := ∏ y ∈ I, (1 - Polynomial.C (φ y) * Polynomial.X))
      (fun j hj => coeff_one_sub_mul_Hpoly_insert hx φ hj) hd
    rw [hstep]
    exact ih d hd

namespace Data

variable {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q] {A : DFA Q α} (D : Data A)

lemma prod_X_sub_lam :
    ∏ k : Fin D.m, (Polynomial.X - Polynomial.C (D.lam k)) = Polynomial.X ^ D.m - 1 := by
  let P : ℂ[X] := ∏ k : Fin D.m, (Polynomial.X - Polynomial.C (D.lam k))
  let Qp : ℂ[X] := Polynomial.X ^ D.m - 1
  have hP_monic : P.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C (D.lam k)
  have hQ_monic : Qp.Monic := by
    simpa [Qp] using Polynomial.monic_X_pow_sub_C (1 : ℂ) (Nat.ne_of_gt D.m_pos)
  have hP_deg : P.natDegree = D.m := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun k _ => Polynomial.monic_X_sub_C _)]
    simp
  have hQ_deg : Qp.natDegree = D.m := by
    simpa [Qp] using Polynomial.natDegree_X_pow_sub_C (n := D.m) (a := (1 : ℂ))
  have hdvd : P ∣ Qp := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro k₁ _ k₂ _ hne
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun h => hne (D.lam_injective h))))
    · intro k _
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      simp [Qp, D.lam_pow_m]
  rcases hdvd with ⟨R, hR⟩
  have hR_ne : R ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hR; exact hQ_monic.ne_zero hR
  have hR_deg : R.natDegree = 0 := by
    have hdeg := congrArg Polynomial.natDegree hR
    rw [Polynomial.natDegree_mul hP_monic.ne_zero hR_ne, hP_deg, hQ_deg] at hdeg
    omega
  have hR_lc : R.leadingCoeff = 1 := by
    have hlc := congrArg Polynomial.leadingCoeff hR
    rw [Polynomial.leadingCoeff_mul, hP_monic.leadingCoeff, hQ_monic.leadingCoeff, one_mul] at hlc
    exact hlc.symm
  have hR0 : R.coeff 0 = 1 := by
    rw [← hR_deg]
    exact hR_lc
  have hR_one : R = 1 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hR_deg, hR0, map_one]
  show P = Qp
  rw [hR, hR_one, mul_one]

lemma prod_one_sub_lam_X :
    ∏ k : Fin D.m, (1 - Polynomial.C (D.lam k) * Polynomial.X) = 1 - Polynomial.X ^ D.m := by
  have hfac : ∀ k : Fin D.m,
      1 - Polynomial.C (D.lam k) * Polynomial.X =
        Polynomial.C (-D.lam k) * (Polynomial.X - Polynomial.C (D.lam k)⁻¹) := by
    intro k
    simp only [mul_sub, ← map_mul, neg_mul, mul_inv_cancel₀ (D.lam_ne_zero k), map_neg, map_one]
    ring
  simp_rw [hfac, Finset.prod_mul_distrib]
  let σ : Fin D.m ≃ Fin D.m :=
    { toFun := fun k => ⟨(D.m - k.val) % D.m, Nat.mod_lt _ D.m_pos⟩
      invFun := fun k => ⟨(D.m - k.val) % D.m, Nat.mod_lt _ D.m_pos⟩
      left_inv := fun k => by
        ext
        dsimp only
        by_cases hk0 : k.val = 0
        · simp [hk0]
        · have hk := k.isLt
          have h1 : D.m - k.val < D.m := by omega
          rw [Nat.mod_eq_of_lt h1]
          have h2 : D.m - (D.m - k.val) = k.val := by omega
          rw [h2, Nat.mod_eq_of_lt hk]
      right_inv := fun k => by
        ext
        dsimp only
        by_cases hk0 : k.val = 0
        · simp [hk0]
        · have hk := k.isLt
          have h1 : D.m - k.val < D.m := by omega
          rw [Nat.mod_eq_of_lt h1]
          have h2 : D.m - (D.m - k.val) = k.val := by omega
          rw [h2, Nat.mod_eq_of_lt hk] }
  have hlam_σ : ∀ k : Fin D.m, D.lam (σ k) = (D.lam k)⁻¹ := by
    intro k
    by_cases hk0 : k.val = 0
    · have hk : k = ⟨0, D.m_pos⟩ := Fin.ext hk0
      subst hk
      have hσ0 : σ ⟨0, D.m_pos⟩ = ⟨0, D.m_pos⟩ := by ext; simp [σ]
      rw [hσ0, D.lam_zero, inv_one]
    · have hk := k.isLt
      have hσ : (σ k).val = D.m - k.val := Nat.mod_eq_of_lt (by omega)
      symm
      apply inv_eq_of_mul_eq_one_left
      rw [lam, lam, hσ, ← pow_add, Nat.sub_add_cancel (le_of_lt hk),
        D.isPrimitiveRoot_zeta.pow_eq_one]
  have hprod_eq : (∏ k : Fin D.m, (Polynomial.X - Polynomial.C (D.lam k)⁻¹)) =
      Polynomial.X ^ D.m - 1 := by
    rw [← D.prod_X_sub_lam]
    symm
    refine Fintype.prod_equiv σ _ _ fun k => ?_
    rw [hlam_σ, inv_inv]
  rw [hprod_eq, ← map_prod]
  let c : ℂ := ∏ k : Fin D.m, (-D.lam k)
  change Polynomial.C c * (Polynomial.X ^ D.m - 1) = 1 - Polynomial.X ^ D.m
  have hc : c = -1 := by
    have hev : Polynomial.eval 0 (∏ k : Fin D.m, (1 - Polynomial.C (D.lam k) * Polynomial.X)) =
        Polynomial.eval 0 (Polynomial.C c * (Polynomial.X ^ D.m - 1)) := by
      congr 1
      simp_rw [hfac, Finset.prod_mul_distrib, hprod_eq, ← map_prod]
      rfl
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, mul_zero, sub_zero, Finset.prod_const_one,
      Polynomial.eval_pow, zero_pow (Nat.ne_of_gt D.m_pos), zero_sub, mul_neg, mul_one] at hev
    exact neg_eq_iff_eq_neg.mp hev.symm
  rw [hc, map_neg, map_one]
  ring

/-- **Lemma 1.9 (Annular Coefficient Identity)**: for `Y ⊆ Fin m` and `d > m - |Y|`,
`h_d(Y) - h_{d - m}(Y) = 0`. -/
lemma annular_tupleSum_sub_eq_zero (Y : Finset (Fin D.m)) {d : ℕ} (hd : D.m - Y.card < d) :
    tupleSum Y D.lam d - (if D.m ≤ d then tupleSum Y D.lam (d - D.m) else 0) = 0 := by
  let Φ : ℂ[X] := ∏ k ∈ Finset.univ \ Y, (1 - Polynomial.C (D.lam k) * Polynomial.X)
  have hΦ_mul : Φ * ∏ k ∈ Y, (1 - Polynomial.C (D.lam k) * Polynomial.X) = 1 - Polynomial.X ^ D.m := by
    rw [← Finset.prod_union disjoint_sdiff_self_left, Finset.sdiff_union_of_subset (Finset.subset_univ Y),
      D.prod_one_sub_lam_X]
  have hcoeff_eq : ((1 - Polynomial.X ^ D.m) * Hpoly Y D.lam d).coeff d = Φ.coeff d := by
    rw [← hΦ_mul, mul_assoc]
    have hstep := coeff_mul_eq_of_coeff_eq_le (P := Φ)
      (coeff_prod_one_sub_mul_Hpoly Y D.lam d) le_rfl
    rw [hstep, mul_one]
  have hlhs : ((1 - Polynomial.X ^ D.m) * Hpoly Y D.lam d).coeff d =
      tupleSum Y D.lam d - (if D.m ≤ d then tupleSum Y D.lam (d - D.m) else 0) := by
    rw [sub_mul, one_mul, Polynomial.coeff_sub, coeff_Hpoly _ _ le_rfl, Polynomial.coeff_X_pow_mul']
    split_ifs with hmd
    · rw [coeff_Hpoly _ _ (by omega)]
    · rfl
  have hrhs : Φ.coeff d = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hdeg_le : Φ.natDegree ≤ (Finset.univ \ Y).card := by
      refine le_trans (Polynomial.natDegree_prod_le (Finset.univ \ Y)
        (fun k => 1 - Polynomial.C (D.lam k) * Polynomial.X)) ?_
      have h1 : ∀ k ∈ Finset.univ \ Y, (1 - Polynomial.C (D.lam k) * Polynomial.X).natDegree ≤ 1 := by
        intro k _
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        simp only [Polynomial.natDegree_one, max_le_iff, zero_le, true_and]
        exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
      calc ∑ k ∈ Finset.univ \ Y, (1 - Polynomial.C (D.lam k) * Polynomial.X).natDegree
          ≤ ∑ _k ∈ Finset.univ \ Y, 1 :=
            Finset.sum_le_sum (f := fun k => (1 - Polynomial.C (D.lam k) * Polynomial.X).natDegree) h1
        _ = (Finset.univ \ Y).card := by simp
    have hcard : (Finset.univ \ Y).card = D.m - Y.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ Y), Finset.card_univ, Fintype.card_fin]
    omega
  rw [← hlhs, hcoeff_eq, hrhs]

/-- Annular endpoints `D_r^- = max(0, κ_r - r)` and `D_r^+ = m + κ_r - r - 1`. -/
def Dminus (r : ℕ) : ℕ := D.kappa r - r

def Dplus (r : ℕ) : ℕ := D.m + D.kappa r - r - 1

/-- Annular scalar sum cancellation (exact form used in Proposition 1.7). -/
lemma annular_sum_Icc_eq_zero {r z s : ℕ} {Y₀ : Finset (Fin D.m)}
    (h0 : ⟨0, D.m_pos⟩ ∉ Y₀) (hm2 : 2 ≤ D.m) (hr : r ≤ D.n - 1)
    (hz : z ≤ r) (hcard : Y₀.card = r + 1 - z) (hcharge : z + s ≤ D.kappa r)
    (hs : s ≤ D.Dplus r) :
    ∑ k ∈ Finset.Icc (D.Dminus r - s) (D.Dplus r - s), tupleSum Y₀ D.lam k = 0 := by
  let Y := insert ⟨0, D.m_pos⟩ Y₀
  have hY_card : Y.card = r + 2 - z := by
    rw [Finset.card_insert_of_notMem h0, hcard]
    omega
  have hY_le_m : Y.card ≤ D.m := by
    simpa [Fintype.card_fin] using Finset.card_le_univ Y
  have hsum_Y : ∀ d : ℕ, tupleSum Y D.lam d = ∑ k ∈ Finset.range (d + 1), tupleSum Y₀ D.lam k := by
    intro d
    rw [tupleSum_insert h0, D.lam_zero]
    simp only [one_pow, one_mul]
    rw [← Finset.sum_range_reflect (fun k => tupleSum Y₀ D.lam k) (d + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
  have hm_le_n := D.m_le_n
  have hm_add_k : r + 1 ≤ D.m + D.kappa r := by
    unfold kappa
    by_cases hlt : D.t ≤ D.ℓ * r
    · rw [min_eq_left hlt, D.m_add_t]; omega
    · rw [min_eq_right (le_of_not_ge hlt)]
      have hℓpos : 1 ≤ D.ℓ := by
        by_contra h0'; push Not at h0'
        have hℓ0 : D.ℓ = 0 := by omega
        have ht0 : D.t = 0 := D.t_eq_zero_of_l_eq_zero hℓ0
        rw [hℓ0, ht0, zero_mul] at hlt
        exact hlt le_rfl
      have : r ≤ D.ℓ * r := Nat.le_mul_of_pos_left r hℓpos
      omega
  have hDle : D.Dminus r ≤ D.Dplus r := by unfold Dminus Dplus; omega
  let L := D.Dminus r - s
  let d := D.Dplus r - s
  have hLd : L ≤ d := Nat.sub_le_sub_right hDle s
  have hd_gt : D.m - Y.card < d := by
    dsimp only [d, Dplus]
    omega
  have hIcc_eq : (∑ k ∈ Finset.Icc L d, tupleSum Y₀ D.lam k) =
      tupleSum Y D.lam d - (if L = 0 then 0 else tupleSum Y D.lam (L - 1)) := by
    by_cases hL0 : L = 0
    · simp only [hL0, ite_true, sub_zero, hsum_Y]
      congr 1
      ext k
      simp only [Finset.mem_Icc, zero_le, true_and, Finset.mem_range]
      omega
    · simp only [hL0, ite_false, hsum_Y]
      have hsub : Finset.range L ⊆ Finset.range (d + 1) := Finset.range_mono (by omega)
      have hdiff : Finset.range (d + 1) \ Finset.range L = Finset.Icc L d := by
        ext k
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc]
        omega
      have hL1 : L - 1 + 1 = L := by omega
      rw [hL1, ← Finset.sum_sdiff hsub, hdiff, add_sub_cancel_right]
  rw [hIcc_eq]
  have hmain := D.annular_tupleSum_sub_eq_zero Y hd_gt
  have hbranch : (if L = 0 then (0 : ℂ) else tupleSum Y D.lam (L - 1)) =
      if D.m ≤ d then tupleSum Y D.lam (d - D.m) else 0 := by
    by_cases hkr : D.kappa r ≤ r
    · have hL0 : L = 0 := by dsimp only [L, Dminus]; omega
      have hdm : ¬ D.m ≤ d := by dsimp only [d, Dplus]; omega
      simp [hL0, hdm]
    · push Not at hkr
      have hDrel : D.Dplus r = D.Dminus r + D.m - 1 := by unfold Dminus Dplus; omega
      by_cases hsD : D.Dminus r ≤ s
      · have hL0 : L = 0 := by dsimp only [L]; omega
        have hdm : ¬ D.m ≤ d := by dsimp only [d]; omega
        simp [hL0, hdm]
      · push Not at hsD
        have hLpos : L ≠ 0 := by dsimp only [L]; omega
        have hmd : D.m ≤ d := by dsimp only [d]; omega
        have hidx : L - 1 = d - D.m := by dsimp only [L, d]; omega
        simp [hLpos, hmd, hidx]
  rw [hbranch]
  exact hmain

/-! ### Section 5: Annular Spectral Descent (Proposition 1.7) -/

/-- Ordered matrix product `F a * F (a + 1) * ... * F (a + k - 1)`. -/
def prodRange (F : ℕ → Matrix Q Q ℂ) (a : ℕ) : ℕ → Matrix Q Q ℂ
  | 0 => 1
  | k + 1 => prodRange F a k * F (a + k)

lemma prodRange_zero (F : ℕ → Matrix Q Q ℂ) (a : ℕ) : prodRange F a 0 = 1 := rfl

lemma prodRange_succ (F : ℕ → Matrix Q Q ℂ) (a k : ℕ) :
    prodRange F a (k + 1) = prodRange F a k * F (a + k) := rfl

lemma prodRange_add (F : ℕ → Matrix Q Q ℂ) (a k₁ k₂ : ℕ) :
    prodRange F a (k₁ + k₂) = prodRange F a k₁ * prodRange F (a + k₁) k₂ := by
  induction k₂ with
  | zero => simp [prodRange]
  | succ k₂ ih =>
    rw [← add_assoc, prodRange_succ, prodRange_succ, ih, mul_assoc, add_assoc]

lemma prodRange_one (F : ℕ → Matrix Q Q ℂ) (a : ℕ) : prodRange F a 1 = F a := by
  simp [prodRange]

lemma prodRange_succ_left (F : ℕ → Matrix Q Q ℂ) (a k : ℕ) :
    prodRange F a (k + 1) = F a * prodRange F (a + 1) k := by
  rw [Nat.add_comm k 1, prodRange_add, prodRange_one]

lemma prodRange_eq_of_shift {F₁ F₂ : ℕ → Matrix Q Q ℂ} {a₁ a₂ k : ℕ}
    (h : ∀ i, i < k → F₁ (a₁ + i) = F₂ (a₂ + i)) :
    prodRange F₁ a₁ k = prodRange F₂ a₂ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [prodRange_succ, prodRange_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h k (Nat.lt_succ_self k)]

lemma prodRange_split_at (F : ℕ → Matrix Q Q ℂ) {p r : ℕ} (hpr : p < r) :
    prodRange F 0 r = prodRange F 0 p * F p * prodRange F (p + 1) (r - p - 1) := by
  have hr_eq : r = p + (1 + (r - p - 1)) := by omega
  conv_lhs => rw [hr_eq]
  rw [prodRange_add, prodRange_add, prodRange_one, zero_add, mul_assoc]

lemma prodRange_split_two (F : ℕ → Matrix Q Q ℂ) {p q r : ℕ} (hpq : p < q) (hqr : q < r) :
    prodRange F 0 r =
      prodRange F 0 p * F p * prodRange F (p + 1) (q - p - 1) * F q *
        prodRange F (q + 1) (r - q - 1) := by
  have hr_eq : r = p + (1 + (q - p - 1) + (1 + (r - q - 1))) := by omega
  conv_lhs => rw [hr_eq]
  rw [prodRange_add, prodRange_add, prodRange_add, prodRange_add, prodRange_one, prodRange_one,
    zero_add]
  have h2 : p + (1 + (q - p - 1)) = q := by omega
  rw [h2]
  simp only [mul_assoc]

lemma prodRange_smul (c : ℕ → ℂ) (F : ℕ → Matrix Q Q ℂ) (a k : ℕ) :
    prodRange (fun i => c i • F i) a k =
      (∏ i ∈ Finset.range k, c (a + i)) • prodRange F a k := by
  induction k with
  | zero => simp [prodRange]
  | succ k ih =>
    rw [prodRange_succ, prodRange_succ, Finset.prod_range_succ, ih, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]

/-- Spectral projector indexed by `Option (Fin m)`: `none ↦ E_N`, `some k ↦ E_eig k`. -/
def Eopt : Option (Fin D.m) → Matrix Q Q ℂ
  | none => D.E_N
  | some k => D.E_eig k

lemma sum_Eopt : ∑ o : Option (Fin D.m), D.Eopt o = 1 := by
  rw [Fintype.sum_option, Eopt]
  exact D.E_N_add_sum_E_eig

lemma vecMul_Eopt_mem_Zsub {v : Q → ℂ} (hv : v ∈ Zsub) (o : Option (Fin D.m)) :
    v ᵥ* D.Eopt o ∈ Zsub := by
  cases o with
  | none => exact D.vecMul_E_N_mem_Zsub hv
  | some k => exact D.vecMul_E_eig_mem_Zsub_of_mem hv k

lemma vecMul_Eopt_mem_Lsub {f : α} {r : ℕ} {v : Q → ℂ} (hv : v ∈ D.Lsub f r)
    (o : Option (Fin D.m)) : v ᵥ* D.Eopt o ∈ D.Lsub f r := by
  cases o with
  | none => exact D.vecMul_E_N_mem_Lsub hv
  | some k => exact D.vecMul_E_eig_mem_Lsub hv k

/-- One-step block factor `E_{α_i} T^{h_i} G_i` for `i < r`. -/
def projStep {r : ℕ} (g : Fin r → α) (αs : Fin (r + 1) → Option (Fin D.m)) (h : Fin (r + 1) → ℕ)
    (i : ℕ) : Matrix Q Q ℂ :=
  if hi : i < r then
    D.Eopt (αs ⟨i, by omega⟩) * D.Tmat ^ (h ⟨i, by omega⟩) * transMat A [g ⟨i, hi⟩]
  else 1

/-- Full projected block matrix `E_{α_0} T^{h_0} G_0 ... G_{r-1} E_{α_r} T^{h_r}`. -/
def projBlockMat {r : ℕ} (g : Fin r → α) (αs : Fin (r + 1) → Option (Fin D.m))
    (h : Fin (r + 1) → ℕ) : Matrix Q Q ℂ :=
  prodRange (D.projStep g αs h) 0 r * D.Eopt (αs (Fin.last r)) * D.Tmat ^ (h (Fin.last r))

/-- Unprojected block matrix `T^{h_0} G_0 ... G_{r-1} T^{h_r}`. -/
def blockStep {r : ℕ} (g : Fin r → α) (h : Fin (r + 1) → ℕ) (i : ℕ) : Matrix Q Q ℂ :=
  if hi : i < r then D.Tmat ^ (h ⟨i, by omega⟩) * transMat A [g ⟨i, hi⟩] else 1

lemma transMat_blockWord {r : ℕ} (g : Fin r → α) (h : Fin (r + 1) → ℕ) :
    transMat A (blockWord D.a g h) =
      prodRange (D.blockStep g h) 0 r * D.Tmat ^ (h (Fin.last r)) := by
  induction r with
  | zero =>
    simp [blockWord, prodRange, D.transMat_replicate, Fin.last_zero]
  | succ r ih =>
    simp only [blockWord, transMat_append, D.transMat_replicate]
    rw [ih (fun i => g i.succ) (fun i => h i.succ), prodRange_succ_left]
    have h0 : D.blockStep g h 0 = D.Tmat ^ (h 0) * transMat A [g 0] := by
      simp [blockStep]
    have htail : prodRange (D.blockStep g h) 1 r =
        prodRange (D.blockStep (fun i => g i.succ) (fun i => h i.succ)) 0 r := by
      refine prodRange_eq_of_shift fun i hi => ?_
      have hi' : 1 + i < r + 1 := by omega
      simp only [blockStep, hi, hi', dite_true, zero_add]
      have hidx1 : (⟨1 + i, by omega⟩ : Fin (r + 2)) = (⟨i, by omega⟩ : Fin (r + 1)).succ := by
        ext; simp [add_comm]
      have hidx2 : (⟨1 + i, hi'⟩ : Fin (r + 1)) = (⟨i, hi⟩ : Fin r).succ := by
        ext; simp [add_comm]
      rw [hidx1, hidx2]
    rw [h0, htail, Fin.succ_last]
    simp only [mul_assoc]

lemma sum_projBlockMat_eq {r : ℕ} (g : Fin r → α) (h : Fin (r + 1) → ℕ) :
    ∑ αs : Fin (r + 1) → Option (Fin D.m), D.projBlockMat g αs h =
      transMat A (blockWord D.a g h) := by
  rw [D.transMat_blockWord]
  induction r with
  | zero =>
    have hsum : (∑ αs : Fin 1 → Option (Fin D.m), D.projBlockMat g αs h) =
        (∑ o : Option (Fin D.m), D.Eopt o) * D.Tmat ^ (h 0) := by
      rw [Finset.sum_mul]
      let e : (Fin 1 → Option (Fin D.m)) ≃ Option (Fin D.m) := Equiv.funUnique (Fin 1) _
      refine Fintype.sum_equiv e _ _ fun αs => ?_
      simp [projBlockMat, prodRange, e, Fin.last_zero]
    rw [hsum, D.sum_Eopt, one_mul, prodRange_zero, one_mul, Fin.last_zero]
  | succ r ih =>
    let e : (Fin (r + 2) → Option (Fin D.m)) ≃
        Option (Fin D.m) × (Fin (r + 1) → Option (Fin D.m)) :=
      { toFun := fun αs => (αs 0, fun i => αs i.succ)
        invFun := fun p => Fin.cases p.1 p.2
        left_inv := fun αs => by funext i; refine Fin.cases rfl (fun _ => rfl) i
        right_inv := fun ⟨o, αs'⟩ => by ext <;> simp }
    have hrewrite : (∑ αs : Fin (r + 2) → Option (Fin D.m), D.projBlockMat g αs h) =
        ∑ p : Option (Fin D.m) × (Fin (r + 1) → Option (Fin D.m)),
          (D.Eopt p.1 * D.Tmat ^ (h 0) * transMat A [g 0]) *
            D.projBlockMat (fun i => g i.succ) p.2 (fun i => h i.succ) := by
      refine Fintype.sum_equiv e _ _ fun αs => ?_
      dsimp only [e]
      simp only [projBlockMat, prodRange_succ_left]
      have h0 : D.projStep g αs h 0 = D.Eopt (αs 0) * D.Tmat ^ (h 0) * transMat A [g 0] := by
        simp [projStep]
      have htail : prodRange (D.projStep g αs h) 1 r =
          prodRange (D.projStep (fun i => g i.succ) (fun i => αs i.succ) (fun i => h i.succ)) 0 r := by
        refine prodRange_eq_of_shift fun i hi => ?_
        have hi' : 1 + i < r + 1 := by omega
        simp only [projStep, hi, hi', dite_true, zero_add]
        have hidx1 : (⟨1 + i, by omega⟩ : Fin (r + 2)) = (⟨i, by omega⟩ : Fin (r + 1)).succ := by
          ext; simp [add_comm]
        have hidx2 : (⟨1 + i, hi'⟩ : Fin (r + 1)) = (⟨i, hi⟩ : Fin r).succ := by
          ext; simp [add_comm]
        rw [hidx1, hidx2]
      rw [h0, htail, Fin.succ_last]
      simp only [mul_assoc]
      rfl
    rw [hrewrite, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, D.sum_Eopt, one_mul,
      prodRange_succ_left]
    have h0 : D.blockStep g h 0 = D.Tmat ^ (h 0) * transMat A [g 0] := by simp [blockStep]
    have htail : prodRange (D.blockStep g h) 1 r =
        prodRange (D.blockStep (fun i => g i.succ) (fun i => h i.succ)) 0 r := by
      refine prodRange_eq_of_shift fun i hi => ?_
      have hi' : 1 + i < r + 1 := by omega
      simp only [blockStep, hi, hi', dite_true, zero_add]
      have hidx1 : (⟨1 + i, by omega⟩ : Fin (r + 2)) = (⟨i, by omega⟩ : Fin (r + 1)).succ := by
        ext; simp [add_comm]
      have hidx2 : (⟨1 + i, hi'⟩ : Fin (r + 1)) = (⟨i, hi⟩ : Fin r).succ := by
        ext; simp [add_comm]
      rw [hidx1, hidx2]
    rw [h0, htail, Fin.succ_last]
    simp only [mul_assoc]

/-- Prefix of `projStep` preserves `Zsub`. -/
lemma vecMul_prodRange_projStep_mem_Zsub {r : ℕ} (g : Fin r → α)
    (αs : Fin (r + 1) → Option (Fin D.m)) (h : Fin (r + 1) → ℕ)
    {v : Q → ℂ} (hv : v ∈ Zsub) (a k : ℕ) :
    v ᵥ* prodRange (D.projStep g αs h) a k ∈ Zsub := by
  induction k with
  | zero => simpa [prodRange] using hv
  | succ k ih =>
    rw [prodRange_succ, ← Matrix.vecMul_vecMul]
    dsimp only [projStep]
    split_ifs with hlt
    · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
      exact vecMul_transMat_mem_Zsub (D.vecMul_Tmat_pow_mem_Zsub (D.vecMul_Eopt_mem_Zsub ih _) _) _
    · simpa using ih

/-- **Lemma 1.10 (Spectral Control Deletion)**: `k` steps of `projStep` shift `L_s(f)` to `L_{s+k}(f)`. -/
lemma vecMul_prodRange_projStep_mem_Lsub {r : ℕ} (f : α) (g : Fin r → α)
    (αs : Fin (r + 1) → Option (Fin D.m)) (h : Fin (r + 1) → ℕ)
    {s : ℕ} {v : Q → ℂ} (hv : v ∈ D.Lsub f s) (a k : ℕ) :
    v ᵥ* prodRange (D.projStep g αs h) a k ∈ D.Lsub f (s + k) := by
  induction k with
  | zero => simpa [prodRange] using hv
  | succ k ih =>
    rw [prodRange_succ, ← Matrix.vecMul_vecMul, ← add_assoc]
    dsimp only [projStep]
    split_ifs with hlt
    · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
      refine D.vecMul_transMat_step_mem_Lsub ?_ _
      exact D.vecMul_Tmat_pow_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_Lsub hw)
        (D.vecMul_Eopt_mem_Lsub ih _) _
    · rw [Matrix.vecMul_one]
      exact D.Lsub_mono f (Nat.le_succ _) ih

/-- Annular exponent set `A_r = { h : D_r^- ≤ ∑ h_i ≤ D_r^+ }`. -/
def Aset (r : ℕ) : Finset (Fin (r + 1) → ℕ) :=
  (Fintype.piFinset (fun _ : Fin (r + 1) => Finset.range (D.Dplus r + 1))).filter
    (fun h => D.Dminus r ≤ ∑ i : Fin (r + 1), h i ∧ ∑ i : Fin (r + 1), h i ≤ D.Dplus r)

lemma mem_Aset {r : ℕ} {h : Fin (r + 1) → ℕ} :
    h ∈ D.Aset r ↔ D.Dminus r ≤ ∑ i : Fin (r + 1), h i ∧ ∑ i : Fin (r + 1), h i ≤ D.Dplus r := by
  simp only [Aset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    and_iff_right_iff_imp]
  intro ⟨_, hle⟩ i
  have hi : h i ≤ ∑ j : Fin (r + 1), h j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- The annular sum `Ω_r(f, g) = ∑_{h ∈ A_r} u_f P_{blockWord g h} T^ℓ`. -/
def Omega {r : ℕ} (f : α) (g : Fin r → α) : Q → ℂ :=
  ∑ h ∈ D.Aset r, D.uRow f ᵥ* (transMat A (blockWord D.a g h) * D.Tmat ^ D.ℓ)

/-- **Proposition 1.7 (Annular Spectral Descent — Zhu Proposition 5.1)**:
for `m ≥ 2` and `1 ≤ r ≤ n - 1`, `Ω_r(f, g) ∈ M_{r-1}(f)`. -/
theorem omega_mem_Msub_pred {r : ℕ} (hm2 : 2 ≤ D.m) (hr1 : 1 ≤ r) (hrn : r ≤ D.n - 1)
    (f : α) (g : Fin r → α) : D.Omega f g ∈ D.Msub f (r - 1) := by
  unfold Omega
  simp_rw [← D.sum_projBlockMat_eq, Finset.sum_mul, Matrix.vecMul_sum]
  rw [Finset.sum_comm]
  refine (D.Msub f (r - 1)).sum_mem fun αs _ => ?_
  -- Goal: ∑ h ∈ Aset r, u_f ᵥ* (projBlockMat g αs h * T^ℓ) ∈ M_{r-1}(f)
  -- Case 0: some αs i = some 0 (killed because u_f ∈ Z and Z ᵥ* E_0 = 0)
  by_cases hhas0 : ∃ i : Fin (r + 1), αs i = some ⟨0, D.m_pos⟩
  · rcases hhas0 with ⟨p, hp⟩
    have hzero : ∀ h : Fin (r + 1) → ℕ,
        D.uRow f ᵥ* (D.projBlockMat g αs h * D.Tmat ^ D.ℓ) = 0 := by
      intro h
      unfold projBlockMat
      by_cases hpr : p.val < r
      · rw [prodRange_split_at (D.projStep g αs h) hpr]
        have hstep_p : D.projStep g αs h p.val =
            D.E_eig ⟨0, D.m_pos⟩ * D.Tmat ^ (h p) * transMat A [g ⟨p.val, hpr⟩] := by
          simp only [projStep, hpr, dite_true]
          have hpeq : (⟨p.val, by omega⟩ : Fin (r + 1)) = p := Fin.ext rfl
          rw [hpeq, hp, Eopt]
        rw [hstep_p]
        have hZ : D.uRow f ᵥ* prodRange (D.projStep g αs h) 0 p.val ∈ Zsub :=
          D.vecMul_prodRange_projStep_mem_Zsub g αs h (D.uRow_mem_Zsub f) 0 p.val
        have hkill : (D.uRow f ᵥ* prodRange (D.projStep g αs h) 0 p.val) ᵥ*
            D.E_eig ⟨0, D.m_pos⟩ = 0 := D.vecMul_E_eig_zero_eq_zero hZ
        simp only [← Matrix.vecMul_vecMul, hkill, Matrix.zero_vecMul]
      · have hplast : p = Fin.last r := by
          ext; have := p.isLt; simp only [Fin.val_last]; omega
        rw [← hplast, hp, Eopt]
        have hZ : D.uRow f ᵥ* prodRange (D.projStep g αs h) 0 r ∈ Zsub :=
          D.vecMul_prodRange_projStep_mem_Zsub g αs h (D.uRow_mem_Zsub f) 0 r
        have hkill : (D.uRow f ᵥ* prodRange (D.projStep g αs h) 0 r) ᵥ*
            D.E_eig ⟨0, D.m_pos⟩ = 0 := D.vecMul_E_eig_zero_eq_zero hZ
        simp only [← Matrix.vecMul_vecMul, hkill, Matrix.zero_vecMul]
    rw [Finset.sum_eq_zero (fun h _ => hzero h)]
    exact (D.Msub f (r - 1)).zero_mem
  -- Case 1: αs (Fin.last r) = none (killed by final T^ℓ since E_N * T^ℓ = 0)
  by_cases hlastN : αs (Fin.last r) = none
  · have hzero : ∀ h : Fin (r + 1) → ℕ,
        D.uRow f ᵥ* (D.projBlockMat g αs h * D.Tmat ^ D.ℓ) = 0 := by
      intro h
      unfold projBlockMat
      rw [hlastN, Eopt, mul_assoc, mul_assoc, ← pow_add, add_comm, pow_add, ← mul_assoc D.E_N,
        D.E_N_mul_Tmat_pow_l, zero_mul, mul_zero, Matrix.vecMul_zero]
    rw [Finset.sum_eq_zero (fun h _ => hzero h)]
    exact (D.Msub f (r - 1)).zero_mem
  -- Case 2: repeated nonzero eigenvalue (1D collapse puts every term in M_{r-1}(f))
  by_cases hrep : ∃ p q : Fin (r + 1), p.val < q.val ∧ ∃ k : Fin D.m, αs p = some k ∧ αs q = some k
  · rcases hrep with ⟨p, q, hpq, k, hpk, hqk⟩
    refine (D.Msub f (r - 1)).sum_mem fun h _ => ?_
    refine ⟨D.uRow f ᵥ* D.projBlockMat g αs h, ?_, by
      change (D.uRow f ᵥ* D.projBlockMat g αs h) ᵥ* D.Tmat ^ D.ℓ = _
      rw [Matrix.vecMul_vecMul]⟩
    -- Show u_f ᵥ* projBlockMat g αs h ∈ L_{r-1}(f) via 1D collapse E_k * M * E_k = η • E_k
    unfold projBlockMat
    have hpr : p.val < r := by have := q.isLt; omega
    by_cases hqr : q.val < r
    · have hsplit := prodRange_split_two (D.projStep g αs h) hpq hqr
      have hsp : D.projStep g αs h p.val =
          D.E_eig k * (D.Tmat ^ (h p) * transMat A [g ⟨p.val, hpr⟩]) := by
        simp only [projStep, hpr, dite_true, mul_assoc]
        have hpeq : (⟨p.val, by omega⟩ : Fin (r + 1)) = p := Fin.ext rfl
        rw [hpeq, hpk, Eopt]
      have hsq : D.projStep g αs h q.val =
          D.E_eig k * (D.Tmat ^ (h q) * transMat A [g ⟨q.val, hqr⟩]) := by
        simp only [projStep, hqr, dite_true, mul_assoc]
        have hqeq : (⟨q.val, by omega⟩ : Fin (r + 1)) = q := Fin.ext rfl
        rw [hqeq, hqk, Eopt]
      let Mmid := (D.Tmat ^ (h p) * transMat A [g ⟨p.val, hpr⟩]) *
        prodRange (D.projStep g αs h) (p.val + 1) (q.val - p.val - 1)
      obtain ⟨η, hη⟩ := D.E_eig_mul_mul_E_eig k Mmid
      rw [hsplit, hsp, hsq]
      have hreassoc :
          prodRange (D.projStep g αs h) 0 p.val *
            (D.E_eig k * (D.Tmat ^ (h p) * transMat A [g ⟨p.val, hpr⟩])) *
            prodRange (D.projStep g αs h) (p.val + 1) (q.val - p.val - 1) *
            (D.E_eig k * (D.Tmat ^ (h q) * transMat A [g ⟨q.val, hqr⟩])) *
            prodRange (D.projStep g αs h) (q.val + 1) (r - q.val - 1) *
            D.Eopt (αs (Fin.last r)) * D.Tmat ^ (h (Fin.last r)) =
          η • (prodRange (D.projStep g αs h) 0 p.val * D.E_eig k *
            D.Tmat ^ (h q) * transMat A [g ⟨q.val, hqr⟩] *
            prodRange (D.projStep g αs h) (q.val + 1) (r - q.val - 1) *
            D.Eopt (αs (Fin.last r)) * D.Tmat ^ (h (Fin.last r))) := by
        have hm1 : prodRange (D.projStep g αs h) 0 p.val *
            (D.E_eig k * (D.Tmat ^ (h p) * transMat A [g ⟨p.val, hpr⟩])) *
            prodRange (D.projStep g αs h) (p.val + 1) (q.val - p.val - 1) *
            (D.E_eig k * (D.Tmat ^ (h q) * transMat A [g ⟨q.val, hqr⟩])) =
          prodRange (D.projStep g αs h) 0 p.val * (D.E_eig k * Mmid * D.E_eig k) *
            (D.Tmat ^ (h q) * transMat A [g ⟨q.val, hqr⟩]) := by
          dsimp only [Mmid]; simp only [mul_assoc]
        rw [hm1, hη]
        simp only [Matrix.smul_mul, Matrix.mul_smul, mul_assoc]
      rw [hreassoc, Matrix.vecMul_smul]
      refine (D.Lsub f (r - 1)).smul_mem η ?_
      have h1 : D.uRow f ᵥ* prodRange (D.projStep g αs h) 0 p.val ∈ D.Lsub f p.val := by
        simpa using D.vecMul_prodRange_projStep_mem_Lsub f g αs h (D.uRow_mem_Lsub f 0) 0 p.val
      have h2 := D.vecMul_E_eig_mem_Lsub h1 k
      have h3 := D.vecMul_Tmat_pow_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_Lsub hw) h2 (h q)
      have h4 := D.vecMul_transMat_step_mem_Lsub h3 (g ⟨q.val, hqr⟩)
      have h5 := D.vecMul_prodRange_projStep_mem_Lsub f g αs h h4 (q.val + 1) (r - q.val - 1)
      have h6 := D.vecMul_Eopt_mem_Lsub h5 (αs (Fin.last r))
      have h7 := D.vecMul_Tmat_pow_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_Lsub hw) h6 (h (Fin.last r))
      have hle : p.val + 1 + (r - q.val - 1) ≤ r - 1 := by omega
      simpa only [Matrix.vecMul_vecMul] using D.Lsub_mono f hle h7
    · -- q = Fin.last r
      have hqlast : q = Fin.last r := by
        ext; have := q.isLt; simp only [Fin.val_last]; omega
      have hsplit := prodRange_split_at (D.projStep g αs h) hpr
      have hsp : D.projStep g αs h p.val =
          D.E_eig k * (D.Tmat ^ (h p) * transMat A [g ⟨p.val, hpr⟩]) := by
        simp only [projStep, hpr, dite_true, mul_assoc]
        have hpeq : (⟨p.val, by omega⟩ : Fin (r + 1)) = p := Fin.ext rfl
        rw [hpeq, hpk, Eopt]
      let Mmid := (D.Tmat ^ (h p) * transMat A [g ⟨p.val, hpr⟩]) *
        prodRange (D.projStep g αs h) (p.val + 1) (r - p.val - 1)
      obtain ⟨η, hη⟩ := D.E_eig_mul_mul_E_eig k Mmid
      rw [hsplit, hsp, ← hqlast, hqk, Eopt]
      have hreassoc :
          prodRange (D.projStep g αs h) 0 p.val *
            (D.E_eig k * (D.Tmat ^ (h p) * transMat A [g ⟨p.val, hpr⟩])) *
            prodRange (D.projStep g αs h) (p.val + 1) (r - p.val - 1) *
            D.E_eig k * D.Tmat ^ (h q) =
          η • (prodRange (D.projStep g αs h) 0 p.val * D.E_eig k * D.Tmat ^ (h q)) := by
        have hm1 : prodRange (D.projStep g αs h) 0 p.val *
            (D.E_eig k * (D.Tmat ^ (h p) * transMat A [g ⟨p.val, hpr⟩])) *
            prodRange (D.projStep g αs h) (p.val + 1) (r - p.val - 1) * D.E_eig k =
          prodRange (D.projStep g αs h) 0 p.val * (D.E_eig k * Mmid * D.E_eig k) := by
          dsimp only [Mmid]; simp only [mul_assoc]
        rw [hm1, hη]
        simp only [Matrix.smul_mul, Matrix.mul_smul, mul_assoc]
      rw [hreassoc, Matrix.vecMul_smul]
      refine (D.Lsub f (r - 1)).smul_mem η ?_
      have h1 : D.uRow f ᵥ* prodRange (D.projStep g αs h) 0 p.val ∈ D.Lsub f p.val := by
        simpa using D.vecMul_prodRange_projStep_mem_Lsub f g αs h (D.uRow_mem_Lsub f 0) 0 p.val
      have h2 := D.vecMul_E_eig_mem_Lsub h1 k
      have h3 := D.vecMul_Tmat_pow_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_Lsub hw) h2 (h q)
      have hle : p.val ≤ r - 1 := by omega
      simpa only [Matrix.vecMul_vecMul] using D.Lsub_mono f hle h3
  -- Case 3: all nonzero eigenvalues are pairwise distinct and ≠ 0, and αs (Fin.last r) ≠ none
  let IN : Finset (Fin (r + 1)) := Finset.univ.filter (fun i => αs i = none)
  let I0 : Finset (Fin (r + 1)) := Finset.univ.filter (fun i => αs i ≠ none)
  let z : ℕ := IN.card
  let pos : Fin z ↪o Fin (r + 1) := IN.orderEmbOfFin rfl
  have hpos_mem : ∀ j : Fin z, pos j ∈ IN := fun j => IN.orderEmbOfFin_mem rfl j
  have hpos_none : ∀ j : Fin z, αs (pos j) = none := fun j => (Finset.mem_filter.mp (hpos_mem j)).2
  have hpos_lt_r : ∀ j : Fin z, (pos j).val < r := by
    intro j
    have hne : pos j ≠ Fin.last r := fun heq => hlastN (heq ▸ hpos_none j)
    have hlt := (pos j).isLt
    have : (pos j).val ≠ r := fun h => hne (Fin.ext h)
    omega
  have hz_le_r : z ≤ r := by
    have hsub : IN ⊆ Finset.univ.erase (Fin.last r) := by
      intro i hi
      refine Finset.mem_erase.mpr ⟨fun heq => hlastN (heq ▸ (Finset.mem_filter.mp hi).2),
        Finset.mem_univ _⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcard
    simpa [z] using hcard
  -- Extract eigenvalue index for i ∈ I0 (default 0 outside I0)
  let kOf : Fin (r + 1) → Fin D.m := fun i => (αs i).getD ⟨0, D.m_pos⟩
  have hα_I0 : ∀ i ∈ I0, αs i = some (kOf i) := by
    intro i hi
    have hne : αs i ≠ none := (Finset.mem_filter.mp hi).2
    cases h : αs i with
    | none => exact absurd h hne
    | some k => simp [kOf, h]
  have hkOf_inj : Set.InjOn kOf I0 := by
    intro i hi j hj heq
    by_contra hne
    have hne_val : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hi_some := hα_I0 i hi
    have hj_some := hα_I0 j hj
    rw [heq] at hi_some
    rcases lt_or_gt_of_ne hne_val with hlt | hgt
    · exact hrep ⟨i, j, hlt, kOf j, hi_some, hj_some⟩
    · exact hrep ⟨j, i, hgt, kOf j, hj_some, hi_some⟩
  -- Any term with h i ≥ ℓ for some i ∈ IN vanishes (E_N * T^ℓ = 0)
  have hkill_ge : ∀ h ∈ D.Aset r, (∃ i ∈ IN, D.ℓ ≤ h i) →
      D.uRow f ᵥ* (D.projBlockMat g αs h * D.Tmat ^ D.ℓ) = 0 := by
    rintro h _ ⟨i, hi, hle⟩
    have hi_none : αs i = none := (Finset.mem_filter.mp hi).2
    have hir : i.val < r := by
      have hne : i ≠ Fin.last r := fun heq => hlastN (heq ▸ hi_none)
      have := i.isLt
      have : i.val ≠ r := fun h' => hne (Fin.ext h')
      omega
    unfold projBlockMat
    have hsplit := prodRange_split_at (D.projStep g αs h) hir
    have hstep_i : D.projStep g αs h i.val = 0 := by
      simp only [projStep, hir, dite_true]
      have hieq : (⟨i.val, by omega⟩ : Fin (r + 1)) = i := Fin.ext rfl
      rw [hieq, hi_none, Eopt]
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, pow_add, ← mul_assoc, D.E_N_mul_Tmat_pow_l, zero_mul, zero_mul]
    rw [hsplit, hstep_i, mul_zero, zero_mul, zero_mul, zero_mul, zero_mul, Matrix.vecMul_zero]
  let Agood := (D.Aset r).filter (fun h => ∀ i ∈ IN, h i < D.ℓ)
  have hsum_good : (∑ h ∈ D.Aset r, D.uRow f ᵥ* (D.projBlockMat g αs h * D.Tmat ^ D.ℓ)) =
      ∑ h ∈ Agood, D.uRow f ᵥ* (D.projBlockMat g αs h * D.Tmat ^ D.ℓ) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun h hh hnot => ?_
    simp only [Agood, Finset.mem_filter, hh, true_and, not_forall, not_lt] at hnot
    rcases hnot with ⟨i, hi, hle⟩
    exact hkill_ge h hh ⟨i, hi, hle⟩
  rw [hsum_good]
  -- Group Agood by the fixed nilpotent exponent tuple ν : Fin z → ℕ
  let NuSet : Finset (Fin z → ℕ) := Fintype.piFinset (fun _ : Fin z => Finset.range D.ℓ)
  have hfib : (∑ h ∈ Agood, D.uRow f ᵥ* (D.projBlockMat g αs h * D.Tmat ^ D.ℓ)) =
      ∑ ν ∈ NuSet, ∑ h ∈ Agood.filter (fun h => (fun j : Fin z => h (pos j)) = ν),
        D.uRow f ᵥ* (D.projBlockMat g αs h * D.Tmat ^ D.ℓ) := by
    symm
    refine Finset.sum_fiberwise_of_maps_to ?_ _
    intro h hh
    have hlt := (Finset.mem_filter.mp hh).2
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_range.mpr (hlt (pos j) (hpos_mem j))
  rw [hfib]
  refine (D.Msub f (r - 1)).sum_mem fun ν hν_mem => ?_
  have hν_lt : ∀ j : Fin z, ν j < D.ℓ := fun j =>
    Finset.mem_range.mp ((Fintype.mem_piFinset.mp hν_mem) j)
  -- Define canonical tuple h̃ agreeing with ν on IN and 0 on I0
  let htilde : Fin (r + 1) → ℕ := fun i =>
    if hi : i ∈ IN then ν ((IN.orderIsoOfFin rfl).symm ⟨i, hi⟩) else 0
  have htilde_pos : ∀ j : Fin z, htilde (pos j) = ν j := by
    intro j
    have hmem := hpos_mem j
    simp only [htilde, hmem, dite_true]
    congr 1
    exact (IN.orderIsoOfFin rfl).symm_apply_apply j
  have htilde_I0 : ∀ i ∈ I0, htilde i = 0 := by
    intro i hi
    have hnotIN : i ∉ IN := by
      simp only [IN, I0, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi
    simp [htilde, hnotIN]
  -- Factor out scalar ∏_{i ∈ I0} lam(kOf i)^(h i) from projBlockMat g αs h
  let cfac : (Fin (r + 1) → ℕ) → ℂ := fun h => ∏ i ∈ I0, (D.lam (kOf i)) ^ (h i)
  have hfactor : ∀ h ∈ Agood.filter (fun h => (fun j : Fin z => h (pos j)) = ν),
      D.projBlockMat g αs h = cfac h • D.projBlockMat g αs htilde := by
    intro h hh
    have hν_eq : ∀ j : Fin z, h (pos j) = ν j := fun j =>
      congrFun (Finset.mem_filter.mp hh).2 j
    have hIN_eq : ∀ i ∈ IN, h i = htilde i := by
      intro i hi
      let j := (IN.orderIsoOfFin rfl).symm ⟨i, hi⟩
      have hj : pos j = i := congrArg Subtype.val ((IN.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
      rw [← hj, hν_eq j, htilde_pos j]
    let scal : ℕ → ℂ := fun i =>
      if hi : i < r + 1 then
        if (⟨i, hi⟩ : Fin (r + 1)) ∈ I0 then (D.lam (kOf ⟨i, hi⟩)) ^ (h ⟨i, hi⟩) else 1
      else 1
    have hstep_eq : ∀ i, i < r →
        D.projStep g αs h (0 + i) = scal (0 + i) • D.projStep g αs htilde (0 + i) := by
      intro i hi
      simp only [zero_add]
      have hir1 : i < r + 1 := by omega
      let idx : Fin (r + 1) := ⟨i, hir1⟩
      by_cases hI0 : idx ∈ I0
      · have hα := hα_I0 idx hI0
        have hht : htilde idx = 0 := htilde_I0 idx hI0
        simp only [projStep, hi, dite_true, scal, hir1, hI0, ite_true, idx]
        rw [hα, Eopt, hht, pow_zero, mul_one, D.E_eig_mul_Tmat_pow, Matrix.smul_mul]
      · have hIN : idx ∈ IN := by
          simp only [IN, I0, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hI0 ⊢
          exact hI0
        simp only [projStep, hi, dite_true, scal, hir1, hI0, ite_false, one_smul, idx]
        rw [hIN_eq idx hIN]
    have hprod_eq : prodRange (D.projStep g αs h) 0 r =
        (∏ i ∈ Finset.range r, scal i) • prodRange (D.projStep g αs htilde) 0 r := by
      have h1 := prodRange_eq_of_shift (F₁ := D.projStep g αs h)
        (F₂ := fun i => scal i • D.projStep g αs htilde i) (a₁ := 0) (a₂ := 0) hstep_eq
      rw [h1, prodRange_smul]
      simp only [zero_add]
    have hlast_I0 : Fin.last r ∈ I0 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlastN⟩
    have hlast_eq : D.Eopt (αs (Fin.last r)) * D.Tmat ^ (h (Fin.last r)) =
        ((D.lam (kOf (Fin.last r))) ^ (h (Fin.last r))) •
          (D.Eopt (αs (Fin.last r)) * D.Tmat ^ (htilde (Fin.last r))) := by
      rw [hα_I0 _ hlast_I0, Eopt, htilde_I0 _ hlast_I0, pow_zero, mul_one, D.E_eig_mul_Tmat_pow]
    have hcfac_eq : (∏ i ∈ Finset.range r, scal i) * (D.lam (kOf (Fin.last r))) ^ (h (Fin.last r)) =
        cfac h := by
      have hprod_all : (∏ i ∈ Finset.range (r + 1), scal i) = cfac h := by
        rw [← Fin.prod_univ_eq_prod_range scal (r + 1)]
        have hscal_fin : ∀ i : Fin (r + 1), scal i.val =
            if i ∈ I0 then (D.lam (kOf i)) ^ (h i) else 1 := fun i => by
          simp only [scal, i.isLt, dite_true, Fin.eta]
        simp_rw [hscal_fin]
        rw [← Finset.prod_subset (Finset.subset_univ I0)]
        · refine Finset.prod_congr rfl fun i hi => by simp [hi]
        · intro i _ hi; simp [hi]
      rw [← hprod_all, Finset.prod_range_succ]
      congr 1
      have hlast_val : (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r := Fin.ext rfl
      simp [scal, hlast_val, hlast_I0]
    unfold projBlockMat
    rw [hprod_eq, mul_assoc, hlast_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcfac_eq,
      mul_assoc]
  -- Rewrite the fiber sum as (scalar sum) • v_tilde
  let vtilde : Q → ℂ := D.uRow f ᵥ* (D.projBlockMat g αs htilde * D.Tmat ^ D.ℓ)
  have hfiber_eq : (∑ h ∈ Agood.filter (fun h => (fun j : Fin z => h (pos j)) = ν),
      D.uRow f ᵥ* (D.projBlockMat g αs h * D.Tmat ^ D.ℓ)) =
      (∑ h ∈ Agood.filter (fun h => (fun j : Fin z => h (pos j)) = ν), cfac h) • vtilde := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [hfactor h hh, Matrix.smul_mul, Matrix.vecMul_smul]
  rw [hfiber_eq]
  -- Define nilpotent prefix vectors x̃_j ∈ N
  let xtilde : Fin z → (Q → ℂ) := fun j =>
    D.uRow f ᵥ* (prodRange (D.projStep g αs htilde) 0 (pos j).val * D.E_N)
  have hxtilde_N : ∀ j : Fin z, xtilde j ∈ D.Nsub := fun j => by
    dsimp only [xtilde]
    rw [← Matrix.vecMul_vecMul]
    exact D.vecMul_E_N_mem_Nsub _
  have hxtilde_L : ∀ j : Fin z, xtilde j ∈ D.Lsub f (pos j).val := fun j => by
    dsimp only [xtilde]
    rw [← Matrix.vecMul_vecMul]
    refine D.vecMul_E_N_mem_Lsub ?_
    simpa using D.vecMul_prodRange_projStep_mem_Lsub f g αs htilde (D.uRow_mem_Lsub f 0) 0 (pos j).val
  -- Apply Lemma 1.8 (Nilpotent Dimension Growth) to xtilde and ν!
  by_cases hdep : ∃ j : Fin z, xtilde j ᵥ* D.Tmat ^ (ν j) ∈ D.nilpSpan xtilde j.val
  · -- Subcase A: vtilde itself lies in M_{r-1}(f)!
    rcases hdep with ⟨j, hj_mem⟩
    refine (D.Msub f (r - 1)).smul_mem _ ?_
    have hpos_r : (pos j).val < r := hpos_lt_r j
    have hvtilde_fac :
        vtilde =
          ((xtilde j ᵥ* D.Tmat ^ (ν j)) ᵥ*
            (transMat A [g ⟨(pos j).val, hpos_r⟩] *
              prodRange (D.projStep g αs htilde) ((pos j).val + 1) (r - (pos j).val - 1) *
              D.Eopt (αs (Fin.last r)) * D.Tmat ^ (htilde (Fin.last r)))) ᵥ* D.Tmat ^ D.ℓ := by
      dsimp only [vtilde, projBlockMat, xtilde]
      have hsplit := prodRange_split_at (D.projStep g αs htilde) hpos_r
      have hstep_j : D.projStep g αs htilde (pos j).val =
          D.E_N * D.Tmat ^ (ν j) * transMat A [g ⟨(pos j).val, hpos_r⟩] := by
        simp only [projStep, hpos_r, dite_true]
        have hjeq : (⟨(pos j).val, by omega⟩ : Fin (r + 1)) = pos j := Fin.ext rfl
        rw [hjeq, hpos_none j, Eopt, htilde_pos j]
      rw [hsplit, hstep_j]
      simp only [Matrix.vecMul_vecMul, mul_assoc]
    rw [hvtilde_fac]
    by_cases hj0 : j.val = 0
    · rw [hj0, D.nilpSpan_zero, Submodule.mem_bot] at hj_mem
      rw [hj_mem, Matrix.zero_vecMul, Matrix.zero_vecMul]
      exact (D.Msub f (r - 1)).zero_mem
    · have hpos_ge1 : 1 ≤ (pos j).val := by
        have hlt : (pos ⟨0, by omega⟩).val < (pos j).val :=
          pos.strictMono (show (⟨0, by omega⟩ : Fin z) < j from Nat.pos_of_ne_zero hj0)
        omega
      have hj_L : xtilde j ᵥ* D.Tmat ^ (ν j) ∈ D.Lsub f ((pos j).val - 1) := by
        have hspan_le : D.nilpSpan xtilde j.val ≤ D.Lsub f ((pos j).val - 1) := by
          rw [nilpSpan, Submodule.span_le]
          rintro v ⟨i, hi, k, _, rfl⟩
          have hpos_lt : (pos i).val < (pos j).val := pos.strictMono hi
          have hiL : xtilde i ∈ D.Lsub f ((pos j).val - 1) :=
            D.Lsub_mono f (by omega) (hxtilde_L i)
          exact D.vecMul_Tmat_pow_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_Lsub hw) hiL k
        exact hspan_le hj_mem
      refine ⟨(xtilde j ᵥ* D.Tmat ^ (ν j)) ᵥ*
          (transMat A [g ⟨(pos j).val, hpos_r⟩] *
            prodRange (D.projStep g αs htilde) ((pos j).val + 1) (r - (pos j).val - 1) *
            D.Eopt (αs (Fin.last r)) * D.Tmat ^ (htilde (Fin.last r))), ?_, rfl⟩
      have h1 := D.vecMul_transMat_step_mem_Lsub hj_L (g ⟨(pos j).val, hpos_r⟩)
      have h2 := D.vecMul_prodRange_projStep_mem_Lsub f g αs htilde h1
        ((pos j).val + 1) (r - (pos j).val - 1)
      have h3 := D.vecMul_Eopt_mem_Lsub h2 (αs (Fin.last r))
      have h4 := D.vecMul_Tmat_pow_mem_of_T_inv (fun _ hw => D.vecMul_Tmat_mem_Lsub hw) h3
        (htilde (Fin.last r))
      have hle : (pos j).val - 1 + 1 + (r - (pos j).val - 1) ≤ r - 1 := by omega
      change (xtilde j ᵥ* D.Tmat ^ (ν j)) ᵥ*
          (transMat A [g ⟨(pos j).val, hpos_r⟩] *
            prodRange (D.projStep g αs htilde) ((pos j).val + 1) (r - (pos j).val - 1) *
            D.Eopt (αs (Fin.last r)) * D.Tmat ^ (htilde (Fin.last r))) ∈ D.Lsub f (r - 1)
      simpa only [Matrix.vecMul_vecMul, mul_assoc] using D.Lsub_mono f hle h4
  · -- Subcase B: nilpotent dimension charge z + s ≤ κ_r, scalar sum vanishes by Lemma 1.9!
    push Not at hdep
    have hcharge_t : z + ∑ j : Fin z, ν j ≤ D.t := D.nilpotent_dim_growth hxtilde_N hν_lt hdep
    have hcharge_l : z + ∑ j : Fin z, ν j ≤ D.ℓ * r := by
      have h1 : ∑ j : Fin z, (ν j + 1) ≤ ∑ _j : Fin z, D.ℓ :=
        Finset.sum_le_sum fun j _ => by have := hν_lt j; omega
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul] at h1
      have h2 : z * D.ℓ ≤ r * D.ℓ := Nat.mul_le_mul_right D.ℓ hz_le_r
      linarith
    have hcharge : z + ∑ j : Fin z, ν j ≤ D.kappa r := le_min hcharge_t hcharge_l
    let s : ℕ := ∑ j : Fin z, ν j
    have hsum_zero : (∑ h ∈ Agood.filter (fun h => (fun j : Fin z => h (pos j)) = ν), cfac h) = 0 := by
      by_cases hs : s ≤ D.Dplus r
      · -- Biject the fiber with ⋃_{k ∈ Icc (Dminus - s) (Dplus - s)} tupleFinset I0 k
        let Fset := Agood.filter (fun h => (fun j : Fin z => h (pos j)) = ν)
        have hsum_Icc : (∑ h ∈ Fset, cfac h) =
            ∑ k ∈ Finset.Icc (D.Dminus r - s) (D.Dplus r - s), tupleSum I0 (D.lam ∘ kOf) k := by
          unfold tupleSum
          rw [← Finset.sum_sigma (Finset.Icc (D.Dminus r - s) (D.Dplus r - s))
            (fun k => tupleFinset I0 k)
            (fun p : Σ _ : ℕ, I0 → ℕ => ∏ i : I0, ((D.lam ∘ kOf) i.1) ^ (p.2 i))]
          have hIN_sum : ∀ h ∈ Fset, ∑ i ∈ IN, h i = s := by
            intro h hh
            have hν_eq : ∀ j : Fin z, h (pos j) = ν j := fun j =>
              congrFun (Finset.mem_filter.mp hh).2 j
            dsimp only [s]
            rw [← Finset.sum_coe_sort IN h]
            symm
            refine Fintype.sum_equiv (IN.orderIsoOfFin rfl).toEquiv _ _ fun j => ?_
            exact (hν_eq j).symm
          have htot_split : ∀ h : Fin (r + 1) → ℕ,
              (∑ i : Fin (r + 1), h i) = (∑ i ∈ IN, h i) + (∑ i ∈ I0, h i) := by
            intro h
            have hdisj : Disjoint IN I0 := by
              rw [Finset.disjoint_left]
              intro i hi1 hi2
              exact (Finset.mem_filter.mp hi2).2 (Finset.mem_filter.mp hi1).2
            have hunion : IN ∪ I0 = Finset.univ := by
              ext i
              simp only [IN, I0, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
                iff_true]
              exact Classical.em (αs i = none)
            rw [← Finset.sum_union hdisj, hunion]
          refine Finset.sum_bij
            (fun h _ => (⟨∑ i ∈ I0, h i, fun i : I0 => h i.1⟩ : Σ _ : ℕ, I0 → ℕ))
            ?_ ?_ ?_ ?_
          · intro h hh
            have hA := (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
            rw [D.mem_Aset, htot_split, hIN_sum h hh] at hA
            simp only [Finset.mem_sigma, Finset.mem_Icc, mem_tupleFinset, Finset.sum_coe_sort]
            exact ⟨⟨by omega, by omega⟩, trivial⟩
          · intro h₁ hh₁ h₂ hh₂ heq
            have h2 : (fun i : I0 => h₁ i.1) = (fun i : I0 => h₂ i.1) :=
              eq_of_heq (Sigma.mk.inj_iff.mp heq).2
            have hν₁ : ∀ j : Fin z, h₁ (pos j) = ν j := fun j =>
              congrFun (Finset.mem_filter.mp hh₁).2 j
            have hν₂ : ∀ j : Fin z, h₂ (pos j) = ν j := fun j =>
              congrFun (Finset.mem_filter.mp hh₂).2 j
            funext i
            by_cases hI0 : i ∈ I0
            · exact congrFun h2 ⟨i, hI0⟩
            · have hIN : i ∈ IN := by
                simp only [IN, I0, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hI0 ⊢
                exact hI0
              let j := (IN.orderIsoOfFin rfl).symm ⟨i, hIN⟩
              have hj : pos j = i := congrArg Subtype.val ((IN.orderIsoOfFin rfl).apply_symm_apply ⟨i, hIN⟩)
              rw [← hj, hν₁ j, hν₂ j]
          · rintro ⟨k, f₀⟩ hmem
            simp only [Finset.mem_sigma, Finset.mem_Icc, mem_tupleFinset] at hmem
            let h : Fin (r + 1) → ℕ := fun i =>
              if hi : i ∈ I0 then f₀ ⟨i, hi⟩
              else htilde i
            have hh_I0 : ∀ i : I0, h i.1 = f₀ i := fun i => by simp [h, i.2]
            have hh_pos : ∀ j : Fin z, h (pos j) = ν j := fun j => by
              have hnotI0 : pos j ∉ I0 := by
                simp only [I0, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
                exact hpos_none j
              simp [h, hnotI0, htilde_pos j]
            have hh_IN_sum : ∑ i ∈ IN, h i = s := by
              rw [← Finset.sum_coe_sort IN h]
              symm
              refine Fintype.sum_equiv (IN.orderIsoOfFin rfl).toEquiv _ _ fun j => ?_
              exact (hh_pos j).symm
            have hh_I0_sum : ∑ i ∈ I0, h i = k := by
              rw [← Finset.sum_coe_sort I0 h]
              simpa [hh_I0] using hmem.2
            refine ⟨h, ?_, ?_⟩
            · simp only [Fset, Agood, Finset.mem_filter, D.mem_Aset, htot_split, hh_IN_sum, hh_I0_sum]
              refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, funext hh_pos⟩
              intro i hi
              let j := (IN.orderIsoOfFin rfl).symm ⟨i, hi⟩
              have hj : pos j = i := congrArg Subtype.val ((IN.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
              rw [← hj, hh_pos j]
              exact hν_lt j
            · exact Sigma.ext hh_I0_sum (heq_of_eq (funext hh_I0))
          · intro h _
            simp only [cfac, Function.comp_apply]
            rw [Finset.prod_coe_sort I0 (fun i => (D.lam (kOf i)) ^ (h i))]
        rw [hsum_Icc]
        let Y₀ : Finset (Fin D.m) := I0.image kOf
        have h0_not : ⟨0, D.m_pos⟩ ∉ Y₀ := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨i, hi, hik⟩
          apply hhas0
          refine ⟨i, ?_⟩
          rw [hα_I0 i hi, hik]
        have hY₀_card : Y₀.card = r + 1 - z := by
          rw [Finset.card_image_of_injOn hkOf_inj]
          have hdisj : Disjoint IN I0 := by
            rw [Finset.disjoint_left]
            intro i hi1 hi2
            exact (Finset.mem_filter.mp hi2).2 (Finset.mem_filter.mp hi1).2
          have hunion : IN ∪ I0 = Finset.univ := by
            ext i
            simp only [IN, I0, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
              iff_true]
            exact Classical.em (αs i = none)
          have hsum_card : IN.card + I0.card = r + 1 := by
            rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
          dsimp only [z]; omega
        have heq_sum : ∀ k : ℕ, tupleSum I0 (D.lam ∘ kOf) k = tupleSum Y₀ D.lam k := by
          intro k
          let e : I0 ≃ Y₀ := Equiv.ofBijective
            (fun i => ⟨kOf i.1, Finset.mem_image_of_mem kOf i.2⟩)
            ⟨fun i₁ i₂ h => Subtype.ext (hkOf_inj i₁.2 i₂.2 (congrArg Subtype.val h)),
             fun ⟨y, hy⟩ => by
               rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
               exact ⟨⟨i, hi⟩, rfl⟩⟩
          exact tupleSum_congr_equiv e (fun i => rfl) k
        simp_rw [heq_sum]
        exact D.annular_sum_Icc_eq_zero h0_not hm2 hrn hz_le_r hY₀_card hcharge hs
      · -- Empty fiber since s > Dplus r
        push Not at hs
        refine Finset.sum_eq_zero fun h hh => ?_
        exfalso
        have hA := (D.mem_Aset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1).2
        have hν_eq : ∀ j : Fin z, h (pos j) = ν j := fun j =>
          congrFun (Finset.mem_filter.mp hh).2 j
        have hle_sum : s ≤ ∑ i : Fin (r + 1), h i := by
          dsimp only [s]
          have hIN_le : ∑ i ∈ IN, h i ≤ ∑ i : Fin (r + 1), h i :=
            Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
          have hIN_eq : ∑ i ∈ IN, h i = ∑ j : Fin z, ν j := by
            rw [← Finset.sum_coe_sort IN h]
            symm
            refine Fintype.sum_equiv (IN.orderIsoOfFin rfl).toEquiv _ _ fun j => ?_
            exact (hν_eq j).symm
          omega
        omega
    rw [hsum_zero, zero_smul]
    exact (D.Msub f (r - 1)).zero_mem

/-! ### Section 6: Positive-Coefficient Induction & Short Relative Extension (Theorem 1.1) -/

lemma nat_eq_of_sum_cast_sub_eq_zero {ι : Type*} {I : Finset ι} {a b : ι → ℕ}
    (hle : ∀ i ∈ I, a i ≤ b i)
    (hsum : ∑ i ∈ I, ((a i : ℂ) - (b i : ℂ)) = 0) :
    ∀ i ∈ I, a i = b i := by
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, sub_eq_zero, Nat.cast_inj] at hsum
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum

lemma card_preimage_replicate_inter_C (S : Finset Q) (hSC : S ⊆ D.C) (k : ℕ) :
    ((A.preimage S (List.replicate k D.a)) ∩ D.C).card = S.card := by
  have h1 : (((A.preimage S (List.replicate k D.a)) ∩ D.C).card : ℂ) = (S.card : ℂ) := by
    rw [← D.dotProduct_indVec_C_transMat S (List.replicate k D.a), D.transMat_replicate,
      D.indVec_C_vecMul_Tmat_pow k]
    have h0 := D.dotProduct_indVec_C_transMat S []
    rw [transMat_nil, Matrix.vecMul_one, DFA.preimage_nil, Finset.inter_eq_left.mpr hSC] at h0
    exact h0
  exact Nat.cast_injective h1

lemma card_preimage_cons_a_inter_C (S : Finset Q) (w : List α) :
    ((A.preimage S (D.a :: w)) ∩ D.C).card = ((A.preimage S w) ∩ D.C).card := by
  have h1 : (((A.preimage S (D.a :: w)) ∩ D.C).card : ℂ) =
      (((A.preimage S w) ∩ D.C).card : ℂ) := by
    rw [← D.dotProduct_indVec_C_transMat S (D.a :: w), transMat_cons, ← Matrix.vecMul_vecMul,
      ← Tmat, D.indVec_C_vecMul_Tmat, D.dotProduct_indVec_C_transMat]
  exact Nat.cast_injective h1

/-- **Theorem 1.1 (Zhu 2026, Theorem 2.3 — Short Relative Extension)**:
for every synchronizing one-cluster automaton with `m ≥ 2` and every nonempty proper `S ⊂ C`,
there exists `w` with `|w| ≤ n` such that `|S (w a^ℓ)⁻¹ ∩ C| > |S|`. -/
theorem short_relative_extension (hm2 : 2 ≤ D.m) (hSync : A.IsSynchronizing)
    {S : Finset Q} (hSne : S.Nonempty) (hSsub : S ⊂ D.C) :
    ∃ w : List α, w.length ≤ D.n ∧
      S.card < ((A.preimage S (w ++ List.replicate D.ℓ D.a)) ∩ D.C).card := by
  have hSC : S ⊆ D.C := hSsub.subset
  have hSlt : S.card < D.m := Finset.card_lt_card hSsub
  by_contra hno
  push Not at hno
  let μ : List α → ℕ := fun w => ((A.preimage S w) ∩ D.C).card
  have hno' : ∀ w : List α, w.length ≤ D.n → μ (w ++ List.replicate D.ℓ D.a) ≤ S.card := hno
  have hμ_rep : ∀ k : ℕ, μ (List.replicate k D.a) = S.card :=
    fun k => D.card_preimage_replicate_inter_C S hSC k
  have hμ_cons_a : ∀ w : List α, μ (D.a :: w) = μ w :=
    fun w => D.card_preimage_cons_a_inter_C S w
  -- Leftmost-control deletion helper: if M_{r-1}(g) ⊥ [S] for all g, then μ(u ++ a^ℓ) = |S| for controls(u) ≤ r.
  have hleftmost : ∀ r : ℕ, (∀ g : α, ∀ v ∈ D.Msub g r, dotProduct v (indVec S) = 0) →
      ∀ u : List α, controls D.a u ≤ r + 1 → μ (u ++ List.replicate D.ℓ D.a) = S.card := by
    intro r horth u
    induction u with
    | nil =>
      intro _
      simpa using hμ_rep D.ℓ
    | cons b u ih =>
      intro hctrl
      by_cases hba : b = D.a
      · subst b
        rw [List.cons_append, hμ_cons_a]
        exact ih (by rwa [controls_cons_self] at hctrl)
      · rw [controls_cons_ne hba] at hctrl
        have hcu : controls D.a u ≤ r := by omega
        have hMmem : D.uRow b ᵥ* transMat A (u ++ List.replicate D.ℓ D.a) ∈ D.Msub b r := by
          refine ⟨D.uRow b ᵥ* transMat A u, D.uRow_vecMul_mem_Lsub b hcu, ?_⟩
          change (D.uRow b ᵥ* transMat A u) ᵥ* D.Tmat ^ D.ℓ = _
          rw [transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul]
        have hzero := horth b _ hMmem
        rw [D.dotProduct_uRow_transMat, sub_eq_zero, Nat.cast_inj] at hzero
        change μ (b :: (u ++ List.replicate D.ℓ D.a)) = μ (u ++ List.replicate D.ℓ D.a) at hzero
        rw [List.cons_append, hzero]
        exact ih (by omega)
  -- Main positive-coefficient induction for 0 ≤ r ≤ n - 2
  have hind : ∀ r : ℕ, r ≤ D.n - 2 →
      ∀ f : α, ∀ v ∈ D.Msub f r, dotProduct v (indVec S) = 0 := by
    intro r
    induction r with
    | zero =>
      intro _ f
      have hB : D.uRow f ᵥ* D.Bmat = 0 := D.vecMul_Bmat_eq_zero (D.uRow_mem_Zsub f)
      have hsum0 : ∑ j ∈ Finset.range D.m,
          ((((A.preimage S (f :: List.replicate (D.ℓ + j) D.a)) ∩ D.C).card : ℂ) -
          (((A.preimage S (List.replicate (D.ℓ + j) D.a)) ∩ D.C).card : ℂ)) = 0 := by
        have h1 : dotProduct (D.uRow f ᵥ* D.Bmat) (indVec S) = 0 := by rw [hB, zero_dotProduct]
        rw [Bmat, Matrix.vecMul_sum, sum_dotProduct] at h1
        refine (Finset.sum_congr rfl fun j _ => ?_).symm.trans h1
        rw [← D.transMat_replicate, D.dotProduct_uRow_transMat]
      have hle_j : ∀ j ∈ Finset.range D.m,
          μ (f :: List.replicate (D.ℓ + j) D.a) ≤ μ (List.replicate (D.ℓ + j) D.a) := by
        intro j hj
        have hj' : j < D.m := Finset.mem_range.mp hj
        rw [hμ_rep]
        have hword : f :: List.replicate (D.ℓ + j) D.a =
            (f :: List.replicate j D.a) ++ List.replicate D.ℓ D.a := by
          rw [add_comm D.ℓ j, List.replicate_add, List.cons_append]
        rw [hword]
        have hlen : (f :: List.replicate j D.a).length ≤ D.n := by
          simp only [List.length_cons, List.length_replicate]
          have := D.m_le_n; omega
        exact hno' _ hlen
      have heq_j := nat_eq_of_sum_cast_sub_eq_zero hle_j hsum0
      have hpow_orth : ∀ k : ℕ, dotProduct (D.uRow f ᵥ* D.Tmat ^ (D.ℓ + k)) (indVec S) = 0 := by
        intro k
        have hmod : D.ℓ + k = (D.ℓ + k % D.m) + (k / D.m) * D.m := by
          have hdm := Nat.div_add_mod k D.m
          rw [mul_comm] at hdm
          omega
        rw [hmod, D.Tmat_pow_add_mul_m (by omega), ← D.transMat_replicate,
          D.dotProduct_uRow_transMat]
        have hlt : k % D.m < D.m := Nat.mod_lt k D.m_pos
        have heq := heq_j (k % D.m) (Finset.mem_range.mpr hlt)
        change ((μ (f :: List.replicate (D.ℓ + k % D.m) D.a) : ℂ) -
          (μ (List.replicate (D.ℓ + k % D.m) D.a) : ℂ)) = 0
        rw [heq, sub_self]
      let K0 : Submodule ℂ (Q → ℂ) := LinearMap.ker
        ({ toFun := fun v => dotProduct v (indVec S)
           map_add' := fun x y => add_dotProduct x y _
           map_smul' := fun c x => smul_dotProduct c x _ } : (Q → ℂ) →ₗ[ℂ] ℂ)
      have hle_ker : D.Msub f 0 ≤ K0 := by
        rw [Msub, Submodule.map_le_iff_le_comap, Lsub, Submodule.span_le]
        rintro x ⟨w, hw, rfl⟩
        have hw0 : controls D.a w = 0 := Nat.eq_zero_of_le_zero hw
        change dotProduct ((D.uRow f ᵥ* transMat A w) ᵥ* D.Tmat ^ D.ℓ) (indVec S) = 0
        rw [eq_replicate_of_controls_zero hw0, D.transMat_replicate, Matrix.vecMul_vecMul,
          ← pow_add, add_comm]
        exact hpow_orth w.length
      intro v hv
      exact hle_ker hv
    | succ r ih =>
      intro hr_le f
      have hr_prev : r ≤ D.n - 2 := by omega
      have horth_prev := ih hr_prev
      have hr1 : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
      have hrn : r + 1 ≤ D.n - 1 := by omega
      -- Step 3: Every annular term for any g : Fin (r+1) → α (all ≠ a) has dotProduct = 0
      have hann_orth : ∀ (g : Fin (r + 1) → α) (_ : ∀ i, g i ≠ D.a)
          (h : Fin (r + 1 + 1) → ℕ), h ∈ D.Aset (r + 1) →
          dotProduct (D.uRow f ᵥ* transMat A (blockWord D.a g h ++ List.replicate D.ℓ D.a))
            (indVec S) = 0 := by
        intro g hg
        have hOm : D.Omega f g ∈ D.Msub f r := by
          simpa using D.omega_mem_Msub_pred (r := r + 1) hm2 hr1 hrn f g
        have hOm0 : dotProduct (D.Omega f g) (indVec S) = 0 := horth_prev f _ hOm
        rw [Omega, sum_dotProduct] at hOm0
        have hsum0 : ∑ h ∈ D.Aset (r + 1),
            ((μ (f :: (blockWord D.a g h ++ List.replicate D.ℓ D.a)) : ℂ) -
              (μ (blockWord D.a g h ++ List.replicate D.ℓ D.a) : ℂ)) = 0 := by
          refine (Finset.sum_congr rfl fun h _ => ?_).symm.trans hOm0
          rw [← D.dotProduct_uRow_transMat, transMat_append, D.transMat_replicate]
        have hle_h : ∀ h ∈ D.Aset (r + 1),
            μ (f :: (blockWord D.a g h ++ List.replicate D.ℓ D.a)) ≤
              μ (blockWord D.a g h ++ List.replicate D.ℓ D.a) := by
          intro h hh
          have hctrl : controls D.a (blockWord D.a g h) ≤ r + 1 := by
            rw [blockWord_controls D.a g hg h]
          have hμ_eq : μ (blockWord D.a g h ++ List.replicate D.ℓ D.a) = S.card :=
            hleftmost r horth_prev (blockWord D.a g h) hctrl
          rw [hμ_eq, ← List.cons_append]
          have hlen : (f :: blockWord D.a g h).length ≤ D.n := by
            rw [List.length_cons, blockWord_length]
            have hA := (D.mem_Aset.mp hh).2
            unfold Dplus at hA
            have hk_le_t : D.kappa (r + 1) ≤ D.t := min_le_left _ _
            have hmt := D.m_add_t
            have hmn := D.m_le_n
            omega
          exact hno' _ hlen
        have heq_h := nat_eq_of_sum_cast_sub_eq_zero hle_h hsum0
        intro h hh
        rw [D.dotProduct_uRow_transMat]
        change ((μ (f :: (blockWord D.a g h ++ List.replicate D.ℓ D.a)) : ℂ) -
          (μ (blockWord D.a g h ++ List.replicate D.ℓ D.a) : ℂ)) = 0
        rw [heq_h h hh, sub_self]
      -- Step 4: Cover every generator of M_{r+1}(f) from Msub_eq_span_combined (using a^(k*m)-shift!)
      let Ksub : Submodule ℂ (Q → ℂ) := LinearMap.ker
        ({ toFun := fun v => dotProduct v (indVec S)
           map_add' := fun x y => add_dotProduct x y _
           map_smul' := fun c x => smul_dotProduct c x _ } : (Q → ℂ) →ₗ[ℂ] ℂ)
      have hle_K : D.Msub f (r + 1) ≤ Ksub := by
        rw [D.Msub_eq_span_combined f (r + 1), Submodule.span_le]
        rintro v ⟨u, huc, hulen, rfl⟩
        change dotProduct (D.uRow f ᵥ* transMat A (u ++ List.replicate D.ℓ D.a)) (indVec S) = 0
        by_cases hlt : controls D.a u ≤ r
        · refine horth_prev f _ ?_
          refine ⟨D.uRow f ᵥ* transMat A u, D.uRow_vecMul_mem_Lsub f hlt, ?_⟩
          change (D.uRow f ᵥ* transMat A u) ᵥ* D.Tmat ^ D.ℓ = _
          rw [transMat_append, D.transMat_replicate, Matrix.vecMul_vecMul]
        · have heq_ctrl : controls D.a u = r + 1 := by omega
          obtain ⟨g₀, h₀, hg₀, hu_eq⟩ := exists_blockWord D.a u
          let g : Fin (r + 1) → α := fun i => g₀ (Fin.cast heq_ctrl.symm i)
          let h : Fin (r + 1 + 1) → ℕ := fun i => h₀ (Fin.cast (congrArg (· + 1) heq_ctrl.symm) i)
          have hg : ∀ i, g i ≠ D.a := fun i => hg₀ _
          have hu_bw : u = blockWord D.a g h := by
            have hcast : ∀ {r₁ r₂ : ℕ} (he : r₁ = r₂) (g₁ : Fin r₁ → α) (h₁ : Fin (r₁ + 1) → ℕ),
                blockWord D.a g₁ h₁ =
                  blockWord D.a (fun i : Fin r₂ => g₁ (Fin.cast he.symm i))
                    (fun i : Fin (r₂ + 1) => h₁ (Fin.cast (congrArg (· + 1) he.symm) i)) := by
              rintro r₁ _ rfl g₁ h₁; rfl
            rw [hu_eq, hcast heq_ctrl]
          rw [hu_bw] at hulen ⊢
          rw [blockWord_length] at hulen
          let τ := ∑ i : Fin (r + 1 + 1), h i
          have hτ_le : τ ≤ D.Dplus (r + 1) := by
            dsimp only [τ, Dplus]; omega
          by_cases hge : D.Dminus (r + 1) ≤ τ
          · exact hann_orth g hg h (D.mem_Aset.mpr ⟨hge, hτ_le⟩)
          · push Not at hge
            have hDpos : 0 < D.Dminus (r + 1) := by omega
            have hDrel : D.Dplus (r + 1) = D.Dminus (r + 1) + D.m - 1 := by
              unfold Dminus at hDpos
              unfold Dminus Dplus
              omega
            let gap := D.Dminus (r + 1) - τ
            let km := (gap + D.m - 1) / D.m
            have hkm_lo : gap ≤ km * D.m := by
              have hdiv := Nat.div_add_mod (gap + D.m - 1) D.m
              rw [mul_comm] at hdiv
              have hmod := Nat.mod_lt (gap + D.m - 1) D.m_pos
              dsimp only [km]
              omega
            have hkm_hi : km * D.m ≤ gap + D.m - 1 := by
              have hdiv := Nat.div_add_mod (gap + D.m - 1) D.m
              rw [mul_comm] at hdiv
              dsimp only [km]
              omega
            let h' := Function.update h (Fin.last (r + 1)) (h (Fin.last (r + 1)) + km * D.m)
            have hsum' : ∑ i : Fin (r + 1 + 1), h' i = τ + km * D.m := by
              dsimp only [h', τ]
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Fin.last (r + 1))),
                ← Finset.add_sum_erase _ h (Finset.mem_univ (Fin.last (r + 1)))]
              rw [Function.update_self]
              have herase : ∑ i ∈ Finset.univ.erase (Fin.last (r + 1)),
                  Function.update h (Fin.last (r + 1)) (h (Fin.last (r + 1)) + km * D.m) i =
                  ∑ i ∈ Finset.univ.erase (Fin.last (r + 1)), h i := by
                refine Finset.sum_congr rfl fun i hi => ?_
                exact Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _
              rw [herase]
              omega
            have hh'_mem : h' ∈ D.Aset (r + 1) := by
              rw [D.mem_Aset, hsum']
              exact ⟨by omega, by omega⟩
            have hmat_eq : transMat A (blockWord D.a g h ++ List.replicate D.ℓ D.a) =
                transMat A (blockWord D.a g h' ++ List.replicate D.ℓ D.a) := by
              have hbw' : blockWord D.a g h' = blockWord D.a g h ++ List.replicate (km * D.m) D.a :=
                (blockWord_append_replicate D.a g h (km * D.m)).symm
              rw [hbw', List.append_assoc, ← List.replicate_add, transMat_append, transMat_append,
                D.transMat_replicate, D.transMat_replicate, add_comm (km * D.m) D.ℓ,
                D.Tmat_pow_add_mul_m le_rfl km]
            rw [hmat_eq]
            exact hann_orth g hg h' hh'_mem
      intro v hv
      exact hle_K hv
  -- Step 5: Stabilization gives M_r(f) ⊥ [S] for ALL r, hence μ(u ++ a^ℓ) = |S| for ALL u
  have hall_orth : ∀ r : ℕ, ∀ f : α, ∀ v ∈ D.Msub f r, dotProduct v (indVec S) = 0 := fun r f v hv =>
    hind (D.n - 2) le_rfl f v (D.Msub_le_Msub_n_sub_two f r hv)
  have hall_μ : ∀ u : List α, μ (u ++ List.replicate D.ℓ D.a) = S.card := fun u =>
    hleftmost (controls D.a u) (hall_orth (controls D.a u)) u (Nat.le_succ _)
  -- Contradiction from a synchronizing word!
  rcases hSync with ⟨w_sync, q₀, hq₀⟩
  rcases hSne with ⟨s, hs⟩
  obtain ⟨j, hj⟩ := D.hC_trans (D.stepA^[D.ℓ] q₀) (D.hℓ q₀) s (hSC hs)
  let u := w_sync ++ List.replicate j D.a
  have hpre_univ : A.preimage S (u ++ List.replicate D.ℓ D.a) = Finset.univ := by
    ext p
    simp only [DFA.mem_preimage, Finset.mem_univ, iff_true, u, DFA.eval_append, hq₀ p,
      DFA.eval_replicate]
    change D.stepA^[D.ℓ] (D.stepA^[j] q₀) ∈ S
    change D.stepA^[j] (D.stepA^[D.ℓ] q₀) = s at hj
    rw [← Function.iterate_add_apply, add_comm D.ℓ j, Function.iterate_add_apply, hj]
    exact hs
  have hcontra := hall_μ u
  dsimp only [μ] at hcontra
  rw [hpre_univ, Finset.univ_inter] at hcontra
  change D.m = S.card at hcontra
  omega

/-! ### Section 7: Singleton Start (Proposition 1.11), Reset Accounting & Main Theorems -/

/-- **Proposition 1.11 (Steinberg 2011b / Zhu Prop. 7.1 — Singleton Start)**:
for `m ≥ 2` and synchronizing `A`, there exist `q₀ ∈ C` and `w₀` with `|w₀| ≤ t + 1 + ℓ`
such that `|{q₀} w₀⁻¹ ∩ C| ≥ 2`. -/
theorem singleton_start (hm2 : 2 ≤ D.m) (hSync : A.IsSynchronizing) :
    ∃ q₀ ∈ D.C, ∃ w₀ : List α,
      w₀.length ≤ D.t + 1 + D.ℓ ∧ 2 ≤ ((A.preimage {q₀} w₀) ∩ D.C).card := by
  -- Left column action on `Q → ℚ`
  let colAct : List α → (Q → ℚ) →ₗ[ℚ] (Q → ℚ) := fun w =>
    { toFun := fun v p => v (A.eval p w)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcol_nil : ∀ v : Q → ℚ, colAct [] v = v := fun _ => rfl
  have hcol_append : ∀ u v : List α, ∀ x : Q → ℚ,
      colAct (u ++ v) x = colAct u (colAct v x) := by
    intro u v x; ext p; simp [colAct]
  let zCol : Q → (Q → ℚ) := fun q p =>
    (if D.stepA^[D.ℓ] p = q then (1 : ℚ) else 0) - (D.m : ℚ)⁻¹
  let sumC : (Q → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun v => ∑ p ∈ D.C, v p
      map_add' := fun x y => Finset.sum_add_distrib
      map_smul' := fun c x => by simp [Finset.mul_sum] }
  let HC : Submodule ℚ (Q → ℚ) := LinearMap.ker sumC
  have hmQ : (D.m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.m_pos)
  have hsumC_colAct : ∀ (u : List α) (q : Q),
      sumC (colAct u (zCol q)) =
        (((A.preimage {q} (u ++ List.replicate D.ℓ D.a)) ∩ D.C).card : ℚ) - 1 := by
    intro u q
    simp only [sumC, colAct, zCol, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul]
    have hcard_m : (D.C.card : ℚ) * (D.m : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hmQ
    rw [hcard_m]
    congr 1
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext p
    simp only [Finset.mem_filter, Finset.mem_inter, DFA.mem_preimage, Finset.mem_singleton,
      DFA.eval_append, DFA.eval_replicate, and_comm]
    rfl
  have hsum_zCol : ∑ q ∈ D.C, zCol q = 0 := by
    ext p
    simp only [Finset.sum_apply, zCol, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Pi.zero_apply]
    have h1 : (∑ q ∈ D.C, if D.stepA^[D.ℓ] p = q then (1 : ℚ) else 0) = 1 := by
      rw [Finset.sum_eq_single (D.stepA^[D.ℓ] p)]
      · simp
      · intro q _ hq; simp [Ne.symm hq]
      · intro h; exact absurd (D.hℓ p) h
    have h2 : (D.C.card : ℚ) * (D.m : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hmQ
    rw [h1, h2, sub_self]
  have hfinrank_HC : Module.finrank ℚ HC = D.n - 1 := by
    have hsurj : LinearMap.range sumC = ⊤ := by
      rw [eq_top_iff]
      intro c _
      refine ⟨c • Pi.single D.c₀ (1 : ℚ), ?_⟩
      simp only [map_smul, sumC, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single D.c₀]
      · simp
      · intro p _ hp; simp [Pi.single_eq_of_ne hp]
      · intro h; exact absurd D.c₀_mem h
    have hadd := LinearMap.finrank_range_add_finrank_ker sumC
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at hadd
    change Module.finrank ℚ (LinearMap.ker sumC) = Fintype.card Q - 1
    omega
  -- Wj j = span { colAct u (zCol q) : u.length ≤ j, q ∈ C }
  let Wj : ℕ → Submodule ℚ (Q → ℚ) := fun j =>
    Submodule.span ℚ {v | ∃ u : List α, u.length ≤ j ∧ ∃ q ∈ D.C, v = colAct u (zCol q)}
  have hWj_mono : ∀ {j₁ j₂}, j₁ ≤ j₂ → Wj j₁ ≤ Wj j₂ := by
    intro j₁ j₂ hle
    refine Submodule.span_mono ?_
    rintro v ⟨u, hu, q, hq, rfl⟩
    exact ⟨u, hu.trans hle, q, hq, rfl⟩
  have hW0_le_HC : Wj 0 ≤ HC := by
    rw [Submodule.span_le]
    rintro v ⟨u, hu, q, hq, rfl⟩
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hu)
    subst hu0
    change sumC (colAct [] (zCol q)) = 0
    rw [hsumC_colAct, List.nil_append]
    have hcard1 : ((A.preimage {q} (List.replicate D.ℓ D.a)) ∩ D.C).card = 1 := by
      simpa using D.card_preimage_replicate_inter_C {q} (Finset.singleton_subset_iff.mpr hq) D.ℓ
    rw [hcard1]
    norm_num
  have hW0_dim : D.m - 1 ≤ Module.finrank ℚ (Wj 0) := by
    let C' := D.C.erase D.c₀
    have hC'_card : C'.card = D.m - 1 := by
      rw [Finset.card_erase_of_mem D.c₀_mem]; rfl
    let bvec : C' → Wj 0 := fun q =>
      ⟨zCol q.1, Submodule.subset_span ⟨[], le_rfl, q.1, (Finset.mem_erase.mp q.2).2, rfl⟩⟩
    have hli : LinearIndependent ℚ bvec := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hfun : ∑ q : C', c q • zCol q.1 = 0 := by
        have := congrArg Subtype.val hc
        simpa [bvec] using this
      -- Preimage under stepAC^[ℓ] for any state in C
      have hpre : ∀ q ∈ D.C, ∃ p ∈ D.C, D.stepA^[D.ℓ] p = q := by
        intro q hq
        obtain ⟨⟨p, hp⟩, hpq⟩ := (D.stepAC_iterate_bijective D.ℓ).2 ⟨q, hq⟩
        have hval := congrArg Subtype.val hpq
        rw [D.stepAC_iterate_val] at hval
        exact ⟨p, hp, hval⟩
      obtain ⟨p₀, _, hp₀⟩ := hpre D.c₀ D.c₀_mem
      have hsum_c : ∑ q : C', c q = 0 := by
        have hv0 := congrFun hfun p₀
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zCol, hp₀, Pi.zero_apply] at hv0
        have hterm : ∀ q : C',
            c q * ((if D.c₀ = q.1 then (1 : ℚ) else 0) - (D.m : ℚ)⁻¹) = c q * -(D.m : ℚ)⁻¹ := by
          intro q
          have hne : D.c₀ ≠ q.1 := (Finset.mem_erase.mp q.2).1.symm
          simp [hne]
        simp_rw [hterm, ← Finset.sum_mul] at hv0
        exact (mul_eq_zero.mp hv0).resolve_right (neg_ne_zero.mpr (inv_ne_zero hmQ))
      intro q₀
      obtain ⟨pq, _, hpq⟩ := hpre q₀.1 (Finset.mem_erase.mp q₀.2).2
      have hvq := congrFun hfun pq
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zCol, hpq, Pi.zero_apply,
        mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_c, zero_mul, sub_zero] at hvq
      rw [Finset.sum_eq_single q₀] at hvq
      · simpa using hvq
      · intro q _ hq
        have hne : q₀.1 ≠ q.1 := fun h => hq (Subtype.ext h.symm)
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hle := hli.fintype_card_le_finrank
    rwa [Fintype.card_coe, hC'_card] at hle
  -- Existence of j with ¬ Wj j ≤ HC (from synchronization)
  have hex_not : ∃ j : ℕ, ¬ Wj j ≤ HC := by
    rcases hSync with ⟨w_sync, qs, hqs⟩
    refine ⟨w_sync.length, fun hle => ?_⟩
    let q₀ := D.stepA^[D.ℓ] qs
    have hq₀C : q₀ ∈ D.C := D.hℓ qs
    have hmem : colAct w_sync (zCol q₀) ∈ HC :=
      hle (Submodule.subset_span ⟨w_sync, le_rfl, q₀, hq₀C, rfl⟩)
    change sumC (colAct w_sync (zCol q₀)) = 0 at hmem
    rw [hsumC_colAct] at hmem
    have hpre_univ : A.preimage {q₀} (w_sync ++ List.replicate D.ℓ D.a) = Finset.univ := by
      ext p
      simp only [DFA.mem_preimage, Finset.mem_univ, iff_true, Finset.mem_singleton,
        DFA.eval_append, hqs p, DFA.eval_replicate]
      rfl
    rw [hpre_univ, Finset.univ_inter] at hmem
    have hm1 : (D.m : ℚ) - 1 = 0 := hmem
    have hm2Q : (2 : ℚ) ≤ (D.m : ℚ) := by exact_mod_cast hm2
    linarith
  let j₀ := Nat.find hex_not
  have hj₀_spec : ¬ Wj j₀ ≤ HC := Nat.find_spec hex_not
  have hj₀_pos : 1 ≤ j₀ := by
    by_contra h0
    have : j₀ = 0 := by omega
    rw [this] at hj₀_spec
    exact hj₀_spec hW0_le_HC
  have hj_lt_HC : ∀ j < j₀, Wj j ≤ HC := fun j hj => by
    by_contra hnot; exact Nat.find_min hex_not hj hnot
  -- Strict ascent before j₀: if Wj j = Wj (j + 1) then Wj j contains all Wj k
  have hstrict : ∀ j, j + 1 < j₀ → Wj j < Wj (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hWj_mono (Nat.le_succ j)) fun heq => ?_
    have hclosed : ∀ (b : α) (v : Q → ℚ), v ∈ Wj j → colAct [b] v ∈ Wj j := by
      intro b v hv
      rw [heq]
      induction hv using Submodule.span_induction with
      | mem x hx =>
        rcases hx with ⟨u, hu, q, hq, rfl⟩
        rw [← hcol_append]
        exact Submodule.subset_span ⟨b :: u, by simp; omega, q, hq, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact (Wj (j + 1)).add_mem hx hy
      | smul c x _ hx => rw [map_smul]; exact (Wj (j + 1)).smul_mem c hx
    have hall_in : ∀ (u : List α) (q : Q), q ∈ D.C → colAct u (zCol q) ∈ Wj j := by
      intro u
      induction u with
      | nil => intro q hq; exact Submodule.subset_span ⟨[], Nat.zero_le j, q, hq, rfl⟩
      | cons b u ih =>
        intro q hq
        have : colAct (b :: u) (zCol q) = colAct [b] (colAct u (zCol q)) := hcol_append [b] u _
        rw [this]
        exact hclosed b _ (ih q hq)
    have hWj0_le : Wj j₀ ≤ Wj j := by
      rw [Submodule.span_le]
      rintro v ⟨u, _, q, hq, rfl⟩
      exact hall_in u q hq
    exact hj₀_spec (hWj0_le.trans (hj_lt_HC j (by omega)))
  have hchain : ∀ k ≤ j₀ - 1, Module.finrank ℚ (Wj 0) + k ≤ Module.finrank ℚ (Wj k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 : Module.finrank ℚ (Wj k) < Module.finrank ℚ (Wj (k + 1)) :=
        Submodule.finrank_lt_finrank_of_lt (hstrict k (by omega))
      omega
  have hj₀_le : j₀ ≤ D.t + 1 := by
    have h1 := hchain (j₀ - 1) le_rfl
    have h2 : Module.finrank ℚ (Wj (j₀ - 1)) ≤ Module.finrank ℚ HC :=
      Submodule.finrank_mono (hj_lt_HC (j₀ - 1) (by omega))
    rw [hfinrank_HC] at h2
    have hmt := D.m_add_t
    omega
  -- Extract u with u.length ≤ j₀ and q' ∈ C with sumC (colAct u (zCol q')) ≠ 0
  have hex_nz : ∃ u : List α, u.length ≤ j₀ ∧ ∃ q' ∈ D.C, sumC (colAct u (zCol q')) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hj₀_spec
    rw [Submodule.span_le]
    rintro v ⟨u, hu, q, hq, rfl⟩
    exact hall u hu q hq
  rcases hex_nz with ⟨u, hu, q', hq', hnz⟩
  have hsum0 : ∑ q ∈ D.C, sumC (colAct u (zCol q)) = 0 := by
    rw [← map_sum, ← map_sum, hsum_zCol, map_zero, map_zero]
  have hex_pos : ∃ q₀ ∈ D.C, 0 < sumC (colAct u (zCol q₀)) := by
    by_contra hle
    push Not at hle
    have hall0 : ∀ q ∈ D.C, sumC (colAct u (zCol q)) = 0 := by
      have hge : ∀ q ∈ D.C, 0 ≤ -sumC (colAct u (zCol q)) := fun q hq => neg_nonneg.mpr (hle q hq)
      have hneg0 : ∑ q ∈ D.C, -sumC (colAct u (zCol q)) = 0 := by
        rw [Finset.sum_neg_distrib, hsum0, neg_zero]
      intro q hq
      have := (Finset.sum_eq_zero_iff_of_nonneg hge).mp hneg0 q hq
      linarith
    exact hnz (hall0 q' hq')
  rcases hex_pos with ⟨q₀, hq₀C, hpos⟩
  rw [hsumC_colAct] at hpos
  refine ⟨q₀, hq₀C, u ++ List.replicate D.ℓ D.a, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    omega
  · have h1 : (1 : ℚ) < (((A.preimage {q₀} (u ++ List.replicate D.ℓ D.a)) ∩ D.C).card : ℚ) := by
      linarith
    have h1' : 1 < ((A.preimage {q₀} (u ++ List.replicate D.ℓ D.a)) ∩ D.C).card := by
      exact_mod_cast h1
    omega

/-- Iterative relative extension from any nonempty `S ⊆ C` all the way to `C`. -/
lemma extend_to_cycle (hm2 : 2 ≤ D.m) (hSync : A.IsSynchronizing) :
    ∀ k : ℕ, ∀ S : Finset Q, S ⊆ D.C → S.Nonempty → D.m - S.card ≤ k →
      ∃ X : List α, D.C ⊆ A.preimage S X ∧ X.length ≤ k * (D.n + D.ℓ) := by
  intro k
  induction k with
  | zero =>
    intro S hSC _ hk
    have hcard_le : S.card ≤ D.m := Finset.card_le_card hSC
    have hEq : S = D.C := Finset.eq_of_subset_of_card_le hSC (by unfold m at hk; omega)
    refine ⟨[], ?_, by simp⟩
    rw [DFA.preimage_nil, hEq]
  | succ k ih =>
    intro S hSC hSne hk
    by_cases hEq : S = D.C
    · refine ⟨[], ?_, by simp⟩
      rw [DFA.preimage_nil, hEq]
    · have hSsub : S ⊂ D.C := Finset.ssubset_iff_subset_ne.mpr ⟨hSC, hEq⟩
      obtain ⟨w, hwlen, hwext⟩ := D.short_relative_extension hm2 hSync hSne hSsub
      let x := w ++ List.replicate D.ℓ D.a
      let S' := (A.preimage S x) ∩ D.C
      have hS'C : S' ⊆ D.C := Finset.inter_subset_right
      have hS'ne : S'.Nonempty := Finset.card_pos.mp (lt_trans (Finset.card_pos.mpr hSne) hwext)
      have hS'k : D.m - S'.card ≤ k := by dsimp only [S', x]; omega
      obtain ⟨X', hX'sub, hX'len⟩ := ih S' hS'C hS'ne hS'k
      refine ⟨X' ++ x, ?_, ?_⟩
      · rw [DFA.preimage_append]
        exact hX'sub.trans (A.preimage_mono Finset.inter_subset_left X')
      · simp only [List.length_append, x, List.length_replicate, Nat.succ_mul]
        omega

/-- **Theorem 1.2 (Zhu 2026, Theorem 2.4 — Sharp One-Cluster Reset Bound)**:
`∃ w, A.IsSyncWord w ∧ w.length ≤ (m - 1) * (n - 1) + m * ℓ`. -/
theorem reset_bound (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (D.m - 1) * (D.n - 1) + D.m * D.ℓ := by
  by_cases hm1 : D.m = 1
  · obtain ⟨q₀, hCeq⟩ := Finset.card_eq_one.mp hm1
    refine ⟨List.replicate D.ℓ D.a, ⟨q₀, fun q => ?_⟩, ?_⟩
    · rw [DFA.eval_replicate]
      have hmem : D.stepA^[D.ℓ] q ∈ D.C := D.hℓ q
      rwa [hCeq, Finset.mem_singleton] at hmem
    · simp [hm1]
  · have hm2 : 2 ≤ D.m := by have := D.m_pos; omega
    obtain ⟨q₀, hq₀C, w₀, hw₀len, hw₀card⟩ := D.singleton_start hm2 hSync
    let S₀ := (A.preimage {q₀} w₀) ∩ D.C
    have hS₀C : S₀ ⊆ D.C := Finset.inter_subset_right
    have hS₀ne : S₀.Nonempty := Finset.card_pos.mp (by dsimp only [S₀]; omega)
    have hS₀k : D.m - S₀.card ≤ D.m - 2 := by dsimp only [S₀]; omega
    obtain ⟨X, hXsub, hXlen⟩ := D.extend_to_cycle hm2 hSync (D.m - 2) S₀ hS₀C hS₀ne hS₀k
    refine ⟨List.replicate D.ℓ D.a ++ X ++ w₀, ⟨q₀, fun q => ?_⟩, ?_⟩
    · rw [DFA.eval_append, DFA.eval_append, DFA.eval_replicate]
      have h1 : D.stepA^[D.ℓ] q ∈ D.C := D.hℓ q
      have h2 : D.stepA^[D.ℓ] q ∈ A.preimage S₀ X := hXsub h1
      rw [DFA.mem_preimage] at h2
      have h3 : A.eval (D.stepA^[D.ℓ] q) X ∈ A.preimage {q₀} w₀ := Finset.inter_subset_left h2
      rw [DFA.mem_preimage, Finset.mem_singleton] at h3
      exact h3
    · simp only [List.length_append, List.length_replicate]
      have hmt := D.m_add_t
      have hmn := D.m_le_n
      have hm1' : 1 ≤ D.m := by omega
      have hn1' : 1 ≤ D.n := by omega
      zify [hm2, hm1', hn1', hmn] at hXlen hw₀len hmt ⊢
      nlinarith

end Data

end

end OneCluster

/-! ### Public Main Theorems -/

universe u v

/-- **Zhu (July 2026, Theorem 2.3 — Short Relative Extension)**:
for every synchronizing one-cluster DFA with cycle `C` (`|C| ≥ 2`) and level `ℓ`, and every
nonempty proper `S ⊂ C`, there exists `w` with `|w| ≤ |Q|` such that `|S (w a^ℓ)⁻¹ ∩ C| > |S|`. -/
theorem oneCluster_short_relative_extension
    {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (a : α) (C : Finset Q) (ℓ : ℕ)
    (hC_card : 2 ≤ C.card)
    (hC_inv : ∀ q ∈ C, A.step q a ∈ C)
    (hC_trans : ∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hℓ : ∀ q : Q, (fun x => A.step x a)^[ℓ] q ∈ C)
    (S : Finset Q) (hSne : S.Nonempty) (hSsub : S ⊂ C) :
    ∃ w : List α, w.length ≤ Fintype.card Q ∧
      S.card < ((A.preimage S (w ++ List.replicate ℓ a)) ∩ C).card := by
  let D : OneCluster.Data A :=
    ⟨a, C, ℓ, Finset.card_pos.mp (by omega), hC_inv, hC_trans, hℓ⟩
  exact D.short_relative_extension hC_card hSync hSne hSsub

/-- **Zhu (July 2026, Theorem 2.4 — Sharp One-Cluster Reset Bound)**:
every synchronizing one-cluster DFA on `n` states with cycle `C` (`|C| = m`) and level `ℓ`
admits a synchronizing word of length at most `(m - 1) * (n - 1) + m * ℓ`. -/
theorem oneCluster_reset_bound
    {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (a : α) (C : Finset Q) (ℓ : ℕ)
    (hC_ne : C.Nonempty)
    (hC_inv : ∀ q ∈ C, A.step q a ∈ C)
    (hC_trans : ∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hℓ : ∀ q : Q, (fun x => A.step x a)^[ℓ] q ∈ C) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ (C.card - 1) * (Fintype.card Q - 1) + C.card * ℓ := by
  let D : OneCluster.Data A := ⟨a, C, ℓ, hC_ne, hC_inv, hC_trans, hℓ⟩
  exact D.reset_bound hSync

/-- **Černý's Conjecture for ALL Synchronizing One-Cluster Automata (Zhu, July 2026)**:
every synchronizing one-cluster DFA on `n` states admits a synchronizing word of length
at most `(n - 1) ^ 2`. -/
theorem oneCluster_cerny
    {Q : Type u} {α : Type v} [Fintype Q]
    (A : DFA Q α) (h1C : A.IsOneCluster) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  obtain ⟨D, hml⟩ := OneCluster.exists_data_of_isOneCluster h1C
  obtain ⟨w, hw, hlen⟩ := D.reset_bound hSync
  refine ⟨w, hw, hlen.trans ?_⟩
  have hm_pos : 1 ≤ D.m := D.m_pos
  have hmn : D.m ≤ D.n := D.m_le_n
  have hbound : (D.m - 1) * (D.n - 1) + D.m * D.ℓ ≤ (D.n - 1) ^ 2 := by
    by_cases ht0 : D.m = D.n
    · have hℓ0 : D.ℓ = 0 := by omega
      rw [ht0, hℓ0, mul_zero, add_zero, sq]
    · have hm_le : D.m ≤ D.n - 1 := by omega
      have hℓ_le : D.ℓ ≤ D.n - D.m := by omega
      calc (D.m - 1) * (D.n - 1) + D.m * D.ℓ
          ≤ (D.m - 1) * (D.n - 1) + (D.n - 1) * (D.n - D.m) :=
            Nat.add_le_add_left (Nat.mul_le_mul hm_le hℓ_le) _
        _ = (D.m - 1 + (D.n - D.m)) * (D.n - 1) := by ring
        _ = (D.n - 1) ^ 2 := by
            have : D.m - 1 + (D.n - D.m) = D.n - 1 := by omega
            rw [this, sq]
  exact hbound

/-- Reset-threshold formulation of Černý's Conjecture for one-cluster automata. -/
theorem oneCluster_resetThreshold_le
    {Q : Type u} {α : Type v} [Fintype Q]
    (A : DFA Q α) (h1C : A.IsOneCluster) (hSync : A.IsSynchronizing) :
    A.resetThreshold hSync ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ := oneCluster_cerny A h1C hSync
  exact (A.resetThreshold_le_of_isSyncWord hSync hw).trans hlen

/-- **Dubuc's Theorem (1998)** as an immediate corollary of `oneCluster_cerny`:
Černý's Conjecture holds for all synchronizing circular automata. -/
theorem oneCluster_circular_cerny
    {Q : Type u} {α : Type v} [Fintype Q]
    (A : DFA Q α) (hCirc : A.IsCircular) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have : Nonempty Q := hSync.nonempty
  exact oneCluster_cerny A hCirc.isOneCluster hSync

end Cerny
