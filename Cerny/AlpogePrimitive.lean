import Cerny.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

/-!
# Alpöge-Method Primitive Permutation Group + Defect-1 Theorems (Theorems T11, T12 & T13)

This file formalizes three constructive, linear-algebra-free theorems for automata containing
a primitive permutation group `G = ⟨S⟩` and a deficiency-1 (rank `n - 1`) letter `a`:

* **Theorem T11 (`primitive_defectOne_reset_bound`)**: Every DFA on `n ≥ 2` states with a
  primitive set of permutation letters `S` and a rank-`(n - 1)` letter `a` is *automatically
  synchronizing* and admits a synchronizing word of length at most `2 * n ^ 2 - 6 * n + 5`
  (proved via the 12-line SCC-Coarsening Lemma `sccCount_strict_dec` on the Rystsov digraph `E_k`).
* **Theorem T12 (`primitive_sameCycle_reset_bound` & `primitive_coprimeCycle_cerny`)**:
  If in addition some `b ∈ S` places the unique merged state `z₀` and omitted state `m₀` of `a`
  on the same `b`-cycle of length `r ≥ 2` at distance `d` (`m₀ = z₀ · b^d`, `1 ≤ d < r`,
  `g = Nat.gcd d r`), then `E_{n + g - 2}` is strongly connected, giving
  `w.length ≤ 1 + (n - 2) * (n + g - 1)`. In particular, whenever `Nat.Coprime d r` (`g = 1`),
  the **exact Černý Conjecture `w.length ≤ (n - 1) ^ 2`** holds!
* **Theorem T13 (`double_degree_sccCount_le`, `primitive_defectOne_eccentricity_bound`,
  `primitive_defectOne_zhu_bound`, `primitive_defectOne_card_three_cerny`)**:
  Via the 5-line Double-Degree Condensation Lemma (`c(H) = 1 ∨ c(H) ≤ n - 2` for any finite
  loopless digraph with `outdeg ≥ 1, indeg ≥ 1`), `A` admits a synchronizing word of length at
  most `1 + (n - 2) * (2 * n - 3) = 2 * n ^ 2 - 7 * n + 7` unconditionally (matching Zhu 2024's
  record with zero linear algebra!), `1 + (n - 2) * (D + n - 2)` for Schreier eccentricity `D`,
  and exact Černý `(3 - 1) ^ 2 = 4` for `n = 3`.
-/

namespace Cerny

universe u v

/-! ### Public Definitions -/

/-- A set of letters `S` acts as a primitive permutation group on `Q`: every `b ∈ S` is
bijective, `S*` acts transitively on `Q`, and every `S`-invariant equivalence relation on `Q`
is trivial (`Eq` or `⊤`). -/
def DFA.IsPrimitivePermSet {Q : Type u} {α : Type v} (A : DFA Q α) (S : Set α) : Prop :=
  (∀ b ∈ S, Function.Bijective (fun q => A.step q b)) ∧
  (∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S) ∧ A.eval p g = q) ∧
  (∀ r : Setoid Q, (∀ b ∈ S, ∀ p q, r.r p q → r.r (A.step p b) (A.step q b)) →
    (∀ p q, r.r p q → p = q) ∨ (∀ p q, r.r p q))

/-- A letter `a` has deficiency `1` (rank `n - 1`), witnessed by its unique merged target `z₀`
(`|{z₀} a⁻¹| = 2`) and unique omitted state `m₀` (`|{m₀} a⁻¹| = 0`). -/
def DFA.IsDefectOneLetter {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a : α) (z₀ m₀ : Q) : Prop :=
  z₀ ≠ m₀ ∧
  (A.preimage {z₀} [a]).card = 2 ∧
  (A.preimage {m₀} [a]).card = 0 ∧
  ∀ q : Q, q ≠ z₀ → q ≠ m₀ → (A.preimage {q} [a]).card = 1

/-- Any letter of rank `n - 1` (`|Q · a| + 1 = |Q|`) satisfies `IsDefectOneLetter` for a unique
pair `z₀ ≠ m₀`. -/
theorem exists_isDefectOneLetter_of_card_image_eq_pred {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α) (a : α)
    (hrank : (A.image Finset.univ [a]).card + 1 = Fintype.card Q) :
    ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀ := by
  have himg_ssub : A.image Finset.univ [a] ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    have hne : A.image Finset.univ [a] ≠ Finset.univ := by
      intro heq
      rw [heq, Finset.card_univ] at hrank
      omega
    exact Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩)
  obtain ⟨m₀, _, hm₀_not⟩ := Finset.exists_of_ssubset himg_ssub
  have hm₀_pre : (A.preimage {m₀} [a]).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [DFA.mem_preimage, DFA.eval_singleton, Finset.mem_singleton] at hp
    exact hm₀_not (by rw [DFA.mem_image]; exact ⟨p, Finset.mem_univ p, hp⟩)
  have himg_eq : A.image Finset.univ [a] = Finset.univ.erase m₀ := by
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      exact Finset.mem_erase.mpr ⟨fun h => hm₀_not (h ▸ hq), Finset.mem_univ q⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_univ m₀), Finset.card_univ]
      omega
  have hge1 : ∀ q ∈ Finset.univ.erase m₀, 1 ≤ (A.preimage {q} [a]).card := by
    intro q hq
    rw [← himg_eq, DFA.mem_image] at hq
    rcases hq with ⟨p, _, hp⟩
    exact Finset.card_pos.mpr ⟨p, by rw [DFA.mem_preimage, Finset.mem_singleton]; exact hp⟩
  have hsum_er : ∑ q ∈ Finset.univ.erase m₀, (A.preimage {q} [a]).card = Fintype.card Q := by
    have hsum := A.sum_card_preimage_singleton [a]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m₀), hm₀_pre, zero_add] at hsum
    exact hsum
  have hex_ge2 : ∃ z₀ ∈ Finset.univ.erase m₀, 2 ≤ (A.preimage {z₀} [a]).card := by
    by_contra hall
    push Not at hall
    have hle : ∑ q ∈ Finset.univ.erase m₀, (A.preimage {q} [a]).card ≤
        ∑ _q ∈ Finset.univ.erase m₀, 1 :=
      Finset.sum_le_sum fun q hq => by have := hall q hq; omega
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ m₀),
      Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_id] at hle
    omega
  rcases hex_ge2 with ⟨z₀, hz₀_er, hz₀_ge2⟩
  have hz₀_ne : z₀ ≠ m₀ := (Finset.mem_erase.mp hz₀_er).1
  have hsum_rest :
      (A.preimage {z₀} [a]).card +
        ∑ q ∈ (Finset.univ.erase m₀).erase z₀, (A.preimage {q} [a]).card = Fintype.card Q := by
    rw [Finset.add_sum_erase (Finset.univ.erase m₀) (fun q => (A.preimage {q} [a]).card) hz₀_er,
      hsum_er]
  have hrest_ge : Fintype.card Q - 2 ≤
      ∑ q ∈ (Finset.univ.erase m₀).erase z₀, (A.preimage {q} [a]).card := by
    have h1 : ∑ _q ∈ (Finset.univ.erase m₀).erase z₀, 1 ≤
        ∑ q ∈ (Finset.univ.erase m₀).erase z₀, (A.preimage {q} [a]).card :=
      Finset.sum_le_sum fun q hq => hge1 q (Finset.mem_of_mem_erase hq)
    simp only [Finset.sum_const, Finset.card_erase_of_mem hz₀_er,
      Finset.card_erase_of_mem (Finset.mem_univ m₀), Finset.card_univ, nsmul_eq_mul,
      mul_one, Nat.cast_id] at h1
    omega
  have hz₀_eq2 : (A.preimage {z₀} [a]).card = 2 := by omega
  refine ⟨z₀, m₀, hz₀_ne, hz₀_eq2, hm₀_pre, fun q hqz hqm => ?_⟩
  have hq_mem : q ∈ (Finset.univ.erase m₀).erase z₀ :=
    Finset.mem_erase.mpr ⟨hqz, Finset.mem_erase.mpr ⟨hqm, Finset.mem_univ q⟩⟩
  have hq_ge1 : 1 ≤ (A.preimage {q} [a]).card := hge1 q (Finset.mem_of_mem_erase hq_mem)
  have hrest_eq : ∑ r ∈ (Finset.univ.erase m₀).erase z₀, (A.preimage {r} [a]).card =
      ∑ _r ∈ (Finset.univ.erase m₀).erase z₀, 1 := by
    simp only [Finset.sum_const, Finset.card_erase_of_mem hz₀_er,
      Finset.card_erase_of_mem (Finset.mem_univ m₀), Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.cast_id]
    omega
  have hall1 := (Finset.sum_eq_sum_iff_of_le (fun r hr => hge1 r (Finset.mem_of_mem_erase hr))).mp
    hrest_eq.symm
  exact (hall1 q hq_mem).symm

namespace AlpogePrimitive

section RystsovDigraph

variable {Q : Type u} {α : Type v}

/-- Directed edge `(u → v)` in the length-`k` Rystsov digraph `E_k`: there exists a word `g`
over `S` of length `≤ k` mapping `z₀ ↦ u` and `m₀ ↦ v`. -/
def ryEdge (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (k : ℕ) (u v : Q) : Prop :=
  ∃ g : List α, g.length ≤ k ∧ (∀ b ∈ g, b ∈ S) ∧ A.eval z₀ g = u ∧ A.eval m₀ g = v

/-- Reachability preorder `R_k := ReflTransGen (ryEdge k)`. -/
def ryReach (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (k : ℕ) : Q → Q → Prop :=
  Relation.ReflTransGen (ryEdge A S z₀ m₀ k)

/-- Strongly connected component equivalence relation of `E_k`. -/
def sccSetoid (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (k : ℕ) : Setoid Q where
  r p q := ryReach A S z₀ m₀ k p q ∧ ryReach A S z₀ m₀ k q p
  iseqv := ⟨fun _ => ⟨.refl, .refl⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩,
    fun ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨h1.trans h3, h4.trans h2⟩⟩

/-- Number of strongly connected components of `E_k`. -/
noncomputable def sccCount [Fintype Q] (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (k : ℕ) : ℕ := by
  classical
  exact Fintype.card (Quotient (sccSetoid A S z₀ m₀ k))

lemma ryEdge_mono (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) {j k : ℕ} (hjk : j ≤ k)
    {u v : Q} (h : ryEdge A S z₀ m₀ j u v) : ryEdge A S z₀ m₀ k u v := by
  rcases h with ⟨g, hlen, hS, hz, hm⟩
  exact ⟨g, hlen.trans hjk, hS, hz, hm⟩

lemma ryReach_mono (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) {j k : ℕ} (hjk : j ≤ k)
    {u v : Q} (h : ryReach A S z₀ m₀ j u v) : ryReach A S z₀ m₀ k u v := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (ryEdge_mono A S z₀ m₀ hjk hstep)

lemma ryEdge_step (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (k : ℕ) {b : α} (hb : b ∈ S)
    {u v : Q} (h : ryEdge A S z₀ m₀ k u v) :
    ryEdge A S z₀ m₀ (k + 1) (A.step u b) (A.step v b) := by
  rcases h with ⟨g, hlen, hS, hz, hm⟩
  refine ⟨g ++ [b], by simp; omega, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hS x hx
    · exact hb
  · rw [DFA.eval_append, hz, DFA.eval_singleton]
  · rw [DFA.eval_append, hm, DFA.eval_singleton]

lemma ryReach_step (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (k : ℕ) {b : α} (hb : b ∈ S)
    {u v : Q} (h : ryReach A S z₀ m₀ k u v) :
    ryReach A S z₀ m₀ (k + 1) (A.step u b) (A.step v b) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (ryEdge_step A S z₀ m₀ k hb hstep)

lemma scc_step (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (k : ℕ) {b : α} (hb : b ∈ S)
    {p q : Q} (h : (sccSetoid A S z₀ m₀ k).r p q) :
    (sccSetoid A S z₀ m₀ (k + 1)).r (A.step p b) (A.step q b) :=
  ⟨ryReach_step A S z₀ m₀ k hb h.1, ryReach_step A S z₀ m₀ k hb h.2⟩

lemma sccCount_le_card [Fintype Q] (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (k : ℕ) :
    sccCount A S z₀ m₀ k ≤ Fintype.card Q := by
  classical
  exact Fintype.card_le_of_surjective
    (Quotient.mk (sccSetoid A S z₀ m₀ k)) Quotient.mk_surjective

lemma sccCount_pos [Fintype Q] [Nonempty Q] (A : DFA Q α) (S : Set α) (z₀ m₀ : Q)
    (k : ℕ) : 1 ≤ sccCount A S z₀ m₀ k := by
  classical
  obtain ⟨q⟩ := ‹Nonempty Q›
  exact Fintype.card_pos_iff.mpr ⟨Quotient.mk _ q⟩

lemma sccCount_antitone [Fintype Q] (A : DFA Q α) (S : Set α) (z₀ m₀ : Q)
    {j k : ℕ} (hjk : j ≤ k) :
    sccCount A S z₀ m₀ k ≤ sccCount A S z₀ m₀ j := by
  classical
  let π : Quotient (sccSetoid A S z₀ m₀ j) → Quotient (sccSetoid A S z₀ m₀ k) :=
    Quotient.lift (Quotient.mk (sccSetoid A S z₀ m₀ k)) fun _ _ h =>
      Quotient.sound ⟨ryReach_mono A S z₀ m₀ hjk h.1, ryReach_mono A S z₀ m₀ hjk h.2⟩
  have hsurj : Function.Surjective π := by
    intro y
    refine Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  exact Fintype.card_le_of_surjective π hsurj

/-- **8-Line SCC-Coarsening Lemma**: For a primitive permutation set `S`, whenever `E_k` has
`1 < sccCount k < |Q|`, the next step strictly decreases the number of SCCs:
`sccCount (k + 1) < sccCount k`. -/
theorem sccCount_strict_dec [Fintype Q] [Nonempty Q] {A : DFA Q α} {S : Set α}
    (hPrim : A.IsPrimitivePermSet S) (z₀ m₀ : Q) (k : ℕ)
    (hgt1 : 1 < sccCount A S z₀ m₀ k) (hlt : sccCount A S z₀ m₀ k < Fintype.card Q) :
    sccCount A S z₀ m₀ (k + 1) < sccCount A S z₀ m₀ k := by
  classical
  have hle : sccCount A S z₀ m₀ (k + 1) ≤ sccCount A S z₀ m₀ k :=
    sccCount_antitone A S z₀ m₀ (Nat.le_succ k)
  refine lt_of_le_of_ne hle fun heq => ?_
  let π : Quotient (sccSetoid A S z₀ m₀ k) → Quotient (sccSetoid A S z₀ m₀ (k + 1)) :=
    Quotient.lift (Quotient.mk (sccSetoid A S z₀ m₀ (k + 1))) fun _ _ h =>
      Quotient.sound ⟨ryReach_mono A S z₀ m₀ (Nat.le_succ k) h.1,
        ryReach_mono A S z₀ m₀ (Nat.le_succ k) h.2⟩
  have hsurj : Function.Surjective π := by
    intro y
    refine Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  have hbij : Function.Bijective π :=
    (Fintype.bijective_iff_surjective_and_card π).mpr ⟨hsurj, heq.symm⟩
  have hinv : ∀ b ∈ S, ∀ p q : Q,
      (sccSetoid A S z₀ m₀ k).r p q → (sccSetoid A S z₀ m₀ k).r (A.step p b) (A.step q b) := by
    intro b hb p q hpq
    have hnext := scc_step A S z₀ m₀ k hb hpq
    have hπeq : π (Quotient.mk _ (A.step p b)) = π (Quotient.mk _ (A.step q b)) :=
      Quotient.sound hnext
    exact Quotient.exact (hbij.1 hπeq)
  rcases hPrim.2.2 (sccSetoid A S z₀ m₀ k) hinv with hdiag | hall
  · have hinj : Function.Injective (Quotient.mk (sccSetoid A S z₀ m₀ k)) := fun p q h =>
      hdiag p q (Quotient.exact h)
    have hcard : Fintype.card Q = sccCount A S z₀ m₀ k :=
      Fintype.card_of_bijective ⟨hinj, Quotient.mk_surjective⟩
    omega
  · have hsub : Subsingleton (Quotient (sccSetoid A S z₀ m₀ k)) :=
      ⟨fun x y => Quotient.inductionOn₂ x y fun p q => Quotient.sound (hall p q)⟩
    have hle1 : sccCount A S z₀ m₀ k ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega

/-- Iterating SCC-coarsening: if `sccCount k < |Q|`, then `E_{k + sccCount k - 1}` is
strongly connected (`sccCount = 1`). -/
theorem sccCount_eq_one_of_lt [Fintype Q] [Nonempty Q] {A : DFA Q α} {S : Set α}
    (hPrim : A.IsPrimitivePermSet S) (z₀ m₀ : Q) :
    ∀ d k : ℕ, sccCount A S z₀ m₀ k < Fintype.card Q →
      sccCount A S z₀ m₀ k ≤ d + 1 →
      sccCount A S z₀ m₀ (k + d) = 1 := by
  intro d
  induction d with
  | zero =>
    intro k _ hle
    have hpos := sccCount_pos A S z₀ m₀ k
    simpa using le_antisymm hle hpos
  | succ d ih =>
    intro k hlt hle
    by_cases h1 : sccCount A S z₀ m₀ k = 1
    · have hle' := sccCount_antitone A S z₀ m₀ (Nat.le_add_right k (d + 1))
      have hpos := sccCount_pos A S z₀ m₀ (k + (d + 1))
      omega
    · have hpos := sccCount_pos A S z₀ m₀ k
      have hdec := sccCount_strict_dec hPrim z₀ m₀ k (by omega) hlt
      have hlt' : sccCount A S z₀ m₀ (k + 1) < Fintype.card Q := lt_trans hdec hlt
      have hres := ih (k + 1) hlt' (by omega)
      have hadd : k + 1 + d = k + (d + 1) := by omega
      rwa [hadd] at hres

/-- If `sccCount L = 1`, then `E_L` is strongly connected, so every nonempty proper subset `T`
has an outgoing edge `(u → v)` in `E_L` (`u ∈ T`, `v ∉ T`). -/
private lemma exists_exiting_ryEdge_of_sccCount_eq_one [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (S : Set α) (z₀ m₀ : Q) (L : ℕ) (h1 : sccCount A S z₀ m₀ L = 1)
    {T : Finset Q} (hT_ne : T.Nonempty) (hT_lt : T.card < Fintype.card Q) :
    ∃ u ∈ T, ∃ v, v ∉ T ∧ ryEdge A S z₀ m₀ L u v := by
  classical
  have hsub : Subsingleton (Quotient (sccSetoid A S z₀ m₀ L)) :=
    Fintype.card_le_one_iff_subsingleton.mp h1.le
  rcases hT_ne with ⟨p₀, hp₀⟩
  have hne_univ : T ≠ Finset.univ := fun heq => by rw [heq, Finset.card_univ] at hT_lt; omega
  obtain ⟨q₀, _, hq₀⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T, hne_univ⟩)
  have hreach : ryReach A S z₀ m₀ L p₀ q₀ :=
    (Quotient.exact (hsub.elim (Quotient.mk _ p₀) (Quotient.mk _ q₀))).1
  have hwalk : ∀ x y : Q, ryReach A S z₀ m₀ L x y → x ∈ T → y ∉ T →
      ∃ u ∈ T, ∃ v, v ∉ T ∧ ryEdge A S z₀ m₀ L u v := by
    intro x y hr
    induction hr with
    | refl => intro hx hnx; exact absurd hx hnx
    | @tail b c _ hbc ih =>
      intro hx hnc
      by_cases hb : b ∈ T
      · exact ⟨b, hb, c, hnc, hbc⟩
      · exact ih hx hb
  exact hwalk p₀ q₀ hreach hp₀ hq₀

/-- Exact preimage cardinality formula for a deficiency-1 letter `a`:
`|T a⁻¹| + (m₀ ∈ T ? 1 : 0) = |T| + (z₀ ∈ T ? 1 : 0)`. -/
private lemma card_preimage_defectOne [Fintype Q] [DecidableEq Q] {A : DFA Q α} {a : α}
    {z₀ m₀ : Q} (hDef : A.IsDefectOneLetter a z₀ m₀) (T : Finset Q) :
    (A.preimage T [a]).card + (if m₀ ∈ T then 1 else 0) =
      T.card + (if z₀ ∈ T then 1 else 0) := by
  rw [A.card_preimage_eq_sum_singleton T [a]]
  have hterm : ∀ q ∈ T, (A.preimage {q} [a]).card + (if q = m₀ then 1 else 0) =
      1 + (if q = z₀ then 1 else 0) := by
    intro q _
    by_cases hqz : q = z₀
    · subst hqz
      simp [hDef.1, hDef.2.1]
    · by_cases hqm : q = m₀
      · subst hqm
        simp [hDef.1.symm, hDef.2.2.1]
      · simp [hqz, hqm, hDef.2.2.2 q hqz hqm]
  have hsum := Finset.sum_congr rfl hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_ite_eq'] at hsum
  exact hsum

/-- From `sccCount L = 1` and a deficiency-1 letter `a`, construct a synchronizing word of length
at most `1 + (n - 2) * (L + 1)` (for `n ≥ 2`). -/
theorem exists_syncWord_of_sccCount_eq_one [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} {S : Set α} {a : α} {z₀ m₀ : Q}
    (hBij : ∀ b ∈ S, Function.Bijective (fun q => A.step q b))
    (hDef : A.IsDefectOneLetter a z₀ m₀) (L : ℕ) (h1 : sccCount A S z₀ m₀ L = 1) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ 1 + (Fintype.card Q - 2) * (L + 1) := by
  have hbij_word : ∀ g : List α, (∀ b ∈ g, b ∈ S) → Function.Bijective (fun q => A.eval q g) := by
    intro g
    induction g with
    | nil => intro _; exact Function.bijective_id
    | cons b g ih =>
      intro hS
      have hb := hBij b (hS b List.mem_cons_self)
      have hg := ih (fun x hx => hS x (List.mem_cons_of_mem b hx))
      exact hg.comp hb
  have hext : ∀ T : Finset Q, T.Nonempty → T.card < Fintype.card Q →
      ∃ w : List α, w.length ≤ L + 1 ∧ T.card < (A.preimage T w).card := by
    intro T hTne hTlt
    obtain ⟨u, huT, v, hvNotT, g, hglen, hgS, hgz, hgm⟩ :=
      exists_exiting_ryEdge_of_sccCount_eq_one A S z₀ m₀ L h1 hTne hTlt
    let T' : Finset Q := A.preimage T g
    have hT'_card : T'.card = T.card := by
      have hbg := hbij_word g hgS
      let e : Q ≃ Q := Equiv.ofBijective (fun q => A.eval q g) hbg
      have hpre_eq : T' = T.image e.symm := by
        ext q
        simp only [T', DFA.mem_preimage, Finset.mem_image]
        constructor
        · intro hq
          refine ⟨e q, hq, e.symm_apply_apply q⟩
        · rintro ⟨r, hr, rfl⟩
          change e (e.symm r) ∈ T
          simpa using hr
      rw [hpre_eq, Finset.card_image_of_injective _ e.symm.injective]
    have hz_mem : z₀ ∈ T' := by rw [DFA.mem_preimage, hgz]; exact huT
    have hm_not : m₀ ∉ T' := by rw [DFA.mem_preimage, hgm]; exact hvNotT
    have hcard := card_preimage_defectOne hDef T'
    simp only [hz_mem, hm_not, ↓reduceIte, add_zero] at hcard
    refine ⟨a :: g, by simp; omega, ?_⟩
    rw [DFA.preimage_cons]
    change T.card < (A.preimage T' [a]).card
    omega
  have hex_univ : ∀ d : ℕ, ∀ T : Finset Q, T.Nonempty → Fintype.card Q - T.card ≤ d →
      ∃ w : List α, A.preimage T w = Finset.univ ∧ w.length ≤ d * (L + 1) := by
    intro d
    induction d with
    | zero =>
      intro T _ hle
      have hTle : T.card ≤ Fintype.card Q := Finset.card_le_univ T
      exact ⟨[], by rw [DFA.preimage_nil, Finset.eq_univ_of_card T (by omega)], by simp⟩
    | succ d ih =>
      intro T hTne hle
      by_cases hfull : T.card = Fintype.card Q
      · exact ⟨[], by rw [DFA.preimage_nil, Finset.eq_univ_of_card T hfull], Nat.zero_le _⟩
      · have hTlt : T.card < Fintype.card Q := lt_of_le_of_ne (Finset.card_le_univ T) hfull
        obtain ⟨u, hulen, hugt⟩ := hext T hTne hTlt
        set T' := A.preimage T u
        have hT'ne : T'.Nonempty := Finset.card_pos.mp (lt_trans (Finset.card_pos.mpr hTne) hugt)
        obtain ⟨v, hvuniv, hvlen⟩ := ih T' hT'ne (by omega)
        refine ⟨v ++ u, by rw [DFA.preimage_append]; exact hvuniv, ?_⟩
        rw [List.length_append]
        calc v.length + u.length ≤ d * (L + 1) + (L + 1) := Nat.add_le_add hvlen hulen
          _ = (d + 1) * (L + 1) := by ring
  set S₀ : Finset Q := A.preimage {z₀} [a]
  have hS₀_card : S₀.card = 2 := hDef.2.1
  have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w, hw_univ, hw_len⟩ := hex_univ (Fintype.card Q - 2) S₀ hS₀_ne (by omega)
  refine ⟨w ++ [a], ?_, ?_⟩
  · rw [DFA.isSyncWord_iff_exists_preimage_eq_univ]
    exact ⟨z₀, by rw [DFA.preimage_append]; exact hw_univ⟩
  · simp only [List.length_append, List.length_singleton]
    omega

/-- Phase 1 of Theorem T11: transitivity gives an outgoing non-loop edge in `E_{n - 1}` at
every state, forcing a directed cycle and hence `sccCount (n - 1) < n`. -/
private lemma sccCount_pred_lt_card [Fintype Q] [Nonempty Q] {A : DFA Q α} {S : Set α}
    (hPrim : A.IsPrimitivePermSet S) {z₀ m₀ : Q} (hzm : z₀ ≠ m₀) :
    sccCount A S z₀ m₀ (Fintype.card Q - 1) < Fintype.card Q := by
  classical
  have hbij_word : ∀ g : List α, (∀ b ∈ g, b ∈ S) → Function.Bijective (fun q => A.eval q g) := by
    intro g
    induction g with
    | nil => intro _; exact Function.bijective_id
    | cons b g ih =>
      intro hS
      exact (ih fun x hx => hS x (List.mem_cons_of_mem b hx)).comp
        (hPrim.1 b (hS b List.mem_cons_self))
  -- Every state u is reached from z₀ by an S-word of length ≤ n - 1 (shortest-path shortcutting).
  have hreach_short : ∀ u : Q, ∃ g : List α, g.length ≤ Fintype.card Q - 1 ∧
      (∀ b ∈ g, b ∈ S) ∧ A.eval z₀ g = u := by
    intro u
    have hex : ∃ k : ℕ, ∃ g : List α, g.length = k ∧ (∀ b ∈ g, b ∈ S) ∧ A.eval z₀ g = u := by
      obtain ⟨g, hgS, hgu⟩ := hPrim.2.1 z₀ u
      exact ⟨g.length, g, rfl, hgS, hgu⟩
    obtain ⟨g, hglen, hgS, hgu⟩ := Nat.find_spec hex
    have hmin : ∀ g' : List α, (∀ b ∈ g', b ∈ S) → A.eval z₀ g' = u → g.length ≤ g'.length := by
      intro g' hg'S hg'u
      rw [hglen]
      exact Nat.find_min' hex ⟨g', rfl, hg'S, hg'u⟩
    have hinj : Function.Injective (fun i : Fin (g.length + 1) => A.eval z₀ (g.take i.val)) := by
      intro i j hij
      by_contra hne
      have hcut : ∀ a b : Fin (g.length + 1), a.val < b.val →
          A.eval z₀ (g.take a.val) ≠ A.eval z₀ (g.take b.val) := by
        intro a b hab heq
        let g' := g.take a.val ++ g.drop b.val
        have hg'S : ∀ c ∈ g', c ∈ S := by
          intro c hc
          simp only [g', List.mem_append] at hc
          rcases hc with hc | hc
          · exact hgS c (List.mem_of_mem_take hc)
          · exact hgS c (List.mem_of_mem_drop hc)
        have hg'u : A.eval z₀ g' = u := by
          dsimp [g']
          rw [DFA.eval_append, heq, ← DFA.eval_append, List.take_append_drop]
          exact hgu
        have hb := hmin g' hg'S hg'u
        simp only [g', List.length_append, List.length_take, List.length_drop] at hb
        omega
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · exact hcut i j hlt hij
      · exact hcut j i hgt hij.symm
    have hcard := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_fin] at hcard
    exact ⟨g, by omega, hgS, hgu⟩
  -- Every u has an outgoing non-loop edge in E_{n - 1}.
  have hout : ∀ u : Q, ∃ v : Q, v ≠ u ∧ ryEdge A S z₀ m₀ (Fintype.card Q - 1) u v := by
    intro u
    obtain ⟨g, hglen, hgS, hgu⟩ := hreach_short u
    refine ⟨A.eval m₀ g, ?_, g, hglen, hgS, hgu, rfl⟩
    intro heq
    exact hzm ((hbij_word g hgS).1 (hgu.trans heq.symm))
  choose next hnext_ne hnext_edge using hout
  -- Pigeonhole on iterates of `next` produces two distinct vertices in the same SCC!
  have hnot_inj : ¬ Function.Injective (fun i : Fin (Fintype.card Q + 1) => next^[i.val] z₀) := by
    intro hinj
    have hle := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_fin] at hle
    omega
  simp only [Function.Injective, not_forall] at hnot_inj
  rcases hnot_inj with ⟨i, j, hij_eq, hij_ne⟩
  have hpair : ∃ a b : ℕ, a < b ∧ next^[a] z₀ = next^[b] z₀ := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij_ne) with hlt | hgt
    · exact ⟨i.val, j.val, hlt, hij_eq⟩
    · exact ⟨j.val, i.val, hgt, hij_eq.symm⟩
  rcases hpair with ⟨a, b, hab, heq⟩
  have hiter_reach : ∀ t : ℕ, ∀ x : Q,
      ryReach A S z₀ m₀ (Fintype.card Q - 1) x (next^[t] x) := by
    intro t
    induction t with
    | zero => intro x; exact .refl
    | succ t ih =>
      intro x
      rw [Function.iterate_succ_apply']
      exact (ih x).tail (hnext_edge (next^[t] x))
  let p := next^[a] z₀
  let q := next p
  have hpq_ne : p ≠ q := (hnext_ne p).symm
  have hpq_reach : ryReach A S z₀ m₀ (Fintype.card Q - 1) p q :=
    Relation.ReflTransGen.single (hnext_edge p)
  have hqp_reach : ryReach A S z₀ m₀ (Fintype.card Q - 1) q p := by
    have hsplit : b = (b - a - 1) + 1 + a := by omega
    have hback : next^[b - a - 1] q = p := by
      dsimp only [p, q]
      rw [← Function.iterate_succ_apply next (b - a - 1), ← Function.iterate_add_apply]
      have hidx : (b - a - 1) + 1 + a = b := by omega
      rw [hidx, ← heq]
    rw [← hback]
    exact hiter_reach (b - a - 1) q
  have hmk_eq : Quotient.mk (sccSetoid A S z₀ m₀ (Fintype.card Q - 1)) p =
      Quotient.mk (sccSetoid A S z₀ m₀ (Fintype.card Q - 1)) q :=
    Quotient.sound ⟨hpq_reach, hqp_reach⟩
  -- Non-injective surjection from Q to Quotient forces strictly smaller cardinality!
  refine lt_of_le_of_ne (sccCount_le_card A S z₀ m₀ (Fintype.card Q - 1)) fun hcard_eq => ?_
  have hbij := (Fintype.bijective_iff_surjective_and_card
    (Quotient.mk (sccSetoid A S z₀ m₀ (Fintype.card Q - 1)))).mpr
    ⟨Quotient.mk_surjective, hcard_eq.symm⟩
  exact hpq_ne (hbij.1 hmk_eq)

/-- Elementary pigeonhole modular inverse: for `Nat.Coprime a q` with `2 ≤ q`,
there exists `u < q` with `(u * a) % q = 1`. -/
private lemma exists_mul_mod_eq_one {a q : ℕ} (hq : 2 ≤ q) (hcop : Nat.Coprime a q) :
    ∃ u : ℕ, (u * a) % q = 1 := by
  let φ : Fin q → Fin q := fun t => ⟨(t.val * a) % q, Nat.mod_lt _ (by omega)⟩
  have hφ_inj : Function.Injective φ := by
    intro t₁ t₂ h
    have hval : (t₁.val * a) % q = (t₂.val * a) % q := congrArg Fin.val h
    apply Fin.ext
    by_contra hne
    have hstep : ∀ x y : ℕ, x < y → y < q → (x * a) % q = (y * a) % q → False := by
      intro x y hxy hyq hmod
      have hdvd_mul : q ∣ (y - x) * a := by
        have hmodeq : x * a ≡ y * a [MOD q] := hmod
        have hsub : (y - x) * a = y * a - x * a := Nat.sub_mul y x a
        have hle : x * a ≤ y * a := Nat.mul_le_mul_right a hxy.le
        rw [hsub]
        exact (Nat.modEq_iff_dvd' hle).mp hmodeq
      have hdvd : q ∣ (y - x) := hcop.symm.dvd_of_dvd_mul_right hdvd_mul
      have hpos : 0 < y - x := by omega
      have hle : q ≤ y - x := Nat.le_of_dvd hpos hdvd
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hstep t₁.val t₂.val hlt t₂.isLt hval
    · exact hstep t₂.val t₁.val hgt t₁.isLt hval.symm
  have hφ_surj : Function.Surjective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, rfl⟩ |>.2
  obtain ⟨u, hu⟩ := hφ_surj ⟨1, by omega⟩
  exact ⟨u.val, congrArg Fin.val hu⟩

/-- Phase 1 of Theorem T12: if `b ∈ S` puts `z₀` and `m₀ = b^[d] z₀` on the same cycle of
minimal length `r ≥ 2` (`1 ≤ d < r`, `g = gcd d r`), then `sccCount (r - 1) ≤ (n - r) + g < n`. -/
private lemma sccCount_sameCycle_le [Fintype Q] [DecidableEq Q] {A : DFA Q α} {S : Set α}
    {z₀ m₀ : Q} {b : α} (hb : b ∈ S) (r d : ℕ) (hr : 2 ≤ r) (hd1 : 1 ≤ d) (hdr : d < r)
    (hper : (fun x => A.step x b)^[r] z₀ = z₀)
    (hmin : ∀ k : ℕ, 0 < k → k < r → (fun x => A.step x b)^[k] z₀ ≠ z₀)
    (hm₀ : (fun x => A.step x b)^[d] z₀ = m₀) :
    sccCount A S z₀ m₀ (r - 1) ≤ Fintype.card Q - r + Nat.gcd d r ∧
      Fintype.card Q - r + Nat.gcd d r < Fintype.card Q ∧
      r ≤ Fintype.card Q := by
  classical
  let f : Q → Q := fun x => A.step x b
  let g : ℕ := Nat.gcd d r
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left r (by omega)
  have hg_dvd_d : g ∣ d := Nat.gcd_dvd_left d r
  have hg_dvd_r : g ∣ r := Nat.gcd_dvd_right d r
  have hg_le_d : g ≤ d := Nat.le_of_dvd (by omega) hg_dvd_d
  have hg_lt_r : g < r := lt_of_le_of_lt hg_le_d hdr
  have hiter_mul : ∀ t : ℕ, f^[r * t] z₀ = z₀ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hper]
  have hiter_mod : ∀ t : ℕ, f^[t] z₀ = f^[t % r] z₀ := by
    intro t
    have hdiv : t = t % r + r * (t / r) := by have := Nat.div_add_mod t r; omega
    conv_lhs => rw [hdiv, Function.iterate_add_apply, hiter_mul]
  -- Orbit elements `f^[j] z₀` for `j : Fin r` are pairwise distinct, so `r ≤ |Q|`.
  have hfin_inj : Function.Injective (fun j : Fin r => f^[j.val] z₀) := by
    intro i j hij
    dsimp only at hij
    by_contra hne
    have hstep : ∀ x y : ℕ, x < y → y < r → f^[x] z₀ = f^[y] z₀ → False := by
      intro x y hxy hyr heq
      have hsub : f^[r - x] (f^[x] z₀) = f^[r - x] (f^[y] z₀) := congrArg (f^[r - x]) heq
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at hsub
      have h1 : r - x + x = r := by omega
      have h2 : r - x + y = (y - x) + r := by omega
      rw [h1, h2, hper, Function.iterate_add_apply, hper] at hsub
      exact hmin (y - x) (by omega) (by omega) hsub.symm
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hstep i.val j.val hlt j.isLt hij
    · exact hstep j.val i.val hgt i.isLt hij.symm
  have hr_le_n : r ≤ Fintype.card Q := by
    have := Fintype.card_le_of_injective _ hfin_inj
    simpa using this
  -- Every `j : ℕ` yields edge `f^[j] z₀ → f^[j + d] z₀` in `E_{r - 1}`.
  have hedge : ∀ j : ℕ, ryEdge A S z₀ m₀ (r - 1) (f^[j] z₀) (f^[j + d] z₀) := by
    intro j
    refine ⟨List.replicate (j % r) b, by rw [List.length_replicate]; have := Nat.mod_lt j (by omega : 0 < r); omega,
      fun x hx => by rw [List.mem_replicate] at hx; exact hx.2 ▸ hb, ?_, ?_⟩
    · rw [DFA.eval_replicate]
      exact (hiter_mod j).symm
    · rw [DFA.eval_replicate, ← hm₀, ← Function.iterate_add_apply]
      have hadd : j % r + d ≡ j + d [MOD r] := (Nat.mod_modEq j r).add_right d
      rw [hiter_mod (j % r + d), hiter_mod (j + d), hadd]
  -- Iterating `u` times gives `f^[j] z₀ ⇝ f^[j + u * d] z₀`.
  have hstep_mul : ∀ u j : ℕ, ryReach A S z₀ m₀ (r - 1) (f^[j] z₀) (f^[j + u * d] z₀) := by
    intro u
    induction u with
    | zero => intro j; simp only [zero_mul, add_zero]; exact Relation.ReflTransGen.refl
    | succ u ih =>
      intro j
      have h1 := ih j
      have h2 := hedge (j + u * d)
      have hidx : j + u * d + d = j + (u + 1) * d := by ring
      rw [hidx] at h2
      exact h1.tail h2
  -- Using `Coprime (d / g) (r / g)` with `r / g ≥ 2`, choose `u` with `(u * d) % r = g`.
  let q := r / g
  have hq2 : 2 ≤ q := by
    obtain ⟨k, hk⟩ := hg_dvd_r
    have hqeq : q = k := Nat.mul_div_cancel_left k hg_pos |> fun h => by dsimp [q]; rw [hk, h]
    rw [hqeq]
    by_contra hlt
    have : k ≤ 1 := by omega
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> omega
  have hcop : Nat.Coprime (d / g) q := Nat.coprime_div_gcd_div_gcd hg_pos
  obtain ⟨u, hu⟩ := exists_mul_mod_eq_one hq2 hcop
  have hud_mod : (u * d) % r = g := by
    obtain ⟨a', ha'⟩ := hg_dvd_d
    obtain ⟨k', hk'⟩ := hg_dvd_r
    have hd_div : d / g = a' := by rw [ha']; exact Nat.mul_div_cancel_left a' hg_pos
    have hr_div : q = k' := by dsimp [q]; rw [hk']; exact Nat.mul_div_cancel_left k' hg_pos
    rw [hd_div, hr_div] at hu
    have hmul_eq : (u * d) % r = g * ((u * a') % k') := by
      rw [ha', hk']
      have : u * (g * a') = g * (u * a') := by ring
      rw [this, Nat.mul_mod_mul_left]
    rw [hmul_eq, hu, mul_one]
  -- Hence `f^[j] z₀ ⇝ f^[j + g] z₀`, and by induction `f^[j] z₀ ⇝ f^[j + t * g] z₀`.
  have hstep_g : ∀ j : ℕ, ryReach A S z₀ m₀ (r - 1) (f^[j] z₀) (f^[j + g] z₀) := by
    intro j
    have h := hstep_mul u j
    have hmod_eq : f^[j + u * d] z₀ = f^[j + g] z₀ := by
      rw [hiter_mod (j + u * d), hiter_mod (j + g)]
      have hm1 : (j + u * d) % r = (j + (u * d) % r) % r := by rw [Nat.add_mod_mod]
      rw [hm1, hud_mod]
    rwa [hmod_eq] at h
  have hstep_tg : ∀ t j : ℕ, ryReach A S z₀ m₀ (r - 1) (f^[j] z₀) (f^[j + t * g] z₀) := by
    intro t
    induction t with
    | zero => intro j; simp only [zero_mul, add_zero]; exact Relation.ReflTransGen.refl
    | succ t ih =>
      intro j
      have h1 := ih j
      have h2 := hstep_g (j + t * g)
      have hidx : j + t * g + g = j + (t + 1) * g := by ring
      rw [hidx] at h2
      exact h1.trans h2
  -- Therefore every `f^[j] z₀` lies in the same SCC as `f^[j % g] z₀`!
  have hscc_mod_g : ∀ j : ℕ,
      (sccSetoid A S z₀ m₀ (r - 1)).r (f^[j % g] z₀) (f^[j] z₀) := by
    intro j
    have hdiv : j % g + (j / g) * g = j := by have := Nat.div_add_mod j g; nlinarith
    have hfwd : ryReach A S z₀ m₀ (r - 1) (f^[j % g] z₀) (f^[j] z₀) := by
      have h := hstep_tg (j / g) (j % g)
      rwa [hdiv] at h
    have hbwd : ryReach A S z₀ m₀ (r - 1) (f^[j] z₀) (f^[j % g] z₀) := by
      obtain ⟨k', hk'⟩ := hg_dvd_r
      have hk'pos : 0 < k' := by
        by_contra h0
        have hk0 : k' = 0 := by omega
        rw [hk0, mul_zero] at hk'
        omega
      let t := k' - (j / g) % k'
      have h := hstep_tg t j
      have heq_back : f^[j + t * g] z₀ = f^[j % g] z₀ := by
        rw [hiter_mod (j + t * g), hiter_mod (j % g)]
        have h1 : j + t * g = j % g + (j / g + t) * g := by
          have := Nat.div_add_mod j g; nlinarith
        have hdiv_k : k' ∣ (j / g + t) := by
          refine ⟨j / g / k' + 1, ?_⟩
          have hmod := Nat.div_add_mod (j / g) k'
          have hlt' := Nat.mod_lt (j / g) hk'pos
          have hmul : k' * (j / g / k' + 1) = k' * (j / g / k') + k' := by ring
          dsimp [t]
          omega
        rcases hdiv_k with ⟨c, hc⟩
        have h2 : j + t * g = j % g + r * c := by rw [h1, hc, hk']; ring
        rw [h2, Nat.add_mul_mod_self_left]
      rwa [heq_back] at h
    exact ⟨hfwd, hbwd⟩
  -- Bound `sccCount (r - 1)` by covering `Quotient` with `C_g` (`≤ g`) and `Q \ C` (`n - r`).
  let C : Finset Q := Finset.univ.image (fun j : Fin r => f^[j.val] z₀)
  have hC_card : C.card = r := by
    rw [Finset.card_image_of_injective _ hfin_inj, Finset.card_univ, Fintype.card_fin]
  let mk := Quotient.mk (sccSetoid A S z₀ m₀ (r - 1))
  let G_img : Finset (Quotient (sccSetoid A S z₀ m₀ (r - 1))) :=
    (Finset.range g).image (fun j => mk (f^[j] z₀))
  let Rest_img : Finset (Quotient (sccSetoid A S z₀ m₀ (r - 1))) :=
    (Finset.univ \ C).image mk
  have hcover : (Finset.univ : Finset (Quotient (sccSetoid A S z₀ m₀ (r - 1)))) ⊆
      G_img ∪ Rest_img := by
    intro y _
    refine Quotient.inductionOn y fun x => ?_
    by_cases hxC : x ∈ C
    · rw [Finset.mem_union]; left
      rw [Finset.mem_image] at hxC
      rcases hxC with ⟨j, _, rfl⟩
      rw [Finset.mem_image]
      refine ⟨j.val % g, Finset.mem_range.mpr (Nat.mod_lt j.val hg_pos), ?_⟩
      exact Quotient.sound (hscc_mod_g j.val)
    · rw [Finset.mem_union]; right
      rw [Finset.mem_image]
      exact ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxC⟩, rfl⟩
  have hle_count : sccCount A S z₀ m₀ (r - 1) ≤ Fintype.card Q - r + g := by
    calc sccCount A S z₀ m₀ (r - 1)
        = (Finset.univ : Finset (Quotient (sccSetoid A S z₀ m₀ (r - 1)))).card := Finset.card_univ.symm
      _ ≤ (G_img ∪ Rest_img).card := Finset.card_le_card hcover
      _ ≤ G_img.card + Rest_img.card := Finset.card_union_le _ _
      _ ≤ (Finset.range g).card + (Finset.univ \ C).card :=
            Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = g + (Fintype.card Q - r) := by
            rw [Finset.card_range, Finset.card_sdiff_of_subset (Finset.subset_univ C),
              Finset.card_univ, hC_card]
      _ = Fintype.card Q - r + g := Nat.add_comm _ _
  exact ⟨hle_count, by omega, hr_le_n⟩

/-- **Double-Degree Condensation Lemma (Lemma 1.1 of Round 2)**:
Any nonempty finite loopless digraph `(Q, E)` in which every vertex has `outdeg ≥ 1` and
`indeg ≥ 1` satisfies `c = 1 ∨ c + 2 ≤ |Q|`, where `c` is the number of strongly connected
components. -/
theorem double_degree_sccCount_le [Fintype Q] [Nonempty Q] (E : Q → Q → Prop)
    (s : Setoid Q) [Fintype (Quotient s)]
    (hs : ∀ p q : Q, s.r p q ↔ Relation.ReflTransGen E p q ∧ Relation.ReflTransGen E q p)
    (h_irrefl : ∀ q : Q, ¬ E q q)
    (h_out : ∀ q : Q, ∃ v : Q, E q v)
    (h_in : ∀ q : Q, ∃ u : Q, E u q) :
    Fintype.card (Quotient s) = 1 ∨ Fintype.card (Quotient s) + 2 ≤ Fintype.card Q := by
  classical
  by_cases h1 : Fintype.card (Quotient s) = 1
  · exact Or.inl h1
  right
  -- Condensation partial order on `C := Quotient s`
  let C := Quotient s
  let leC : C → C → Prop :=
    Quotient.lift₂ (fun p q => Relation.ReflTransGen E p q) fun p₁ q₁ p₂ q₂ hp hq => by
      have hp' := (hs p₁ p₂).mp hp
      have hq' := (hs q₁ q₂).mp hq
      exact propext ⟨fun h => hp'.2.trans (h.trans hq'.1), fun h => hp'.1.trans (h.trans hq'.2)⟩
  have hle_refl : ∀ x : C, leC x x := fun x =>
    Quotient.inductionOn x fun _ => .refl
  have hle_trans : ∀ {x y z : C}, leC x y → leC y z → leC x z := fun {x y z} =>
    Quotient.inductionOn₃ x y z fun _ _ _ h1 h2 => h1.trans h2
  have hle_antisymm : ∀ {x y : C}, leC x y → leC y x → x = y := fun {x y} =>
    Quotient.inductionOn₂ x y fun p q h1 h2 => Quotient.sound ((hs p q).mpr ⟨h1, h2⟩)
  have hc_pos : 0 < Fintype.card C := by
    obtain ⟨q₀⟩ := ‹Nonempty Q›
    exact Fintype.card_pos_iff.mpr ⟨Quotient.mk s q₀⟩
  have h1' : Fintype.card C ≠ 1 := h1
  have hc_ge2 : 2 ≤ Fintype.card C := by omega
  -- Pick a maximal element `V` of `C` by minimizing `|{y | V ≤ y}|`.
  have huniv_ne : (Finset.univ : Finset C).Nonempty := Finset.card_pos.mp hc_pos
  have hex_up : ∃ m : ℕ, ∃ x ∈ (Finset.univ : Finset C),
      (Finset.univ.filter (fun y => leC x y)).card = m := by
    rcases huniv_ne with ⟨x₀, hx₀⟩
    exact ⟨_, x₀, hx₀, rfl⟩
  obtain ⟨V, _, hV_eq⟩ := Nat.find_spec hex_up
  have hV_min : ∀ Y : C, (Finset.univ.filter (fun y => leC V y)).card ≤
      (Finset.univ.filter (fun y => leC Y y)).card := fun Y =>
    hV_eq ▸ Nat.find_min' hex_up ⟨Y, Finset.mem_univ Y, rfl⟩
  have hV_max : ∀ Y : C, leC V Y → Y = V := by
    intro Y hVY
    have hsub : Finset.univ.filter (fun z => leC Y z) ⊆
        Finset.univ.filter (fun z => leC V z) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨Finset.mem_univ z, hle_trans hVY hz.2⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (hV_min Y)
    have hV_in : V ∈ Finset.univ.filter (fun z => leC Y z) := by
      rw [heq, Finset.mem_filter]
      exact ⟨Finset.mem_univ V, hle_refl V⟩
    rw [Finset.mem_filter] at hV_in
    exact hle_antisymm hV_in.2 hVY
  -- Pick `W ≠ V` (possible since `|C| ≥ 2`) and a minimal element `U` in `{x | x ≤ W}`.
  have hexW : ∃ W : C, W ≠ V := by
    by_contra hall
    push Not at hall
    have hsub : Subsingleton C := ⟨fun x y => (hall x).trans (hall y).symm⟩
    have hle1 : Fintype.card C ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  obtain ⟨W, hWV⟩ := hexW
  let DW : Finset C := Finset.univ.filter (fun x => leC x W)
  have hDW_ne : DW.Nonempty := ⟨W, Finset.mem_filter.mpr ⟨Finset.mem_univ W, hle_refl W⟩⟩
  have hex_dn : ∃ m : ℕ, ∃ x ∈ DW, (DW.filter (fun y => leC y x)).card = m := by
    rcases hDW_ne with ⟨x₀, hx₀⟩
    exact ⟨_, x₀, hx₀, rfl⟩
  obtain ⟨U, hU_DW, hU_eq⟩ := Nat.find_spec hex_dn
  have hU_min : ∀ Y ∈ DW, (DW.filter (fun y => leC y U)).card ≤
      (DW.filter (fun y => leC y Y)).card := fun Y hY =>
    hU_eq ▸ Nat.find_min' hex_dn ⟨Y, hY, rfl⟩
  have hUW : leC U W := (Finset.mem_filter.mp hU_DW).2
  have hU_isMin : ∀ Y : C, leC Y U → Y = U := by
    intro Y hYU
    have hY_DW : Y ∈ DW := Finset.mem_filter.mpr ⟨Finset.mem_univ Y, hle_trans hYU hUW⟩
    have hsub : DW.filter (fun z => leC z Y) ⊆ DW.filter (fun z => leC z U) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hle_trans hz.2 hYU⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (hU_min Y hY_DW)
    have hU_in : U ∈ DW.filter (fun z => leC z Y) := by
      rw [heq, Finset.mem_filter]
      exact ⟨hU_DW, hle_refl U⟩
    rw [Finset.mem_filter] at hU_in
    exact hle_antisymm hYU hU_in.2
  have hUV : U ≠ V := by
    intro heq
    rw [heq] at hUW
    exact hWV (hV_max W hUW)
  -- Fibers of `Quotient.mk s`
  let fiber : C → Finset Q := fun X => Finset.univ.filter (fun q => Quotient.mk s q = X)
  have hfiber_ge1 : ∀ X : C, 1 ≤ (fiber X).card := by
    intro X
    obtain ⟨q, rfl⟩ := Quotient.exists_rep X
    exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, rfl⟩⟩
  have hfiber_V : 2 ≤ (fiber V).card := by
    obtain ⟨v, hv⟩ := Quotient.exists_rep V
    obtain ⟨v', hvv'⟩ := h_out v
    have hne : v ≠ v' := fun h => h_irrefl v (h ▸ hvv')
    have hv'_eq : Quotient.mk s v' = V := by
      have hle : leC V (Quotient.mk s v') := by
        rw [← hv]; exact Relation.ReflTransGen.single hvv'
      exact hV_max (Quotient.mk s v') hle
    have hsub : ({v, v'} : Finset Q) ⊆ fiber V := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl | rfl
      · exact ⟨Finset.mem_univ _, hv⟩
      · exact ⟨Finset.mem_univ _, hv'_eq⟩
    have h2 : ({v, v'} : Finset Q).card = 2 := Finset.card_pair hne
    calc 2 = ({v, v'} : Finset Q).card := h2.symm
      _ ≤ (fiber V).card := Finset.card_le_card hsub
  have hfiber_U : 2 ≤ (fiber U).card := by
    obtain ⟨u, hu⟩ := Quotient.exists_rep U
    obtain ⟨u', hu'u⟩ := h_in u
    have hne : u ≠ u' := fun h => h_irrefl u (h ▸ hu'u)
    have hu'_eq : Quotient.mk s u' = U := by
      have hle : leC (Quotient.mk s u') U := by
        rw [← hu]; exact Relation.ReflTransGen.single hu'u
      exact hU_isMin (Quotient.mk s u') hle
    have hsub : ({u, u'} : Finset Q) ⊆ fiber U := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [Finset.mem_filter]
      rcases hq with rfl | rfl
      · exact ⟨Finset.mem_univ _, hu⟩
      · exact ⟨Finset.mem_univ _, hu'_eq⟩
    have h2 : ({u, u'} : Finset Q).card = 2 := Finset.card_pair hne
    calc 2 = ({u, u'} : Finset Q).card := h2.symm
      _ ≤ (fiber U).card := Finset.card_le_card hsub
  -- Sum fiber cardinalities to partition `Q`
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset C) : Set C) fiber := by
    intro X _ Y _ hXY
    show Disjoint (fiber X) (fiber Y)
    rw [Finset.disjoint_left]
    intro q hqX hqY
    rw [Finset.mem_filter] at hqX hqY
    exact hXY (hqX.2.symm.trans hqY.2)
  have hunion : (Finset.univ : Finset C).biUnion fiber = Finset.univ := by
    ext q
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, fiber, Finset.mem_filter, iff_true]
    exact ⟨Quotient.mk s q, rfl⟩
  have hsum_card : ∑ X : C, (fiber X).card = Fintype.card Q := by
    rw [← Finset.card_biUnion hdisj, hunion, Finset.card_univ]
  have hU_in_er : U ∈ (Finset.univ : Finset C).erase V :=
    Finset.mem_erase.mpr ⟨hUV, Finset.mem_univ U⟩
  have hsplit : (fiber V).card + ((fiber U).card +
      ∑ X ∈ ((Finset.univ : Finset C).erase V).erase U, (fiber X).card) = Fintype.card Q := by
    rw [Finset.add_sum_erase ((Finset.univ : Finset C).erase V) (fun X => (fiber X).card) hU_in_er,
      Finset.add_sum_erase (Finset.univ : Finset C) (fun X => (fiber X).card) (Finset.mem_univ V),
      hsum_card]
  have hrest : (((Finset.univ : Finset C).erase V).erase U).card ≤
      ∑ X ∈ ((Finset.univ : Finset C).erase V).erase U, (fiber X).card := by
    calc (((Finset.univ : Finset C).erase V).erase U).card
        = ∑ _X ∈ ((Finset.univ : Finset C).erase V).erase U, 1 := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
      _ ≤ ∑ X ∈ ((Finset.univ : Finset C).erase V).erase U, (fiber X).card :=
          Finset.sum_le_sum fun X _ => hfiber_ge1 X
  have hcard_er : (((Finset.univ : Finset C).erase V).erase U).card = Fintype.card C - 2 := by
    rw [Finset.card_erase_of_mem hU_in_er, Finset.card_erase_of_mem (Finset.mem_univ V),
      Finset.card_univ]
    omega
  change Fintype.card C + 2 ≤ Fintype.card Q
  omega

/-- Shortest-path diameter bound for any transitive permutation letter set `S`:
every `u` is reachable from `p` in at most `|Q| - 1` steps over `S`. -/
lemma exists_short_word_of_primitive [Fintype Q] {A : DFA Q α} {S : Set α}
    (hPrim : A.IsPrimitivePermSet S) (p u : Q) :
    ∃ g : List α, g.length ≤ Fintype.card Q - 1 ∧ (∀ b ∈ g, b ∈ S) ∧ A.eval p g = u := by
  classical
  have hex : ∃ k : ℕ, ∃ g : List α, g.length = k ∧ (∀ b ∈ g, b ∈ S) ∧ A.eval p g = u := by
    obtain ⟨g, hgS, hgu⟩ := hPrim.2.1 p u
    exact ⟨g.length, g, rfl, hgS, hgu⟩
  obtain ⟨g, hglen, hgS, hgu⟩ := Nat.find_spec hex
  have hmin : ∀ g' : List α, (∀ b ∈ g', b ∈ S) → A.eval p g' = u → g.length ≤ g'.length := by
    intro g' hg'S hg'u
    rw [hglen]
    exact Nat.find_min' hex ⟨g', rfl, hg'S, hg'u⟩
  have hinj : Function.Injective (fun i : Fin (g.length + 1) => A.eval p (g.take i.val)) := by
    intro i j hij
    by_contra hne
    have hcut : ∀ a b : Fin (g.length + 1), a.val < b.val →
        A.eval p (g.take a.val) ≠ A.eval p (g.take b.val) := by
      intro a b hab heq
      let g' := g.take a.val ++ g.drop b.val
      have hg'S : ∀ c ∈ g', c ∈ S := by
        intro c hc
        simp only [g', List.mem_append] at hc
        rcases hc with hc | hc
        · exact hgS c (List.mem_of_mem_take hc)
        · exact hgS c (List.mem_of_mem_drop hc)
      have hg'u : A.eval p g' = u := by
        dsimp [g']
        rw [DFA.eval_append, heq, ← DFA.eval_append, List.take_append_drop]
        exact hgu
      have hb := hmin g' hg'S hg'u
      simp only [g', List.length_append, List.length_take, List.length_drop] at hb
      omega
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hcut i j hlt hij
    · exact hcut j i hgt hij.symm
  have hcard := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin] at hcard
  exact ⟨g, by omega, hgS, hgu⟩

/-- Application of `double_degree_sccCount_le` to `ryEdge A S z₀ m₀ D`:
whenever both `z₀` and `m₀` reach every state within `D` steps over `S`,
either `sccCount D = 1` or `sccCount D + 2 ≤ |Q|`. -/
theorem sccCount_double_degree_le [Fintype Q] [Nonempty Q] {A : DFA Q α} {S : Set α}
    (hBij : ∀ b ∈ S, Function.Bijective (fun q => A.step q b))
    {z₀ m₀ : Q} (hzm : z₀ ≠ m₀) (D : ℕ)
    (hDz : ∀ q : Q, ∃ g : List α, g.length ≤ D ∧ (∀ b ∈ g, b ∈ S) ∧ A.eval z₀ g = q)
    (hDm : ∀ q : Q, ∃ g : List α, g.length ≤ D ∧ (∀ b ∈ g, b ∈ S) ∧ A.eval m₀ g = q) :
    sccCount A S z₀ m₀ D = 1 ∨ sccCount A S z₀ m₀ D + 2 ≤ Fintype.card Q := by
  classical
  have hbij_word : ∀ g : List α, (∀ b ∈ g, b ∈ S) → Function.Bijective (fun q => A.eval q g) := by
    intro g
    induction g with
    | nil => intro _; exact Function.bijective_id
    | cons b g ih =>
      intro hS
      exact (ih fun x hx => hS x (List.mem_cons_of_mem b hx)).comp
        (hBij b (hS b List.mem_cons_self))
  have hirrefl : ∀ q : Q, ¬ ryEdge A S z₀ m₀ D q q := by
    rintro q ⟨g, _, hgS, hgz, hgm⟩
    exact hzm ((hbij_word g hgS).1 (hgz.trans hgm.symm))
  have hout : ∀ q : Q, ∃ v : Q, ryEdge A S z₀ m₀ D q v := by
    intro q
    obtain ⟨g, hglen, hgS, hgz⟩ := hDz q
    exact ⟨A.eval m₀ g, g, hglen, hgS, hgz, rfl⟩
  have hin : ∀ q : Q, ∃ u : Q, ryEdge A S z₀ m₀ D u q := by
    intro q
    obtain ⟨g, hglen, hgS, hgm⟩ := hDm q
    exact ⟨A.eval z₀ g, g, hglen, hgS, rfl, hgm⟩
  have hres := double_degree_sccCount_le (ryEdge A S z₀ m₀ D) (sccSetoid A S z₀ m₀ D)
    (fun _ _ => Iff.rfl) hirrefl hout hin
  simpa only [sccCount] using hres

end RystsovDigraph

end AlpogePrimitive

/-! ### Main Public Theorems (Theorems T11 & T12) -/

/-- **Theorem T11 (Primitive Permutation Group + Defect-1 Quadratic Reset Bound)**:
Every DFA on `n ≥ 2` states possessing a primitive permutation letter set `S` and a rank-`(n - 1)`
letter `a` is automatically synchronizing and admits a synchronizing word of length at most
`2 * n ^ 2 - 6 * n + 5` (in fact `1 + (n - 2) * (2 * n - 2)`). -/
theorem primitive_defectOne_reset_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S : Set α) (a : α)
    (hPrim : A.IsPrimitivePermSet S)
    (hrank : (A.image Finset.univ [a]).card + 1 = Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ 1 + (Fintype.card Q - 2) * (2 * Fintype.card Q - 2) := by
  obtain ⟨z₀, m₀, hDef⟩ := exists_isDefectOneLetter_of_card_image_eq_pred A a hrank
  have hlt := AlpogePrimitive.sccCount_pred_lt_card hPrim hDef.1
  have hn2 : 2 ≤ Fintype.card Q := by
    have hle := Finset.card_le_univ (A.preimage {z₀} [a])
    have := hDef.2.1
    omega
  have h1 := AlpogePrimitive.sccCount_eq_one_of_lt hPrim z₀ m₀ (Fintype.card Q - 2)
    (Fintype.card Q - 1) hlt (by omega)
  obtain ⟨w, hw, hlen⟩ := AlpogePrimitive.exists_syncWord_of_sccCount_eq_one hPrim.1 hDef
    ((Fintype.card Q - 1) + (Fintype.card Q - 2)) h1
  refine ⟨w, hw, le_trans hlen ?_⟩
  have heq : (Fintype.card Q - 1) + (Fintype.card Q - 2) + 1 = 2 * Fintype.card Q - 2 := by omega
  rw [heq]

/-- **Theorem T12 (General Same-Cycle Bound inside Volkov D6)**:
If `b ∈ S` puts `z₀` and `m₀ = z₀ · b^d` on the same `b`-cycle of length `r ≥ 2` (`1 ≤ d < r`,
`g = gcd d r`), then `A` is automatically synchronizing with reset word length at most
`1 + (n - 2) * (n + g - 1)`. -/
theorem primitive_sameCycle_reset_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S : Set α) (a b : α)
    (z₀ m₀ : Q) (r d : ℕ)
    (hPrim : A.IsPrimitivePermSet S) (hDef : A.IsDefectOneLetter a z₀ m₀)
    (hb : b ∈ S) (hr : 2 ≤ r) (hd1 : 1 ≤ d) (hdr : d < r)
    (hper : (fun x => A.step x b)^[r] z₀ = z₀)
    (hmin : ∀ k : ℕ, 0 < k → k < r → (fun x => A.step x b)^[k] z₀ ≠ z₀)
    (hm₀ : (fun x => A.step x b)^[d] z₀ = m₀) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 1 + (Fintype.card Q - 2) * (Fintype.card Q + Nat.gcd d r - 1) := by
  obtain ⟨hle_c, hlt_n, hr_le_n⟩ :=
    AlpogePrimitive.sccCount_sameCycle_le hb r d hr hd1 hdr hper hmin hm₀
  have hlt_c : AlpogePrimitive.sccCount A S z₀ m₀ (r - 1) < Fintype.card Q :=
    lt_of_le_of_lt hle_c hlt_n
  have hg_pos : 1 ≤ Nat.gcd d r := Nat.gcd_pos_of_pos_left r (by omega)
  let steps := Fintype.card Q - r + Nat.gcd d r - 1
  have h1 := AlpogePrimitive.sccCount_eq_one_of_lt hPrim z₀ m₀ steps (r - 1) hlt_c (by omega)
  obtain ⟨w, hw, hlen⟩ := AlpogePrimitive.exists_syncWord_of_sccCount_eq_one hPrim.1 hDef
    ((r - 1) + steps) h1
  refine ⟨w, hw, le_trans hlen ?_⟩
  have heq : (r - 1) + steps + 1 = Fintype.card Q + Nat.gcd d r - 1 := by
    dsimp [steps]; omega
  rw [heq]

/-- **Theorem T12 Corollary (EXACT ČERNÝ CONJECTURE `(n - 1) ^ 2` inside Volkov D6!)**:
Whenever a primitive permutation group `⟨S⟩` + rank-`(n - 1)` letter `a` (merged `z₀`, omitted `m₀`)
has *some* `b ∈ S` placing `z₀, m₀` on the same `b`-cycle of length `r ≥ 2` at **coprime distance**
`d` (`Nat.Coprime d r` — e.g., `z₀ · b = m₀`, any transposition `(z₀, m₀)`, or any prime-length cycle
containing `z₀, m₀`), `A` is automatically synchronizing and satisfies **Černý's Conjecture**:
`∃ w, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2`! -/
theorem primitive_coprimeCycle_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S : Set α) (a b : α)
    (z₀ m₀ : Q) (r d : ℕ)
    (hPrim : A.IsPrimitivePermSet S) (hDef : A.IsDefectOneLetter a z₀ m₀)
    (hb : b ∈ S) (hr : 2 ≤ r) (hd1 : 1 ≤ d) (hdr : d < r)
    (hcop : Nat.Coprime d r)
    (hper : (fun x => A.step x b)^[r] z₀ = z₀)
    (hmin : ∀ k : ℕ, 0 < k → k < r → (fun x => A.step x b)^[k] z₀ ≠ z₀)
    (hm₀ : (fun x => A.step x b)^[d] z₀ = m₀) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ :=
    primitive_sameCycle_reset_bound A S a b z₀ m₀ r d hPrim hDef hb hr hd1 hdr hper hmin hm₀
  rw [hcop.gcd_eq_one] at hlen
  refine ⟨w, hw, le_trans hlen ?_⟩
  have hn2 : 2 ≤ Fintype.card Q := by
    have hle := Finset.card_le_univ (A.preimage {z₀} [a])
    have := hDef.2.1
    omega
  have hsub : Fintype.card Q + 1 - 1 = Fintype.card Q := by omega
  rw [hsub]
  set k := Fintype.card Q - 2
  have hn : Fintype.card Q = k + 2 := by omega
  have hn1 : Fintype.card Q - 1 = k + 1 := by omega
  rw [hn1, hn, sq]
  nlinarith

/-- **Theorem T13 (Schreier-Eccentricity Reset Bound via Double-Degree Condensation)**:
If `3 ≤ |Q|` and both `z₀` and `m₀` reach every state in at most `D` steps over the primitive
permutation set `S`, then `E_{D + n - 3}` is strongly connected and `A` admits a synchronizing
word of length at most `1 + (n - 2) * (D + n - 2)` (e.g. `D ≤ n / 2` gives `≤ 3/2 * n^2`,
and `D = O(log n)` gives `n^2 + O(n log n)`!). -/
theorem primitive_defectOne_eccentricity_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S : Set α) (a : α)
    (z₀ m₀ : Q) (D : ℕ) (hn3 : 3 ≤ Fintype.card Q)
    (hPrim : A.IsPrimitivePermSet S) (hDef : A.IsDefectOneLetter a z₀ m₀)
    (hDz : ∀ q : Q, ∃ g : List α, g.length ≤ D ∧ (∀ b ∈ g, b ∈ S) ∧ A.eval z₀ g = q)
    (hDm : ∀ q : Q, ∃ g : List α, g.length ≤ D ∧ (∀ b ∈ g, b ∈ S) ∧ A.eval m₀ g = q) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 1 + (Fintype.card Q - 2) * (D + Fintype.card Q - 2) := by
  have hdd := AlpogePrimitive.sccCount_double_degree_le hPrim.1 hDef.1 D hDz hDm
  have h1 : AlpogePrimitive.sccCount A S z₀ m₀ (D + (Fintype.card Q - 3)) = 1 := by
    rcases hdd with h1 | hle
    · have hlt : AlpogePrimitive.sccCount A S z₀ m₀ D < Fintype.card Q := by omega
      exact AlpogePrimitive.sccCount_eq_one_of_lt hPrim z₀ m₀ (Fintype.card Q - 3) D hlt (by omega)
    · have hlt : AlpogePrimitive.sccCount A S z₀ m₀ D < Fintype.card Q := by omega
      exact AlpogePrimitive.sccCount_eq_one_of_lt hPrim z₀ m₀ (Fintype.card Q - 3) D hlt (by omega)
  obtain ⟨w, hw, hlen⟩ :=
    AlpogePrimitive.exists_syncWord_of_sccCount_eq_one hPrim.1 hDef (D + (Fintype.card Q - 3)) h1
  refine ⟨w, hw, le_trans hlen ?_⟩
  have heq : D + (Fintype.card Q - 3) + 1 = D + Fintype.card Q - 2 := by omega
  rw [heq]

/-- **Theorem T13 (Unconditional Zhu 2024 Record `2n^2 - 7n + 7` — Purely Combinatorial!)**:
Every DFA on `n ≥ 2` states possessing a primitive permutation letter set `S` and a rank-`(n - 1)`
letter `a` is automatically synchronizing and admits a synchronizing word of length at most
`1 + (n - 2) * (2 * n - 3)` (`= 2 * n ^ 2 - 7 * n + 7`), matching Zhu's 2024 record with
ZERO linear algebra! -/
theorem primitive_defectOne_zhu_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S : Set α) (a : α)
    (hPrim : A.IsPrimitivePermSet S)
    (hrank : (A.image Finset.univ [a]).card + 1 = Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 1 + (Fintype.card Q - 2) * (2 * Fintype.card Q - 3) := by
  obtain ⟨z₀, m₀, hDef⟩ := exists_isDefectOneLetter_of_card_image_eq_pred A a hrank
  have hn2 : 2 ≤ Fintype.card Q := by
    have hle := Finset.card_le_univ (A.preimage {z₀} [a])
    have := hDef.2.1
    omega
  by_cases hn3 : 3 ≤ Fintype.card Q
  · obtain ⟨w, hw, hlen⟩ := primitive_defectOne_eccentricity_bound A S a z₀ m₀
      (Fintype.card Q - 1) hn3 hPrim hDef
      (fun q => AlpogePrimitive.exists_short_word_of_primitive hPrim z₀ q)
      (fun q => AlpogePrimitive.exists_short_word_of_primitive hPrim m₀ q)
    refine ⟨w, hw, le_trans hlen ?_⟩
    have heq : (Fintype.card Q - 1) + Fintype.card Q - 2 = 2 * Fintype.card Q - 3 := by omega
    rw [heq]
  · -- `|Q| = 2`: the rank-1 letter `[a]` itself synchronizes `Q` in length `1`!
    have hcard2 : Fintype.card Q = 2 := by omega
    have hpre_univ : A.preimage {z₀} [a] = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hDef.2.1, hcard2])
    refine ⟨[a], ?_, by simp⟩
    rw [DFA.isSyncWord_iff_exists_preimage_eq_univ]
    exact ⟨z₀, hpre_univ⟩

/-- **Theorem T13 Corollary (Exact Černý Conjecture for `n = 3`)**:
For `|Q| = 3`, `primitive_defectOne_zhu_bound` yields `w.length ≤ (3 - 1) ^ 2 = 4`. -/
theorem primitive_defectOne_card_three_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S : Set α) (a : α)
    (hcard : Fintype.card Q = 3)
    (hPrim : A.IsPrimitivePermSet S)
    (hrank : (A.image Finset.univ [a]).card + 1 = Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ := primitive_defectOne_zhu_bound A S a hPrim hrank
  refine ⟨w, hw, le_trans hlen ?_⟩
  rw [hcard]
  decide

end Cerny
