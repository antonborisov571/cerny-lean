import Cerny.Defs
import Cerny.SmallCases
import Cerny.AlpogePrimitive
import Cerny.VolkovD6Record
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push

/-!
# World-Record Reset Bound for Full-Transitive Volkov D6 Automata (Theorem T18: `2n² - 8n + 9`)

This file formalizes **Theorem T18** (`docs/round4_d6_leading_and_subshitov.md` §1),
unconditionally proving
`rt(A) ≤ 2n² - 8n + 9 < 2n² - 7n + 7`
for EVERY synchronizing DFA on `n ≥ 4` states in **Zhu (FSTTCS 2024)'s exact full published class**:
every letter has defect `≤ 1` (`Σ = Σ₀ ⊔ Σ₁`, multiple defect-1 letters allowed) and the bijective
letters `Σ₀` generate a **transitive** permutation group on `Q` (both primitive and imprimitive
groups included!). This strictly beats Zhu (2024)'s `2n² - 7n + 7` by `n - 2` for every `n ≥ 4`,
with exact Černý `(n - 1)²` for `n ≤ 4` — using **ZERO cones**:

* **Lemma 1.1 (`VolkovD6Transitive.transReachInf_symm`, `blockCard_eq`)**:
  The orbit-digraph reachability preorder `R_∞` is symmetric (`Π_∞ = Ω_∞`), partitioning `Q` into
  `d` equal-size blocks of size `s₀ = n / d ≥ 2` (`d ∣ n`, `1 ≤ d ≤ n / 2`).
* **Lemma 1.2 (`transWeakCount_eq_blockCount`, `transSCCCount_eq_blockCount_of_zhuF`,
  `transSCCCount_eq_blockCount_of_zhuG`)**:
  Weak coarsening gives `w(n - d - 1) = d`, and Zhu's dual potentials
  `f(k) = c(k) + |Sink(Γ_k)|`, `g(k) = c(k) + |Source(Γ_k)|` strictly decrease while `c(k) > d`,
  yielding `m ≤ k + min(f(k), g(k)) - 2d`.
* **Lemma 1.3 (`blockEscape_extend`)**:
  Zero-cone `ℚ`-subspace block-escape extensibility: whenever `c(m) = d`, every nonempty proper
  subset `S ⊂ Q` extends (`|S w⁻¹| = |S| + 1`) in length `≤ m + d`.
* **Lemma 1.4 (`trans_d_eq_one_bound`)**:
  Full-transitive `d = 1` world-record bound `c(2n - 5) = 1` for all `n ≥ 5`, fusing DAG-Shift
  Teleportation (`VolkovD6.sccCount_half_eq_one_of_acyclic`), dual-potential counting,
  `S₀`-invariant equipartition `(n - 2) ∤ n`, and 2-Block Shift-Isolation.
* **Theorem T18 (`Cerny.transitive_defectOne_ge_five_bound`,
  `Cerny.transitive_defectOne_beats_zhu`, `Cerny.transitive_defectOne_card_le_four_cerny`)**:
  Combining `d = 1`, `2 ≤ d ≤ n / 3`, and `d = n / 2` (`n ≥ 6` even) yields `ext(S) ≤ 2n - 4`
  universally for `n ≥ 5`, hence `w.length ≤ 1 + (n - 2)(2n - 4) = 2n² - 8n + 9 < 2n² - 7n + 7`
  for all `n ≥ 4`, and exact `(n - 1)²` for `n ≤ 4`.
-/

namespace Cerny

universe u v

/-! ### Public Hypothesis Class (Zhu FSTTCS 2024 Full Transitive Defect-≤1 Class) -/

/-- A DFA `A` lies in the full transitive defect-≤1 class witnessed by `(S₀, S₁)` if:
1. Every letter lies in `S₀ ∪ S₁`;
2. Every `b ∈ S₀` acts bijectively on `Q`;
3. Words over `S₀` act transitively on `Q` (primitive or imprimitive!);
4. Every `a ∈ S₁` has rank `n - 1` (defect `1`). -/
def IsTransitiveDefectLeOne {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (S₀ S₁ : Set α) : Prop :=
  (∀ a : α, a ∈ S₀ ∨ a ∈ S₁) ∧
  (∀ b ∈ S₀, Function.Bijective (fun q => A.step q b)) ∧
  (∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q) ∧
  (∀ a ∈ S₁, (A.image Finset.univ [a]).card + 1 = Fintype.card Q)

namespace VolkovD6Transitive

section BasicHelpers

variable {Q : Type u} {α : Type v}

lemma bijective_eval_of_mem {A : DFA Q α} {S₀ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b)) :
    ∀ g : List α, (∀ b ∈ g, b ∈ S₀) → Function.Bijective (fun q => A.eval q g) := by
  intro g
  induction g with
  | nil => intro _; exact Function.bijective_id
  | cons b g ih =>
    intro hS
    exact (ih fun x hx => hS x (List.mem_cons_of_mem b hx)).comp
      (hBij b (hS b List.mem_cons_self))

/-- Exact preimage cardinality formula for a deficiency-1 letter `a`:
`|T a⁻¹| + (m₀ ∈ T ? 1 : 0) = |T| + (z₀ ∈ T ? 1 : 0)`. -/
lemma card_preimage_defectOne [Fintype Q] [DecidableEq Q] {A : DFA Q α} {a : α}
    {z₀ m₀ : Q} (hDef : A.IsDefectOneLetter a z₀ m₀) (T : Finset Q) :
    (A.preimage T [a]).card + (if m₀ ∈ T then 1 else 0) =
      T.card + (if z₀ ∈ T then 1 else 0) := by
  rw [A.card_preimage_eq_sum_singleton T [a]]
  have hterm : ∀ q ∈ T, (A.preimage {q} [a]).card + (if q = m₀ then 1 else 0) =
      1 + (if q = z₀ then 1 else 0) := by
    intro q _
    by_cases hqz : q = z₀
    · subst hqz; simp [hDef.1, hDef.2.1]
    · by_cases hqm : q = m₀
      · subst hqm; simp [hDef.1.symm, hDef.2.2.1]
      · simp [hqz, hqm, hDef.2.2.2 q hqz hqm]
  have hsum := Finset.sum_congr rfl hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_ite_eq'] at hsum
  exact hsum

/-- Preimage cardinality is preserved under any bijective word. -/
lemma card_preimage_of_bijective [Fintype Q] [DecidableEq Q] {A : DFA Q α}
    (T : Finset Q) (g : List α) (hbij : Function.Bijective (fun q => A.eval q g)) :
    (A.preimage T g).card = T.card := by
  let e : Q ≃ Q := Equiv.ofBijective (fun q => A.eval q g) hbij
  have hpre_eq : A.preimage T g = T.image e.symm := by
    ext q
    simp only [DFA.mem_preimage, Finset.mem_image]
    constructor
    · intro hq; exact ⟨e q, hq, e.symm_apply_apply q⟩
    · rintro ⟨r, hr, rfl⟩; change e (e.symm r) ∈ T; simpa using hr
  rw [hpre_eq, Finset.card_image_of_injective _ e.symm.injective]

/-- Every synchronizing DFA with `n ≥ 2` in `IsTransitiveDefectLeOne A S₀ S₁` has a defect-1
letter in `S₁`. -/
lemma exists_defectOne_in_S₁ [Fintype Q] [DecidableEq Q] {A : DFA Q α} {S₀ S₁ : Set α}
    (hSync : A.IsSynchronizing) (hn2 : 2 ≤ Fintype.card Q)
    (hT : IsTransitiveDefectLeOne A S₀ S₁) :
    ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀ := by
  obtain ⟨a, hnotinj⟩ := exists_non_injective_letter A hSync hn2
  have haS₁ : a ∈ S₁ := by
    rcases hT.1 a with ha0 | ha1
    · exact absurd (hT.2.1 a ha0).1 hnotinj
    · exact ha1
  obtain ⟨z₀, m₀, hDef⟩ := exists_isDefectOneLetter_of_card_image_eq_pred A a (hT.2.2.2 a haS₁)
  exact ⟨a, haS₁, z₀, m₀, hDef⟩

/-- Radius-`t` Schreier ball from `q₀` under `S₀`. -/
private noncomputable def schreierBall [Fintype Q] (A : DFA Q α) (S₀ : Set α) (q₀ : Q) (t : ℕ) :
    Finset Q := by
  classical
  exact Finset.univ.filter (fun q => ∃ g : List α, g.length ≤ t ∧ (∀ b ∈ g, b ∈ S₀) ∧ A.eval q₀ g = q)

/-- Transitivity of `⟨S₀⟩` implies Schreier diameter `≤ n - 1`: any `p` reaches any `q` in
length `≤ Fintype.card Q - 1`. -/
lemma exists_short_S₀_word [Fintype Q] [Nonempty Q] {A : DFA Q α} {S₀ : Set α}
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q) (p q : Q) :
    ∃ g : List α, g.length ≤ Fintype.card Q - 1 ∧ (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q := by
  classical
  have hcard : ∀ t : ℕ, min (t + 1) (Fintype.card Q) ≤ (schreierBall A S₀ p t).card := by
    intro t
    induction t with
    | zero =>
      have hmem : p ∈ schreierBall A S₀ p 0 := by
        simp only [schreierBall, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨[], le_rfl, fun _ h => absurd h (List.not_mem_nil), rfl⟩
      exact le_trans (min_le_left 1 (Fintype.card Q)) (Finset.card_pos.mpr ⟨p, hmem⟩)
    | succ t ih =>
      have hsub : schreierBall A S₀ p t ⊆ schreierBall A S₀ p (t + 1) := by
        intro x hx
        simp only [schreierBall, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rcases hx with ⟨g, hlen, hgS, hge⟩
        exact ⟨g, by omega, hgS, hge⟩
      by_cases hfull : schreierBall A S₀ p t = Finset.univ
      · have hfull' : schreierBall A S₀ p (t + 1) = Finset.univ :=
          Finset.eq_univ_iff_forall.mpr fun x => hsub (hfull ▸ Finset.mem_univ x)
        rw [hfull', Finset.card_univ]
        exact min_le_right _ _
      · have hstrict : (schreierBall A S₀ p t).card < (schreierBall A S₀ p (t + 1)).card := by
          refine lt_of_le_of_ne (Finset.card_le_card hsub) fun heq => ?_
          have hball_eq : schreierBall A S₀ p t = schreierBall A S₀ p (t + 1) :=
            Finset.eq_of_subset_of_card_le hsub heq.symm.le
          have hclosed : ∀ x ∈ schreierBall A S₀ p t, ∀ b ∈ S₀,
              A.step x b ∈ schreierBall A S₀ p t := by
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
          have hall : ∀ g : List α, (∀ b ∈ g, b ∈ S₀) → A.eval p g ∈ schreierBall A S₀ p t := by
            intro g
            induction g using List.reverseRecOn with
            | nil =>
              intro _
              simp only [DFA.eval_nil, schreierBall, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨[], Nat.zero_le t, fun _ h => absurd h (List.not_mem_nil), rfl⟩
            | append_singleton g b ihg =>
              intro hS
              rw [DFA.eval_append, DFA.eval_singleton]
              exact hclosed _ (ihg fun c hc => hS c (List.mem_append_left [b] hc)) b
                (hS b (List.mem_append_right g List.mem_cons_self))
          obtain ⟨y, _, hy⟩ := Finset.exists_of_ssubset
            (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hfull⟩)
          obtain ⟨g, hgS, hgy⟩ := hTrans p y
          exact hy (hgy ▸ hall g hgS)
        have hle_n : (schreierBall A S₀ p t).card < Fintype.card Q := by
          have := Finset.card_le_univ (schreierBall A S₀ p t)
          have hne : (schreierBall A S₀ p t).card ≠ Fintype.card Q := fun hc =>
            hfull (Finset.eq_univ_of_card _ hc)
          omega
        omega
  have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos
  have hge := hcard (Fintype.card Q - 1)
  have hle := Finset.card_le_univ (schreierBall A S₀ p (Fintype.card Q - 1))
  have hfull : schreierBall A S₀ p (Fintype.card Q - 1) = Finset.univ :=
    Finset.eq_univ_of_card _ (by omega)
  have hmem : q ∈ schreierBall A S₀ p (Fintype.card Q - 1) := hfull ▸ Finset.mem_univ q
  simpa only [schreierBall, Finset.mem_filter, Finset.mem_univ, true_and] using hmem

/-- Fiber `{q ∈ Q | ⟦q⟧ = X}` of an equivalence relation `r`, independent of decidability instances. -/
noncomputable def fiberOf [Fintype Q] (r : Setoid Q) (X : Quotient r) : Finset Q := by
  classical
  exact Finset.univ.filter (fun q => Quotient.mk r q = X)

lemma mem_fiberOf [Fintype Q] (r : Setoid Q) (X : Quotient r) (q : Q) :
    q ∈ fiberOf r X ↔ Quotient.mk r q = X := by
  classical
  simp [fiberOf]

lemma fiberOf_eq_filter [Fintype Q] (r : Setoid Q) (X : Quotient r)
    [DecidablePred (fun q => Quotient.mk r q = X)] :
    fiberOf r X = Finset.univ.filter (fun q => Quotient.mk r q = X) := by
  ext q
  simp [mem_fiberOf]

/-- Cardinality of `Quotient r`, independent of decidability instances. -/
noncomputable def quotCard [Fintype Q] (r : Setoid Q) : ℕ := by
  classical
  exact Fintype.card (Quotient r)

lemma quotCard_eq_card [Fintype Q] (r : Setoid Q) [inst : Fintype (Quotient r)] :
    quotCard r = @Fintype.card (Quotient r) inst := by
  classical
  unfold quotCard
  exact @Fintype.card_congr (Quotient r) (Quotient r) (Quotient.fintype r) inst (Equiv.refl _)

/-- Any `S₀`-invariant equivalence relation under a transitive permutation set `S₀` partitions `Q`
into equal-size blocks. -/
lemma inv_setoid_block_card_eq [Fintype Q] [Nonempty Q]
    {A : DFA Q α} {S₀ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (r : Setoid Q)
    (hInv : ∀ b ∈ S₀, ∀ p q : Q, r.r p q → r.r (A.step p b) (A.step q b)) :
    ∃ s : ℕ, 1 ≤ s ∧
      (∀ X : Quotient r, (fiberOf r X).card = s) ∧
      quotCard r * s = Fintype.card Q := by
  classical
  have hInv_word : ∀ g : List α, (∀ b ∈ g, b ∈ S₀) →
      ∀ p q : Q, r.r p q → r.r (A.eval p g) (A.eval q g) := by
    intro g
    induction g with
    | nil => intro _ _ _ h; exact h
    | cons b g ih =>
      intro hS p q h
      exact ih (fun c hc => hS c (List.mem_cons_of_mem b hc)) _ _
        (hInv b (hS b List.mem_cons_self) p q h)
  let blk : Quotient r → Finset Q := fiberOf r
  have hle_blk : ∀ X Y : Quotient r, (blk X).card ≤ (blk Y).card := by
    intro X Y
    obtain ⟨p, rfl⟩ := Quotient.exists_rep X
    obtain ⟨q, rfl⟩ := Quotient.exists_rep Y
    obtain ⟨g, hgS, hgpq⟩ := hTrans p q
    have hsub : (blk (Quotient.mk r p)).image (fun x => A.eval x g) ⊆ blk (Quotient.mk r q) := by
      intro y hy
      rw [Finset.mem_image] at hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [mem_fiberOf] at hx ⊢
      have hxp : r.r x p := Quotient.exact hx
      have hgx : r.r (A.eval x g) q := hgpq ▸ hInv_word g hgS x p hxp
      exact Quotient.sound hgx
    have hcard_img : ((blk (Quotient.mk r p)).image (fun x => A.eval x g)).card =
        (blk (Quotient.mk r p)).card :=
      Finset.card_image_of_injective _ (bijective_eval_of_mem hBij g hgS).1
    exact hcard_img ▸ Finset.card_le_card hsub
  obtain ⟨q₀⟩ := ‹Nonempty Q›
  let X₀ : Quotient r := Quotient.mk r q₀
  let s : ℕ := (blk X₀).card
  have hs_pos : 1 ≤ s := Finset.card_pos.mpr ⟨q₀, (mem_fiberOf r X₀ q₀).mpr rfl⟩
  have hblk_eq : ∀ X : Quotient r, (blk X).card = s := fun X =>
    le_antisymm (hle_blk X X₀) (hle_blk X₀ X)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Quotient r)) : Set (Quotient r)) blk := by
    intro X _ Y _ hXY
    show Disjoint (blk X) (blk Y)
    rw [Finset.disjoint_left]
    intro q hqX hqY
    rw [mem_fiberOf] at hqX hqY
    exact hXY (hqX.symm.trans hqY)
  have hsum : quotCard r * s = Fintype.card Q := by
    have hunion : (Finset.univ : Finset (Quotient r)).biUnion blk = Finset.univ := by
      ext q
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, blk, mem_fiberOf, iff_true]
      exact ⟨Quotient.mk r q, rfl⟩
    have hcard := Finset.card_biUnion hdisj
    rw [hunion, Finset.card_univ] at hcard
    change Fintype.card (Quotient r) * s = Fintype.card Q
    calc Fintype.card (Quotient r) * s
        = ∑ _X : Quotient r, s := by simp [Finset.sum_const]
      _ = ∑ X : Quotient r, (blk X).card := Finset.sum_congr rfl fun X _ => (hblk_eq X).symm
      _ = Fintype.card Q := hcard.symm
  exact ⟨s, hs_pos, hblk_eq, hsum⟩

end BasicHelpers

/-! ### Multi-Letter Orbit Digraph `Γ_k = (Q, E_k)` and `Γ_∞ = (Q, E_∞)` -/

section OrbitDigraph

variable {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]

/-- Directed edge `(u → v)` in the length-`k` multi-letter orbit digraph `E_k`. -/
def transEdge (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) (u v : Q) : Prop :=
  ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀ ∧
    ∃ g : List α, g.length ≤ k ∧ (∀ b ∈ g, b ∈ S₀) ∧ A.eval z₀ g = u ∧ A.eval m₀ g = v

/-- Directed edge `(u → v)` in the full orbit digraph `E_∞ = ⋃_k E_k`. -/
def transEdgeInf (A : DFA Q α) (S₀ S₁ : Set α) (u v : Q) : Prop :=
  ∃ k : ℕ, transEdge A S₀ S₁ k u v

/-- Reachability preorder `R_k := ReflTransGen E_k`. -/
def transReach (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) : Q → Q → Prop :=
  Relation.ReflTransGen (transEdge A S₀ S₁ k)

/-- Full reachability preorder `R_∞ := ReflTransGen E_∞`. -/
def transReachInf (A : DFA Q α) (S₀ S₁ : Set α) : Q → Q → Prop :=
  Relation.ReflTransGen (transEdgeInf A S₀ S₁)

/-- Strongly connected component equivalence relation `Π_k` of `Γ_k`. -/
def transSCC (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) : Setoid Q where
  r p q := transReach A S₀ S₁ k p q ∧ transReach A S₀ S₁ k q p
  iseqv := ⟨fun _ => ⟨.refl, .refl⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩,
    fun ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨h1.trans h3, h4.trans h2⟩⟩

/-- Strongly connected component equivalence relation `Π_∞` of `Γ_∞`. -/
def transSCCInf (A : DFA Q α) (S₀ S₁ : Set α) : Setoid Q where
  r p q := transReachInf A S₀ S₁ p q ∧ transReachInf A S₀ S₁ q p
  iseqv := ⟨fun _ => ⟨.refl, .refl⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩,
    fun ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨h1.trans h3, h4.trans h2⟩⟩

/-- Weakly connected component equivalence relation `Ω_k` of `Γ_k`. -/
def transWeak (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) : Setoid Q where
  r := Relation.EqvGen (transEdge A S₀ S₁ k)
  iseqv := Relation.EqvGen.is_equivalence _

/-- Weakly connected component equivalence relation `Ω_∞` of `Γ_∞`. -/
def transWeakInf (A : DFA Q α) (S₀ S₁ : Set α) : Setoid Q where
  r := Relation.EqvGen (transEdgeInf A S₀ S₁)
  iseqv := Relation.EqvGen.is_equivalence _

/-- Number of SCCs `c(k) = |Π_k|`. -/
noncomputable def transSCCCount (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) : ℕ :=
  quotCard (transSCC A S₀ S₁ k)

/-- Number of WCCs `w(k) = |Ω_k|`. -/
noncomputable def transWeakCount (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) : ℕ :=
  quotCard (transWeak A S₀ S₁ k)

/-- Number of blocks `d = |Π_∞|`. -/
noncomputable def blockCount (A : DFA Q α) (S₀ S₁ : Set α) : ℕ :=
  quotCard (transSCCInf A S₀ S₁)

/-- Condensation partial order on `Quotient (transSCC k)`. -/
def condLe (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) :
    Quotient (transSCC A S₀ S₁ k) → Quotient (transSCC A S₀ S₁ k) → Prop :=
  Quotient.lift₂ (fun p q => transReach A S₀ S₁ k p q) fun _ _ _ _ hp hq =>
    propext ⟨fun h => hp.2.trans (h.trans hq.1), fun h => hp.1.trans (h.trans hq.2)⟩

/-- Sink SCC predicate in `Γ_k`. -/
def IsSink (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) (X : Quotient (transSCC A S₀ S₁ k)) : Prop :=
  ∀ Y, condLe A S₀ S₁ k X Y → Y = X

/-- Source SCC predicate in `Γ_k`. -/
def IsSource (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) (X : Quotient (transSCC A S₀ S₁ k)) : Prop :=
  ∀ Y, condLe A S₀ S₁ k Y X → Y = X

/-- Number of sink SCCs `|Sink(Γ_k)|`. -/
noncomputable def transSinkCount (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (IsSink A S₀ S₁ k)).card

/-- Number of source SCCs `|Source(Γ_k)|`. -/
noncomputable def transSourceCount (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (IsSource A S₀ S₁ k)).card

/-- Zhu's dual potentials `f(k) = c(k) + |Sink(Γ_k)|` and `g(k) = c(k) + |Source(Γ_k)|`. -/
noncomputable def zhuF (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) : ℕ :=
  transSCCCount A S₀ S₁ k + transSinkCount A S₀ S₁ k

noncomputable def zhuG (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) : ℕ :=
  transSCCCount A S₀ S₁ k + transSourceCount A S₀ S₁ k

/-! #### Basic Monotonicity, Shift, and Partial-Order Lemmas -/

lemma transEdge_mono (A : DFA Q α) (S₀ S₁ : Set α) {j k : ℕ} (hjk : j ≤ k)
    {u v : Q} (h : transEdge A S₀ S₁ j u v) : transEdge A S₀ S₁ k u v := by
  rcases h with ⟨a, ha, z₀, m₀, hDef, g, hlen, hS, hz, hm⟩
  exact ⟨a, ha, z₀, m₀, hDef, g, hlen.trans hjk, hS, hz, hm⟩

lemma transReach_mono (A : DFA Q α) (S₀ S₁ : Set α) {j k : ℕ} (hjk : j ≤ k)
    {u v : Q} (h : transReach A S₀ S₁ j u v) : transReach A S₀ S₁ k u v := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (transEdge_mono A S₀ S₁ hjk hstep)

lemma transReach_le_inf (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ)
    {u v : Q} (h : transReach A S₀ S₁ k u v) : transReachInf A S₀ S₁ u v := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail ⟨k, hstep⟩

lemma transEdge_irrefl {A : DFA Q α} {S₀ : Set α} (S₁ : Set α)
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b)) (k : ℕ) (q : Q) :
    ¬ transEdge A S₀ S₁ k q q := by
  rintro ⟨_, _, _, _, hDef, g, _, hgS, hgz, hgm⟩
  exact hDef.1 ((bijective_eval_of_mem hBij g hgS).1 (hgz.trans hgm.symm))

lemma transEdgeInf_irrefl {A : DFA Q α} {S₀ : Set α} (S₁ : Set α)
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b)) (q : Q) :
    ¬ transEdgeInf A S₀ S₁ q q := by
  rintro ⟨k, hk⟩
  exact transEdge_irrefl S₁ hBij k q hk

lemma transEdge_step (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) {b : α} (hb : b ∈ S₀)
    {u v : Q} (h : transEdge A S₀ S₁ k u v) :
    transEdge A S₀ S₁ (k + 1) (A.step u b) (A.step v b) := by
  rcases h with ⟨a, ha, z₀, m₀, hDef, g, hlen, hgS, hz, hm⟩
  refine ⟨a, ha, z₀, m₀, hDef, g ++ [b], by simp; omega, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hgS x hx
    · exact hb
  · rw [DFA.eval_append, hz, DFA.eval_singleton]
  · rw [DFA.eval_append, hm, DFA.eval_singleton]

lemma transReach_step (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) {b : α} (hb : b ∈ S₀)
    {u v : Q} (h : transReach A S₀ S₁ k u v) :
    transReach A S₀ S₁ (k + 1) (A.step u b) (A.step v b) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (transEdge_step A S₀ S₁ k hb hstep)

lemma transSCC_step (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) {b : α} (hb : b ∈ S₀)
    {p q : Q} (h : (transSCC A S₀ S₁ k).r p q) :
    (transSCC A S₀ S₁ (k + 1)).r (A.step p b) (A.step q b) :=
  ⟨transReach_step A S₀ S₁ k hb h.1, transReach_step A S₀ S₁ k hb h.2⟩

lemma transWeak_mono (A : DFA Q α) (S₀ S₁ : Set α) {j k : ℕ} (hjk : j ≤ k)
    {p q : Q} (h : (transWeak A S₀ S₁ j).r p q) : (transWeak A S₀ S₁ k).r p q := by
  induction h with
  | rel u v huv => exact Relation.EqvGen.rel u v (transEdge_mono A S₀ S₁ hjk huv)
  | refl x => exact Relation.EqvGen.refl x
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

lemma transWeak_step (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) {b : α} (hb : b ∈ S₀)
    {p q : Q} (h : (transWeak A S₀ S₁ k).r p q) :
    (transWeak A S₀ S₁ (k + 1)).r (A.step p b) (A.step q b) := by
  induction h with
  | rel u v huv => exact Relation.EqvGen.rel _ _ (transEdge_step A S₀ S₁ k hb huv)
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

lemma transEdgeInf_step (A : DFA Q α) (S₀ S₁ : Set α) {b : α} (hb : b ∈ S₀)
    {u v : Q} (h : transEdgeInf A S₀ S₁ u v) :
    transEdgeInf A S₀ S₁ (A.step u b) (A.step v b) := by
  rcases h with ⟨k, hk⟩
  exact ⟨k + 1, transEdge_step A S₀ S₁ k hb hk⟩

lemma transReachInf_step (A : DFA Q α) (S₀ S₁ : Set α) {b : α} (hb : b ∈ S₀)
    {u v : Q} (h : transReachInf A S₀ S₁ u v) :
    transReachInf A S₀ S₁ (A.step u b) (A.step v b) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (transEdgeInf_step A S₀ S₁ hb hstep)

lemma transReachInf_eval (A : DFA Q α) (S₀ S₁ : Set α) :
    ∀ g : List α, (∀ b ∈ g, b ∈ S₀) → ∀ {u v : Q},
      transReachInf A S₀ S₁ u v → transReachInf A S₀ S₁ (A.eval u g) (A.eval v g) := by
  intro g
  induction g with
  | nil => intro _ _ _ h; exact h
  | cons b g ih =>
    intro hS u v h
    exact ih (fun c hc => hS c (List.mem_cons_of_mem b hc))
      (transReachInf_step A S₀ S₁ (hS b List.mem_cons_self) h)

lemma condLe_refl (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ)
    (X : Quotient (transSCC A S₀ S₁ k)) : condLe A S₀ S₁ k X X :=
  Quotient.inductionOn X fun _ => .refl

lemma condLe_trans (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ)
    {X Y Z : Quotient (transSCC A S₀ S₁ k)}
    (h1 : condLe A S₀ S₁ k X Y) (h2 : condLe A S₀ S₁ k Y Z) : condLe A S₀ S₁ k X Z :=
  Quotient.inductionOn₃ X Y Z (fun _ _ _ a b => a.trans b) h1 h2

lemma condLe_antisymm (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ)
    {X Y : Quotient (transSCC A S₀ S₁ k)}
    (h1 : condLe A S₀ S₁ k X Y) (h2 : condLe A S₀ S₁ k Y X) : X = Y :=
  Quotient.inductionOn₂ X Y (fun _ _ a b => Quotient.sound ⟨a, b⟩) h1 h2

/-- Every nonempty finset in `Quotient (transSCC k)` has a `condLe`-maximal element. -/
lemma exists_max_in_finset (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ)
    (F : Finset (Quotient (transSCC A S₀ S₁ k))) (hF : F.Nonempty) :
    ∃ X ∈ F, ∀ Y ∈ F, condLe A S₀ S₁ k X Y → Y = X := by
  classical
  have hex : ∃ c : ℕ, ∃ X ∈ F, (F.filter (fun Y => condLe A S₀ S₁ k X Y)).card = c := by
    rcases hF with ⟨X₀, hX₀⟩; exact ⟨_, X₀, hX₀, rfl⟩
  obtain ⟨X, hXF, hXeq⟩ := Nat.find_spec hex
  have hmin : ∀ Y ∈ F, (F.filter (fun Z => condLe A S₀ S₁ k X Z)).card ≤
      (F.filter (fun Z => condLe A S₀ S₁ k Y Z)).card := fun Y hY =>
    hXeq ▸ Nat.find_min' hex ⟨Y, hY, rfl⟩
  refine ⟨X, hXF, fun Y hYF hXY => ?_⟩
  have hsub : F.filter (fun Z => condLe A S₀ S₁ k Y Z) ⊆
      F.filter (fun Z => condLe A S₀ S₁ k X Z) := by
    intro Z hZ
    rw [Finset.mem_filter] at hZ ⊢
    exact ⟨hZ.1, condLe_trans A S₀ S₁ k hXY hZ.2⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (hmin Y hYF)
  have hXin : X ∈ F.filter (fun Z => condLe A S₀ S₁ k Y Z) := by
    rw [heq, Finset.mem_filter]; exact ⟨hXF, condLe_refl A S₀ S₁ k X⟩
  exact condLe_antisymm A S₀ S₁ k (Finset.mem_filter.mp hXin).2 hXY

/-- Dual: every nonempty finset in `Quotient (transSCC k)` has a `condLe`-minimal element. -/
lemma exists_min_in_finset (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ)
    (F : Finset (Quotient (transSCC A S₀ S₁ k))) (hF : F.Nonempty) :
    ∃ X ∈ F, ∀ Y ∈ F, condLe A S₀ S₁ k Y X → Y = X := by
  classical
  have hex : ∃ c : ℕ, ∃ X ∈ F, (F.filter (fun Y => condLe A S₀ S₁ k Y X)).card = c := by
    rcases hF with ⟨X₀, hX₀⟩; exact ⟨_, X₀, hX₀, rfl⟩
  obtain ⟨X, hXF, hXeq⟩ := Nat.find_spec hex
  have hmin : ∀ Y ∈ F, (F.filter (fun Z => condLe A S₀ S₁ k Z X)).card ≤
      (F.filter (fun Z => condLe A S₀ S₁ k Z Y)).card := fun Y hY =>
    hXeq ▸ Nat.find_min' hex ⟨Y, hY, rfl⟩
  refine ⟨X, hXF, fun Y hYF hYX => ?_⟩
  have hsub : F.filter (fun Z => condLe A S₀ S₁ k Z Y) ⊆
      F.filter (fun Z => condLe A S₀ S₁ k Z X) := by
    intro Z hZ
    rw [Finset.mem_filter] at hZ ⊢
    exact ⟨hZ.1, condLe_trans A S₀ S₁ k hZ.2 hYX⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (hmin Y hYF)
  have hXin : X ∈ F.filter (fun Z => condLe A S₀ S₁ k Z Y) := by
    rw [heq, Finset.mem_filter]; exact ⟨hXF, condLe_refl A S₀ S₁ k X⟩
  exact condLe_antisymm A S₀ S₁ k hYX (Finset.mem_filter.mp hXin).2

lemma transSCCCount_antitone (A : DFA Q α) (S₀ S₁ : Set α) {j k : ℕ} (hjk : j ≤ k) :
    transSCCCount A S₀ S₁ k ≤ transSCCCount A S₀ S₁ j := by
  classical
  let π : Quotient (transSCC A S₀ S₁ j) → Quotient (transSCC A S₀ S₁ k) :=
    Quotient.lift (Quotient.mk (transSCC A S₀ S₁ k)) fun _ _ h =>
      Quotient.sound ⟨transReach_mono A S₀ S₁ hjk h.1, transReach_mono A S₀ S₁ hjk h.2⟩
  have hsurj : Function.Surjective π := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  exact Fintype.card_le_of_surjective π hsurj

lemma transSCCCount_le_card (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) :
    transSCCCount A S₀ S₁ k ≤ Fintype.card Q := by
  classical
  exact Fintype.card_le_of_surjective (Quotient.mk (transSCC A S₀ S₁ k)) Quotient.mk_surjective

lemma blockCount_le_transSCCCount (A : DFA Q α) (S₀ S₁ : Set α) (k : ℕ) :
    blockCount A S₀ S₁ ≤ transSCCCount A S₀ S₁ k := by
  classical
  let π : Quotient (transSCC A S₀ S₁ k) → Quotient (transSCCInf A S₀ S₁) :=
    Quotient.lift (Quotient.mk (transSCCInf A S₀ S₁)) fun _ _ h =>
      Quotient.sound ⟨transReach_le_inf A S₀ S₁ k h.1, transReach_le_inf A S₀ S₁ k h.2⟩
  have hsurj : Function.Surjective π := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  exact Fintype.card_le_of_surjective π hsurj

lemma blockCount_pos [Nonempty Q] (A : DFA Q α) (S₀ S₁ : Set α) :
    1 ≤ blockCount A S₀ S₁ := by
  classical
  obtain ⟨q⟩ := ‹Nonempty Q›
  exact Fintype.card_pos_iff.mpr ⟨Quotient.mk _ q⟩

lemma transWeakCount_antitone (A : DFA Q α) (S₀ S₁ : Set α) {j k : ℕ} (hjk : j ≤ k) :
    transWeakCount A S₀ S₁ k ≤ transWeakCount A S₀ S₁ j := by
  classical
  let π : Quotient (transWeak A S₀ S₁ j) → Quotient (transWeak A S₀ S₁ k) :=
    Quotient.lift (Quotient.mk (transWeak A S₀ S₁ k)) fun _ _ h =>
      Quotient.sound (transWeak_mono A S₀ S₁ hjk h)
  have hsurj : Function.Surjective π := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  exact Fintype.card_le_of_surjective π hsurj

/-! ### Lemma 1.1: Equipartition & Symmetry of `Γ_∞` -/

/-- **Lemma 1.1(a)**: Under transitive bijective `S₀`, full orbit-digraph reachability
`transReachInf` is symmetric (hence `Π_∞ = Ω_∞`). -/
theorem transReachInf_symm {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    {p y : Q} (h : transReachInf A S₀ S₁ p y) :
    transReachInf A S₀ S₁ y p := by
  classical
  let S : Q → Finset Q := fun x => Finset.univ.filter (fun z => transReachInf A S₀ S₁ x z)
  have hsub : S y ⊆ S p := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨Finset.mem_univ z, h.trans hz.2⟩
  obtain ⟨g, hgS, hgp⟩ := hTrans p y
  have himg_sub : (S p).image (fun z => A.eval z g) ⊆ S y := by
    intro w hw
    rw [Finset.mem_image] at hw
    rcases hw with ⟨z, hz, rfl⟩
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨Finset.mem_univ _, hgp ▸ transReachInf_eval A S₀ S₁ g hgS hz.2⟩
  have hcard_le : (S p).card ≤ (S y).card := by
    have hcard_img : ((S p).image (fun z => A.eval z g)).card = (S p).card :=
      Finset.card_image_of_injective _ (bijective_eval_of_mem hBij g hgS).1
    exact hcard_img ▸ Finset.card_le_card himg_sub
  have heq : S y = S p := Finset.eq_of_subset_of_card_le hsub hcard_le
  have hp_in : p ∈ S y := by
    rw [heq, Finset.mem_filter]; exact ⟨Finset.mem_univ p, .refl⟩
  exact (Finset.mem_filter.mp hp_in).2

lemma transSCCInf_iff_reachInf {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    {p q : Q} :
    (transSCCInf A S₀ S₁).r p q ↔ transReachInf A S₀ S₁ p q :=
  ⟨fun h => h.1, fun h => ⟨h, transReachInf_symm hBij hTrans h⟩⟩

lemma transWeakInf_iff_sccInf {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    {p q : Q} :
    (transWeakInf A S₀ S₁).r p q ↔ (transSCCInf A S₀ S₁).r p q := by
  constructor
  · intro h
    induction h with
    | rel u v huv =>
      exact (transSCCInf_iff_reachInf hBij hTrans).mpr (Relation.ReflTransGen.single huv)
    | refl x => exact (transSCCInf A S₀ S₁).iseqv.refl x
    | symm _ _ _ ih => exact (transSCCInf A S₀ S₁).iseqv.symm ih
    | trans _ _ _ _ _ ih1 ih2 => exact (transSCCInf A S₀ S₁).iseqv.trans ih1 ih2
  · intro h
    have hr := h.1
    clear h
    induction hr with
    | refl => exact Relation.EqvGen.refl _
    | tail _ hstep ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hstep)

/-- **Lemma 1.1(b) (Equipartition)**: All `d = blockCount` blocks of `Π_∞` have equal size
`s₀ ≥ 2`, with `d * s₀ = n` (hence `d ∣ n` and `1 ≤ d ≤ n / 2`). -/
theorem blockCard_eq [Nonempty Q] {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (hS₁ : ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀) :
    ∃ s₀ : ℕ, 2 ≤ s₀ ∧
      (∀ B : Quotient (transSCCInf A S₀ S₁),
        (fiberOf (transSCCInf A S₀ S₁) B).card = s₀) ∧
      blockCount A S₀ S₁ * s₀ = Fintype.card Q := by
  classical
  have hInv : ∀ b ∈ S₀, ∀ p q : Q,
      (transSCCInf A S₀ S₁).r p q → (transSCCInf A S₀ S₁).r (A.step p b) (A.step q b) :=
    fun b hb _ _ h => ⟨transReachInf_step A S₀ S₁ hb h.1, transReachInf_step A S₀ S₁ hb h.2⟩
  obtain ⟨s₀, _, hblk, hmul⟩ := inv_setoid_block_card_eq hBij hTrans (transSCCInf A S₀ S₁) hInv
  rcases hS₁ with ⟨a, ha, z₀, m₀, hDef⟩
  have hzm_edge : transEdgeInf A S₀ S₁ z₀ m₀ :=
    ⟨0, a, ha, z₀, m₀, hDef, [], le_rfl, fun _ h => absurd h (List.not_mem_nil), rfl, rfl⟩
  have hzm_rel : (transSCCInf A S₀ S₁).r z₀ m₀ :=
    (transSCCInf_iff_reachInf hBij hTrans).mpr (Relation.ReflTransGen.single hzm_edge)
  let B₀ : Quotient (transSCCInf A S₀ S₁) := Quotient.mk _ z₀
  have hsub : ({z₀, m₀} : Finset Q) ⊆ fiberOf (transSCCInf A S₀ S₁) B₀ := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rw [mem_fiberOf]
    rcases hq with rfl | rfl
    · rfl
    · exact Quotient.sound hzm_rel.symm
  have hs₀_ge2 : 2 ≤ s₀ := by
    rw [← hblk B₀]
    calc 2 = ({z₀, m₀} : Finset Q).card := (Finset.card_pair hDef.1).symm
      _ ≤ (fiberOf (transSCCInf A S₀ S₁) B₀).card := Finset.card_le_card hsub
  exact ⟨s₀, hs₀_ge2, hblk, hmul⟩

/-! ### Lemma 1.2: Weak-Component Coarsening & Zhu's Dual Potential Decrease -/

lemma blockCount_le_transWeakCount {A : DFA Q α} {S₀ : Set α} (S₁ : Set α)
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (k : ℕ) :
    blockCount A S₀ S₁ ≤ transWeakCount A S₀ S₁ k := by
  classical
  let π : Quotient (transWeak A S₀ S₁ k) → Quotient (transSCCInf A S₀ S₁) :=
    Quotient.lift (Quotient.mk (transSCCInf A S₀ S₁)) fun p q h => by
      have hw : (transWeakInf A S₀ S₁).r p q := by
        induction h with
        | rel u v huv => exact Relation.EqvGen.rel u v ⟨k, huv⟩
        | refl x => exact Relation.EqvGen.refl x
        | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
        | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
      exact Quotient.sound ((transWeakInf_iff_sccInf hBij hTrans).mp hw)
  have hsurj : Function.Surjective π := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  exact Fintype.card_le_of_surjective π hsurj

lemma transWeakCount_zero_lt_card {A : DFA Q α} (S₀ : Set α) {S₁ : Set α}
    (hS₁ : ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀) :
    transWeakCount A S₀ S₁ 0 < Fintype.card Q := by
  classical
  have hle : transWeakCount A S₀ S₁ 0 ≤ Fintype.card Q :=
    Fintype.card_le_of_surjective (Quotient.mk (transWeak A S₀ S₁ 0)) Quotient.mk_surjective
  refine lt_of_le_of_ne hle fun heq => ?_
  have hbij := (Fintype.bijective_iff_surjective_and_card
    (Quotient.mk (transWeak A S₀ S₁ 0))).mpr ⟨Quotient.mk_surjective, heq.symm⟩
  rcases hS₁ with ⟨a, ha, z₀, m₀, hDef⟩
  have hedge : transEdge A S₀ S₁ 0 z₀ m₀ :=
    ⟨a, ha, z₀, m₀, hDef, [], le_rfl, fun _ h => absurd h (List.not_mem_nil), rfl, rfl⟩
  exact hDef.1 (hbij.1 (Quotient.sound (Relation.EqvGen.rel z₀ m₀ hedge)))

lemma transWeakCount_strict_dec {A : DFA Q α} {S₀ : Set α} (S₁ : Set α)
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (k : ℕ) (hgt : blockCount A S₀ S₁ < transWeakCount A S₀ S₁ k) :
    transWeakCount A S₀ S₁ (k + 1) < transWeakCount A S₀ S₁ k := by
  classical
  have hle := transWeakCount_antitone A S₀ S₁ (by omega : k ≤ k + 1)
  refine lt_of_le_of_ne hle fun heq => ?_
  let π : Quotient (transWeak A S₀ S₁ k) → Quotient (transWeak A S₀ S₁ (k + 1)) :=
    Quotient.lift (Quotient.mk (transWeak A S₀ S₁ (k + 1))) fun _ _ h =>
      Quotient.sound (transWeak_mono A S₀ S₁ (Nat.le_succ k) h)
  have hsurj : Function.Surjective π := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  have hbij : Function.Bijective π :=
    (Fintype.bijective_iff_surjective_and_card π).mpr ⟨hsurj, heq.symm⟩
  have hInv : ∀ b ∈ S₀, ∀ p q : Q,
      (transWeak A S₀ S₁ k).r p q → (transWeak A S₀ S₁ k).r (A.step p b) (A.step q b) := by
    intro b hb p q hpq
    have hπ : π (Quotient.mk _ (A.step p b)) = π (Quotient.mk _ (A.step q b)) :=
      Quotient.sound (transWeak_step A S₀ S₁ k hb hpq)
    exact Quotient.exact (hbij.1 hπ)
  have hInv_word : ∀ g : List α, (∀ b ∈ g, b ∈ S₀) →
      ∀ p q : Q, (transWeak A S₀ S₁ k).r p q →
        (transWeak A S₀ S₁ k).r (A.eval p g) (A.eval q g) := by
    intro g
    induction g with
    | nil => intro _ _ _ h; exact h
    | cons b g ih =>
      intro hS p q h
      exact ih (fun c hc => hS c (List.mem_cons_of_mem b hc)) _ _
        (hInv b (hS b List.mem_cons_self) p q h)
  have hInf_to_k : ∀ p q : Q, (transSCCInf A S₀ S₁).r p q → (transWeak A S₀ S₁ k).r p q := by
    intro p q hpq
    have hw : (transWeakInf A S₀ S₁).r p q := (transWeakInf_iff_sccInf hBij hTrans).mpr hpq
    clear hpq
    induction hw with
    | rel u v huv =>
      rcases huv with ⟨_, a, ha, z₀, m₀, hDef, g, _, hgS, rfl, rfl⟩
      have h0 : transEdge A S₀ S₁ k z₀ m₀ :=
        ⟨a, ha, z₀, m₀, hDef, [], Nat.zero_le k, fun _ h => absurd h (List.not_mem_nil), rfl, rfl⟩
      exact hInv_word g hgS z₀ m₀ (Relation.EqvGen.rel z₀ m₀ h0)
    | refl x => exact Relation.EqvGen.refl x
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  let ψ : Quotient (transSCCInf A S₀ S₁) → Quotient (transWeak A S₀ S₁ k) :=
    Quotient.lift (Quotient.mk (transWeak A S₀ S₁ k)) fun _ _ h =>
      Quotient.sound (hInf_to_k _ _ h)
  have hψ_surj : Function.Surjective ψ := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  have hle_d : transWeakCount A S₀ S₁ k ≤ blockCount A S₀ S₁ :=
    Fintype.card_le_of_surjective ψ hψ_surj
  omega

/-- **Lemma 1.2(1)**: `transWeakCount (n - d - 1) = d` (every block of `Π_∞` is weakly connected
in `Γ_{n - d - 1}`). -/
theorem transWeakCount_eq_blockCount [Nonempty Q] {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (hS₁ : ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀) :
    transWeakCount A S₀ S₁ (Fintype.card Q - blockCount A S₀ S₁ - 1) = blockCount A S₀ S₁ := by
  have hiter : ∀ t k : ℕ, transWeakCount A S₀ S₁ k ≤ blockCount A S₀ S₁ + t →
      transWeakCount A S₀ S₁ (k + t) = blockCount A S₀ S₁ := by
    intro t
    induction t with
    | zero =>
      intro k hle
      have hge := blockCount_le_transWeakCount S₁ hBij hTrans k
      simpa using le_antisymm hle hge
    | succ t ih =>
      intro k hle
      have hge := blockCount_le_transWeakCount S₁ hBij hTrans k
      by_cases heq : transWeakCount A S₀ S₁ k = blockCount A S₀ S₁
      · have hle' := transWeakCount_antitone A S₀ S₁ (Nat.le_add_right k (t + 1))
        have hge' := blockCount_le_transWeakCount S₁ hBij hTrans (k + (t + 1))
        omega
      · have hdec := transWeakCount_strict_dec S₁ hBij hTrans k (by omega)
        have hres := ih (k + 1) (by omega)
        have hadd : k + 1 + t = k + (t + 1) := by omega
        rwa [hadd] at hres
  have h0 := transWeakCount_zero_lt_card S₀ hS₁
  obtain ⟨s₀, hs₀, _, hmul⟩ := blockCard_eq hBij hTrans hS₁
  have hd_pos := blockCount_pos A S₀ S₁
  have hd_lt : blockCount A S₀ S₁ < Fintype.card Q := by nlinarith
  simpa using hiter (Fintype.card Q - blockCount A S₀ S₁ - 1) 0 (by omega)

/-- Every block of `Π_∞` contains at least one sink SCC and at least one source SCC of `Γ_k`. -/
lemma blockCount_le_transSinkCount {A : DFA Q α} {S₀ : Set α} (S₁ : Set α)
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q) (k : ℕ) :
    blockCount A S₀ S₁ ≤ transSinkCount A S₀ S₁ k := by
  classical
  let π : Quotient (transSCC A S₀ S₁ k) → Quotient (transSCCInf A S₀ S₁) :=
    Quotient.lift (Quotient.mk (transSCCInf A S₀ S₁)) fun _ _ h =>
      Quotient.sound ⟨transReach_le_inf A S₀ S₁ k h.1, transReach_le_inf A S₀ S₁ k h.2⟩
  have hex : ∀ B : Quotient (transSCCInf A S₀ S₁),
      ∃ X : Quotient (transSCC A S₀ S₁ k), π X = B ∧ IsSink A S₀ S₁ k X := by
    intro B
    obtain ⟨q, rfl⟩ := Quotient.exists_rep B
    let F := Finset.univ.filter (fun X => π X = Quotient.mk (transSCCInf A S₀ S₁) q)
    have hF_ne : F.Nonempty := ⟨Quotient.mk _ q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    obtain ⟨X, hXF, hXmax⟩ := exists_max_in_finset A S₀ S₁ k F hF_ne
    have hπX : π X = Quotient.mk (transSCCInf A S₀ S₁) q := (Finset.mem_filter.mp hXF).2
    refine ⟨X, hπX, fun Y hXY => ?_⟩
    have hπY : π Y = π X := by
      refine Quotient.inductionOn₂ X Y (fun x y hxy => ?_) hXY
      exact Quotient.sound ((transSCCInf_iff_reachInf hBij hTrans).mpr
        (transReachInf_symm hBij hTrans (transReach_le_inf A S₀ S₁ k hxy)))
    exact hXmax Y (Finset.mem_filter.mpr ⟨Finset.mem_univ Y, hπY.trans hπX⟩) hXY
  let φ : Quotient (transSCCInf A S₀ S₁) → {X // X ∈ Finset.univ.filter (IsSink A S₀ S₁ k)} :=
    fun B => ⟨(hex B).choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hex B).choose_spec.2⟩⟩
  have hφ_inj : Function.Injective φ := fun B₁ B₂ h => by
    have h1 := congrArg Subtype.val h
    have := congrArg π h1
    rwa [(hex B₁).choose_spec.1, (hex B₂).choose_spec.1] at this
  have hcard := Fintype.card_le_of_injective φ hφ_inj
  rw [Fintype.card_coe] at hcard
  have h1 : blockCount A S₀ S₁ = Fintype.card (Quotient (transSCCInf A S₀ S₁)) :=
    quotCard_eq_card (transSCCInf A S₀ S₁)
  have h2 : (Finset.univ.filter (IsSink A S₀ S₁ k)).card = transSinkCount A S₀ S₁ k := by
    unfold transSinkCount; congr 1
  omega

lemma blockCount_le_transSourceCount {A : DFA Q α} {S₀ : Set α} (S₁ : Set α)
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q) (k : ℕ) :
    blockCount A S₀ S₁ ≤ transSourceCount A S₀ S₁ k := by
  classical
  let π : Quotient (transSCC A S₀ S₁ k) → Quotient (transSCCInf A S₀ S₁) :=
    Quotient.lift (Quotient.mk (transSCCInf A S₀ S₁)) fun _ _ h =>
      Quotient.sound ⟨transReach_le_inf A S₀ S₁ k h.1, transReach_le_inf A S₀ S₁ k h.2⟩
  have hex : ∀ B : Quotient (transSCCInf A S₀ S₁),
      ∃ X : Quotient (transSCC A S₀ S₁ k), π X = B ∧ IsSource A S₀ S₁ k X := by
    intro B
    obtain ⟨q, rfl⟩ := Quotient.exists_rep B
    let F := Finset.univ.filter (fun X => π X = Quotient.mk (transSCCInf A S₀ S₁) q)
    have hF_ne : F.Nonempty := ⟨Quotient.mk _ q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    obtain ⟨X, hXF, hXmin⟩ := exists_min_in_finset A S₀ S₁ k F hF_ne
    have hπX : π X = Quotient.mk (transSCCInf A S₀ S₁) q := (Finset.mem_filter.mp hXF).2
    refine ⟨X, hπX, fun Y hYX => ?_⟩
    have hπY : π Y = π X := by
      refine Quotient.inductionOn₂ Y X (fun y x hyx => ?_) hYX
      exact Quotient.sound ((transSCCInf_iff_reachInf hBij hTrans).mpr
        (transReach_le_inf A S₀ S₁ k hyx))
    exact hXmin Y (Finset.mem_filter.mpr ⟨Finset.mem_univ Y, hπY.trans hπX⟩) hYX
  let φ : Quotient (transSCCInf A S₀ S₁) → {X // X ∈ Finset.univ.filter (IsSource A S₀ S₁ k)} :=
    fun B => ⟨(hex B).choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hex B).choose_spec.2⟩⟩
  have hφ_inj : Function.Injective φ := fun B₁ B₂ h => by
    have h1 := congrArg Subtype.val h
    have := congrArg π h1
    rwa [(hex B₁).choose_spec.1, (hex B₂).choose_spec.1] at this
  have hcard := Fintype.card_le_of_injective φ hφ_inj
  rw [Fintype.card_coe] at hcard
  have h1 : blockCount A S₀ S₁ = Fintype.card (Quotient (transSCCInf A S₀ S₁)) :=
    quotCard_eq_card (transSCCInf A S₀ S₁)
  have h2 : (Finset.univ.filter (IsSource A S₀ S₁ k)).card = transSourceCount A S₀ S₁ k := by
    unfold transSourceCount; congr 1
  omega

lemma transSinkCount_antitone (A : DFA Q α) (S₀ S₁ : Set α) {j k : ℕ} (hjk : j ≤ k) :
    transSinkCount A S₀ S₁ k ≤ transSinkCount A S₀ S₁ j := by
  classical
  let π : Quotient (transSCC A S₀ S₁ j) → Quotient (transSCC A S₀ S₁ k) :=
    Quotient.lift (Quotient.mk (transSCC A S₀ S₁ k)) fun _ _ h =>
      Quotient.sound ⟨transReach_mono A S₀ S₁ hjk h.1, transReach_mono A S₀ S₁ hjk h.2⟩
  have hex : ∀ Y : Quotient (transSCC A S₀ S₁ k), IsSink A S₀ S₁ k Y →
      ∃ X : Quotient (transSCC A S₀ S₁ j), π X = Y ∧ IsSink A S₀ S₁ j X := by
    intro Y hY
    obtain ⟨q, rfl⟩ := Quotient.exists_rep Y
    let F := Finset.univ.filter (fun X => π X = Quotient.mk (transSCC A S₀ S₁ k) q)
    have hF_ne : F.Nonempty := ⟨Quotient.mk _ q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    obtain ⟨X, hXF, hXmax⟩ := exists_max_in_finset A S₀ S₁ j F hF_ne
    have hπX : π X = Quotient.mk (transSCC A S₀ S₁ k) q := (Finset.mem_filter.mp hXF).2
    refine ⟨X, hπX, fun Z hXZ => ?_⟩
    have hπZ : condLe A S₀ S₁ k (π X) (π Z) :=
      Quotient.inductionOn₂ X Z (fun _ _ h => transReach_mono A S₀ S₁ hjk h) hXZ
    rw [hπX] at hπZ
    exact hXmax Z (Finset.mem_filter.mpr ⟨Finset.mem_univ Z, hY (π Z) hπZ⟩) hXZ
  let φ : {Y // Y ∈ Finset.univ.filter (IsSink A S₀ S₁ k)} →
      {X // X ∈ Finset.univ.filter (IsSink A S₀ S₁ j)} := fun ⟨Y, hY⟩ =>
    ⟨(hex Y (Finset.mem_filter.mp hY).2).choose,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hex Y (Finset.mem_filter.mp hY).2).choose_spec.2⟩⟩
  have hφ_inj : Function.Injective φ := by
    rintro ⟨Y₁, hY₁⟩ ⟨Y₂, hY₂⟩ h
    apply Subtype.ext
    have h1 := congrArg (fun x => π x.1) h
    dsimp only [φ] at h1
    rwa [(hex Y₁ (Finset.mem_filter.mp hY₁).2).choose_spec.1,
      (hex Y₂ (Finset.mem_filter.mp hY₂).2).choose_spec.1] at h1
  have hcard := Fintype.card_le_of_injective φ hφ_inj
  simpa only [Fintype.card_coe, transSinkCount] using hcard

lemma transSourceCount_antitone (A : DFA Q α) (S₀ S₁ : Set α) {j k : ℕ} (hjk : j ≤ k) :
    transSourceCount A S₀ S₁ k ≤ transSourceCount A S₀ S₁ j := by
  classical
  let π : Quotient (transSCC A S₀ S₁ j) → Quotient (transSCC A S₀ S₁ k) :=
    Quotient.lift (Quotient.mk (transSCC A S₀ S₁ k)) fun _ _ h =>
      Quotient.sound ⟨transReach_mono A S₀ S₁ hjk h.1, transReach_mono A S₀ S₁ hjk h.2⟩
  have hex : ∀ Y : Quotient (transSCC A S₀ S₁ k), IsSource A S₀ S₁ k Y →
      ∃ X : Quotient (transSCC A S₀ S₁ j), π X = Y ∧ IsSource A S₀ S₁ j X := by
    intro Y hY
    obtain ⟨q, rfl⟩ := Quotient.exists_rep Y
    let F := Finset.univ.filter (fun X => π X = Quotient.mk (transSCC A S₀ S₁ k) q)
    have hF_ne : F.Nonempty := ⟨Quotient.mk _ q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    obtain ⟨X, hXF, hXmin⟩ := exists_min_in_finset A S₀ S₁ j F hF_ne
    have hπX : π X = Quotient.mk (transSCC A S₀ S₁ k) q := (Finset.mem_filter.mp hXF).2
    refine ⟨X, hπX, fun Z hZX => ?_⟩
    have hπZ : condLe A S₀ S₁ k (π Z) (π X) :=
      Quotient.inductionOn₂ Z X (fun _ _ h => transReach_mono A S₀ S₁ hjk h) hZX
    rw [hπX] at hπZ
    exact hXmin Z (Finset.mem_filter.mpr ⟨Finset.mem_univ Z, hY (π Z) hπZ⟩) hZX
  let φ : {Y // Y ∈ Finset.univ.filter (IsSource A S₀ S₁ k)} →
      {X // X ∈ Finset.univ.filter (IsSource A S₀ S₁ j)} := fun ⟨Y, hY⟩ =>
    ⟨(hex Y (Finset.mem_filter.mp hY).2).choose,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hex Y (Finset.mem_filter.mp hY).2).choose_spec.2⟩⟩
  have hφ_inj : Function.Injective φ := by
    rintro ⟨Y₁, hY₁⟩ ⟨Y₂, hY₂⟩ h
    apply Subtype.ext
    have h1 := congrArg (fun x => π x.1) h
    dsimp only [φ] at h1
    rwa [(hex Y₁ (Finset.mem_filter.mp hY₁).2).choose_spec.1,
      (hex Y₂ (Finset.mem_filter.mp hY₂).2).choose_spec.1] at h1
  have hcard := Fintype.card_le_of_injective φ hφ_inj
  simpa only [Fintype.card_coe, transSourceCount] using hcard

lemma zhuF_strict_dec [Nonempty Q] {A : DFA Q α} {S₀ : Set α} (S₁ : Set α)
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (k : ℕ) (hgt : blockCount A S₀ S₁ < transSCCCount A S₀ S₁ k) :
    zhuF A S₀ S₁ (k + 1) < zhuF A S₀ S₁ k := by
  classical
  have hc_le := transSCCCount_antitone A S₀ S₁ (by omega : k ≤ k + 1)
  have hs_le := transSinkCount_antitone A S₀ S₁ (by omega : k ≤ k + 1)
  refine lt_of_le_of_ne (Nat.add_le_add hc_le hs_le) fun heq => ?_
  have hc_eq : transSCCCount A S₀ S₁ (k + 1) = transSCCCount A S₀ S₁ k := by
    dsimp only [zhuF] at heq; omega
  have hs_eq : transSinkCount A S₀ S₁ (k + 1) = transSinkCount A S₀ S₁ k := by
    dsimp only [zhuF] at heq; omega
  let π : Quotient (transSCC A S₀ S₁ k) → Quotient (transSCC A S₀ S₁ (k + 1)) :=
    Quotient.lift (Quotient.mk (transSCC A S₀ S₁ (k + 1))) fun _ _ h =>
      Quotient.sound ⟨transReach_mono A S₀ S₁ (Nat.le_succ k) h.1,
        transReach_mono A S₀ S₁ (Nat.le_succ k) h.2⟩
  have hπ_surj : Function.Surjective π := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  have hπ_bij : Function.Bijective π :=
    (Fintype.bijective_iff_surjective_and_card π).mpr ⟨hπ_surj, hc_eq.symm⟩
  -- `transSCC k` is `S₀`-invariant
  have hInv : ∀ b ∈ S₀, ∀ p q : Q,
      (transSCC A S₀ S₁ k).r p q → (transSCC A S₀ S₁ k).r (A.step p b) (A.step q b) := by
    intro b hb p q hpq
    have hπ : π (Quotient.mk _ (A.step p b)) = π (Quotient.mk _ (A.step q b)) :=
      Quotient.sound (transSCC_step A S₀ S₁ k hb hpq)
    exact Quotient.exact (hπ_bij.1 hπ)
  have hInv_word : ∀ g : List α, (∀ b ∈ g, b ∈ S₀) → ∀ p q : Q,
      (transSCC A S₀ S₁ k).r p q → (transSCC A S₀ S₁ k).r (A.eval p g) (A.eval q g) := by
    intro g
    induction g with
    | nil => intro _ _ _ h; exact h
    | cons b g ih =>
      intro hS p q h
      exact ih (fun c hc => hS c (List.mem_cons_of_mem b hc)) _ _
        (hInv b (hS b List.mem_cons_self) p q h)
  -- `IsSink k X ↔ IsSink (k + 1) (π X)`
  have hsink_back : ∀ X : Quotient (transSCC A S₀ S₁ k),
      IsSink A S₀ S₁ (k + 1) (π X) → IsSink A S₀ S₁ k X := by
    intro X hX Y hXY
    have hπXY : condLe A S₀ S₁ (k + 1) (π X) (π Y) :=
      Quotient.inductionOn₂ X Y (fun _ _ h => transReach_mono A S₀ S₁ (Nat.le_succ k) h) hXY
    exact hπ_bij.1 (hX (π Y) hπXY)
  have hsink_iff : ∀ X : Quotient (transSCC A S₀ S₁ k),
      IsSink A S₀ S₁ k X ↔ IsSink A S₀ S₁ (k + 1) (π X) := by
    let S_k := Finset.univ.filter (IsSink A S₀ S₁ k)
    let S_k1 := Finset.univ.filter (IsSink A S₀ S₁ (k + 1))
    let S_pull := Finset.univ.filter (fun X => IsSink A S₀ S₁ (k + 1) (π X))
    have hsub : S_pull ⊆ S_k := fun X hX =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ X, hsink_back X (Finset.mem_filter.mp hX).2⟩
    have himg : S_pull.image π = S_k1 := by
      ext Y
      simp only [Finset.mem_image, S_pull, S_k1, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨X, hX, rfl⟩; exact hX
      · intro hY; obtain ⟨X, rfl⟩ := hπ_bij.2 Y; exact ⟨X, hY, rfl⟩
    have hcard_eq : S_pull.card = S_k.card := by
      rw [← Finset.card_image_of_injective S_pull hπ_bij.1, himg]
      exact hs_eq
    have hset_eq : S_pull = S_k := Finset.eq_of_subset_of_card_le hsub hcard_eq.ge
    intro X
    have hmem : X ∈ S_pull ↔ X ∈ S_k := by rw [hset_eq]
    simpa only [S_pull, S_k, Finset.mem_filter, Finset.mem_univ, true_and] using hmem.symm
  -- Every `b ∈ S₀` maps `NonSinks_k` into `NonSinks_k`, hence permutes `Sinks_k`!
  have hsink_step : ∀ b ∈ S₀, ∀ q : Q,
      IsSink A S₀ S₁ k (Quotient.mk (transSCC A S₀ S₁ k) q) →
      IsSink A S₀ S₁ k (Quotient.mk (transSCC A S₀ S₁ k) (A.step q b)) := by
    intro b hb
    let act : Quotient (transSCC A S₀ S₁ k) → Quotient (transSCC A S₀ S₁ k) :=
      Quotient.lift (fun x => Quotient.mk (transSCC A S₀ S₁ k) (A.step x b)) fun _ _ h =>
        Quotient.sound (hInv b hb _ _ h)
    have hact_surj : Function.Surjective act := fun Y => by
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Y
      obtain ⟨x, hx⟩ := (hBij b hb).2 y
      dsimp only at hx
      exact ⟨Quotient.mk _ x, by change Quotient.mk _ (A.step x b) = _; rw [hx]⟩
    have hact_bij : Function.Bijective act :=
      (Fintype.bijective_iff_surjective_and_card act).mpr ⟨hact_surj, rfl⟩
    have hnon_sink : ∀ X : Quotient (transSCC A S₀ S₁ k),
        ¬ IsSink A S₀ S₁ k X → ¬ IsSink A S₀ S₁ k (act X) := by
      intro X hnot hact_sink
      apply hnot
      intro Y hXY
      have hπ_le : condLe A S₀ S₁ (k + 1) (π (act X)) (π (act Y)) :=
        Quotient.inductionOn₂ X Y (fun _ _ h => transReach_step A S₀ S₁ k hb h) hXY
      have hact_sink1 : IsSink A S₀ S₁ (k + 1) (π (act X)) := (hsink_iff (act X)).mp hact_sink
      exact hact_bij.1 (hπ_bij.1 (hact_sink1 (π (act Y)) hπ_le))
    -- Since `act` is bijective and preserves `¬ IsSink`, it preserves `IsSink`
    let NS := Finset.univ.filter (fun X => ¬ IsSink A S₀ S₁ k X)
    have himg_sub : NS.image act ⊆ NS := by
      intro Z hZ
      rw [Finset.mem_image] at hZ
      rcases hZ with ⟨X, hX, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnon_sink X (Finset.mem_filter.mp hX).2⟩
    have himg_eq : NS.image act = NS :=
      Finset.eq_of_subset_of_card_le himg_sub (by rw [Finset.card_image_of_injective _ hact_bij.1])
    intro q hq
    by_contra hnot
    have hmem : act (Quotient.mk _ q) ∈ NS.image act := by
      rw [himg_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨X, hX, hXeq⟩
    have hqeq : X = Quotient.mk _ q := hact_bij.1 hXeq
    exact (Finset.mem_filter.mp hX).2 (hqeq ▸ hq)
  -- Nonempty `S₀`-invariant set of sink vertices must equal `Q`!
  obtain ⟨q₀⟩ := ‹Nonempty Q›
  obtain ⟨X₀, _, hX₀_max⟩ := exists_max_in_finset A S₀ S₁ k Finset.univ ⟨Quotient.mk _ q₀, Finset.mem_univ _⟩
  obtain ⟨p₀, hp₀⟩ := Quotient.exists_rep X₀
  have hp₀_sink : IsSink A S₀ S₁ k (Quotient.mk _ p₀) := by
    rw [hp₀]; exact fun Y h => hX₀_max Y (Finset.mem_univ Y) h
  have hall_sink : ∀ q : Q, IsSink A S₀ S₁ k (Quotient.mk _ q) := by
    intro q
    obtain ⟨g, hgS, rfl⟩ := hTrans p₀ q
    have hstep_word : ∀ w : List α, (∀ b ∈ w, b ∈ S₀) →
        ∀ x : Q, IsSink A S₀ S₁ k (Quotient.mk _ x) →
          IsSink A S₀ S₁ k (Quotient.mk _ (A.eval x w)) := by
      intro w
      induction w with
      | nil => intro _ _ hx; exact hx
      | cons b w ih =>
        intro hS x hx
        exact ih (fun c hc => hS c (List.mem_cons_of_mem b hc)) _
          (hsink_step b (hS b List.mem_cons_self) x hx)
    exact hstep_word g hgS p₀ hp₀_sink
  -- Hence every arc of `E_∞` stays inside a single class of `Π_k`!
  have hInf_to_k : ∀ p q : Q, transReachInf A S₀ S₁ p q → (transSCC A S₀ S₁ k).r p q := by
    intro p q hpq
    induction hpq with
    | refl => exact (transSCC A S₀ S₁ k).iseqv.refl _
    | tail _ hstep ih =>
      rcases hstep with ⟨_, a, ha, z₀, m₀, hDef, g, _, hgS, rfl, rfl⟩
      have h0 : transEdge A S₀ S₁ k z₀ m₀ :=
        ⟨a, ha, z₀, m₀, hDef, [], Nat.zero_le k, fun _ h => absurd h (List.not_mem_nil), rfl, rfl⟩
      have hzm_eq : Quotient.mk (transSCC A S₀ S₁ k) m₀ = Quotient.mk (transSCC A S₀ S₁ k) z₀ :=
        hall_sink z₀ (Quotient.mk _ m₀) (Relation.ReflTransGen.single h0)
      have hzm_r : (transSCC A S₀ S₁ k).r z₀ m₀ := (Quotient.exact hzm_eq).symm
      exact (transSCC A S₀ S₁ k).iseqv.trans ih (hInv_word g hgS z₀ m₀ hzm_r)
  let ψ : Quotient (transSCCInf A S₀ S₁) → Quotient (transSCC A S₀ S₁ k) :=
    Quotient.lift (Quotient.mk (transSCC A S₀ S₁ k)) fun _ _ h =>
      Quotient.sound (hInf_to_k _ _ h.1)
  have hψ_surj : Function.Surjective ψ := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  have hle_d : transSCCCount A S₀ S₁ k ≤ blockCount A S₀ S₁ :=
    Fintype.card_le_of_surjective ψ hψ_surj
  omega

lemma zhuG_strict_dec [Nonempty Q] {A : DFA Q α} {S₀ : Set α} (S₁ : Set α)
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (k : ℕ) (hgt : blockCount A S₀ S₁ < transSCCCount A S₀ S₁ k) :
    zhuG A S₀ S₁ (k + 1) < zhuG A S₀ S₁ k := by
  classical
  have hc_le := transSCCCount_antitone A S₀ S₁ (by omega : k ≤ k + 1)
  have hs_le := transSourceCount_antitone A S₀ S₁ (by omega : k ≤ k + 1)
  refine lt_of_le_of_ne (Nat.add_le_add hc_le hs_le) fun heq => ?_
  have hc_eq : transSCCCount A S₀ S₁ (k + 1) = transSCCCount A S₀ S₁ k := by
    dsimp only [zhuG] at heq; omega
  have hs_eq : transSourceCount A S₀ S₁ (k + 1) = transSourceCount A S₀ S₁ k := by
    dsimp only [zhuG] at heq; omega
  let π : Quotient (transSCC A S₀ S₁ k) → Quotient (transSCC A S₀ S₁ (k + 1)) :=
    Quotient.lift (Quotient.mk (transSCC A S₀ S₁ (k + 1))) fun _ _ h =>
      Quotient.sound ⟨transReach_mono A S₀ S₁ (Nat.le_succ k) h.1,
        transReach_mono A S₀ S₁ (Nat.le_succ k) h.2⟩
  have hπ_surj : Function.Surjective π := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  have hπ_bij : Function.Bijective π :=
    (Fintype.bijective_iff_surjective_and_card π).mpr ⟨hπ_surj, hc_eq.symm⟩
  have hInv : ∀ b ∈ S₀, ∀ p q : Q,
      (transSCC A S₀ S₁ k).r p q → (transSCC A S₀ S₁ k).r (A.step p b) (A.step q b) := by
    intro b hb p q hpq
    have hπ : π (Quotient.mk _ (A.step p b)) = π (Quotient.mk _ (A.step q b)) :=
      Quotient.sound (transSCC_step A S₀ S₁ k hb hpq)
    exact Quotient.exact (hπ_bij.1 hπ)
  have hInv_word : ∀ g : List α, (∀ b ∈ g, b ∈ S₀) → ∀ p q : Q,
      (transSCC A S₀ S₁ k).r p q → (transSCC A S₀ S₁ k).r (A.eval p g) (A.eval q g) := by
    intro g
    induction g with
    | nil => intro _ _ _ h; exact h
    | cons b g ih =>
      intro hS p q h
      exact ih (fun c hc => hS c (List.mem_cons_of_mem b hc)) _ _
        (hInv b (hS b List.mem_cons_self) p q h)
  have hsrc_back : ∀ X : Quotient (transSCC A S₀ S₁ k),
      IsSource A S₀ S₁ (k + 1) (π X) → IsSource A S₀ S₁ k X := by
    intro X hX Y hYX
    have hπYX : condLe A S₀ S₁ (k + 1) (π Y) (π X) :=
      Quotient.inductionOn₂ Y X (fun _ _ h => transReach_mono A S₀ S₁ (Nat.le_succ k) h) hYX
    exact hπ_bij.1 (hX (π Y) hπYX)
  have hsrc_iff : ∀ X : Quotient (transSCC A S₀ S₁ k),
      IsSource A S₀ S₁ k X ↔ IsSource A S₀ S₁ (k + 1) (π X) := by
    let S_k := Finset.univ.filter (IsSource A S₀ S₁ k)
    let S_k1 := Finset.univ.filter (IsSource A S₀ S₁ (k + 1))
    let S_pull := Finset.univ.filter (fun X => IsSource A S₀ S₁ (k + 1) (π X))
    have hsub : S_pull ⊆ S_k := fun X hX =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ X, hsrc_back X (Finset.mem_filter.mp hX).2⟩
    have himg : S_pull.image π = S_k1 := by
      ext Y
      simp only [Finset.mem_image, S_pull, S_k1, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨X, hX, rfl⟩; exact hX
      · intro hY; obtain ⟨X, rfl⟩ := hπ_bij.2 Y; exact ⟨X, hY, rfl⟩
    have hcard_eq : S_pull.card = S_k.card := by
      rw [← Finset.card_image_of_injective S_pull hπ_bij.1, himg]
      exact hs_eq
    have hset_eq : S_pull = S_k := Finset.eq_of_subset_of_card_le hsub hcard_eq.ge
    intro X
    have hmem : X ∈ S_pull ↔ X ∈ S_k := by rw [hset_eq]
    simpa only [S_pull, S_k, Finset.mem_filter, Finset.mem_univ, true_and] using hmem.symm
  have hsrc_step : ∀ b ∈ S₀, ∀ q : Q,
      IsSource A S₀ S₁ k (Quotient.mk (transSCC A S₀ S₁ k) q) →
      IsSource A S₀ S₁ k (Quotient.mk (transSCC A S₀ S₁ k) (A.step q b)) := by
    intro b hb
    let act : Quotient (transSCC A S₀ S₁ k) → Quotient (transSCC A S₀ S₁ k) :=
      Quotient.lift (fun x => Quotient.mk (transSCC A S₀ S₁ k) (A.step x b)) fun _ _ h =>
        Quotient.sound (hInv b hb _ _ h)
    have hact_surj : Function.Surjective act := fun Y => by
      obtain ⟨y, rfl⟩ := Quotient.exists_rep Y
      obtain ⟨x, hx⟩ := (hBij b hb).2 y
      dsimp only at hx
      exact ⟨Quotient.mk _ x, by change Quotient.mk _ (A.step x b) = _; rw [hx]⟩
    have hact_bij : Function.Bijective act :=
      (Fintype.bijective_iff_surjective_and_card act).mpr ⟨hact_surj, rfl⟩
    have hnon_src : ∀ X : Quotient (transSCC A S₀ S₁ k),
        ¬ IsSource A S₀ S₁ k X → ¬ IsSource A S₀ S₁ k (act X) := by
      intro X hnot hact_src
      apply hnot
      intro Y hYX
      have hπ_le : condLe A S₀ S₁ (k + 1) (π (act Y)) (π (act X)) :=
        Quotient.inductionOn₂ Y X (fun _ _ h => transReach_step A S₀ S₁ k hb h) hYX
      have hact_src1 : IsSource A S₀ S₁ (k + 1) (π (act X)) := (hsrc_iff (act X)).mp hact_src
      exact hact_bij.1 (hπ_bij.1 (hact_src1 (π (act Y)) hπ_le))
    let NS := Finset.univ.filter (fun X => ¬ IsSource A S₀ S₁ k X)
    have himg_sub : NS.image act ⊆ NS := by
      intro Z hZ
      rw [Finset.mem_image] at hZ
      rcases hZ with ⟨X, hX, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnon_src X (Finset.mem_filter.mp hX).2⟩
    have himg_eq : NS.image act = NS :=
      Finset.eq_of_subset_of_card_le himg_sub (by rw [Finset.card_image_of_injective _ hact_bij.1])
    intro q hq
    by_contra hnot
    have hmem : act (Quotient.mk _ q) ∈ NS.image act := by
      rw [himg_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨X, hX, hXeq⟩
    have hqeq : X = Quotient.mk _ q := hact_bij.1 hXeq
    exact (Finset.mem_filter.mp hX).2 (hqeq ▸ hq)
  obtain ⟨q₀⟩ := ‹Nonempty Q›
  obtain ⟨X₀, _, hX₀_min⟩ := exists_min_in_finset A S₀ S₁ k Finset.univ ⟨Quotient.mk _ q₀, Finset.mem_univ _⟩
  obtain ⟨p₀, hp₀⟩ := Quotient.exists_rep X₀
  have hp₀_src : IsSource A S₀ S₁ k (Quotient.mk _ p₀) := by
    rw [hp₀]; exact fun Y h => hX₀_min Y (Finset.mem_univ Y) h
  have hall_src : ∀ q : Q, IsSource A S₀ S₁ k (Quotient.mk _ q) := by
    intro q
    obtain ⟨g, hgS, rfl⟩ := hTrans p₀ q
    have hstep_word : ∀ w : List α, (∀ b ∈ w, b ∈ S₀) →
        ∀ x : Q, IsSource A S₀ S₁ k (Quotient.mk _ x) →
          IsSource A S₀ S₁ k (Quotient.mk _ (A.eval x w)) := by
      intro w
      induction w with
      | nil => intro _ _ hx; exact hx
      | cons b w ih =>
        intro hS x hx
        exact ih (fun c hc => hS c (List.mem_cons_of_mem b hc)) _
          (hsrc_step b (hS b List.mem_cons_self) x hx)
    exact hstep_word g hgS p₀ hp₀_src
  have hInf_to_k : ∀ p q : Q, transReachInf A S₀ S₁ p q → (transSCC A S₀ S₁ k).r p q := by
    intro p q hpq
    induction hpq with
    | refl => exact (transSCC A S₀ S₁ k).iseqv.refl _
    | tail _ hstep ih =>
      rcases hstep with ⟨_, a, ha, z₀, m₀, hDef, g, _, hgS, rfl, rfl⟩
      have h0 : transEdge A S₀ S₁ k z₀ m₀ :=
        ⟨a, ha, z₀, m₀, hDef, [], Nat.zero_le k, fun _ h => absurd h (List.not_mem_nil), rfl, rfl⟩
      have hzm_eq : Quotient.mk (transSCC A S₀ S₁ k) z₀ = Quotient.mk (transSCC A S₀ S₁ k) m₀ :=
        hall_src m₀ (Quotient.mk _ z₀) (Relation.ReflTransGen.single h0)
      have hzm_r : (transSCC A S₀ S₁ k).r z₀ m₀ := Quotient.exact hzm_eq
      exact (transSCC A S₀ S₁ k).iseqv.trans ih (hInv_word g hgS z₀ m₀ hzm_r)
  let ψ : Quotient (transSCCInf A S₀ S₁) → Quotient (transSCC A S₀ S₁ k) :=
    Quotient.lift (Quotient.mk (transSCC A S₀ S₁ k)) fun _ _ h =>
      Quotient.sound (hInf_to_k _ _ h.1)
  have hψ_surj : Function.Surjective ψ := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  have hle_d : transSCCCount A S₀ S₁ k ≤ blockCount A S₀ S₁ :=
    Fintype.card_le_of_surjective ψ hψ_surj
  omega

/-- **Lemma 1.2(2a) (Zhu Sink-Potential Coarsening)**:
If `f(k) ≤ 2d + t`, then `c(k + t) = d`. -/
theorem transSCCCount_eq_blockCount_of_zhuF [Nonempty Q] {A : DFA Q α} {S₀ : Set α} (S₁ : Set α)
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q) :
    ∀ t k : ℕ, zhuF A S₀ S₁ k ≤ 2 * blockCount A S₀ S₁ + t →
      transSCCCount A S₀ S₁ (k + t) = blockCount A S₀ S₁ := by
  intro t
  induction t with
  | zero =>
    intro k hle
    have hc := blockCount_le_transSCCCount A S₀ S₁ k
    have hs := blockCount_le_transSinkCount S₁ hBij hTrans k
    dsimp only [zhuF] at hle
    simpa using (show transSCCCount A S₀ S₁ k = blockCount A S₀ S₁ by omega)
  | succ t ih =>
    intro k hle
    have hc := blockCount_le_transSCCCount A S₀ S₁ k
    by_cases heq : transSCCCount A S₀ S₁ k = blockCount A S₀ S₁
    · have hle' := transSCCCount_antitone A S₀ S₁ (Nat.le_add_right k (t + 1))
      have hge' := blockCount_le_transSCCCount A S₀ S₁ (k + (t + 1))
      omega
    · have hdec := zhuF_strict_dec S₁ hBij hTrans k (by omega)
      have hres := ih (k + 1) (by omega)
      have hadd : k + 1 + t = k + (t + 1) := by omega
      rwa [hadd] at hres

/-- **Lemma 1.2(2b) (Zhu Source-Potential Coarsening)**:
If `g(k) ≤ 2d + t`, then `c(k + t) = d`. -/
theorem transSCCCount_eq_blockCount_of_zhuG [Nonempty Q] {A : DFA Q α} {S₀ : Set α} (S₁ : Set α)
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q) :
    ∀ t k : ℕ, zhuG A S₀ S₁ k ≤ 2 * blockCount A S₀ S₁ + t →
      transSCCCount A S₀ S₁ (k + t) = blockCount A S₀ S₁ := by
  intro t
  induction t with
  | zero =>
    intro k hle
    have hc := blockCount_le_transSCCCount A S₀ S₁ k
    have hs := blockCount_le_transSourceCount S₁ hBij hTrans k
    dsimp only [zhuG] at hle
    simpa using (show transSCCCount A S₀ S₁ k = blockCount A S₀ S₁ by omega)
  | succ t ih =>
    intro k hle
    have hc := blockCount_le_transSCCCount A S₀ S₁ k
    by_cases heq : transSCCCount A S₀ S₁ k = blockCount A S₀ S₁
    · have hle' := transSCCCount_antitone A S₀ S₁ (Nat.le_add_right k (t + 1))
      have hge' := blockCount_le_transSCCCount A S₀ S₁ (k + (t + 1))
      omega
    · have hdec := zhuG_strict_dec S₁ hBij hTrans k (by omega)
      have hres := ih (k + 1) (by omega)
      have hadd : k + 1 + t = k + (t + 1) := by omega
      rwa [hadd] at hres

/-! ### Lemma 1.3: Zero-Cone `ℚ`-Subspace Block-Escape Extensibility (`ext(S) ≤ m + d`) -/

/-- Pullback `ℚ`-linear operator `(pullback A w v) q = v (A.eval q w)`. -/
def pullback (A : DFA Q α) (w : List α) : (Q → ℚ) →ₗ[ℚ] (Q → ℚ) where
  toFun v q := v (A.eval q w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Indicator vector `1_T : Q → ℚ`. -/
def indVec (T : Finset Q) : Q → ℚ := fun q => if q ∈ T then 1 else 0

lemma pullback_indVec (A : DFA Q α) (w : List α) (T : Finset Q) :
    pullback A w (indVec T) = indVec (A.preimage T w) := by
  funext q
  simp only [pullback, LinearMap.coe_mk, AddHom.coe_mk, indVec, DFA.mem_preimage]

omit [Fintype Q] [DecidableEq Q] in
lemma pullback_ones (A : DFA Q α) (w : List α) :
    pullback A w (fun _ => (1 : ℚ)) = (fun _ => (1 : ℚ)) := rfl

omit [Fintype Q] [DecidableEq Q] in
lemma pullback_cons (A : DFA Q α) (a : α) (w : List α) (v : Q → ℚ) :
    pullback A (a :: w) v = pullback A [a] (pullback A w v) := by
  funext q
  simp only [pullback, LinearMap.coe_mk, AddHom.coe_mk, DFA.eval_cons, DFA.eval_nil]

/-- Predicate: `T` is a union of blocks of `Π_∞`. -/
def IsBlockUnion (A : DFA Q α) (S₀ S₁ : Set α) (T : Finset Q) : Prop :=
  ∀ p q : Q, (transSCCInf A S₀ S₁).r p q → (p ∈ T ↔ q ∈ T)

/-- **Lemma 1.3 (Zero-Cone `ℚ`-Subspace Block-Escape Extensibility)**:
Whenever `c(m) = d`, every nonempty proper subset `S ⊂ Q` admits an extending word `w` of length
`w.length ≤ m + d` with `(A.preimage S w).card = S.card + 1`. -/
theorem blockEscape_extend [Nonempty Q] {A : DFA Q α} {S₀ S₁ : Set α}
    (hSync : A.IsSynchronizing) (hT : IsTransitiveDefectLeOne A S₀ S₁)
    (m : ℕ) (hm : transSCCCount A S₀ S₁ m = blockCount A S₀ S₁)
    {S : Finset Q} (hS_ne : S.Nonempty) (hS_lt : S.card < Fintype.card Q) :
    ∃ w : List α, w.length ≤ m + blockCount A S₀ S₁ ∧ (A.preimage S w).card = S.card + 1 := by
  classical
  let sInf := transSCCInf A S₀ S₁
  let B := Quotient sInf
  let d := blockCount A S₀ S₁
  have hd_pos : 1 ≤ d := blockCount_pos A S₀ S₁
  -- Single-letter size preservation on any block union `T`
  have hletter_card : ∀ (T : Finset Q) (a : α),
      IsBlockUnion A S₀ S₁ T → (A.preimage T [a]).card = T.card := by
    intro T a hTbl
    rcases hT.1 a with ha0 | ha1
    · exact card_preimage_of_bijective T [a] (by
        simpa only [DFA.eval_singleton] using hT.2.1 a ha0)
    · obtain ⟨z₀, m₀, hDef⟩ := exists_isDefectOneLetter_of_card_image_eq_pred A a (hT.2.2.2 a ha1)
      have hzm_e : transEdgeInf A S₀ S₁ z₀ m₀ :=
        ⟨0, a, ha1, z₀, m₀, hDef, [], le_rfl, fun _ h => absurd h (List.not_mem_nil), rfl, rfl⟩
      have hzm_r : sInf.r z₀ m₀ :=
        (transSCCInf_iff_reachInf hT.2.1 hT.2.2.1).mpr (Relation.ReflTransGen.single hzm_e)
      have hiff : z₀ ∈ T ↔ m₀ ∈ T := hTbl z₀ m₀ hzm_r
      have hcard := card_preimage_defectOne hDef T
      by_cases hz : z₀ ∈ T
      · have hm' : m₀ ∈ T := hiff.mp hz
        simp only [hz, hm', ↓reduceIte] at hcard; omega
      · have hm' : m₀ ∉ T := fun h => hz (hiff.mpr h)
        simp only [hz, hm', ↓reduceIte, add_zero] at hcard; exact hcard
  -- Size preservation along any word whose proper suffixes all land in block unions
  have hword_card : ∀ u : List α,
      (∀ v : List α, v <:+ u → v ≠ u → IsBlockUnion A S₀ S₁ (A.preimage S v)) →
      (A.preimage S u).card = S.card := by
    intro u
    induction u with
    | nil => intro _; simp
    | cons a u' ih =>
      intro hprop
      have hu'_blk : IsBlockUnion A S₀ S₁ (A.preimage S u') :=
        hprop u' (List.suffix_cons a u') (by intro h; have := congrArg List.length h; simp at this)
      have hu'_card : (A.preimage S u').card = S.card := by
        apply ih
        intro v hv hne
        refine hprop v (hv.trans (List.suffix_cons a u')) ?_
        intro heq
        have hlen := hv.length_le
        have := congrArg List.length heq
        simp at this
        omega
      rw [DFA.preimage_cons]
      exact (hletter_card (A.preimage S u') a hu'_blk).trans hu'_card
  -- Block-constant subspace `H_blk ⊆ (Q → ℚ)` with `finrank H_blk ≤ d`
  let liftMap : (B → ℚ) →ₗ[ℚ] (Q → ℚ) := LinearMap.funLeft ℚ ℚ (Quotient.mk sInf)
  let H_blk : Submodule ℚ (Q → ℚ) := LinearMap.range liftMap
  have hH_dim : Module.finrank ℚ H_blk ≤ d := by
    calc Module.finrank ℚ H_blk
        ≤ Module.finrank ℚ (B → ℚ) := LinearMap.finrank_range_le liftMap
      _ = Fintype.card B := Module.finrank_fintype_fun_eq_card ℚ
      _ = d := rfl
  have hmem_H : ∀ T : Finset Q, indVec T ∈ H_blk ↔ IsBlockUnion A S₀ S₁ T := by
    intro T
    constructor
    · rintro ⟨f, hf⟩ p q hpq
      have heq : indVec T p = indVec T q := by
        have hp : f (Quotient.mk sInf p) = indVec T p := congrFun hf p
        have hq : f (Quotient.mk sInf q) = indVec T q := congrFun hf q
        rw [← hp, ← hq, Quotient.sound hpq]
      simp only [indVec] at heq
      by_cases hp : p ∈ T <;> by_cases hq : q ∈ T <;> simp [hp, hq] at heq ⊢
    · intro hTbl
      let f : B → ℚ := Quotient.lift (indVec T) fun p q hpq => by
        simp only [indVec, hTbl p q hpq]
      exact ⟨f, rfl⟩
  have hones_H : (fun _ : Q => (1 : ℚ)) ∈ H_blk := ⟨fun _ => 1, rfl⟩
  -- Step 1 & 2: Find a word `u` of length `≤ d - 1` escaping `IsBlockUnion`
  have hex_escape : ∃ u : List α, u.length ≤ d - 1 ∧ ¬ IsBlockUnion A S₀ S₁ (A.preimage S u) := by
    by_contra hall
    push Not at hall
    -- Build ascending subspaces `W̃ t ≤ H_blk` for `t ≤ d - 1`
    let W : ℕ → Submodule ℚ (Q → ℚ) := fun t =>
      Submodule.span ℚ
        ({(fun _ : Q => (1 : ℚ))} ∪ {v : Q → ℚ | ∃ u : List α, u.length ≤ t ∧ v = indVec (A.preimage S u)})
    have hW_mono : ∀ t : ℕ, W t ≤ W (t + 1) := fun t => by
      apply Submodule.span_mono
      intro v hv
      rcases hv with hv | ⟨u, hulen, rfl⟩
      · exact Or.inl hv
      · exact Or.inr ⟨u, by omega, rfl⟩
    have hW_le_H : W (d - 1) ≤ H_blk := by
      rw [Submodule.span_le]
      intro v hv
      rcases hv with rfl | ⟨u, hulen, rfl⟩
      · exact hones_H
      · exact (hmem_H (A.preimage S u)).mpr (hall u hulen)
    have hW0_ge2 : 2 ≤ Module.finrank ℚ (W 0) := by
      have h1_in : (fun _ : Q => (1 : ℚ)) ∈ W 0 :=
        Submodule.subset_span (Or.inl rfl)
      have hS_in : indVec S ∈ W 0 :=
        Submodule.subset_span (Or.inr ⟨[], le_rfl, by simp⟩)
      let f : Fin 2 → W 0 := ![⟨(fun _ => 1), h1_in⟩, ⟨indVec S, hS_in⟩]
      have hli : LinearIndependent ℚ f := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have h0 : c 0 • (fun _ : Q => (1 : ℚ)) + c 1 • indVec S = 0 := by
          have := congrArg Subtype.val hc
          simpa [Fin.sum_univ_two, f] using this
        have hS_ne_univ : S ≠ Finset.univ := fun heq => by
          rw [heq, Finset.card_univ] at hS_lt; omega
        obtain ⟨q_out, _, hq_out⟩ := Finset.exists_of_ssubset
          (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hS_ne_univ⟩)
        rcases hS_ne with ⟨q_in, hq_in⟩
        have hc0 : c 0 = 0 := by
          have := congrFun h0 q_out
          simp [indVec, hq_out] at this
          exact this
        have hc1 : c 1 = 0 := by
          have := congrFun h0 q_in
          simp [indVec, hq_in, hc0] at this
          exact this
        intro i
        fin_cases i
        · exact hc0
        · exact hc1
      have hcard := hli.fintype_card_le_finrank
      simpa using hcard
    have hW0_le_H : Module.finrank ℚ (W 0) ≤ d := by
      have hle0 : W 0 ≤ W (d - 1) := by
        have hiter : ∀ k : ℕ, W 0 ≤ W k := fun k => by
          induction k with
          | zero => exact le_rfl
          | succ k ih => exact ih.trans (hW_mono k)
        exact hiter (d - 1)
      exact (Submodule.finrank_mono (hle0.trans hW_le_H)).trans hH_dim
    -- Pigeonhole on `2 ≤ finrank (W 0) ≤ ... ≤ finrank (W (d - 1)) ≤ d` gives `j < d - 1` with `W j = W (j + 1)`
    have hex_eq : ∃ j < d - 1, W j = W (j + 1) := by
      by_contra hstrict
      push Not at hstrict
      have hgrow : ∀ t ≤ d - 1, Module.finrank ℚ (W 0) + t ≤ Module.finrank ℚ (W t) := by
        intro t
        induction t with
        | zero => intro _; omega
        | succ t ih =>
          intro htle
          have hlt_sub : W t < W (t + 1) :=
            lt_of_le_of_ne (hW_mono t) (hstrict t (by omega))
          have hlt_dim : Module.finrank ℚ (W t) < Module.finrank ℚ (W (t + 1)) :=
            Submodule.finrank_lt_finrank_of_lt hlt_sub
          have := ih (by omega)
          omega
      have htop := hgrow (d - 1) le_rfl
      have hfin_top : Module.finrank ℚ (W (d - 1)) ≤ d :=
        (Submodule.finrank_mono hW_le_H).trans hH_dim
      omega
    rcases hex_eq with ⟨j, hj_lt, hWj_eq⟩
    -- `W j` is invariant under every `pullback A [a]`
    have hWj_inv : ∀ (a : α) (v : Q → ℚ), v ∈ W j → pullback A [a] v ∈ W j := by
      intro a v hv
      rw [hWj_eq]
      have hmap : Submodule.map (pullback A [a]) (W j) ≤ W (j + 1) := by
        rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
        intro x hx
        show pullback A [a] x ∈ W (j + 1)
        rcases hx with rfl | ⟨u, hulen, rfl⟩
        · rw [pullback_ones]; exact Submodule.subset_span (Or.inl rfl)
        · rw [pullback_indVec, ← DFA.preimage_cons]
          exact Submodule.subset_span (Or.inr ⟨a :: u, by simp; omega, rfl⟩)
      exact hmap ⟨v, hv, rfl⟩
    have hWj_word : ∀ (w : List α) (v : Q → ℚ), v ∈ W j → pullback A w v ∈ W j := by
      intro w
      induction w with
      | nil => intro v hv; exact hv
      | cons a w ih =>
        intro v hv
        rw [pullback_cons]
        exact hWj_inv a _ (ih v hv)
    have hWj_le_H : W j ≤ H_blk := by
      have hle : ∀ t₁ t₂ : ℕ, t₁ ≤ t₂ → W t₁ ≤ W t₂ := fun t₁ t₂ h => by
        induction h with
        | refl => exact le_rfl
        | step _ ih => exact ih.trans (hW_mono _)
      exact (hle j (d - 1) (by omega)).trans hW_le_H
    have hall_blk : ∀ w : List α, IsBlockUnion A S₀ S₁ (A.preimage S w) := by
      intro w
      have hS_in : indVec S ∈ W j :=
        Submodule.subset_span (Or.inr ⟨[], Nat.zero_le j, by simp⟩)
      have hpull_in : indVec (A.preimage S w) ∈ H_blk := by
        rw [← pullback_indVec]
        exact hWj_le_H (hWj_word w (indVec S) hS_in)
      exact (hmem_H (A.preimage S w)).mp hpull_in
    -- Contradiction with synchronization!
    rcases hSync with ⟨w_sync, q_sync, hq_sync⟩
    have hcard_eq : (A.preimage S w_sync).card = S.card :=
      hword_card w_sync fun v _ _ => hall_blk v
    by_cases hqs : q_sync ∈ S
    · have huniv : A.preimage S w_sync = Finset.univ := by
        ext p; simp [DFA.mem_preimage, hq_sync p, hqs]
      rw [huniv, Finset.card_univ] at hcard_eq
      omega
    · have hempty : A.preimage S w_sync = ∅ := by
        ext p; simp [DFA.mem_preimage, hq_sync p, hqs]
      rw [hempty, Finset.card_empty] at hcard_eq
      have := Finset.card_pos.mpr hS_ne
      omega
  -- Step 3: Pick a SHORTEST escaping word `u` (`|u| ≤ d - 1`)
  have hex_len : ∃ k : ℕ, ∃ u : List α, u.length = k ∧ ¬ IsBlockUnion A S₀ S₁ (A.preimage S u) := by
    rcases hex_escape with ⟨u, _, hu⟩; exact ⟨u.length, u, rfl, hu⟩
  let k₀ := Nat.find hex_len
  obtain ⟨u, hu_len, hu_not⟩ := Nat.find_spec hex_len
  have hk₀_le : k₀ ≤ d - 1 := by
    rcases hex_escape with ⟨u', hu'len, hu'not⟩
    exact (Nat.find_min' hex_len ⟨u', rfl, hu'not⟩).trans hu'len
  have hu_card : (A.preimage S u).card = S.card := by
    apply hword_card u
    intro v hv hne
    by_contra hnot
    have hlt : v.length < k₀ := by
      have hle := hv.length_le
      have hne_len : v.length ≠ u.length := fun heq => hne (hv.eq_of_length heq)
      omega
    exact Nat.find_min hex_len hlt ⟨v, rfl, hnot⟩
  -- Step 4: Since `S' = S u⁻¹` is NOT a block union and `c(m) = d`, find a crossing arc in `E_m`!
  let S' := A.preimage S u
  have hnot_blk : ∃ p ∈ S', ∃ q, q ∉ S' ∧ sInf.r p q := by
    dsimp only [IsBlockUnion] at hu_not
    push Not at hu_not
    rcases hu_not with ⟨p, q, hpq, hdiff⟩
    rcases hdiff with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact ⟨p, hp, q, hq, hpq⟩
    · exact ⟨q, hq, p, hp, sInf.iseqv.symm hpq⟩
  rcases hnot_blk with ⟨p, hpS', q, hqS', hpq_inf⟩
  -- Bijectivity of `Quotient (transSCC m) → Quotient sInf` gives `transReach m p q`
  let π_m : Quotient (transSCC A S₀ S₁ m) → B :=
    Quotient.lift (Quotient.mk sInf) fun _ _ h =>
      Quotient.sound ⟨transReach_le_inf A S₀ S₁ m h.1, transReach_le_inf A S₀ S₁ m h.2⟩
  have hπm_surj : Function.Surjective π_m := fun y =>
    Quotient.inductionOn y fun x => ⟨Quotient.mk _ x, rfl⟩
  have hπm_bij : Function.Bijective π_m :=
    (Fintype.bijective_iff_surjective_and_card π_m).mpr ⟨hπm_surj, hm⟩
  have hpq_m : transReach A S₀ S₁ m p q :=
    (Quotient.exact (hπm_bij.1 (Quotient.sound hpq_inf))).1
  -- Walk induction along `transReach m p q` yields a boundary-crossing edge `(x → y)` in `E_m`
  have hwalk : ∀ x y : Q, transReach A S₀ S₁ m x y → x ∈ S' → y ∉ S' →
      ∃ x₀ ∈ S', ∃ y₀, y₀ ∉ S' ∧ transEdge A S₀ S₁ m x₀ y₀ := by
    intro x y hr
    induction hr with
    | refl => intro hx hnx; exact absurd hx hnx
    | @tail b c _ hbc ih =>
      intro hx hnc
      by_cases hb : b ∈ S'
      · exact ⟨b, hb, c, hnc, hbc⟩
      · exact ih hx hb
  obtain ⟨x₀, hx₀, y₀, hy₀, a, ha, z₀, m₀, hDef, g, hglen, hgS, hgz, hgm⟩ :=
    hwalk p q hpq_m hpS' hqS'
  let T' := A.preimage S' g
  have hT'_card : T'.card = S.card :=
    (card_preimage_of_bijective S' g (bijective_eval_of_mem hT.2.1 g hgS)).trans hu_card
  have hz_mem : z₀ ∈ T' := by rw [DFA.mem_preimage, hgz]; exact hx₀
  have hm_not : m₀ ∉ T' := by rw [DFA.mem_preimage, hgm]; exact hy₀
  have hcard_a := card_preimage_defectOne hDef T'
  simp only [hz_mem, hm_not, ↓reduceIte, add_zero] at hcard_a
  refine ⟨a :: (g ++ u), ?_, ?_⟩
  · simp only [List.length_cons, List.length_append]
    omega
  · rw [DFA.preimage_cons, DFA.preimage_append]
    change (A.preimage T' [a]).card = S.card + 1
    omega

/-! ### Lemma 1.4: Full-Transitive `d = 1` World-Record Bound (`c(2n - 5) = 1` for `n ≥ 5`) -/

/-- Helper: at `k = n - 1`, every sink SCC and every source SCC has cardinality `≥ 2`. -/
lemma sink_source_fiber_ge_two [Nonempty Q] {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (hS₁ : ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀) :
    (∀ X : Quotient (transSCC A S₀ S₁ (Fintype.card Q - 1)),
      IsSink A S₀ S₁ (Fintype.card Q - 1) X →
      2 ≤ (fiberOf (transSCC A S₀ S₁ (Fintype.card Q - 1)) X).card) ∧
    (∀ X : Quotient (transSCC A S₀ S₁ (Fintype.card Q - 1)),
      IsSource A S₀ S₁ (Fintype.card Q - 1) X →
      2 ≤ (fiberOf (transSCC A S₀ S₁ (Fintype.card Q - 1)) X).card) := by
  classical
  rcases hS₁ with ⟨a₀, ha₀, z₀, m₀, hDef⟩
  let s₁ := transSCC A S₀ S₁ (Fintype.card Q - 1)
  constructor
  · intro X hX
    obtain ⟨v, hv⟩ := Quotient.exists_rep X
    obtain ⟨g, hglen, hgS, hgz⟩ := exists_short_S₀_word hTrans z₀ v
    have hedge : transEdge A S₀ S₁ (Fintype.card Q - 1) v (A.eval m₀ g) :=
      ⟨a₀, ha₀, z₀, m₀, hDef, g, hglen, hgS, hgz, rfl⟩
    have hne : v ≠ A.eval m₀ g := fun h =>
      transEdge_irrefl S₁ hBij (Fintype.card Q - 1) v (by rwa [← h] at hedge)
    have hv'_eq : Quotient.mk s₁ (A.eval m₀ g) = X :=
      hX (Quotient.mk s₁ (A.eval m₀ g)) (by rw [← hv]; exact Relation.ReflTransGen.single hedge)
    have hsub : ({v, A.eval m₀ g} : Finset Q) ⊆ fiberOf s₁ X := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [mem_fiberOf]
      rcases hq with rfl | rfl
      · exact hv
      · exact hv'_eq
    calc 2 = ({v, A.eval m₀ g} : Finset Q).card := (Finset.card_pair hne).symm
      _ ≤ (fiberOf s₁ X).card := Finset.card_le_card hsub
  · intro X hX
    obtain ⟨u, hu⟩ := Quotient.exists_rep X
    obtain ⟨g, hglen, hgS, hgm⟩ := exists_short_S₀_word hTrans m₀ u
    have hedge : transEdge A S₀ S₁ (Fintype.card Q - 1) (A.eval z₀ g) u :=
      ⟨a₀, ha₀, z₀, m₀, hDef, g, hglen, hgS, rfl, hgm⟩
    have hne : u ≠ A.eval z₀ g := fun h =>
      transEdge_irrefl S₁ hBij (Fintype.card Q - 1) u (by rwa [← h] at hedge)
    have hu'_eq : Quotient.mk s₁ (A.eval z₀ g) = X :=
      hX (Quotient.mk s₁ (A.eval z₀ g)) (by rw [← hu]; exact Relation.ReflTransGen.single hedge)
    have hsub : ({u, A.eval z₀ g} : Finset Q) ⊆ fiberOf s₁ X := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rw [mem_fiberOf]
      rcases hq with rfl | rfl
      · exact hu
      · exact hu'_eq
    calc 2 = ({u, A.eval z₀ g} : Finset Q).card := (Finset.card_pair hne).symm
      _ ≤ (fiberOf s₁ X).card := Finset.card_le_card hsub

/-- Helper: when `d = 1`, `w(n - 2) = 1`, so every nonempty proper subset `W ⊂ Q` has a
boundary-crossing edge in `E_{n - 2}`. -/
lemma exists_transEdge_crossing_d_eq_one [Nonempty Q] {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (hS₁ : ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀)
    (hd1 : blockCount A S₀ S₁ = 1)
    {W : Finset Q} (hW_ne : W.Nonempty) (hW_proper : W ≠ Finset.univ) :
    ∃ u v : Q, transEdge A S₀ S₁ (Fintype.card Q - 2) u v ∧ ¬ (u ∈ W ↔ v ∈ W) := by
  classical
  have hw1 : transWeakCount A S₀ S₁ (Fintype.card Q - 2) = 1 := by
    have h := transWeakCount_eq_blockCount hBij hTrans hS₁
    rw [hd1] at h
    have hidx : Fintype.card Q - 1 - 1 = Fintype.card Q - 2 := by omega
    rwa [hidx] at h
  have hsub : Subsingleton (Quotient (transWeak A S₀ S₁ (Fintype.card Q - 2))) :=
    Fintype.card_le_one_iff_subsingleton.mp hw1.le
  rcases hW_ne with ⟨p₀, hp₀⟩
  obtain ⟨q₀, _, hq₀⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ W, hW_proper⟩)
  by_contra hall
  push Not at hall
  have hrel : (transWeak A S₀ S₁ (Fintype.card Q - 2)).r p₀ q₀ :=
    Quotient.exact (hsub.elim (Quotient.mk _ p₀) (Quotient.mk _ q₀))
  have hpres : ∀ x y : Q, (transWeak A S₀ S₁ (Fintype.card Q - 2)).r x y → (x ∈ W ↔ y ∈ W) := by
    intro x y hxy
    induction hxy with
    | rel u v huv => exact hall u v huv
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  exact hq₀ ((hpres p₀ q₀ hrel).mp hp₀)

/-- Helper for Case 2 of Lemma 1.4: if `d = 1`, `n ≥ 5`, and `c(n - 1) ≤ n - 3`, then
`c(2n - 5) = 1`. -/
lemma trans_d_eq_one_of_le_sub_three [Nonempty Q] {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (hS₁ : ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀)
    (hn5 : 5 ≤ Fintype.card Q) (hd1 : blockCount A S₀ S₁ = 1)
    (hc1 : transSCCCount A S₀ S₁ (Fintype.card Q - 1) ≤ Fintype.card Q - 3) :
    transSCCCount A S₀ S₁ (2 * Fintype.card Q - 5) = 1 := by
  classical
  set n := Fintype.card Q
  have hc1_ge1 : 1 ≤ transSCCCount A S₀ S₁ (n - 1) := by
    calc 1 = blockCount A S₀ S₁ := hd1.symm
      _ ≤ transSCCCount A S₀ S₁ (n - 1) := blockCount_le_transSCCCount A S₀ S₁ (n - 1)
  by_cases h1 : transSCCCount A S₀ S₁ (n - 1) = 1
  · have hle := transSCCCount_antitone A S₀ S₁ (show n - 1 ≤ 2 * n - 5 by omega)
    have hge : 1 ≤ transSCCCount A S₀ S₁ (2 * n - 5) := by
      calc 1 = blockCount A S₀ S₁ := hd1.symm
        _ ≤ transSCCCount A S₀ S₁ (2 * n - 5) := blockCount_le_transSCCCount A S₀ S₁ (2 * n - 5)
    omega
  · -- `2 ≤ c(n - 1) ≤ n - 3`: sinks and sources are disjoint and each has size `≥ 2`
    let s₁ := transSCC A S₀ S₁ (n - 1)
    let C₁ := Quotient s₁
    let Sinks : Finset C₁ := Finset.univ.filter (IsSink A S₀ S₁ (n - 1))
    let Sources : Finset C₁ := Finset.univ.filter (IsSource A S₀ S₁ (n - 1))
    let fib : C₁ → Finset Q := fiberOf s₁
    have hdisj_SS : Disjoint Sinks Sources := by
      rw [Finset.disjoint_left]
      intro X hX_snk hX_src
      have hsnk : IsSink A S₀ S₁ (n - 1) X := (Finset.mem_filter.mp hX_snk).2
      have hsrc : IsSource A S₀ S₁ (n - 1) X := (Finset.mem_filter.mp hX_src).2
      obtain ⟨p₀, hp₀⟩ := Quotient.exists_rep X
      have hfib_ne : (fib X).Nonempty := ⟨p₀, (mem_fiberOf s₁ X p₀).mpr hp₀⟩
      have hfib_proper : fib X ≠ Finset.univ := by
        intro huniv
        have hsub : Subsingleton C₁ := ⟨fun Y Z => by
          obtain ⟨y, rfl⟩ := Quotient.exists_rep Y
          obtain ⟨z, rfl⟩ := Quotient.exists_rep Z
          have hy : y ∈ fib X := huniv ▸ Finset.mem_univ y
          have hz : z ∈ fib X := huniv ▸ Finset.mem_univ z
          exact ((mem_fiberOf s₁ X y).mp hy).trans ((mem_fiberOf s₁ X z).mp hz).symm⟩
        have hle1 : Fintype.card C₁ ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
        change transSCCCount A S₀ S₁ (n - 1) ≤ 1 at hle1
        omega
      obtain ⟨u, v, huv2, hcross⟩ :=
        exists_transEdge_crossing_d_eq_one hBij hTrans hS₁ hd1 hfib_ne hfib_proper
      have huv1 : transEdge A S₀ S₁ (n - 1) u v :=
        transEdge_mono A S₀ S₁ (by omega) huv2
      apply hcross
      constructor
      · intro hu
        rw [mem_fiberOf] at hu ⊢
        refine hsnk (Quotient.mk s₁ v) ?_
        rw [← hu]; exact Relation.ReflTransGen.single huv1
      · intro hv
        rw [mem_fiberOf] at hv ⊢
        refine hsrc (Quotient.mk s₁ u) ?_
        rw [← hv]; exact Relation.ReflTransGen.single huv1
    have hge2 := sink_source_fiber_ge_two hBij hTrans hS₁
    have hfib_ge1 : ∀ X : C₁, 1 ≤ (fib X).card := fun X => by
      obtain ⟨q, rfl⟩ := Quotient.exists_rep X
      exact Finset.card_pos.mpr ⟨q, (mem_fiberOf s₁ _ q).mpr rfl⟩
    have hfib_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset C₁) : Set C₁) fib := by
      intro X _ Y _ hXY
      show Disjoint (fib X) (fib Y)
      rw [Finset.disjoint_left]
      intro q hqX hqY
      rw [mem_fiberOf] at hqX hqY
      exact hXY (hqX.symm.trans hqY)
    have hfib_sum : ∑ X : C₁, (fib X).card = n := by
      have hunion : (Finset.univ : Finset C₁).biUnion fib = Finset.univ := by
        ext q
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, fib, mem_fiberOf, iff_true]
        exact ⟨Quotient.mk s₁ q, rfl⟩
      rw [← Finset.card_biUnion hfib_disj, hunion, Finset.card_univ]
    have hsum_ineq : transSCCCount A S₀ S₁ (n - 1) +
        transSinkCount A S₀ S₁ (n - 1) + transSourceCount A S₀ S₁ (n - 1) ≤ n := by
      have hexcess : (∑ X : C₁, ((fib X).card - 1)) + Fintype.card C₁ = ∑ X : C₁, (fib X).card := by
        calc (∑ X : C₁, ((fib X).card - 1)) + Fintype.card C₁
            = (∑ X : C₁, ((fib X).card - 1)) + ∑ _X : C₁, 1 := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_id]
          _ = ∑ X : C₁, ((fib X).card - 1 + 1) := (Finset.sum_add_distrib).symm
          _ = ∑ X : C₁, (fib X).card :=
              Finset.sum_congr rfl fun X _ => by have := hfib_ge1 X; omega
      have hge_SS : (Sinks ∪ Sources).card ≤ ∑ X : C₁, ((fib X).card - 1) := by
        calc (Sinks ∪ Sources).card
            = ∑ _X ∈ Sinks ∪ Sources, 1 := by simp
          _ ≤ ∑ X ∈ Sinks ∪ Sources, ((fib X).card - 1) := by
              refine Finset.sum_le_sum fun X hX => ?_
              rw [Finset.mem_union] at hX
              rcases hX with hX | hX
              · have h2 : 2 ≤ (fib X).card := hge2.1 X (Finset.mem_filter.mp hX).2; omega
              · have h2 : 2 ≤ (fib X).card := hge2.2 X (Finset.mem_filter.mp hX).2; omega
          _ ≤ ∑ X : C₁, ((fib X).card - 1) :=
              Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      rw [Finset.card_union_of_disjoint hdisj_SS] at hge_SS
      have hC1 : Fintype.card C₁ = transSCCCount A S₀ S₁ (n - 1) := (quotCard_eq_card s₁).symm
      have hSnk : Sinks.card = transSinkCount A S₀ S₁ (n - 1) := by
        unfold transSinkCount; congr 1
      have hSrc : Sources.card = transSourceCount A S₀ S₁ (n - 1) := by
        unfold transSourceCount; congr 1
      omega
    have hSrc_ge1 : 1 ≤ transSourceCount A S₀ S₁ (n - 1) := by
      calc 1 = blockCount A S₀ S₁ := hd1.symm
        _ ≤ transSourceCount A S₀ S₁ (n - 1) := blockCount_le_transSourceCount S₁ hBij hTrans (n - 1)
    by_cases ha2 : 2 ≤ transSourceCount A S₀ S₁ (n - 1)
    · have hf : zhuF A S₀ S₁ (n - 1) ≤ 2 * blockCount A S₀ S₁ + (n - 4) := by
        dsimp only [zhuF]; omega
      have hres := transSCCCount_eq_blockCount_of_zhuF S₁ hBij hTrans (n - 4) (n - 1) hf
      rw [hd1] at hres
      have hidx : n - 1 + (n - 4) = 2 * n - 5 := by omega
      rwa [hidx] at hres
    · have hg : zhuG A S₀ S₁ (n - 1) ≤ 2 * blockCount A S₀ S₁ + (n - 4) := by
        dsimp only [zhuG]; omega
      have hres := transSCCCount_eq_blockCount_of_zhuG S₁ hBij hTrans (n - 4) (n - 1) hg
      rw [hd1] at hres
      have hidx : n - 1 + (n - 4) = 2 * n - 5 := by omega
      rwa [hidx] at hres

/-- Helper for Case 4 of Lemma 1.4: Full-transitive 2-Block Shift-Isolation Contradiction
(`d = 1, n ≥ 5, c(n - 2) = n - 1 → c(n - 1) ≠ n - 2`). -/
lemma trans_pred_one_ne_pred_two [Nonempty Q] {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (hS₁ : ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀)
    (hn5 : 5 ≤ Fintype.card Q) (hd1 : blockCount A S₀ S₁ = 1)
    (hc2 : transSCCCount A S₀ S₁ (Fintype.card Q - 2) = Fintype.card Q - 1) :
    transSCCCount A S₀ S₁ (Fintype.card Q - 1) ≠ Fintype.card Q - 2 := by
  classical
  intro hc1
  let n := Fintype.card Q
  let s₂ := transSCC A S₀ S₁ (n - 2)
  let s₁ := transSCC A S₀ S₁ (n - 1)
  let C₂ := Quotient s₂
  let C₁ := Quotient s₁
  have hC₂_card : Fintype.card C₂ = n - 1 := (quotCard_eq_card s₂).symm.trans hc2
  have hC₁_card : Fintype.card C₁ = n - 2 := (quotCard_eq_card s₁).symm.trans hc1
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
    show (fib₂ xW).card = 2
    omega
  have hW_ne : W.Nonempty := Finset.card_pos.mp (by omega)
  -- Step 2: Pick a sink `V` and a distinct source `U ≠ V` in `Π_{n - 1}`
  have huniv₁_ne : (Finset.univ : Finset C₁).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
  obtain ⟨V, _, hV_max'⟩ := exists_max_in_finset A S₀ S₁ (n - 1) Finset.univ huniv₁_ne
  have hV_max : IsSink A S₀ S₁ (n - 1) V := fun Y h => hV_max' Y (Finset.mem_univ Y) h
  have hexW₁ : ∃ W₁ : C₁, W₁ ≠ V := by
    by_contra hall; push Not at hall
    have hsub : Subsingleton C₁ := ⟨fun x y => (hall x).trans (hall y).symm⟩
    have hle1 : Fintype.card C₁ ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  obtain ⟨W₁, hW₁V⟩ := hexW₁
  let DW : Finset C₁ := Finset.univ.filter (fun x => condLe A S₀ S₁ (n - 1) x W₁)
  have hDW_ne : DW.Nonempty :=
    ⟨W₁, Finset.mem_filter.mpr ⟨Finset.mem_univ W₁, condLe_refl A S₀ S₁ (n - 1) W₁⟩⟩
  obtain ⟨U, hU_DW, hU_min'⟩ := exists_min_in_finset A S₀ S₁ (n - 1) DW hDW_ne
  have hUW₁ : condLe A S₀ S₁ (n - 1) U W₁ := (Finset.mem_filter.mp hU_DW).2
  have hU_isMin : IsSource A S₀ S₁ (n - 1) U := fun Y hYU =>
    hU_min' Y (Finset.mem_filter.mpr ⟨Finset.mem_univ Y, condLe_trans A S₀ S₁ (n - 1) hYU hUW₁⟩) hYU
  have hUV : U ≠ V := fun heq => hW₁V (hV_max W₁ (heq ▸ hUW₁))
  -- Exact fibers of `C₁`: `|fib₁ U| = 2`, `|fib₁ V| = 2`, all other fibers have size `1`
  let fib₁ : C₁ → Finset Q := fun y => Finset.univ.filter (fun q => Quotient.mk s₁ q = y)
  have hfib₁_ge1 : ∀ y : C₁, 1 ≤ (fib₁ y).card := fun y => by
    obtain ⟨q, rfl⟩ := Quotient.exists_rep y
    exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, rfl⟩⟩
  have hge2 := sink_source_fiber_ge_two hBij hTrans hS₁
  have hfib₁_V_ge2 : 2 ≤ (fib₁ V).card := by
    have := hge2.1 V hV_max; rwa [fiberOf_eq_filter] at this
  have hfib₁_U_ge2 : 2 ≤ (fib₁ U).card := by
    have := hge2.2 U hU_isMin; rwa [fiberOf_eq_filter] at this
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
  -- Step 3: `W` equals `fib₁ U` or `fib₁ V`, and so does every shift `W · b` (`b ∈ S₀`)
  have hsub_fib₁_eq : ∀ T : Finset Q, T.card = 2 →
      (∀ p ∈ T, ∀ q ∈ T, s₁.r p q) → T = fib₁ U ∨ T = fib₁ V := by
    intro T hTcard hTrel
    obtain ⟨p₀, hp₀⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    let y₀ : C₁ := Quotient.mk s₁ p₀
    have hTsub : T ⊆ fib₁ y₀ := fun q hq =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ q, Quotient.sound (hTrel q hq p₀ hp₀)⟩
    have hy₀_ge2 : 2 ≤ (fib₁ y₀).card := hTcard ▸ Finset.card_le_card hTsub
    by_cases hU : y₀ = U
    · left; rw [hU] at hTsub; exact Finset.eq_of_subset_of_card_le hTsub (by omega)
    · right
      have hV : y₀ = V := by
        by_contra hneV; have := hfib₁_other_eq1 y₀ hU hneV; omega
      rw [hV] at hTsub; exact Finset.eq_of_subset_of_card_le hTsub (by omega)
  have hW_rel1 : ∀ p ∈ W, ∀ q ∈ W, s₁.r p q := by
    intro p hp q hq
    rw [Finset.mem_filter] at hp hq
    have hrel2 : s₂.r p q := Quotient.exact (hp.2.trans hq.2.symm)
    exact ⟨transReach_mono A S₀ S₁ (by omega) hrel2.1, transReach_mono A S₀ S₁ (by omega) hrel2.2⟩
  have hW_eq : W = fib₁ U ∨ W = fib₁ V := hsub_fib₁_eq W hW_card hW_rel1
  have hW_step_cases : ∀ b ∈ S₀, W.image (fun q => A.step q b) = fib₁ U ∨
      W.image (fun q => A.step q b) = fib₁ V := by
    intro b hb
    have hcard_img : (W.image (fun q => A.step q b)).card = 2 := by
      rw [Finset.card_image_of_injective W (hBij b hb).1, hW_card]
    refine hsub_fib₁_eq _ hcard_img ?_
    intro x hx y hy
    rw [Finset.mem_image] at hx hy
    rcases hx with ⟨p, hpW, rfl⟩
    rcases hy with ⟨q, hqW, rfl⟩
    rw [Finset.mem_filter] at hpW hqW
    have hrel2 : s₂.r p q := Quotient.exact (hpW.2.trans hqW.2.symm)
    have hstep := transSCC_step A S₀ S₁ (n - 2) hb hrel2
    have hidx : n - 2 + 1 = n - 1 := by omega
    rwa [hidx] at hstep
  -- Step 4: Transitivity of `⟨S₀⟩` yields `bstar ∈ S₀` moving `W` onto the other 2-block
  have hex_bstar : ∃ b ∈ S₀, W.image (fun q => A.step q b) ≠ W := by
    by_contra hall
    push Not at hall
    have hclosed : ∀ g : List α, (∀ b ∈ g, b ∈ S₀) → ∀ p ∈ W, A.eval p g ∈ W := by
      intro g
      induction g with
      | nil => intro _ p hp; exact hp
      | cons b g ih =>
        intro hS p hp
        have hb : b ∈ S₀ := hS b List.mem_cons_self
        have hstep_mem : A.step p b ∈ W := by
          rw [← hall b hb]; exact Finset.mem_image_of_mem _ hp
        exact ih (fun c hc => hS c (List.mem_cons_of_mem b hc)) (A.step p b) hstep_mem
    obtain ⟨p₀, hp₀⟩ := hW_ne
    have hW_proper : W ≠ Finset.univ := fun heq => by
      have := congrArg Finset.card heq; rw [hW_card, Finset.card_univ] at this; omega
    obtain ⟨r₀, _, hr₀⟩ := Finset.exists_of_ssubset
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ W, hW_proper⟩)
    obtain ⟨g, hgS, hgr⟩ := hTrans p₀ r₀
    exact hr₀ (hgr ▸ hclosed g hgS p₀ hp₀)
  obtain ⟨bstar, hbstar, hbstar_ne⟩ := hex_bstar
  -- Step 5: Every edge of `E_{n - 2}` preserves `∈ W`, contradicting `w(n - 2) = 1`!
  have hV_closed : ∀ u v : Q, transEdge A S₀ S₁ (n - 1) u v → u ∈ fib₁ V → v ∈ fib₁ V := by
    intro u v huv hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨Finset.mem_univ v, hV_max (Quotient.mk s₁ v) ?_⟩
    rw [← hu.2]; exact Relation.ReflTransGen.single huv
  have hU_closed : ∀ u v : Q, transEdge A S₀ S₁ (n - 1) u v → v ∈ fib₁ U → u ∈ fib₁ U := by
    intro u v huv hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨Finset.mem_univ u, hU_isMin (Quotient.mk s₁ u) ?_⟩
    rw [← hv.2]; exact Relation.ReflTransGen.single huv
  have hno_cross : ∀ u v : Q, transEdge A S₀ S₁ (n - 2) u v → (u ∈ W ↔ v ∈ W) := by
    intro u v huv
    have huv1 : transEdge A S₀ S₁ (n - 1) u v := transEdge_mono A S₀ S₁ (by omega) huv
    have huv_step : transEdge A S₀ S₁ (n - 1) (A.step u bstar) (A.step v bstar) := by
      have h := transEdge_step A S₀ S₁ (n - 2) hbstar huv
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
        exact (hBij bstar hbstar).1 hv'eq ▸ hv'W
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
        exact (hBij bstar hbstar).1 hu'eq ▸ hu'W
  have hW_proper : W ≠ Finset.univ := fun heq => by
    have := congrArg Finset.card heq; rw [hW_card, Finset.card_univ] at this; omega
  obtain ⟨u, v, huv, hcross⟩ :=
    exists_transEdge_crossing_d_eq_one hBij hTrans hS₁ hd1 hW_ne hW_proper
  exact hcross (hno_cross u v huv)

/-- **Lemma 1.4 (Full-Transitive `d = 1` World-Record Bound)**:
Whenever `d = 1` and `n ≥ 5`, `Γ_{2n - 5}` is strongly connected (`c(2n - 5) = 1`). -/
theorem trans_d_eq_one_bound [Nonempty Q] {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (hS₁ : ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀)
    (hn5 : 5 ≤ Fintype.card Q) (hd1 : blockCount A S₀ S₁ = 1) :
    transSCCCount A S₀ S₁ (2 * Fintype.card Q - 5) = 1 := by
  classical
  set n := Fintype.card Q
  have hle_n := transSCCCount_le_card A S₀ S₁ (n - 2)
  -- Equipartition impossibility when `c(n - 1) = c(n - 2) ∈ {n - 2, n - 1}`
  have hno_eq_inv : transSCCCount A S₀ S₁ (n - 1) = transSCCCount A S₀ S₁ (n - 2) →
      transSCCCount A S₀ S₁ (n - 2) ≠ n - 2 ∧ transSCCCount A S₀ S₁ (n - 2) ≠ n - 1 := by
    intro heq
    let π : Quotient (transSCC A S₀ S₁ (n - 2)) → Quotient (transSCC A S₀ S₁ (n - 1)) :=
      Quotient.lift (Quotient.mk (transSCC A S₀ S₁ (n - 1))) fun _ _ h =>
        Quotient.sound ⟨transReach_mono A S₀ S₁ (by omega) h.1,
          transReach_mono A S₀ S₁ (by omega) h.2⟩
    have hπ_surj : Function.Surjective π := fun y =>
      Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
    have hπ_bij : Function.Bijective π :=
      (Fintype.bijective_iff_surjective_and_card π).mpr ⟨hπ_surj, heq.symm⟩
    have hInv : ∀ b ∈ S₀, ∀ p q : Q,
        (transSCC A S₀ S₁ (n - 2)).r p q →
        (transSCC A S₀ S₁ (n - 2)).r (A.step p b) (A.step q b) := by
      intro b hb p q hpq
      have hstep := transSCC_step A S₀ S₁ (n - 2) hb hpq
      have hidx : n - 2 + 1 = n - 1 := by omega
      rw [hidx] at hstep
      exact Quotient.exact (hπ_bij.1 (Quotient.sound hstep))
    obtain ⟨s, hs1, _, hmul⟩ := inv_setoid_block_card_eq hBij hTrans (transSCC A S₀ S₁ (n - 2)) hInv
    change transSCCCount A S₀ S₁ (n - 2) * s = n at hmul
    have hs_cases : s = 1 ∨ 2 ≤ s := by omega
    constructor
    · intro h2
      rw [h2] at hmul
      rcases hs_cases with rfl | hs2
      · omega
      · zify [(show 2 ≤ n by omega)] at hmul; nlinarith
    · intro h1
      rw [h1] at hmul
      rcases hs_cases with rfl | hs2
      · omega
      · zify [(show 1 ≤ n by omega)] at hmul; nlinarith
  by_cases hacyc : transSCCCount A S₀ S₁ (n - 2) = n
  · -- Case 1: `c(n - 2) = n` → DAG-Shift Teleportation (`VolkovD6.sccCount_half_eq_one_of_acyclic`)!
    rcases hS₁ with ⟨a₀, ha₀, z₀, m₀, hDef⟩
    have hle_ry : ∀ k : ℕ, transSCCCount A S₀ S₁ k ≤ AlpogePrimitive.sccCount A S₀ z₀ m₀ k := by
      intro k
      have hre : ∀ p q : Q, AlpogePrimitive.ryReach A S₀ z₀ m₀ k p q → transReach A S₀ S₁ k p q := by
        intro p q hr
        induction hr with
        | refl => exact .refl
        | tail _ hstep ih =>
          rcases hstep with ⟨g, hglen, hgS, hgz, hgm⟩
          exact ih.tail ⟨a₀, ha₀, z₀, m₀, hDef, g, hglen, hgS, hgz, hgm⟩
      let φ : Quotient (AlpogePrimitive.sccSetoid A S₀ z₀ m₀ k) → Quotient (transSCC A S₀ S₁ k) :=
        Quotient.lift (Quotient.mk (transSCC A S₀ S₁ k)) fun _ _ h =>
          Quotient.sound ⟨hre _ _ h.1, hre _ _ h.2⟩
      have hsurj : Function.Surjective φ := fun y =>
        Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
      exact Fintype.card_le_of_surjective φ hsurj
    have hry_n : AlpogePrimitive.sccCount A S₀ z₀ m₀ (n - 2) = n := by
      have h1 := hle_ry (n - 2)
      have h2 := AlpogePrimitive.sccCount_le_card A S₀ z₀ m₀ (n - 2)
      omega
    have hhalf := VolkovD6.sccCount_half_eq_one_of_acyclic hBij hTrans hDef.1 (by omega) hry_n
    have htrans_half : transSCCCount A S₀ S₁ (n - 2 + n / 2) ≤ 1 :=
      (hle_ry (n - 2 + n / 2)).trans hhalf.le
    have hmono := transSCCCount_antitone A S₀ S₁ (show n - 2 + n / 2 ≤ 2 * n - 5 by omega)
    have hpos : 1 ≤ transSCCCount A S₀ S₁ (2 * n - 5) :=
      hd1 ▸ blockCount_le_transSCCCount A S₀ S₁ (2 * n - 5)
    omega
  · by_cases hnm1 : transSCCCount A S₀ S₁ (n - 2) = n - 1
    · -- Case 4: `c(n - 2) = n - 1` → equipartition rules out `c(n - 1) = n - 1`,
      -- and 2-Block Shift-Isolation rules out `c(n - 1) = n - 2`!
      have hc1_le := transSCCCount_antitone A S₀ S₁ (show n - 2 ≤ n - 1 by omega)
      have hne1 : transSCCCount A S₀ S₁ (n - 1) ≠ n - 1 := fun h =>
        (hno_eq_inv (h.trans hnm1.symm)).2 hnm1
      have hne2 : transSCCCount A S₀ S₁ (n - 1) ≠ n - 2 :=
        trans_pred_one_ne_pred_two hBij hTrans hS₁ hn5 hd1 hnm1
      exact trans_d_eq_one_of_le_sub_three hBij hTrans hS₁ hn5 hd1
        (show transSCCCount A S₀ S₁ (n - 1) ≤ n - 3 by omega)
    · by_cases hnm2 : transSCCCount A S₀ S₁ (n - 2) = n - 2
      · -- Case 3: `c(n - 2) = n - 2` → equipartition rules out `c(n - 1) = n - 2`!
        have hc1_le := transSCCCount_antitone A S₀ S₁ (show n - 2 ≤ n - 1 by omega)
        have hne2 : transSCCCount A S₀ S₁ (n - 1) ≠ n - 2 := fun h =>
          (hno_eq_inv (h.trans hnm2.symm)).1 hnm2
        exact trans_d_eq_one_of_le_sub_three hBij hTrans hS₁ hn5 hd1
          (show transSCCCount A S₀ S₁ (n - 1) ≤ n - 3 by omega)
      · -- Case 2: `c(n - 2) ≤ n - 3`
        have hc1_le := transSCCCount_antitone A S₀ S₁ (show n - 2 ≤ n - 1 by omega)
        exact trans_d_eq_one_of_le_sub_three hBij hTrans hS₁ hn5 hd1
          (show transSCCCount A S₀ S₁ (n - 1) ≤ n - 3 by omega)

/-! ### Regimes 2 (`2 ≤ d ≤ n / 3`) and 3 (`d = n / 2`, `n ≥ 6` even) -/

/-- Regime 2 (`2 ≤ d`, `3 * d ≤ n`): `zhuF (n - 1) ≤ n - d`, hence `c(2n - 3d - 1) = d`. -/
lemma trans_mid_d_bound [Nonempty Q] {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (hS₁ : ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀)
    (h3d : 3 * blockCount A S₀ S₁ ≤ Fintype.card Q) :
    transSCCCount A S₀ S₁ (Fintype.card Q - 1 + (Fintype.card Q - 3 * blockCount A S₀ S₁)) =
      blockCount A S₀ S₁ := by
  classical
  set n := Fintype.card Q
  set d := blockCount A S₀ S₁
  obtain ⟨s₀, hs₀_ge2, hblk_card, hmul⟩ := blockCard_eq hBij hTrans hS₁
  have hd_pos : 1 ≤ d := blockCount_pos A S₀ S₁
  have hs₀_ge3 : 3 ≤ s₀ := by
    by_contra hlt
    have : s₀ = 2 := by omega
    rw [this] at hmul
    omega
  -- Prove `zhuF (n - 1) ≤ n - d` by summing per block `B` of `Π_∞`
  let sInf := transSCCInf A S₀ S₁
  let s₁ := transSCC A S₀ S₁ (n - 1)
  let C₁ := Quotient s₁
  let BType := Quotient sInf
  let πInf : C₁ → BType :=
    Quotient.lift (Quotient.mk sInf) fun _ _ h =>
      Quotient.sound ⟨transReach_le_inf A S₀ S₁ (n - 1) h.1, transReach_le_inf A S₀ S₁ (n - 1) h.2⟩
  let F_B : BType → Finset C₁ := fun B => Finset.univ.filter (fun X => πInf X = B)
  let Snk_B : BType → Finset C₁ := fun B => (F_B B).filter (IsSink A S₀ S₁ (n - 1))
  let Src_B : BType → Finset C₁ := fun B => (F_B B).filter (IsSource A S₀ S₁ (n - 1))
  let fib₁ : C₁ → Finset Q := fiberOf s₁
  let blk : BType → Finset Q := fiberOf sInf
  -- `w(n - d - 1) = d` gives bijectivity of `Quotient (transWeak (n - d - 1)) → BType`
  have hw_eq : transWeakCount A S₀ S₁ (n - d - 1) = d :=
    transWeakCount_eq_blockCount hBij hTrans hS₁
  let ψ_w : Quotient (transWeak A S₀ S₁ (n - d - 1)) → BType :=
    Quotient.lift (Quotient.mk sInf) fun p q h => by
      have hw : (transWeakInf A S₀ S₁).r p q := by
        induction h with
        | rel u v huv => exact Relation.EqvGen.rel u v ⟨n - d - 1, huv⟩
        | refl x => exact Relation.EqvGen.refl x
        | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
        | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
      exact Quotient.sound ((transWeakInf_iff_sccInf hBij hTrans).mp hw)
  have hψw_surj : Function.Surjective ψ_w := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  have hψw_bij : Function.Bijective ψ_w :=
    (Fintype.bijective_iff_surjective_and_card ψ_w).mpr ⟨hψw_surj, hw_eq⟩
  have hge2 := sink_source_fiber_ge_two hBij hTrans hS₁
  have hper_block : ∀ B : BType, (F_B B).card + (Snk_B B).card ≤ s₀ - 1 := by
    intro B
    obtain ⟨q_rep, hq_rep⟩ := Quotient.exists_rep B
    have hFB_ne : (F_B B).Nonempty :=
      ⟨Quotient.mk s₁ q_rep, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq_rep⟩⟩
    by_cases h1 : (F_B B).card = 1
    · have hsub : Snk_B B ⊆ F_B B := Finset.filter_subset _ _
      have hle := Finset.card_le_card hsub
      omega
    · have hFB_ge2 : 2 ≤ (F_B B).card := by
        have := Finset.card_pos.mpr hFB_ne; omega
      -- `Snk_B B` and `Src_B B` are disjoint inside `F_B B`!
      have hdisj : Disjoint (Snk_B B) (Src_B B) := by
        rw [Finset.disjoint_left]
        intro X hX_snk hX_src
        have hX_FB : X ∈ F_B B := (Finset.mem_filter.mp hX_snk).1
        have hsnk : IsSink A S₀ S₁ (n - 1) X := (Finset.mem_filter.mp hX_snk).2
        have hsrc : IsSource A S₀ S₁ (n - 1) X := (Finset.mem_filter.mp hX_src).2
        obtain ⟨p, hp⟩ := Quotient.exists_rep X
        have hother : ∃ Y ∈ F_B B, Y ≠ X := by
          by_contra hall
          push Not at hall
          have hsub : F_B B ⊆ {X} := fun Y hY => Finset.mem_singleton.mpr (hall Y hY)
          have := (Finset.card_le_card hsub).trans (Finset.card_singleton X).le
          omega
        rcases hother with ⟨Y, hY_FB, hYX⟩
        obtain ⟨q, hq⟩ := Quotient.exists_rep Y
        have hpB : Quotient.mk sInf p = B := by
          have := (Finset.mem_filter.mp hX_FB).2; rwa [← hp] at this
        have hqB : Quotient.mk sInf q = B := by
          have := (Finset.mem_filter.mp hY_FB).2; rwa [← hq] at this
        have hrel_w : (transWeak A S₀ S₁ (n - d - 1)).r p q :=
          Quotient.exact (hψw_bij.1 (hpB.trans hqB.symm))
        -- Every edge of `E_{n - d - 1}` preserves `∈ fib₁ X`
        have hpres : ∀ u v : Q, (transWeak A S₀ S₁ (n - d - 1)).r u v →
            (u ∈ fib₁ X ↔ v ∈ fib₁ X) := by
          intro u v huv
          induction huv with
          | rel a' b' hab =>
            have hab1 : transEdge A S₀ S₁ (n - 1) a' b' :=
              transEdge_mono A S₀ S₁ (by omega) hab
            constructor
            · intro ha'
              rw [mem_fiberOf] at ha' ⊢
              refine hsnk (Quotient.mk s₁ b') ?_
              rw [← ha']; exact Relation.ReflTransGen.single hab1
            · intro hb'
              rw [mem_fiberOf] at hb' ⊢
              refine hsrc (Quotient.mk s₁ a') ?_
              rw [← hb']; exact Relation.ReflTransGen.single hab1
          | refl _ => exact Iff.rfl
          | symm _ _ _ ih => exact ih.symm
          | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
        have hp_in : p ∈ fib₁ X := (mem_fiberOf s₁ X p).mpr hp
        have hq_in : q ∈ fib₁ X := (hpres p q hrel_w).mp hp_in
        exact hYX (hq.symm.trans ((mem_fiberOf s₁ X q).mp hq_in))
      -- `Src_B B` is nonempty (minimal element of `F_B B` under `condLe (n - 1)`)
      have hSrc_ne : (Src_B B).Nonempty := by
        obtain ⟨X, hXF, hXmin⟩ := exists_min_in_finset A S₀ S₁ (n - 1) (F_B B) hFB_ne
        have hπX : πInf X = B := (Finset.mem_filter.mp hXF).2
        refine ⟨X, Finset.mem_filter.mpr ⟨hXF, fun Y hYX => ?_⟩⟩
        have hπY : πInf Y = πInf X :=
          Quotient.inductionOn₂ Y X (fun y x hyx =>
            Quotient.sound ((transSCCInf_iff_reachInf hBij hTrans).mpr
              (transReach_le_inf A S₀ S₁ (n - 1) hyx))) hYX
        exact hXmin Y (Finset.mem_filter.mpr ⟨Finset.mem_univ Y, hπY.trans hπX⟩) hYX
      -- Partition `blk B = (F_B B).biUnion fib₁`
      have hfib_disj : Set.PairwiseDisjoint (↑(F_B B) : Set C₁) fib₁ := by
        intro X _ Y _ hXY
        show Disjoint (fib₁ X) (fib₁ Y)
        rw [Finset.disjoint_left]
        intro q hqX hqY
        rw [mem_fiberOf] at hqX hqY
        exact hXY (hqX.symm.trans hqY)
      have hblk_eq_biUnion : (F_B B).biUnion fib₁ = blk B := by
        ext q
        simp only [Finset.mem_biUnion, F_B, fib₁, blk, Finset.mem_filter, Finset.mem_univ,
          true_and, mem_fiberOf]
        constructor
        · rintro ⟨X, hXB, rfl⟩; exact hXB
        · intro hqB; exact ⟨Quotient.mk s₁ q, hqB, rfl⟩
      have hsum_blk : ∑ X ∈ F_B B, (fib₁ X).card = s₀ := by
        rw [← Finset.card_biUnion hfib_disj, hblk_eq_biUnion]
        exact hblk_card B
      have hfib_ge1 : ∀ X : C₁, 1 ≤ (fib₁ X).card := fun X => by
        obtain ⟨q, rfl⟩ := Quotient.exists_rep X
        exact Finset.card_pos.mpr ⟨q, (mem_fiberOf s₁ _ q).mpr rfl⟩
      have hexcess : (∑ X ∈ F_B B, ((fib₁ X).card - 1)) + (F_B B).card = s₀ := by
        calc (∑ X ∈ F_B B, ((fib₁ X).card - 1)) + (F_B B).card
            = (∑ X ∈ F_B B, ((fib₁ X).card - 1)) + ∑ _X ∈ F_B B, 1 := by simp
          _ = ∑ X ∈ F_B B, ((fib₁ X).card - 1 + 1) := (Finset.sum_add_distrib).symm
          _ = ∑ X ∈ F_B B, (fib₁ X).card :=
              Finset.sum_congr rfl fun X _ => by have := hfib_ge1 X; omega
          _ = s₀ := hsum_blk
      have hsub_SS : Snk_B B ∪ Src_B B ⊆ F_B B :=
        Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have hge_SS : (Snk_B B ∪ Src_B B).card ≤ ∑ X ∈ F_B B, ((fib₁ X).card - 1) := by
        calc (Snk_B B ∪ Src_B B).card
            = ∑ _X ∈ Snk_B B ∪ Src_B B, 1 := by simp
          _ ≤ ∑ X ∈ Snk_B B ∪ Src_B B, ((fib₁ X).card - 1) := by
              refine Finset.sum_le_sum fun X hX => ?_
              rw [Finset.mem_union] at hX
              rcases hX with hX | hX
              · have h2 : 2 ≤ (fib₁ X).card := hge2.1 X (Finset.mem_filter.mp hX).2; omega
              · have h2 : 2 ≤ (fib₁ X).card := hge2.2 X (Finset.mem_filter.mp hX).2; omega
          _ ≤ ∑ X ∈ F_B B, ((fib₁ X).card - 1) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_SS fun _ _ _ => Nat.zero_le _
      rw [Finset.card_union_of_disjoint hdisj] at hge_SS
      have hSrc_ge1 : 1 ≤ (Src_B B).card := Finset.card_pos.mpr hSrc_ne
      omega
  -- Sum over all `B : BType` to obtain `zhuF (n - 1) ≤ n - d`
  have hFB_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset BType) : Set BType) F_B := by
    intro B₁ _ B₂ _ hne
    show Disjoint (F_B B₁) (F_B B₂)
    rw [Finset.disjoint_left]
    intro X h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hSnk_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset BType) : Set BType) Snk_B := by
    intro B₁ _ B₂ _ hne
    show Disjoint (Snk_B B₁) (Snk_B B₂)
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hFB_disj (Finset.mem_univ B₁) (Finset.mem_univ B₂) hne)
  have hsum_FB : ∑ B : BType, (F_B B).card = transSCCCount A S₀ S₁ (n - 1) := by
    have hunion : (Finset.univ : Finset BType).biUnion F_B = Finset.univ := by
      ext X
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, F_B, Finset.mem_filter, iff_true]
      exact ⟨πInf X, rfl⟩
    rw [← Finset.card_biUnion hFB_disj, hunion, Finset.card_univ]
    exact (quotCard_eq_card s₁).symm
  have hsum_Snk : ∑ B : BType, (Snk_B B).card = transSinkCount A S₀ S₁ (n - 1) := by
    have hunion : (Finset.univ : Finset BType).biUnion Snk_B =
        Finset.univ.filter (IsSink A S₀ S₁ (n - 1)) := by
      ext X
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Snk_B, F_B, Finset.mem_filter]
      constructor
      · rintro ⟨_, ⟨_, hsnk⟩⟩; exact hsnk
      · intro hsnk; exact ⟨πInf X, ⟨rfl, hsnk⟩⟩
    rw [← Finset.card_biUnion hSnk_disj, hunion]
    unfold transSinkCount; congr 1
  have hzhuF_le : zhuF A S₀ S₁ (n - 1) ≤ n - d := by
    have hsum_le : ∑ B : BType, ((F_B B).card + (Snk_B B).card) ≤ ∑ _B : BType, (s₀ - 1) :=
      Finset.sum_le_sum fun B _ => hper_block B
    rw [Finset.sum_add_distrib, hsum_FB, hsum_Snk, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.cast_id] at hsum_le
    have hB_card : Fintype.card BType = d := (quotCard_eq_card sInf).symm
    rw [hB_card] at hsum_le
    have hds : d * (s₀ - 1) = n - d := by
      have h1 : d * (s₀ - 1) + d = n := by
        calc d * (s₀ - 1) + d = d * ((s₀ - 1) + 1) := by ring
          _ = d * s₀ := by congr 1; omega
          _ = n := hmul
      omega
    change transSCCCount A S₀ S₁ (n - 1) + transSinkCount A S₀ S₁ (n - 1) ≤ n - d
    exact hsum_le.trans hds.le
  exact transSCCCount_eq_blockCount_of_zhuF S₁ hBij hTrans (n - 3 * d) (n - 1)
    (show zhuF A S₀ S₁ (n - 1) ≤ 2 * d + (n - 3 * d) by omega)

/-- Regime 3 (`s₀ = 2`, i.e., `2 * d = n`): `E_{n - 1} = E_∞`, so `c(n - 1) = d`. -/
lemma trans_half_d_bound [Nonempty Q] {A : DFA Q α} {S₀ S₁ : Set α}
    (hBij : ∀ b ∈ S₀, Function.Bijective (fun q => A.step q b))
    (hTrans : ∀ p q : Q, ∃ g : List α, (∀ b ∈ g, b ∈ S₀) ∧ A.eval p g = q)
    (hS₁ : ∃ a ∈ S₁, ∃ z₀ m₀ : Q, A.IsDefectOneLetter a z₀ m₀)
    (hblk2 : ∀ B : Quotient (transSCCInf A S₀ S₁),
      (fiberOf (transSCCInf A S₀ S₁) B).card = 2) :
    transSCCCount A S₀ S₁ (Fintype.card Q - 1) = blockCount A S₀ S₁ := by
  classical
  let E : ℕ → Finset (Q × Q) := fun k => Finset.univ.filter (fun p => transEdge A S₀ S₁ k p.1 p.2)
  let Einf : Finset (Q × Q) := Finset.univ.filter (fun p => transEdgeInf A S₀ S₁ p.1 p.2)
  have hE_mono : ∀ {j k : ℕ}, j ≤ k → E j ⊆ E k := fun hjk p hp => by
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ p, transEdge_mono A S₀ S₁ hjk hp.2⟩
  have hE_sub_inf : ∀ k : ℕ, E k ⊆ Einf := fun k p hp => by
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ p, ⟨k, hp.2⟩⟩
  have hE0_pos : 1 ≤ (E 0).card := by
    rcases hS₁ with ⟨a, ha, z₀, m₀, hDef⟩
    refine Finset.card_pos.mpr ⟨(z₀, m₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨a, ha, z₀, m₀, hDef, [], le_rfl, fun _ h => absurd h (List.not_mem_nil), rfl, rfl⟩
  -- `Prod.fst` is injective on `Einf` because every block of `Π_∞` has size `2` and `E_∞` is irreflexive!
  have hEinf_le : Einf.card ≤ Fintype.card Q := by
    have hinj : Set.InjOn Prod.fst (Einf : Set (Q × Q)) := by
      rintro ⟨u, v₁⟩ h1 ⟨u', v₂⟩ h2 hfst
      dsimp only at hfst
      subst hfst
      have he1 : transEdgeInf A S₀ S₁ u v₁ := (Finset.mem_filter.mp h1).2
      have he2 : transEdgeInf A S₀ S₁ u v₂ := (Finset.mem_filter.mp h2).2
      have hne1 : v₁ ≠ u := fun h => transEdgeInf_irrefl S₁ hBij u (by rwa [h] at he1)
      have hne2 : v₂ ≠ u := fun h => transEdgeInf_irrefl S₁ hBij u (by rwa [h] at he2)
      let B := Quotient.mk (transSCCInf A S₀ S₁) u
      let blkB := fiberOf (transSCCInf A S₀ S₁) B
      have hu_in : u ∈ blkB := (mem_fiberOf _ B u).mpr rfl
      have hv1_in : v₁ ∈ blkB := (mem_fiberOf _ B v₁).mpr
        (Quotient.sound ((transSCCInf_iff_reachInf hBij hTrans).mpr
          (transReachInf_symm hBij hTrans (Relation.ReflTransGen.single he1))))
      have hv2_in : v₂ ∈ blkB := (mem_fiberOf _ B v₂).mpr
        (Quotient.sound ((transSCCInf_iff_reachInf hBij hTrans).mpr
          (transReachInf_symm hBij hTrans (Relation.ReflTransGen.single he2))))
      by_contra hne
      have hv12 : v₁ ≠ v₂ := fun h => hne (by rw [h])
      have hsub : ({u, v₁, v₂} : Finset Q) ⊆ blkB := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hu_in
        · exact hv1_in
        · exact hv2_in
      have hcard3 : ({u, v₁, v₂} : Finset Q).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hne1.symm, hne2.symm]),
          Finset.card_insert_of_notMem (by simp [hv12]), Finset.card_singleton]
      have hle2 := (Finset.card_le_card hsub).trans (hblk2 B).le
      omega
    calc Einf.card = (Einf.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ : Finset Q).card := Finset.card_le_univ _
      _ = Fintype.card Q := Finset.card_univ
  -- Strict edge growth while `E k ≠ Einf`
  have hgrow : ∀ k : ℕ, E k ≠ Einf → (E k).card < (E (k + 1)).card := by
    intro k hne
    refine lt_of_le_of_ne (Finset.card_le_card (hE_mono (Nat.le_succ k))) fun heq => hne ?_
    have hEeq : E k = E (k + 1) := Finset.eq_of_subset_of_card_le (hE_mono (Nat.le_succ k)) heq.symm.le
    have hstep : ∀ b ∈ S₀, ∀ u v : Q,
        transEdge A S₀ S₁ k u v → transEdge A S₀ S₁ k (A.step u b) (A.step v b) := by
      intro b hb u v huv
      have hmem : (A.step u b, A.step v b) ∈ E (k + 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, transEdge_step A S₀ S₁ k hb huv⟩
      rw [← hEeq] at hmem
      exact (Finset.mem_filter.mp hmem).2
    have hword : ∀ g : List α, (∀ b ∈ g, b ∈ S₀) → ∀ u v : Q,
        transEdge A S₀ S₁ k u v → transEdge A S₀ S₁ k (A.eval u g) (A.eval v g) := by
      intro g
      induction g with
      | nil => intro _ _ _ h; exact h
      | cons b g ih =>
        intro hS u v h
        exact ih (fun c hc => hS c (List.mem_cons_of_mem b hc)) _ _
          (hstep b (hS b List.mem_cons_self) u v h)
    refine Finset.Subset.antisymm (hE_sub_inf k) fun p hp => ?_
    rcases (Finset.mem_filter.mp hp).2 with ⟨_, a, ha, z₀, m₀, hDef, g, _, hgS, hgz, hgm⟩
    have h0 : transEdge A S₀ S₁ k z₀ m₀ :=
      ⟨a, ha, z₀, m₀, hDef, [], Nat.zero_le k, fun _ h => absurd h (List.not_mem_nil), rfl, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ p, ?_⟩
    have := hword g hgS z₀ m₀ h0
    rwa [hgz, hgm] at this
  have hiter : ∀ t k : ℕ, Einf.card ≤ (E k).card + t → E (k + t) = Einf := by
    intro t
    induction t with
    | zero =>
      intro k hle
      exact Finset.eq_of_subset_of_card_le (hE_sub_inf k) (by simpa using hle)
    | succ t ih =>
      intro k hle
      by_cases heq : E k = Einf
      · exact Finset.Subset.antisymm (hE_sub_inf _) (heq ▸ hE_mono (Nat.le_add_right k (t + 1)))
      · have hlt := hgrow k heq
        have hres := ih (k + 1) (by omega)
        have hadd : k + 1 + t = k + (t + 1) := by omega
        rwa [hadd] at hres
  have hE_eq : E (Fintype.card Q - 1) = Einf := by
    simpa using hiter (Fintype.card Q - 1) 0 (by omega)
  have hInf_to_n1 : ∀ p q : Q, transReachInf A S₀ S₁ p q →
      transReach A S₀ S₁ (Fintype.card Q - 1) p q := by
    intro p q hr
    induction hr with
    | refl => exact .refl
    | @tail b c _ hstep ih =>
      have hmem : (b, c) ∈ E (Fintype.card Q - 1) := by
        rw [hE_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstep⟩
      exact ih.tail (Finset.mem_filter.mp hmem).2
  let ψ : Quotient (transSCCInf A S₀ S₁) → Quotient (transSCC A S₀ S₁ (Fintype.card Q - 1)) :=
    Quotient.lift (Quotient.mk (transSCC A S₀ S₁ (Fintype.card Q - 1))) fun _ _ h =>
      Quotient.sound ⟨hInf_to_n1 _ _ h.1, hInf_to_n1 _ _ h.2⟩
  have hψ_surj : Function.Surjective ψ := fun y =>
    Quotient.inductionOn y fun q => ⟨Quotient.mk _ q, rfl⟩
  have hle_d : transSCCCount A S₀ S₁ (Fintype.card Q - 1) ≤ blockCount A S₀ S₁ :=
    Fintype.card_le_of_surjective ψ hψ_surj
  have hge_d := blockCount_le_transSCCCount A S₀ S₁ (Fintype.card Q - 1)
  omega

end OrbitDigraph

end VolkovD6Transitive

/-! ### Main Public World-Record Theorems (Theorem T18) -/

/-- **Theorem T18 (`n ≥ 5` Exact Bound `1 + (n - 2)(2n - 4) = 2n² - 8n + 9`)**:
For EVERY synchronizing DFA on `n ≥ 5` states in Zhu (FSTTCS 2024)'s exact full transitive
defect-`≤ 1` class (primitive OR imprimitive, multiple defect-1 letters allowed), every nonempty
proper subset extends in length `≤ 2n - 4`, yielding a synchronizing word of length at most
`1 + (n - 2) * (2 * n - 4)`. -/
theorem transitive_defectOne_ge_five_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S₀ S₁ : Set α)
    (hn5 : 5 ≤ Fintype.card Q) (hSync : A.IsSynchronizing)
    (hT : IsTransitiveDefectLeOne A S₀ S₁) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 1 + (Fintype.card Q - 2) * (2 * Fintype.card Q - 4) := by
  open VolkovD6Transitive in
  set n := Fintype.card Q
  have hS₁ := exists_defectOne_in_S₁ hSync (by omega) hT
  obtain ⟨s₀, hs₀_ge2, hblk_card, hmul⟩ := blockCard_eq hT.2.1 hT.2.2.1 hS₁
  set d := blockCount A S₀ S₁
  have hd_pos : 1 ≤ d := blockCount_pos A S₀ S₁
  -- Universal extension bound `ext(S) ≤ 2n - 4` across ALL three regimes (`d = 1`, `2 ≤ d ≤ n/3`, `d = n/2`)
  have hext : ∀ S : Finset Q, S.Nonempty → S.card < n →
      ∃ w : List α, w.length ≤ 2 * n - 4 ∧ (A.preimage S w).card = S.card + 1 := by
    intro S hSne hSlt
    by_cases hd1 : d = 1
    · -- Regime 1 (`d = 1`): Lemma 1.4 gives `c(2n - 5) = 1`, Lemma 1.3 gives `ext(S) ≤ (2n - 5) + 1 = 2n - 4`
      have hm := trans_d_eq_one_bound hT.2.1 hT.2.2.1 hS₁ hn5 hd1
      rw [← hd1] at hm
      obtain ⟨w, hwlen, hwcard⟩ := blockEscape_extend hSync hT (2 * n - 5) hm hSne hSlt
      exact ⟨w, by omega, hwcard⟩
    · by_cases h3d : 3 * d ≤ n
      · -- Regime 2 (`2 ≤ d ≤ n / 3`): `c(2n - 3d - 1) = d`, Lemma 1.3 gives `ext(S) ≤ 2n - 2d - 1 ≤ 2n - 5`
        have hm := trans_mid_d_bound hT.2.1 hT.2.2.1 hS₁ h3d
        obtain ⟨w, hwlen, hwcard⟩ :=
          blockEscape_extend hSync hT (n - 1 + (n - 3 * d)) hm hSne hSlt
        exact ⟨w, by omega, hwcard⟩
      · -- Regime 3 (`3 * d > n`, so `s₀ = 2` and `2 * d = n`, `d ≥ 3`): `c(n - 1) = d`, `ext(S) ≤ n - 1 + d ≤ 2n - 4`
        have hs₀_eq2 : s₀ = 2 := by
          by_contra hne
          have : 3 ≤ s₀ := by omega
          nlinarith
        have h2d : 2 * d = n := by rw [hs₀_eq2] at hmul; omega
        have hblk2 : ∀ B : Quotient (transSCCInf A S₀ S₁),
            (fiberOf (transSCCInf A S₀ S₁) B).card = 2 :=
          fun B => (hblk_card B).trans hs₀_eq2
        have hm := trans_half_d_bound hT.2.1 hT.2.2.1 hS₁ hblk2
        obtain ⟨w, hwlen, hwcard⟩ := blockEscape_extend hSync hT (n - 1) hm hSne hSlt
        exact ⟨w, by omega, hwcard⟩
  -- Iterate extension `n - 2` times from `S_init = {z₀} a₀⁻¹` (size `2`, length `1`)
  have hex_univ : ∀ k : ℕ, ∀ T : Finset Q, T.Nonempty → n - T.card ≤ k →
      ∃ w : List α, A.preimage T w = Finset.univ ∧ w.length ≤ k * (2 * n - 4) := by
    intro k
    induction k with
    | zero =>
      intro T _ hle
      have hTle : T.card ≤ n := Finset.card_le_univ T
      exact ⟨[], by rw [DFA.preimage_nil, Finset.eq_univ_of_card T (by omega)], by simp⟩
    | succ k ih =>
      intro T hTne hle
      by_cases hfull : T.card = n
      · exact ⟨[], by rw [DFA.preimage_nil, Finset.eq_univ_of_card T hfull], Nat.zero_le _⟩
      · have hTlt : T.card < n := lt_of_le_of_ne (Finset.card_le_univ T) hfull
        obtain ⟨u, hulen, hucard⟩ := hext T hTne hTlt
        set T' := A.preimage T u
        have hT'ne : T'.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨v, hvuniv, hvlen⟩ := ih T' hT'ne (by omega)
        refine ⟨v ++ u, by rw [DFA.preimage_append]; exact hvuniv, ?_⟩
        rw [List.length_append]
        calc v.length + u.length ≤ k * (2 * n - 4) + (2 * n - 4) := Nat.add_le_add hvlen hulen
          _ = (k + 1) * (2 * n - 4) := by ring
  rcases hS₁ with ⟨a₀, _, z₀, m₀, hDef⟩
  set S_init : Finset Q := A.preimage {z₀} [a₀]
  have hS_init_card : S_init.card = 2 := hDef.2.1
  have hS_init_ne : S_init.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w_ext, hw_univ, hw_len⟩ := hex_univ (n - 2) S_init hS_init_ne (by omega)
  refine ⟨w_ext ++ [a₀], ?_, ?_⟩
  · rw [DFA.isSyncWord_iff_exists_preimage_eq_univ]
    exact ⟨z₀, by rw [DFA.preimage_append]; exact hw_univ⟩
  · simp only [List.length_append, List.length_singleton]
    omega

/-- **Theorem T18 (NEW WORLD RECORD ON ZHU FSTTCS 2024'S EXACT FULL TRANSITIVE CLASS)**:
For EVERY `n ≥ 4` and EVERY synchronizing DFA on `n` states where every letter has defect `≤ 1`
and the bijective letters generate a transitive permutation group (primitive OR imprimitive,
arbitrary number of defect-1 letters):
`∃ w, A.IsSyncWord w ∧ w.length ≤ 2 * n^2 - 8 * n + 9 ∧ w.length < 2 * n^2 - 7 * n + 7`,
strictly beating Zhu (FSTTCS 2024)'s published bound `2n² - 7n + 7` by `n - 2` for ALL `n ≥ 4`! -/
theorem transitive_defectOne_beats_zhu {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S₀ S₁ : Set α)
    (hn4 : 4 ≤ Fintype.card Q) (hSync : A.IsSynchronizing)
    (hT : IsTransitiveDefectLeOne A S₀ S₁) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 2 * (Fintype.card Q) ^ 2 - 8 * Fintype.card Q + 9 ∧
      w.length < 2 * (Fintype.card Q) ^ 2 - 7 * Fintype.card Q + 7 := by
  have hstrict : 2 * (Fintype.card Q) ^ 2 - 8 * Fintype.card Q + 9 <
      2 * (Fintype.card Q) ^ 2 - 7 * Fintype.card Q + 7 := by
    set n := Fintype.card Q
    have h8 : 8 * n ≤ 2 * n ^ 2 := by nlinarith
    have h7 : 7 * n ≤ 2 * n ^ 2 := by nlinarith
    zify [h8, h7]
    linarith
  by_cases hn5 : 5 ≤ Fintype.card Q
  · obtain ⟨w, hw, hlen⟩ := transitive_defectOne_ge_five_bound A S₀ S₁ hn5 hSync hT
    have hle : w.length ≤ 2 * (Fintype.card Q) ^ 2 - 8 * Fintype.card Q + 9 := by
      refine le_trans hlen ?_
      set n := Fintype.card Q
      have h8 : 8 * n ≤ 2 * n ^ 2 := by nlinarith
      zify [h8, (show 2 ≤ n by omega), (show 4 ≤ 2 * n by omega)]
      nlinarith
    exact ⟨w, hw, hle, lt_of_le_of_lt hle hstrict⟩
  · have hcard4 : Fintype.card Q = 4 := by omega
    obtain ⟨w, hw, hlen⟩ := cerny_card_le_four A (by omega) hSync
    have hle : w.length ≤ 2 * (Fintype.card Q) ^ 2 - 8 * Fintype.card Q + 9 := by
      rw [hcard4] at hlen ⊢
      exact le_trans hlen (by decide)
    exact ⟨w, hw, hle, lt_of_le_of_lt hle hstrict⟩

/-- **Theorem T18 Small-Case Corollary (`n ≤ 4`)**:
Every synchronizing DFA on `n ≤ 4` states in the full transitive defect-`≤ 1` class satisfies
the exact Černý Conjecture `w.length ≤ (n - 1) ^ 2`. -/
theorem transitive_defectOne_card_le_four_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (S₀ S₁ : Set α)
    (hn4 : Fintype.card Q ≤ 4) (hSync : A.IsSynchronizing)
    (_hT : IsTransitiveDefectLeOne A S₀ S₁) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  cerny_card_le_four A hn4 hSync

end Cerny
