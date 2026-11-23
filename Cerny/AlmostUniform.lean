import Cerny.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Zify

/-!
# Almost-Uniform Stationary Vectors & Full Berlinkov QE-1 Exact Černý Bound (Theorems H, H.2, H_k)

This file formalizes our unified 2-case proof of the **exact Černý Conjecture `(n - 1)^2`**
over `ℝ` (covering irrational letter weights `β_a > 0` and irrational exceptional weight `α₀ > 0`!)
for synchronizing DFAs admitting an almost-uniform positive stationary vector (`Theorem H`),
together with **unconditional Berlinkov Quasi-Eulerian Degree-1 without strong connectivity**
(`Theorem H.2`) and **multi-exception rational stationary vectors** (`Theorem H_k`), from
`docs/round4_two_cluster_dichotomy.md` §1 & §3.1.

## Main Results
* `Cerny.PositiveStationary`: positive letter weights `β : α → ℝ` (`∑ β = 1`) and positive
  stationary vector `π : Q → ℝ` (`π M_β = π`).
* `Cerny.positiveStationary_stronglyConnected` (**Lemma H.0(1)**): automatic strong connectivity.
* `Cerny.positiveStationary_word_avg` (**Lemma H.0(2)**): exact length-`k` `β`-weighted averaging.
* `Cerny.stronglyConnected_escape_entry` (**Lemma H.0(3)**): BFS escape (`≤ |S|`) and entry
  (`≤ n - |S|`) orbit bounds.
* `Cerny.almostUniform_cerny` (**Theorem H**): ANY synchronizing DFA with a positive stationary
  vector constant off 1 exceptional state `x₀` satisfies `w.length ≤ (Fintype.card Q - 1) ^ 2`.
  - Case 1 (`α₀ ∈ ℤ_{≥ 1}`): Steinberg `ℝ`-subspace averaging over `n - 1` integer levels.
  - Case 2 (`α₀ ∉ ℤ`): ZERO linear algebra — single unified `Finset.sum` potential `Ψ(S)`.
* `Cerny.berlinkov_qe1_cerny` (**Theorem H.2**): Full Berlinkov Quasi-Eulerian Degree-1 (NO
  strong connectivity assumed!) satisfies `w.length ≤ (Fintype.card Q - 1) ^ 2`.
* `Cerny.multiException_rational_bound` & `Cerny.multiException_half_bound` (**Theorem H_k**):
  Two-value rational stationary vector `(1, p / q₀)` with `k` exceptional states satisfies
  `w.length ≤ (q₀ * (n - k) + k * p - max p q₀) * (n - 1)`; in particular `α = 1/2` gives
  `w.length ≤ (2 * n - k - 2) * (n - 1) < 2 * (n - 1) ^ 2` for arbitrary `k`.
-/

namespace Cerny

universe u v

/-- Positive letter weights `β : α → ℝ` (`∑ β = 1`) and a positive stationary vector `π : Q → ℝ`
satisfying `(π M_β)(q) = ∑ p, π(p) ∑_{p·a = q} β(a) = π(q)` for all `q : Q`. -/
structure PositiveStationary {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q] (A : DFA Q α) where
  β : α → ℝ
  π : Q → ℝ
  hβ_pos : ∀ a : α, 0 < β a
  hβ_sum : ∑ a : α, β a = 1
  hπ_pos : ∀ q : Q, 0 < π q
  hstat : ∀ q : Q, ∑ p : Q, π p * (∑ a : α, if A.step p a = q then β a else 0) = π q

namespace AlmostUniform

section Helpers

variable {Q : Type u} {α : Type v}

/-- Pullback linear operator `(pullbackR A w v) q = v (A.eval q w)` on `Q → ℝ`. -/
private def pullbackR (A : DFA Q α) (w : List α) : (Q → ℝ) →ₗ[ℝ] (Q → ℝ) where
  toFun v q := v (A.eval q w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma pullbackR_nil (A : DFA Q α) (v : Q → ℝ) : pullbackR A [] v = v := rfl

private lemma pullbackR_append (A : DFA Q α) (u₁ u₂ : List α) (v : Q → ℝ) :
    pullbackR A (u₁ ++ u₂) v = pullbackR A u₁ (pullbackR A u₂ v) := by
  ext q; simp [pullbackR]

private lemma pullbackR_cons (A : DFA Q α) (a : α) (u : List α) (v : Q → ℝ) :
    pullbackR A (a :: u) v = pullbackR A [a] (pullbackR A u v) :=
  pullbackR_append A [a] u v

/-- Weighted inner-product linear functional `v ↦ ∑ q, π q * v q` on `Q → ℝ`. -/
private def dotLinR [Fintype Q] (π : Q → ℝ) : (Q → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ q : Q, π q * v q
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => by ring

private lemma finrank_ker_dotLinR [Fintype Q] {π : Q → ℝ} (hπ_sum : ∑ q : Q, π q ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (dotLinR π)) = Fintype.card Q - 1 := by
  classical
  have hex_nz : ∃ q₀ : Q, π q₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hπ_sum (Finset.sum_eq_zero fun q _ => hall q)
  obtain ⟨q₀, hq₀⟩ := hex_nz
  have hsurj : Function.Surjective (dotLinR π) := by
    intro c
    refine ⟨Pi.single q₀ (c / π q₀), ?_⟩
    simp only [dotLinR, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single q₀]
    · simp [Pi.single_eq_same, mul_div_cancel₀ _ hq₀]
    · intro q _ hq; simp [Pi.single_eq_of_ne hq]
    · intro h; exact absurd (Finset.mem_univ q₀) h
  have hrn := LinearMap.finrank_range_add_finrank_ker (dotLinR π)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, Module.finrank_pi] at hrn
  omega

/-- Product weight `∏ i : Fin k, β (f i)` of a length-`k` word `List.ofFn f`. -/
private def wordWeight (β : α → ℝ) {k : ℕ} (f : Fin k → α) : ℝ :=
  ∏ i : Fin k, β (f i)

/-- Equivalence `(α × (Fin k → α)) ≃ (Fin (k + 1) → α)` splitting off the head letter. -/
private def finConsEquiv (α : Type v) (k : ℕ) : (α × (Fin k → α)) ≃ (Fin (k + 1) → α) where
  toFun p := Fin.cons p.1 p.2
  invFun g := ⟨g 0, fun i => g i.succ⟩
  left_inv p := by
    ext
    · rfl
    · rfl
  right_inv g := by
    ext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; rfl

/-- Scale a positive stationary vector by a positive constant `c > 0`. -/
private def scaleStationary [Fintype Q] [Fintype α] [DecidableEq Q]
    {A : DFA Q α} (P : PositiveStationary A) (c : ℝ) (hc : 0 < c) :
    PositiveStationary A where
  β := P.β
  π q := c * P.π q
  hβ_pos := P.hβ_pos
  hβ_sum := P.hβ_sum
  hπ_pos q := mul_pos hc (P.hπ_pos q)
  hstat q := by
    have h := P.hstat q
    calc ∑ p : Q, (c * P.π p) * (∑ a : α, if A.step p a = q then P.β a else 0)
        = c * ∑ p : Q, P.π p * (∑ a : α, if A.step p a = q then P.β a else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => by ring
      _ = c * P.π q := by rw [h]

end Helpers

end AlmostUniform

/-! ### Section 1: Lemma H.0 — Automatic Strong Connectivity, Length-`k` Averaging & Escape/Entry -/

/-- **Lemma H.0(1) (Automatic Strong Connectivity)**:
Every synchronizing DFA with a positive stationary vector for positive letter weights `β` is
automatically strongly connected. -/
theorem positiveStationary_stronglyConnected {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    {A : DFA Q α} (hSync : A.IsSynchronizing) (P : PositiveStationary A) :
    A.IsStronglyConnected := by
  classical
  intro p q
  let R : Finset Q := Finset.univ.filter (fun x => ∃ w : List α, A.eval p w = x)
  have hpR : p ∈ R := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨[], rfl⟩
  have hR_closed : ∀ x ∈ R, ∀ a : α, A.step x a ∈ R := by
    intro x hx a
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨w, hw⟩
    exact ⟨w ++ [a], by rw [DFA.eval_append, hw]; rfl⟩
  have hR_eval : ∀ x ∈ R, ∀ w : List α, A.eval x w ∈ R := by
    intro x hx w
    induction w generalizing x with
    | nil => exact hx
    | cons a u ih => exact ih (A.step x a) (hR_closed x hx a)
  -- Sum stationarity over `R` to prove no edge enters `R` from `univ \ R`
  have hsum_eq : ∑ r ∈ R, P.π r =
      ∑ x : Q, P.π x * (∑ a : α, if A.step x a ∈ R then P.β a else 0) := by
    calc ∑ r ∈ R, P.π r
        = ∑ r ∈ R, ∑ x : Q, P.π x * (∑ a : α, if A.step x a = r then P.β a else 0) :=
            Finset.sum_congr rfl fun r _ => (P.hstat r).symm
      _ = ∑ x : Q, ∑ r ∈ R, P.π x * (∑ a : α, if A.step x a = r then P.β a else 0) :=
            Finset.sum_comm
      _ = ∑ x : Q, P.π x * (∑ a : α, ∑ r ∈ R, if A.step x a = r then P.β a else 0) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [← Finset.mul_sum, Finset.sum_comm]
      _ = ∑ x : Q, P.π x * (∑ a : α, if A.step x a ∈ R then P.β a else 0) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            congr 1
            refine Finset.sum_congr rfl fun a _ => ?_
            by_cases hmem : A.step x a ∈ R
            · simp only [hmem, ↓reduceIte]
              rw [Finset.sum_eq_single (A.step x a)]
              · simp
              · intro r _ hr; simp [Ne.symm hr]
              · intro h; exact absurd hmem h
            · simp only [hmem, ↓reduceIte]
              exact Finset.sum_eq_zero fun r hr => by
                have hne : A.step x a ≠ r := fun h => hmem (h ▸ hr)
                simp [hne]
  have hsplit :
      (∑ x : Q, P.π x * (∑ a : α, if A.step x a ∈ R then P.β a else 0)) =
        (∑ x ∈ R, P.π x * (∑ a : α, if A.step x a ∈ R then P.β a else 0)) +
        (∑ x ∈ Finset.univ \ R, P.π x * (∑ a : α, if A.step x a ∈ R then P.β a else 0)) := by
    have hdisj : Disjoint R (Finset.univ \ R) := Finset.disjoint_sdiff
    have hunion : R ∪ (Finset.univ \ R) = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ R)
    conv_lhs => rw [← hunion, Finset.sum_union hdisj]
  have hinR : (∑ x ∈ R, P.π x * (∑ a : α, if A.step x a ∈ R then P.β a else 0)) =
      ∑ x ∈ R, P.π x := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have h1 : (∑ a : α, if A.step x a ∈ R then P.β a else 0) = 1 := by
      rw [← P.hβ_sum]
      refine Finset.sum_congr rfl fun a _ => by simp [hR_closed x hx a]
    rw [h1, mul_one]
  have hout_zero :
      (∑ x ∈ Finset.univ \ R, P.π x * (∑ a : α, if A.step x a ∈ R then P.β a else 0)) = 0 := by
    linarith
  have hout_nonneg : ∀ x ∈ Finset.univ \ R,
      0 ≤ P.π x * (∑ a : α, if A.step x a ∈ R then P.β a else 0) := by
    intro x _
    refine mul_nonneg (P.hπ_pos x).le (Finset.sum_nonneg fun a _ => ?_)
    split_ifs
    · exact (P.hβ_pos a).le
    · exact le_rfl
  have hcompl_closed : ∀ x, x ∉ R → ∀ a : α, A.step x a ∉ R := by
    intro x hx a hstep
    have hx_mem : x ∈ Finset.univ \ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
    have hx0 := (Finset.sum_eq_zero_iff_of_nonneg hout_nonneg).mp hout_zero x hx_mem
    have hinner0 : (∑ b : α, if A.step x b ∈ R then P.β b else 0) = 0 :=
      (mul_eq_zero.mp hx0).resolve_left (P.hπ_pos x).ne'
    have hinner_nn : ∀ b ∈ (Finset.univ : Finset α),
        0 ≤ (if A.step x b ∈ R then P.β b else 0) := by
      intro b _; split_ifs
      · exact (P.hβ_pos b).le
      · exact le_rfl
    have ha0 := (Finset.sum_eq_zero_iff_of_nonneg hinner_nn).mp hinner0 a (Finset.mem_univ a)
    simp only [hstep, ↓reduceIte] at ha0
    exact (P.hβ_pos a).ne' ha0
  have hcompl_eval : ∀ x, x ∉ R → ∀ w : List α, A.eval x w ∉ R := by
    intro x hx w
    induction w generalizing x with
    | nil => exact hx
    | cons a u ih => exact ih (A.step x a) (hcompl_closed x hx a)
  have hqR : q ∈ R := by
    by_contra hq_not
    rcases hSync with ⟨w_sync, q₀, hq₀⟩
    have h1 : q₀ ∈ R := hq₀ p ▸ hR_eval p hpR w_sync
    have h2 : q₀ ∉ R := hq₀ q ▸ hcompl_eval q hq_not w_sync
    exact h2 h1
  simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and] using hqR

/-- **Lemma H.0(2) (Exact Length-`k` Averaging)**:
For every `k : ℕ` and `S : Finset Q`, the `β`-weighted average of `π(S w⁻¹)` over all length-`k`
words `w = List.ofFn f` equals `π(S)`. -/
theorem positiveStationary_word_avg {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    {A : DFA Q α} (P : PositiveStationary A) (S : Finset Q) (k : ℕ) :
    (∑ f : Fin k → α, AlmostUniform.wordWeight P.β f = 1) ∧
    (∑ f : Fin k → α, AlmostUniform.wordWeight P.β f *
        (∑ p ∈ A.preimage S (List.ofFn f), P.π p)) = ∑ q ∈ S, P.π q := by
  have hstep1 : ∀ T : Finset Q,
      (∑ a : α, P.β a * (∑ p ∈ A.preimage T [a], P.π p)) = ∑ q ∈ T, P.π q := by
    intro T
    calc (∑ a : α, P.β a * (∑ p ∈ A.preimage T [a], P.π p))
        = ∑ a : α, P.β a * (∑ p : Q, if A.step p a ∈ T then P.π p else 0) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            congr 1
            rw [DFA.preimage, Finset.sum_filter]
            refine Finset.sum_congr rfl fun p _ => rfl
      _ = ∑ a : α, ∑ p : Q, P.π p * (if A.step p a ∈ T then P.β a else 0) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
      _ = ∑ p : Q, P.π p * (∑ a : α, if A.step p a ∈ T then P.β a else 0) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => by rw [← Finset.mul_sum]
      _ = ∑ p : Q, P.π p * (∑ a : α, ∑ q ∈ T, if A.step p a = q then P.β a else 0) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            congr 1
            refine Finset.sum_congr rfl fun a _ => ?_
            by_cases hmem : A.step p a ∈ T
            · simp only [hmem, ↓reduceIte]
              rw [Finset.sum_eq_single (A.step p a)]
              · simp
              · intro q _ hq; simp [Ne.symm hq]
              · intro h; exact absurd hmem h
            · simp only [hmem, ↓reduceIte]
              exact (Finset.sum_eq_zero fun q hq => by
                have hne : A.step p a ≠ q := fun h => hmem (h ▸ hq)
                simp [hne]).symm
      _ = ∑ q ∈ T, ∑ p : Q, P.π p * (∑ a : α, if A.step p a = q then P.β a else 0) := by
            trans ∑ p : Q, ∑ q ∈ T, P.π p * (∑ a : α, if A.step p a = q then P.β a else 0)
            · refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_comm, Finset.mul_sum]
            · exact Finset.sum_comm
      _ = ∑ q ∈ T, P.π q := Finset.sum_congr rfl fun q _ => P.hstat q
  induction k with
  | zero =>
    constructor
    · simp [AlmostUniform.wordWeight]
    · simp [AlmostUniform.wordWeight, DFA.preimage]
  | succ k ih =>
    rcases ih with ⟨ih_sum, ih_avg⟩
    let e := AlmostUniform.finConsEquiv α k
    have hweight : ∀ p : α × (Fin k → α),
        AlmostUniform.wordWeight P.β (e p) = P.β p.1 * AlmostUniform.wordWeight P.β p.2 := by
      intro ⟨a, f⟩
      simp only [AlmostUniform.wordWeight, e, AlmostUniform.finConsEquiv, Equiv.coe_fn_mk,
        Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rw [← Fintype.sum_equiv e (fun p => P.β p.1 * AlmostUniform.wordWeight P.β p.2)
        (fun g => AlmostUniform.wordWeight P.β g) (fun p => (hweight p).symm)]
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, ih_sum, mul_one, P.hβ_sum]
    · rw [← Fintype.sum_equiv e
        (fun p => P.β p.1 * AlmostUniform.wordWeight P.β p.2 *
          (∑ x ∈ A.preimage (A.preimage S (List.ofFn p.2)) [p.1], P.π x))
        (fun g => AlmostUniform.wordWeight P.β g * (∑ x ∈ A.preimage S (List.ofFn g), P.π x))
        (fun ⟨a, f⟩ => by
          rw [hweight (a, f)]
          congr 2
          ext x
          simp only [DFA.mem_preimage, e, AlmostUniform.finConsEquiv, Equiv.coe_fn_mk,
            List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, DFA.eval_cons, DFA.eval_nil])]
      rw [Fintype.sum_prod_type_right]
      have hinner : ∀ f : Fin k → α,
          (∑ a : α, P.β a * AlmostUniform.wordWeight P.β f *
              (∑ x ∈ A.preimage (A.preimage S (List.ofFn f)) [a], P.π x)) =
            AlmostUniform.wordWeight P.β f * (∑ q ∈ A.preimage S (List.ofFn f), P.π q) := by
        intro f
        have hrew :
            (∑ a : α, P.β a * AlmostUniform.wordWeight P.β f *
                (∑ x ∈ A.preimage (A.preimage S (List.ofFn f)) [a], P.π x)) =
              AlmostUniform.wordWeight P.β f *
                (∑ a : α, P.β a * (∑ x ∈ A.preimage (A.preimage S (List.ofFn f)) [a], P.π x)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => by ring
        rw [hrew, hstep1 (A.preimage S (List.ofFn f))]
      simp_rw [hinner]
      exact ih_avg

/-- Same-length positive-deviation extraction from `positiveStationary_word_avg`:
if `π(S u⁻¹) ≠ π(S)`, there exists `w` with `w.length = u.length` and `π(S w⁻¹) > π(S)`. -/
private lemma positiveStationary_exists_gt_of_ne {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    {A : DFA Q α} (P : PositiveStationary A) (S : Finset Q) (u : List α)
    (hne : ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q) :
    ∃ w : List α, w.length = u.length ∧
      ∑ q ∈ S, P.π q < ∑ p ∈ A.preimage S w, P.π p := by
  set k := u.length
  obtain ⟨hsum1, havg⟩ := positiveStationary_word_avg P S k
  let f₀ : Fin k → α := fun i => u.get i
  have hf₀_ofFn : List.ofFn f₀ = u := List.ofFn_get u
  have hW_pos : ∀ f : Fin k → α, 0 < AlmostUniform.wordWeight P.β f :=
    fun f => Finset.prod_pos fun i _ => P.hβ_pos (f i)
  have hzero :
      (∑ f : Fin k → α, AlmostUniform.wordWeight P.β f *
          ((∑ p ∈ A.preimage S (List.ofFn f), P.π p) - ∑ q ∈ S, P.π q)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, havg, hsum1, one_mul, sub_self]
  have hex : ∃ f : Fin k → α, ∑ q ∈ S, P.π q < ∑ p ∈ A.preimage S (List.ofFn f), P.π p := by
    by_contra hall
    push Not at hall
    have hle : ∀ f : Fin k → α,
        AlmostUniform.wordWeight P.β f *
          ((∑ p ∈ A.preimage S (List.ofFn f), P.π p) - ∑ q ∈ S, P.π q) ≤ 0 :=
      fun f => mul_nonpos_of_nonneg_of_nonpos (hW_pos f).le (sub_nonpos.mpr (hall f))
    have hlt₀ :
        AlmostUniform.wordWeight P.β f₀ *
          ((∑ p ∈ A.preimage S (List.ofFn f₀), P.π p) - ∑ q ∈ S, P.π q) < 0 := by
      refine mul_neg_of_pos_of_neg (hW_pos f₀) ?_
      rw [hf₀_ofFn]
      exact sub_neg.mpr (lt_of_le_of_ne (by simpa [hf₀_ofFn] using hall f₀) hne)
    have hsum_lt :
        (∑ f : Fin k → α, AlmostUniform.wordWeight P.β f *
            ((∑ p ∈ A.preimage S (List.ofFn f), P.π p) - ∑ q ∈ S, P.π q)) <
          ∑ _f : Fin k → α, (0 : ℝ) :=
      Finset.sum_lt_sum (fun f _ => hle f) ⟨f₀, Finset.mem_univ f₀, hlt₀⟩
    rw [hzero, Finset.sum_const_zero] at hsum_lt
    exact lt_irrefl _ hsum_lt
  rcases hex with ⟨f, hf⟩
  exact ⟨List.ofFn f, List.length_ofFn, hf⟩

/-- **Lemma H.0(3) (BFS Escape & Entry Orbit Bounds)**:
In any strongly connected DFA, for any `x₀ : Q` and nonempty proper `S ⊂ Q`:
1. If `x₀ ∈ S`, some word `u` with `u.length ≤ S.card` sends `x₀` outside `S`.
2. If `x₀ ∉ S`, some word `u` with `u.length ≤ Fintype.card Q - S.card` sends `x₀` into `S`. -/
theorem stronglyConnected_escape_entry {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} (hSC : A.IsStronglyConnected) (x₀ : Q) (S : Finset Q) :
    (x₀ ∈ S → S.card < Fintype.card Q →
      ∃ u : List α, u.length ≤ S.card ∧ A.eval x₀ u ∉ S) ∧
    (x₀ ∉ S → S.Nonempty →
      ∃ u : List α, u.length ≤ Fintype.card Q - S.card ∧ A.eval x₀ u ∈ S) := by
  classical
  have hescape : ∀ (T : Finset Q), x₀ ∈ T → T.card < Fintype.card Q →
      ∃ u : List α, u.length ≤ T.card ∧ A.eval x₀ u ∉ T := by
    intro T hxT hT_lt
    have hex_y : ∃ y : Q, y ∉ T := by
      by_contra hall
      push Not at hall
      have hsub : (Finset.univ : Finset Q) ⊆ T := fun y _ => hall y
      have := Finset.card_le_card hsub
      rw [Finset.card_univ] at this
      omega
    obtain ⟨y, hy⟩ := hex_y
    obtain ⟨w₀, hw₀⟩ := hSC x₀ y
    have hex : ∃ k : ℕ, ∃ u : List α, u.length = k ∧ A.eval x₀ u ∉ T :=
      ⟨w₀.length, w₀, rfl, hw₀ ▸ hy⟩
    let k := Nat.find hex
    obtain ⟨u, hu_len, hu_out⟩ := Nat.find_spec hex
    refine ⟨u, ?_, hu_out⟩
    by_contra hgt
    have hk_gt : T.card < k := by omega
    have hprefix : ∀ i : Fin k, A.eval x₀ (u.take i.val) ∈ T := by
      intro i
      by_contra hnot
      have htake_len : (u.take i.val).length = i.val := by
        rw [List.length_take]; omega
      exact Nat.find_min hex i.isLt ⟨u.take i.val, htake_len, hnot⟩
    let φ : Fin k → T := fun i => ⟨A.eval x₀ (u.take i.val), hprefix i⟩
    have hcard_lt : Fintype.card T < Fintype.card (Fin k) := by
      rw [Fintype.card_coe, Fintype.card_fin]
      exact hk_gt
    obtain ⟨i, j, hne, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hcard_lt
    have heq_state : A.eval x₀ (u.take i.val) = A.eval x₀ (u.take j.val) :=
      congrArg Subtype.val hφ
    have hcut : ∀ (a b : Fin k), a.val < b.val →
        A.eval x₀ (u.take a.val) = A.eval x₀ (u.take b.val) → False := by
      intro a b hab hst
      let u' := u.take a.val ++ u.drop b.val
      have hu'_out : A.eval x₀ u' ∉ T := by
        have h1 : A.eval x₀ u' = A.eval x₀ u := by
          dsimp only [u']
          rw [DFA.eval_append, hst, ← DFA.eval_append, List.take_append_drop]
        rw [h1]
        exact hu_out
      have hu'_len : u'.length < k := by
        dsimp only [u']
        rw [List.length_append, List.length_take, List.length_drop]
        have ha := a.isLt
        have hb := b.isLt
        omega
      exact Nat.find_min hex hu'_len ⟨u', rfl, hu'_out⟩
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt'
    · exact hcut i j hlt heq_state
    · exact hcut j i hgt' heq_state.symm
  refine ⟨hescape S, ?_⟩
  intro hxS hS_ne
  let T := Finset.univ \ S
  have hxT : x₀ ∈ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x₀, hxS⟩
  have hT_card : T.card = Fintype.card Q - S.card := by
    dsimp only [T]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  have hS_pos : 0 < S.card := Finset.card_pos.mpr hS_ne
  have hS_le : S.card ≤ Fintype.card Q := Finset.card_le_univ S
  obtain ⟨u, hu_len, hu_out⟩ := hescape T hxT (by omega)
  refine ⟨u, by omega, ?_⟩
  by_contra hnotS
  exact hu_out (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotS⟩)

/-! ### Section 2: Integer-Weight Steinberg Engine (Theorem H Case 1 & Theorem H_k) -/

/-- **Integer-Weight Steinberg Reset Bound**:
If `P : PositiveStationary A` has positive integer values `P.π q = (w_int q : ℝ)`, then every
nonempty `S₀ : Finset Q` reaches `Finset.univ` in total length
`≤ ((∑ q, w_int q) - (∑ q ∈ S₀, w_int q)) * (Fintype.card Q - 1)`. -/
private lemma integerStationary_reset_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    {A : DFA Q α} (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (w_int : Q → ℕ)
    (hw_eq : ∀ q : Q, P.π q = (w_int q : ℝ))
    (S₀ : Finset Q) (hS₀_ne : S₀.Nonempty) :
    ∃ v : List α, A.preimage S₀ v = Finset.univ ∧
      v.length ≤ ((∑ q : Q, w_int q) - (∑ q ∈ S₀, w_int q)) * (Fintype.card Q - 1) := by
  classical
  have hπ_total_pos : 0 < ∑ q : Q, P.π q := by
    have : Nonempty Q := hSync.nonempty
    exact Finset.sum_pos (fun q _ => P.hπ_pos q) Finset.univ_nonempty
  -- Single extending step of length `≤ n - 1` via ascending `ℝ`-subspace chain
  have hextend : ∀ S : Finset Q, S.Nonempty → S.card < Fintype.card Q →
      ∃ w : List α, w.length ≤ Fintype.card Q - 1 ∧
        (∑ q ∈ S, w_int q) + 1 ≤ ∑ p ∈ A.preimage S w, w_int p := by
    intro S hS_ne hS_lt
    let tot : ℝ := ∑ q : Q, P.π q
    let cS : ℝ := (∑ q ∈ S, P.π q) / tot
    have hcS_pos : 0 < cS := div_pos (Finset.sum_pos (fun q _ => P.hπ_pos q) hS_ne) hπ_total_pos
    have hcS_lt1 : cS < 1 := by
      have hex_out : ∃ y : Q, y ∉ S := by
        by_contra hall; push Not at hall
        have hle := Finset.card_le_card (show (Finset.univ : Finset Q) ⊆ S from fun y _ => hall y)
        rw [Finset.card_univ] at hle; omega
      obtain ⟨y, hy⟩ := hex_out
      have hS_lt_tot : ∑ q ∈ S, P.π q < tot := by
        have hsub : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr fun h => hy (h ▸ Finset.mem_univ y)
        exact Finset.sum_lt_sum_of_subset (Finset.subset_univ S) (Finset.mem_univ y) hy (P.hπ_pos y)
          (fun q _ _ => (P.hπ_pos q).le)
      have hmul : cS * tot = ∑ q ∈ S, P.π q := div_mul_cancel₀ _ hπ_total_pos.ne'
      nlinarith
    let γ : Q → ℝ := fun q => (if q ∈ S then (1 : ℝ) else 0) - cS
    have hdot_eval : ∀ u : List α,
        AlmostUniform.dotLinR P.π (AlmostUniform.pullbackR A u γ) =
          (∑ p ∈ A.preimage S u, P.π p) - ∑ q ∈ S, P.π q := by
      intro u
      simp only [AlmostUniform.dotLinR, AlmostUniform.pullbackR, γ, LinearMap.coe_mk, AddHom.coe_mk]
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      have h1 : (∑ p : Q, P.π p * if A.eval p u ∈ S then (1 : ℝ) else 0) =
          ∑ p ∈ A.preimage S u, P.π p := by
        rw [DFA.preimage, Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
      have h2 : (∑ p : Q, P.π p) * cS = ∑ q ∈ S, P.π q := by
        dsimp only [cS, tot]; exact mul_div_cancel₀ _ hπ_total_pos.ne'
      rw [h1, h2]
    let H : Submodule ℝ (Q → ℝ) := LinearMap.ker (AlmostUniform.dotLinR P.π)
    let W : ℕ → Submodule ℝ (Q → ℝ) := fun k =>
      Submodule.span ℝ { v : Q → ℝ | ∃ u : List α, u.length ≤ k ∧
        v = AlmostUniform.pullbackR A u γ }
    have hW_mono : ∀ {j k}, j ≤ k → W j ≤ W k := by
      intro j k hjk
      apply Submodule.span_mono
      rintro v ⟨u, hu, rfl⟩
      exact ⟨u, hu.trans hjk, rfl⟩
    have hW0_dim : 1 ≤ Module.finrank ℝ (W 0) := by
      have hγ_mem : γ ∈ W 0 := Submodule.subset_span ⟨[], le_rfl, rfl⟩
      have hγ_ne : γ ≠ 0 := by
        obtain ⟨p₀⟩ := hSync.nonempty
        intro h0
        have hval := congrFun h0 p₀
        simp only [γ, Pi.zero_apply] at hval
        split_ifs at hval <;> linarith
      have hbot : (⊥ : Submodule ℝ (Q → ℝ)) < W 0 := by
        rw [bot_lt_iff_ne_bot]
        intro hb; rw [hb, Submodule.mem_bot] at hγ_mem; exact hγ_ne hγ_mem
      have hlt := Submodule.finrank_lt_finrank_of_lt hbot
      rw [finrank_bot] at hlt
      omega
    rcases hSync with ⟨w_sync, q₀, hq₀⟩
    have hsync_notH : AlmostUniform.pullbackR A w_sync γ ∉ H := by
      intro hmem
      change AlmostUniform.dotLinR P.π (AlmostUniform.pullbackR A w_sync γ) = 0 at hmem
      have hconst : ∀ p : Q, AlmostUniform.pullbackR A w_sync γ p = γ q₀ := by
        intro p; simp only [AlmostUniform.pullbackR, LinearMap.coe_mk, AddHom.coe_mk, hq₀ p]
      simp only [AlmostUniform.dotLinR, LinearMap.coe_mk, AddHom.coe_mk] at hmem
      simp_rw [hconst, ← Finset.sum_mul] at hmem
      have hγq0 : γ q₀ = 0 := (mul_eq_zero.mp hmem).resolve_left hπ_total_pos.ne'
      simp only [γ] at hγq0
      split_ifs at hγq0 <;> linarith
    have hex_esc : ∃ k : ℕ, ¬ (W k ≤ H) :=
      ⟨w_sync.length, fun hle => hsync_notH (hle (Submodule.subset_span ⟨w_sync, le_rfl, rfl⟩))⟩
    let k₀ := Nat.find hex_esc
    have hk₀_not : ¬ (W k₀ ≤ H) := Nat.find_spec hex_esc
    have hk₀_min : ∀ j < k₀, W j ≤ H := fun j hj => not_not.mp (Nat.find_min hex_esc hj)
    have hk₀_le : k₀ ≤ Fintype.card Q - 1 := by
      by_cases hk0 : k₀ = 0
      · omega
      · have hstrict : ∀ j, j + 1 < k₀ → W j < W (j + 1) := by
          intro j hj
          refine lt_of_le_of_ne (hW_mono (Nat.le_succ j)) fun heq => ?_
          have hclosed : ∀ (a : α) (v : Q → ℝ), v ∈ W j →
              AlmostUniform.pullbackR A [a] v ∈ W j := by
            intro a v hv
            rw [heq]
            induction hv using Submodule.span_induction with
            | mem x hx =>
              rcases hx with ⟨u, hu, rfl⟩
              rw [← AlmostUniform.pullbackR_cons]
              exact Submodule.subset_span ⟨a :: u, by simp; omega, rfl⟩
            | zero => simp
            | add x y _ _ hx hy => rw [map_add]; exact (W (j + 1)).add_mem hx hy
            | smul c x _ hx => rw [map_smul]; exact (W (j + 1)).smul_mem c hx
          have hall : ∀ u : List α, AlmostUniform.pullbackR A u γ ∈ W j := by
            intro u
            induction u with
            | nil => exact Submodule.subset_span ⟨[], Nat.zero_le j, rfl⟩
            | cons a u ih => rw [AlmostUniform.pullbackR_cons]; exact hclosed a _ ih
          exact hsync_notH (hk₀_min j (by omega) (hall w_sync))
        have hdim : ∀ j ≤ k₀ - 1, j + 1 ≤ Module.finrank ℝ (W j) := by
          intro j
          induction j with
          | zero => intro _; exact hW0_dim
          | succ j ih =>
            intro hj
            have ih' := ih (by omega)
            have hlt := Submodule.finrank_lt_finrank_of_lt (hstrict j (by omega))
            omega
        have h1 := hdim (k₀ - 1) le_rfl
        have h2 : Module.finrank ℝ (W (k₀ - 1)) ≤ Module.finrank ℝ H :=
          Submodule.finrank_mono (hk₀_min (k₀ - 1) (by omega))
        rw [AlmostUniform.finrank_ker_dotLinR hπ_total_pos.ne'] at h2
        omega
    have hex_u : ∃ u : List α, u.length ≤ k₀ ∧
        AlmostUniform.dotLinR P.π (AlmostUniform.pullbackR A u γ) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hk₀_not
      rw [Submodule.span_le]
      rintro v ⟨u, hu, rfl⟩
      exact hall u hu
    rcases hex_u with ⟨u, hu_len, hu_nz⟩
    rw [hdot_eval u] at hu_nz
    have hne : ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q := sub_ne_zero.mp hu_nz
    obtain ⟨w, hw_len, hw_gt⟩ := positiveStationary_exists_gt_of_ne P S u hne
    refine ⟨w, by omega, ?_⟩
    have hcast : ((∑ q ∈ S, w_int q : ℕ) : ℝ) < ((∑ p ∈ A.preimage S w, w_int p : ℕ) : ℝ) := by
      simpa only [Nat.cast_sum, ← hw_eq] using hw_gt
    have hlt_nat : ∑ q ∈ S, w_int q < ∑ p ∈ A.preimage S w, w_int p := by exact_mod_cast hcast
    omega
  -- Strong induction on `k := (∑ q, w_int q) - (∑ q ∈ S, w_int q)`
  have hind : ∀ k : ℕ, ∀ S : Finset Q, S.Nonempty →
      (∑ q : Q, w_int q) - (∑ q ∈ S, w_int q) = k →
      ∃ v : List α, A.preimage S v = Finset.univ ∧ v.length ≤ k * (Fintype.card Q - 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro S hS_ne hk
      have hsum_le : ∑ q ∈ S, w_int q ≤ ∑ q : Q, w_int q :=
        Finset.sum_le_univ_sum_of_nonneg fun q => Nat.zero_le _
      by_cases hfull : S = Finset.univ
      · refine ⟨[], ?_, by simp⟩
        rw [hfull]; ext q; simp
      · have hS_lt : S.card < Fintype.card Q := by
          have hsub : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hfull
          simpa using Finset.card_lt_card hsub
        obtain ⟨w, hw_len, hw_inc⟩ := hextend S hS_ne hS_lt
        set S' := A.preimage S w
        have hS'_ne : S'.Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          rw [hemp, Finset.sum_empty] at hw_inc
          omega
        have hS'_le : ∑ q ∈ S', w_int q ≤ ∑ q : Q, w_int q :=
          Finset.sum_le_univ_sum_of_nonneg fun q => Nat.zero_le _
        have hk'_lt : (∑ q : Q, w_int q) - (∑ q ∈ S', w_int q) < k := by omega
        obtain ⟨v', hv'_full, hv'_len⟩ :=
          ih ((∑ q : Q, w_int q) - (∑ q ∈ S', w_int q)) hk'_lt S' hS'_ne rfl
        refine ⟨v' ++ w, ?_, ?_⟩
        · ext q
          simp only [DFA.mem_preimage, DFA.eval_append, Finset.mem_univ, iff_true]
          have hq' : q ∈ A.preimage S' v' := hv'_full ▸ Finset.mem_univ q
          exact (DFA.mem_preimage A S w _).mp ((DFA.mem_preimage A S' v' q).mp hq')
        · rw [List.length_append]
          have h1 : (((∑ q : Q, w_int q) - (∑ q ∈ S', w_int q)) + 1) * (Fintype.card Q - 1) ≤
              k * (Fintype.card Q - 1) := Nat.mul_le_mul_right _ (by omega)
          nlinarith
  exact hind _ S₀ hS₀_ne rfl

/-! ### Section 3: Theorem H — Almost-Uniform Stationary Vector Exact `(n - 1)^2` -/

/-- **Theorem H, Case 2 (Unified `Finset.sum` Potential `Ψ(S)` for ALL Non-Integer `α₀ > 0`)**:
ZERO linear algebra! For any `α₀ ∈ (0, ∞) \ ℤ`, the remaining-level budget potential `Ψ(S)`
decreases by `≥ cost(ℓ(S)) ≥ |w|` at every step, yielding `rt(A) ≤ (n - 1)^2`. -/
private lemma almostUniform_noninteger_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    {A : DFA Q α} (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (hn2 : 2 ≤ Fintype.card Q)
    (x₀ : Q) (α₀ : ℝ) (hα₀_pos : 0 < α₀) (hnonint : ∀ m : ℤ, α₀ ≠ (m : ℝ))
    (hπ_eq : ∀ q : Q, P.π q = if q = x₀ then α₀ else 1) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  set n := Fintype.card Q
  have hSC : A.IsStronglyConnected := positiveStationary_stronglyConnected hSync P
  -- Index set `I = {1, ..., n - 1} × Bool`, level value `val`, and budget `cost`
  let Rng : Finset ℕ := (Finset.range n).erase 0
  let I : Finset (ℕ × Bool) := Rng ×ˢ (Finset.univ : Finset Bool)
  let val : ℕ × Bool → ℝ := fun rb => if rb.2 then (rb.1 : ℝ) - 1 + α₀ else (rb.1 : ℝ)
  let cost : ℕ × Bool → ℕ := fun rb => if rb.2 then rb.1 else n - rb.1
  let Ψ : Finset Q → ℕ := fun S =>
    ∑ rb ∈ I.filter (fun rb => ∑ q ∈ S, P.π q ≤ val rb), cost rb
  -- Total budget `∑_{rb ∈ I} cost rb = n * (n - 1)`
  have hRng_card : Rng.card = n - 1 := by
    dsimp only [Rng]
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
  have hI_sum : ∑ rb ∈ I, cost rb = (n - 1) * n := by
    dsimp only [I]
    rw [Finset.sum_product]
    have hinner : ∀ r ∈ Rng, ∑ b : Bool, cost (r, b) = n := by
      intro r hr
      have hr_lt : r < n := Finset.mem_range.mp (Finset.mem_of_mem_erase hr)
      simp only [Fintype.sum_bool, cost, ↓reduceIte, Bool.false_eq_true]
      omega
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, hRng_card]
  -- Exact value of `∑ q ∈ S, P.π q`
  have hπ_S_in : ∀ S : Finset Q, x₀ ∈ S → ∑ q ∈ S, P.π q = (S.card : ℝ) - 1 + α₀ := by
    intro S hxS
    rw [← Finset.add_sum_erase _ _ hxS, hπ_eq x₀]
    simp only [↓reduceIte]
    have hrest : ∑ q ∈ S.erase x₀, P.π q = ((S.erase x₀).card : ℝ) := by
      have h1 : ∑ q ∈ S.erase x₀, P.π q = ∑ _q ∈ S.erase x₀, (1 : ℝ) :=
        Finset.sum_congr rfl fun q hq => by
          rw [hπ_eq q]; simp [Finset.ne_of_mem_erase hq]
      rw [h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hrest, Finset.card_erase_of_mem hxS]
    have h1le : 1 ≤ S.card := Finset.card_pos.mpr ⟨x₀, hxS⟩
    rw [Nat.cast_sub h1le, Nat.cast_one]
    ring
  have hπ_S_out : ∀ S : Finset Q, x₀ ∉ S → ∑ q ∈ S, P.π q = (S.card : ℝ) := by
    intro S hxS
    have h1 : ∑ q ∈ S, P.π q = ∑ _q ∈ S, (1 : ℝ) :=
      Finset.sum_congr rfl fun q hq => by
        rw [hπ_eq q]; simp [show q ≠ x₀ from fun h => hxS (h ▸ hq)]
    rw [h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Single-step `Ψ`-descent for every nonempty proper `S ⊂ Q`
  have hdescent : ∀ S : Finset Q, S.Nonempty → S.card < n →
      ∃ w : List α, (A.preimage S w).Nonempty ∧
        Ψ (A.preimage S w) + w.length ≤ Ψ S ∧ Ψ (A.preimage S w) < Ψ S := by
    intro S hS_ne hS_lt
    let ℓS : ℕ × Bool := (S.card, decide (x₀ ∈ S))
    have hS_pos : 0 < S.card := Finset.card_pos.mpr hS_ne
    have hℓS_mem : ℓS ∈ I := by
      dsimp only [I, Rng, ℓS]
      exact Finset.mem_product.mpr
        ⟨Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hS_lt⟩, Finset.mem_univ _⟩
    have hℓS_val : val ℓS = ∑ q ∈ S, P.π q := by
      dsimp only [val, ℓS]
      by_cases hxS : x₀ ∈ S
      · simp only [hxS, decide_true, ↓reduceIte]; exact (hπ_S_in S hxS).symm
      · simp only [hxS, decide_false, Bool.false_eq_true, ↓reduceIte]; exact (hπ_S_out S hxS).symm
    have hℓS_cost_pos : 0 < cost ℓS := by
      dsimp only [cost, ℓS]
      split_ifs <;> omega
    -- Find `u` of length `≤ cost ℓS` changing membership of `x₀`, hence changing `π`!
    have hex_u : ∃ u : List α, u.length ≤ cost ℓS ∧
        ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q := by
      by_cases hxS : x₀ ∈ S
      · obtain ⟨u, hu_len, hu_out⟩ := (stronglyConnected_escape_entry hSC x₀ S).1 hxS hS_lt
        have hx_not_pre : x₀ ∉ A.preimage S u := by simp [DFA.mem_preimage, hu_out]
        refine ⟨u, ?_, ?_⟩
        · simpa only [cost, ℓS, hxS, decide_true, ↓reduceIte] using hu_len
        · rw [hπ_S_out _ hx_not_pre, hπ_S_in S hxS]
          intro heq
          have hm : α₀ = (((A.preimage S u).card : ℤ) - (S.card : ℤ) + 1 : ℤ) := by
            push_cast; linarith
          exact hnonint _ hm
      · obtain ⟨u, hu_len, hu_in⟩ := (stronglyConnected_escape_entry hSC x₀ S).2 hxS hS_ne
        have hx_in_pre : x₀ ∈ A.preimage S u := by simp [DFA.mem_preimage, hu_in]
        refine ⟨u, ?_, ?_⟩
        · simpa only [cost, ℓS, hxS, decide_false, Bool.false_eq_true, ↓reduceIte] using hu_len
        · rw [hπ_S_in _ hx_in_pre, hπ_S_out S hxS]
          intro heq
          have hm : α₀ = ((S.card : ℤ) - ((A.preimage S u).card : ℤ) + 1 : ℤ) := by
            push_cast; linarith
          exact hnonint _ hm
    rcases hex_u with ⟨u, hu_len, hu_ne⟩
    obtain ⟨w, hw_len, hw_gt⟩ := positiveStationary_exists_gt_of_ne P S u hu_ne
    have hpre_ne : (A.preimage S w).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.sum_empty] at hw_gt
      have hpos : 0 < ∑ q ∈ S, P.π q := Finset.sum_pos (fun q _ => P.hπ_pos q) hS_ne
      linarith
    -- Compare filtered sums: `F₁ ⊆ F₀.erase ℓS`
    let F₀ := I.filter (fun rb => ∑ q ∈ S, P.π q ≤ val rb)
    let F₁ := I.filter (fun rb => ∑ q ∈ A.preimage S w, P.π q ≤ val rb)
    have hℓS_F₀ : ℓS ∈ F₀ := Finset.mem_filter.mpr ⟨hℓS_mem, hℓS_val.ge⟩
    have hF₁_sub : F₁ ⊆ F₀.erase ℓS := by
      intro rb hrb
      rcases Finset.mem_filter.mp hrb with ⟨hrbI, hrb_val⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hrbI, hw_gt.le.trans hrb_val⟩⟩
      intro heq; rw [heq, hℓS_val] at hrb_val; linarith
    have hsum_drop : Ψ (A.preimage S w) + cost ℓS ≤ Ψ S := by
      change (∑ rb ∈ F₁, cost rb) + cost ℓS ≤ ∑ rb ∈ F₀, cost rb
      have h1 : ∑ rb ∈ F₁, cost rb ≤ ∑ rb ∈ F₀.erase ℓS, cost rb :=
        Finset.sum_le_sum_of_subset hF₁_sub
      have h2 : (∑ rb ∈ F₀.erase ℓS, cost rb) + cost ℓS = ∑ rb ∈ F₀, cost rb :=
        Finset.sum_erase_add F₀ cost hℓS_F₀
      omega
    exact ⟨w, hpre_ne, by omega, by omega⟩
  -- Strong induction on `k := Ψ S` reaches `Finset.univ` in length `≤ Ψ S`
  have hind : ∀ k : ℕ, ∀ S : Finset Q, S.Nonempty → Ψ S = k →
      ∃ v : List α, A.preimage S v = Finset.univ ∧ v.length ≤ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro S hS_ne hk
      by_cases hfull : S = Finset.univ
      · refine ⟨[], ?_, by simp⟩
        rw [hfull]; ext q; simp
      · have hS_lt : S.card < n := by
          have hsub : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hfull
          simpa [n] using Finset.card_lt_card hsub
        obtain ⟨w, hpre_ne, hdrop, hlt⟩ := hdescent S hS_ne hS_lt
        obtain ⟨v', hv'_full, hv'_len⟩ := ih (Ψ (A.preimage S w)) (by omega) _ hpre_ne rfl
        refine ⟨v' ++ w, ?_, ?_⟩
        · ext q
          simp only [DFA.mem_preimage, DFA.eval_append, Finset.mem_univ, iff_true]
          have hq' : q ∈ A.preimage (A.preimage S w) v' := hv'_full ▸ Finset.mem_univ q
          exact (DFA.mem_preimage A S w _).mp ((DFA.mem_preimage A (A.preimage S w) v' q).mp hq')
        · rw [List.length_append]; omega
  -- Close at `(n - 1)^2`: split `1 < α₀` vs `α₀ < 1`
  have h1_mem_Rng : 1 ∈ Rng := Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have h1f_mem : (1, false) ∈ I := Finset.mem_product.mpr ⟨h1_mem_Rng, Finset.mem_univ _⟩
  have h1t_mem : (1, true) ∈ I := Finset.mem_product.mpr ⟨h1_mem_Rng, Finset.mem_univ _⟩
  have hα₀_ne1 : α₀ ≠ 1 := by simpa using hnonint 1
  rcases lt_or_gt_of_ne hα₀_ne1 with hlt1 | hgt1
  · -- **Subcase 2b (`0 < α₀ < 1`)**: non-injective letter `g` gives `|S₁| ≥ 2`, omitting BOTH `(1, false)` and `(1, true)`!
    have hex_noninj : ∃ g : α, ¬ Function.Injective (fun q => A.step q g) := by
      by_contra hall
      push Not at hall
      have heval_inj : ∀ w : List α, Function.Injective (fun q => A.eval q w) := by
        intro w
        induction w with
        | nil => exact Function.injective_id
        | cons a u ih =>
          intro p q hpq
          exact hall a (ih hpq)
      rcases hSync with ⟨w_sync, q₀, hq₀⟩
      have hex_pair : ∃ p₁ p₂ : Q, p₁ ≠ p₂ := by
        have hlt : 1 < Fintype.card Q := by omega
        exact Fintype.exists_pair_of_one_lt_card hlt
      rcases hex_pair with ⟨p₁, p₂, hpne⟩
      exact hpne (heval_inj w_sync ((hq₀ p₁).trans (hq₀ p₂).symm))
    obtain ⟨g, hg_notinj⟩ := hex_noninj
    unfold Function.Injective at hg_notinj
    push Not at hg_notinj
    rcases hg_notinj with ⟨p₁, p₂, hstep_eq, hpne⟩
    let q₀ := A.step p₁ g
    let S₁ := A.preimage {q₀} [g]
    have hS₁_ge2 : 2 ≤ S₁.card := by
      have hsub : ({p₁, p₂} : Finset Q) ⊆ S₁ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · simp [S₁, q₀]
        · simp [S₁, q₀, hstep_eq]
      have hcard := Finset.card_le_card hsub
      rwa [Finset.card_pair hpne] at hcard
    have hS₁_ne : S₁.Nonempty := Finset.card_pos.mp (by omega)
    have hπS₁_gt1 : 1 < ∑ q ∈ S₁, P.π q := by
      have hS₁_r : (2 : ℝ) ≤ (S₁.card : ℝ) := by exact_mod_cast hS₁_ge2
      by_cases hxS₁ : x₀ ∈ S₁
      · rw [hπ_S_in S₁ hxS₁]; linarith
      · rw [hπ_S_out S₁ hxS₁]; linarith
    have hF_sub : I.filter (fun rb => ∑ q ∈ S₁, P.π q ≤ val rb) ⊆
        (I.erase (1, false)).erase (1, true) := by
      intro rb hrb
      rcases Finset.mem_filter.mp hrb with ⟨hrbI, hrb_val⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hrbI⟩⟩
      · intro heq; rw [heq] at hrb_val
        simp only [val, ↓reduceIte, Nat.cast_one, sub_self, zero_add] at hrb_val
        linarith
      · intro heq; rw [heq] at hrb_val
        simp only [val, Bool.false_eq_true, ↓reduceIte, Nat.cast_one] at hrb_val
        linarith
    have hΨ_le : Ψ S₁ + 1 + (n - 1) ≤ (n - 1) * n := by
      dsimp only [Ψ]
      have h1 : ∑ rb ∈ I.filter (fun rb => ∑ q ∈ S₁, P.π q ≤ val rb), cost rb ≤
          ∑ rb ∈ (I.erase (1, false)).erase (1, true), cost rb :=
        Finset.sum_le_sum_of_subset hF_sub
      have h1t_er : (1, true) ∈ I.erase (1, false) :=
        Finset.mem_erase.mpr ⟨by decide, h1t_mem⟩
      have h2 := Finset.sum_erase_add (I.erase (1, false)) cost h1t_er
      have h3 := Finset.sum_erase_add I cost h1f_mem
      have hc1 : cost (1, true) = 1 := rfl
      have hc2 : cost (1, false) = n - 1 := rfl
      rw [hc1] at h2
      rw [hc2, hI_sum] at h3
      omega
    obtain ⟨v, hv_full, hv_len⟩ := hind (Ψ S₁) S₁ hS₁_ne rfl
    refine ⟨v ++ [g], ⟨q₀, fun p => ?_⟩, ?_⟩
    · rw [DFA.eval_append]
      have hp : p ∈ A.preimage S₁ v := hv_full ▸ Finset.mem_univ p
      have hp' : A.eval p v ∈ S₁ := (DFA.mem_preimage A S₁ v p).mp hp
      simpa [S₁, DFA.mem_preimage] using hp'
    · rw [List.length_append, List.length_singleton]
      have hsq : (n - 1) ^ 2 + (n - 1) = (n - 1) * n := by
        zify [show 1 ≤ n by omega]; ring
      omega
  · -- **Subcase 2a (`1 < α₀`)**: start at `{x₀}`, omitting `(1, false)` of cost `n - 1`!
    have hF_sub : I.filter (fun rb => ∑ q ∈ ({x₀} : Finset Q), P.π q ≤ val rb) ⊆
        I.erase (1, false) := by
      intro rb hrb
      rcases Finset.mem_filter.mp hrb with ⟨hrbI, hrb_val⟩
      refine Finset.mem_erase.mpr ⟨?_, hrbI⟩
      intro heq; rw [heq] at hrb_val
      simp only [Finset.sum_singleton, hπ_eq x₀, val, Bool.false_eq_true, ↓reduceIte,
        Nat.cast_one] at hrb_val
      linarith
    have hΨ_le : Ψ {x₀} + (n - 1) ≤ (n - 1) * n := by
      dsimp only [Ψ]
      have h1 : ∑ rb ∈ I.filter (fun rb => ∑ q ∈ ({x₀} : Finset Q), P.π q ≤ val rb), cost rb ≤
          ∑ rb ∈ I.erase (1, false), cost rb :=
        Finset.sum_le_sum_of_subset hF_sub
      have h2 := Finset.sum_erase_add I cost h1f_mem
      have hc2 : cost (1, false) = n - 1 := rfl
      rw [hc2, hI_sum] at h2
      omega
    obtain ⟨v, hv_full, hv_len⟩ := hind (Ψ {x₀}) {x₀} (Finset.singleton_nonempty x₀) rfl
    refine ⟨v, ⟨x₀, fun p => ?_⟩, ?_⟩
    · have hp : p ∈ A.preimage {x₀} v := hv_full ▸ Finset.mem_univ p
      simpa [DFA.mem_preimage] using hp
    · have hsq : (n - 1) ^ 2 + (n - 1) = (n - 1) * n := by
        zify [show 1 ≤ n by omega]; ring
      omega

/-- **Theorem H (EXACT Černý Conjecture `(n - 1)^2` for Almost-Uniform Stationary Vectors)**:
For ANY synchronizing DFA on `n ≥ 1` states admitting positive real letter weights `β` (`∑ β = 1`)
and a positive stationary vector `π` that takes a constant value `c` on `Q \ {x₀}` for some `x₀ : Q`,
there exists a synchronizing word of length at most `(Fintype.card Q - 1) ^ 2`. -/
theorem almostUniform_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (x₀ : Q) (c : ℝ) (hconst : ∀ q : Q, q ≠ x₀ → P.π q = c) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  by_cases hn1 : Fintype.card Q ≤ 1
  · obtain ⟨q₀⟩ := hSync.nonempty
    refine ⟨[], ⟨q₀, fun p => ?_⟩, by simp⟩
    have hsub : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp hn1
    exact Subsingleton.elim p q₀
  · have hn2 : 2 ≤ Fintype.card Q := by omega
    have hex_ne : ∃ q₁ : Q, q₁ ≠ x₀ := by
      by_contra hall; push Not at hall
      have hle : Fintype.card Q ≤ 1 := by
        rw [Fintype.card_le_one_iff]
        intro a b; rw [hall a, hall b]
      omega
    obtain ⟨q₁, hq₁⟩ := hex_ne
    have hc_pos : 0 < c := by rw [← hconst q₁ hq₁]; exact P.hπ_pos q₁
    let P' : PositiveStationary A := AlmostUniform.scaleStationary P c⁻¹ (inv_pos.mpr hc_pos)
    set α₀ : ℝ := c⁻¹ * P.π x₀
    have hα₀_pos : 0 < α₀ := mul_pos (inv_pos.mpr hc_pos) (P.hπ_pos x₀)
    have hP'_eq : ∀ q : Q, P'.π q = if q = x₀ then α₀ else 1 := by
      intro q
      dsimp only [P', AlmostUniform.scaleStationary]
      by_cases hqx : q = x₀
      · subst hqx; simp [α₀]
      · simp only [hqx, ↓reduceIte, hconst q hqx, inv_mul_cancel₀ hc_pos.ne']
    by_cases hint : ∃ m : ℤ, α₀ = (m : ℝ)
    · -- **Case 1 (`α₀ = m ∈ ℤ_{≥ 1}`)**: Steinberg `ℝ`-subspace averaging over `n - 1` integer levels
      rcases hint with ⟨m, hm⟩
      have hm_pos : 0 < m := by
        have : (0 : ℝ) < (m : ℝ) := hm ▸ hα₀_pos
        exact_mod_cast this
      let m_nat : ℕ := m.toNat
      have hm_nat_pos : 0 < m_nat := by omega
      have hm_nat_cast : (m_nat : ℝ) = α₀ := by
        rw [hm]
        have : (m_nat : ℤ) = m := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      let w_int : Q → ℕ := fun q => if q = x₀ then m_nat else 1
      have hw_eq : ∀ q : Q, P'.π q = (w_int q : ℝ) := fun q => by
        rw [hP'_eq q]; dsimp only [w_int]; split_ifs
        · exact hm_nat_cast.symm
        · simp
      obtain ⟨v, hv_full, hv_len⟩ :=
        integerStationary_reset_bound hSync P' w_int hw_eq {x₀} (Finset.singleton_nonempty x₀)
      refine ⟨v, ⟨x₀, fun p => ?_⟩, ?_⟩
      · have hp : p ∈ A.preimage {x₀} v := hv_full ▸ Finset.mem_univ p
        simpa [DFA.mem_preimage] using hp
      · have htot : (∑ q : Q, w_int q) - (∑ q ∈ ({x₀} : Finset Q), w_int q) = Fintype.card Q - 1 := by
          rw [Finset.sum_singleton, ← Finset.add_sum_erase _ _ (Finset.mem_univ x₀)]
          have hrest : ∑ q ∈ Finset.univ.erase x₀, w_int q = Fintype.card Q - 1 := by
            have h1 : ∑ q ∈ Finset.univ.erase x₀, w_int q = ∑ _q ∈ Finset.univ.erase x₀, (1 : ℕ) :=
              Finset.sum_congr rfl fun q hq => by
                dsimp only [w_int]; simp [Finset.ne_of_mem_erase hq]
            rw [h1, Finset.sum_const, smul_eq_mul, mul_one,
              Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ]
          rw [hrest]; omega
        rw [htot, ← sq] at hv_len
        exact hv_len
    · -- **Case 2 (`α₀ ∉ ℤ`)**: Unified `Finset.sum` potential `Ψ(S)`!
      push Not at hint
      exact almostUniform_noninteger_cerny hSync P' hn2 x₀ α₀ hα₀_pos hint hP'_eq

/-! ### Section 4: Theorem H.2 — Unconditional Berlinkov QE-1 (NO Strong Connectivity!) -/

/-- **Theorem H.2 (Unconditional Berlinkov Quasi-Eulerian Degree-1 Exact Černý `(n - 1)^2`)**:
Let `A` be ANY synchronizing DFA (NO strong connectivity assumed!) that is quasi-Eulerian of
degree 1: there exist `x₀ ≠ s : Q` and positive letter weights `β : α → ℝ` (`∑ β = 1`) such that
(i) every outgoing transition from `x₀` goes to `x₀` or `s`, and
(ii) every `q ∉ {x₀, s}` has total incoming `β`-weight equal to `1`.
Then `∃ w, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2`. -/
theorem berlinkov_qe1_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (x₀ s : Q) (hxs : x₀ ≠ s)
    (β : α → ℝ) (hβ_pos : ∀ a : α, 0 < β a) (hβ_sum : ∑ a : α, β a = 1)
    (hx₀_out : ∀ a : α, A.step x₀ a = x₀ ∨ A.step x₀ a = s)
    (hin : ∀ q : Q, q ≠ x₀ → q ≠ s →
      (∑ p : Q, ∑ a : α, if A.step p a = q then β a else 0) = 1) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  classical
  let z : ℝ := ∑ a : α, if A.step x₀ a = x₀ then β a else 0
  let y : ℝ := ∑ p ∈ Finset.univ.erase x₀, ∑ a : α, if A.step p a = x₀ then β a else 0
  have hz_le1 : z ≤ 1 := by
    rw [← hβ_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs
    · exact le_rfl
    · exact (hβ_pos a).le
  have hy_nonneg : 0 ≤ y :=
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun a _ => by
      split_ifs
      · exact (hβ_pos a).le
      · exact le_rfl
  by_cases hz1 : z = 1
  · -- **Branch 2 (`z = 1`, `x₀` is a sink)**: reset all `n - 1` states to `x₀` in `≤ (n - 1)^2`!
    have hx₀_sink : ∀ a : α, A.step x₀ a = x₀ := by
      have hdiff : (∑ a : α, (β a - if A.step x₀ a = x₀ then β a else 0)) = 0 := by
        rw [Finset.sum_sub_distrib, hβ_sum]
        change 1 - z = 0
        linarith
      have hnn : ∀ a ∈ (Finset.univ : Finset α),
          0 ≤ β a - (if A.step x₀ a = x₀ then β a else 0) := by
        intro a _; split_ifs
        · linarith
        · linarith [hβ_pos a]
      intro a
      have ha0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hdiff a (Finset.mem_univ a)
      by_contra hne
      simp only [hne, ↓reduceIte, sub_zero] at ha0
      exact (hβ_pos a).ne' ha0
    have hx₀_eval : ∀ w : List α, A.eval x₀ w = x₀ := by
      intro w
      induction w with
      | nil => rfl
      | cons a u ih => rw [DFA.eval_cons, hx₀_sink a, ih]
    rcases hSync with ⟨w_sync, q_sync, hq_sync⟩
    have hq_eq : q_sync = x₀ := (hq_sync x₀).symm.trans (hx₀_eval w_sync)
    -- Every state reaches `x₀` in length `≤ n - 1` by minimal-path pigeonhole
    have hreach_short : ∀ p : Q, ∃ u : List α, u.length ≤ Fintype.card Q - 1 ∧ A.eval p u = x₀ := by
      intro p
      have hex : ∃ k : ℕ, ∃ u : List α, u.length = k ∧ A.eval p u = x₀ :=
        ⟨w_sync.length, w_sync, rfl, (hq_sync p).trans hq_eq⟩
      let k := Nat.find hex
      obtain ⟨u, hu_len, hu_hit⟩ := Nat.find_spec hex
      refine ⟨u, ?_, hu_hit⟩
      by_contra hgt
      have hk_gt : Fintype.card Q - 1 < k := by omega
      have hprefix : ∀ i : Fin k, A.eval p (u.take i.val) ∈ Finset.univ.erase x₀ := by
        intro i
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro heq
        have htl : (u.take i.val).length = i.val := by rw [List.length_take]; omega
        exact Nat.find_min hex i.isLt ⟨u.take i.val, htl, heq⟩
      let T : Finset Q := Finset.univ.erase x₀
      let φ : Fin k → T := fun i => ⟨A.eval p (u.take i.val), hprefix i⟩
      have hcard_lt : Fintype.card T < Fintype.card (Fin k) := by
        rw [Fintype.card_coe]
        dsimp only [T]
        rw [Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ, Fintype.card_fin]
        exact hk_gt
      obtain ⟨i, j, hne, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hcard_lt
      have heq_st : A.eval p (u.take i.val) = A.eval p (u.take j.val) := congrArg Subtype.val hφ
      have hcut : ∀ (a b : Fin k), a.val < b.val →
          A.eval p (u.take a.val) = A.eval p (u.take b.val) → False := by
        intro a b hab hst
        let u' := u.take a.val ++ u.drop b.val
        have hu'_hit : A.eval p u' = x₀ := by
          dsimp only [u']
          rw [DFA.eval_append, hst, ← DFA.eval_append, List.take_append_drop]
          exact hu_hit
        have hu'_len : u'.length < k := by
          dsimp only [u']
          rw [List.length_append, List.length_take, List.length_drop]
          have ha := a.isLt; have hb := b.isLt; omega
        exact Nat.find_min hex hu'_len ⟨u', rfl, hu'_hit⟩
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt'
      · exact hcut i j hlt heq_st
      · exact hcut j i hgt' heq_st.symm
    -- Iteratively drain `S.erase x₀` to `x₀` in `|S.erase x₀| * (n - 1)` steps
    have hdrain : ∀ k : ℕ, ∀ S : Finset Q, (S.erase x₀).card = k →
        ∃ w : List α, (∀ q ∈ S, A.eval q w = x₀) ∧ w.length ≤ k * (Fintype.card Q - 1) := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro S hSk
        by_cases hk0 : k = 0
        · refine ⟨[], fun q hq => ?_, by simp⟩
          by_contra hne
          have hmem : q ∈ S.erase x₀ := Finset.mem_erase.mpr ⟨hne, hq⟩
          have hpos : 0 < (S.erase x₀).card := Finset.card_pos.mpr ⟨q, hmem⟩
          omega
        · obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (S.erase x₀).card)
          obtain ⟨u, hu_len, hu_hit⟩ := hreach_short p
          let S' := A.image S u
          have hS'_sub : S'.erase x₀ ⊆ ((S.erase x₀).erase p).image (fun q => A.eval q u) := by
            intro y hy
            rcases Finset.mem_erase.mp hy with ⟨hy_ne, hyS'⟩
            rcases (DFA.mem_image A S u y).mp hyS' with ⟨q, hqS, rfl⟩
            have hq_ne_x₀ : q ≠ x₀ := fun h => hy_ne (h ▸ hx₀_eval u)
            have hq_ne_p : q ≠ p := fun h => hy_ne (h ▸ hu_hit)
            exact Finset.mem_image.mpr
              ⟨q, Finset.mem_erase.mpr ⟨hq_ne_p, Finset.mem_erase.mpr ⟨hq_ne_x₀, hqS⟩⟩, rfl⟩
          have hcard_lt : (S'.erase x₀).card < k := by
            have h1 := (Finset.card_le_card hS'_sub).trans Finset.card_image_le
            rw [Finset.card_erase_of_mem hp, hSk] at h1
            omega
          obtain ⟨v, hv_hit, hv_len⟩ := ih (S'.erase x₀).card hcard_lt S' rfl
          refine ⟨u ++ v, fun q hq => ?_, ?_⟩
          · rw [DFA.eval_append]
            exact hv_hit (A.eval q u) ((DFA.mem_image A S u _).mpr ⟨q, hq, rfl⟩)
          · rw [List.length_append]
            have h1 : ((S'.erase x₀).card + 1) * (Fintype.card Q - 1) ≤ k * (Fintype.card Q - 1) :=
              Nat.mul_le_mul_right _ (by omega)
            nlinarith
    obtain ⟨w, hw_hit, hw_len⟩ := hdrain ((Finset.univ : Finset Q).erase x₀).card Finset.univ rfl
    refine ⟨w, ⟨x₀, fun q => hw_hit q (Finset.mem_univ q)⟩, ?_⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ, ← sq] at hw_len
    exact hw_len
  · have hz_lt1 : z < 1 := lt_of_le_of_ne hz_le1 hz1
    by_cases hy0 : y = 0
    · -- **Branch 3 (`z < 1 ∧ y = 0`)**: `E = Q \ {x₀}` is closed, uniform on `E` gives `1 + (n - 2)^2 ≤ (n - 1)^2`!
      have hE_closed : ∀ p : Q, p ≠ x₀ → ∀ a : α, A.step p a ≠ x₀ := by
        intro p hp a hstep
        have hp_mem : p ∈ Finset.univ.erase x₀ := Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩
        have hnn1 : ∀ q ∈ Finset.univ.erase x₀,
            0 ≤ ∑ b : α, if A.step q b = x₀ then β b else 0 := fun q _ =>
          Finset.sum_nonneg fun b _ => by split_ifs; exact (hβ_pos b).le; exact le_rfl
        have hp0 := (Finset.sum_eq_zero_iff_of_nonneg hnn1).mp hy0 p hp_mem
        have hnn2 : ∀ b ∈ (Finset.univ : Finset α),
            0 ≤ (if A.step p b = x₀ then β b else 0) := fun b _ => by
          split_ifs; exact (hβ_pos b).le; exact le_rfl
        have ha0 := (Finset.sum_eq_zero_iff_of_nonneg hnn2).mp hp0 a (Finset.mem_univ a)
        simp only [hstep, ↓reduceIte] at ha0
        exact (hβ_pos a).ne' ha0
      -- Pick `b : α` with `A.step x₀ b = s ≠ x₀`
      have hex_b : ∃ b : α, A.step x₀ b ≠ x₀ := by
        by_contra hall; push Not at hall
        have : z = 1 := by
          dsimp only [z]; rw [← hβ_sum]
          exact Finset.sum_congr rfl fun a _ => by simp [hall a]
        exact hz1 this
      obtain ⟨b, hb⟩ := hex_b
      have hQ_to_E : ∀ p : Q, A.step p b ≠ x₀ := by
        intro p
        by_cases hp : p = x₀
        · subst hp; exact hb
        · exact hE_closed p hp b
      let E := {q : Q // q ≠ x₀}
      let AE : DFA E α := ⟨fun p a => ⟨A.step p.1 a, hE_closed p.1 p.2 a⟩⟩
      have hAE_eval : ∀ (p : E) (w : List α), (AE.eval p w).1 = A.eval p.1 w := by
        intro p w
        induction w generalizing p with
        | nil => rfl
        | cons a u ih => exact ih (AE.step p a)
      have hcard_E : Fintype.card E = Fintype.card Q - 1 := by
        dsimp only [E]
        have h1 : Fintype.card {q : Q // q = x₀} = 1 := Fintype.card_unique
        rw [Fintype.card_subtype_compl, h1]
      have hE_sync : AE.IsSynchronizing := by
        rcases hSync with ⟨w_sync, q₀, hq₀⟩
        have hsE : s ≠ x₀ := hxs.symm
        have hq₀_ne : q₀ ≠ x₀ := by
          have h1 := hAE_eval ⟨s, hsE⟩ w_sync
          rw [hq₀ s] at h1
          exact h1 ▸ (AE.eval ⟨s, hsE⟩ w_sync).2
        refine ⟨w_sync, ⟨q₀, hq₀_ne⟩, fun p => Subtype.ext ?_⟩
        rw [hAE_eval, hq₀ p.1]
      -- Construct uniform stationary vector `π_E = 1` on `AE`
      let PE : PositiveStationary AE :=
        { β := β
          π := fun _ => 1
          hβ_pos := hβ_pos
          hβ_sum := hβ_sum
          hπ_pos := fun _ => zero_lt_one
          hstat := by
            let sE : E := ⟨s, hxs.symm⟩
            have hstat_ne : ∀ q : E, q ≠ sE →
                (∑ p : E, (1 : ℝ) * (∑ a : α, if AE.step p a = q then β a else 0)) = 1 := by
              intro q hqs
              have hq_nes : q.1 ≠ s := fun h => hqs (Subtype.ext h)
              have hstep_iff : ∀ (p : E) (a : α), AE.step p a = q ↔ A.step p.1 a = q.1 :=
                fun p a => Subtype.ext_iff
              simp_rw [one_mul, hstep_iff]
              have hx₀_zero : (∑ a : α, if A.step x₀ a = q.1 then β a else 0) = 0 := by
                refine Finset.sum_eq_zero fun a _ => ?_
                have hne : A.step x₀ a ≠ q.1 := by
                  rcases hx₀_out a with h | h
                  · rw [h]; exact q.2.symm
                  · rw [h]; exact hq_nes.symm
                simp [hne]
              have hsum_eq :
                  (∑ p : E, ∑ a : α, if A.step p.1 a = q.1 then β a else 0) =
                    ∑ p : Q, ∑ a : α, if A.step p a = q.1 then β a else 0 := by
                rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x₀), hx₀_zero, zero_add]
                refine Finset.sum_nbij (fun p : E => p.1)
                  (fun p _ => Finset.mem_erase.mpr ⟨p.2, Finset.mem_univ p.1⟩)
                  (fun p₁ _ p₂ _ h => Subtype.ext h)
                  (fun p hp => ⟨⟨p, Finset.ne_of_mem_erase hp⟩, Finset.mem_univ _, rfl⟩)
                  (fun _ _ => rfl)
              rw [hsum_eq, hin q.1 q.2 hq_nes]
            intro q
            by_cases hqs : q = sE
            · subst hqs
              have htot :
                  (∑ r : E, ∑ p : E, (1 : ℝ) * (∑ a : α, if AE.step p a = r then β a else 0)) =
                    ∑ _r : E, (1 : ℝ) := by
                simp_rw [one_mul]
                rw [Finset.sum_comm]
                have h1 : ∀ p : E,
                    (∑ r : E, ∑ a : α, if AE.step p a = r then β a else 0) = 1 := by
                  intro p
                  rw [Finset.sum_comm]
                  have h2 : ∀ a : α, (∑ r : E, if AE.step p a = r then β a else 0) = β a := by
                    intro a
                    rw [Finset.sum_eq_single (AE.step p a)]
                    · simp
                    · intro r _ hr; simp [Ne.symm hr]
                    · intro h; exact absurd (Finset.mem_univ _) h
                  simp_rw [h2]; exact hβ_sum
                simp_rw [h1]
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ sE),
                  ← Finset.add_sum_erase _ (fun _ => (1 : ℝ)) (Finset.mem_univ sE)] at htot
              have hrest :
                  (∑ r ∈ Finset.univ.erase sE,
                    ∑ p : E, (1 : ℝ) * (∑ a : α, if AE.step p a = r then β a else 0)) =
                  ∑ _r ∈ Finset.univ.erase sE, (1 : ℝ) :=
                Finset.sum_congr rfl fun r hr => hstat_ne r (Finset.ne_of_mem_erase hr)
              linarith
            · exact hstat_ne q hqs }
      obtain ⟨wE, ⟨qE, hqE⟩, hwE_len⟩ :=
        almostUniform_cerny AE hE_sync PE ⟨s, hxs.symm⟩ 1 (fun _ _ => rfl)
      refine ⟨b :: wE, ⟨qE.1, fun p => ?_⟩, ?_⟩
      · rw [DFA.eval_cons]
        have h1 := hAE_eval ⟨A.step p b, hQ_to_E p⟩ wE
        rw [hqE ⟨A.step p b, hQ_to_E p⟩] at h1
        exact h1.symm
      · rw [hcard_E] at hwE_len
        rw [List.length_cons]
        have hn2 : 2 ≤ Fintype.card Q := by
          have hpair : ({x₀, s} : Finset Q).card = 2 := Finset.card_pair hxs
          have := Finset.card_le_univ ({x₀, s} : Finset Q)
          omega
        have h1 : 1 + (Fintype.card Q - 1 - 1) ^ 2 ≤ (Fintype.card Q - 1) ^ 2 := by
          have hsub1 : 1 ≤ Fintype.card Q := by omega
          have hsub2 : 1 ≤ Fintype.card Q - 1 := by omega
          have h2z : (2 : ℤ) ≤ (Fintype.card Q : ℤ) := by omega
          zify [hsub1, hsub2]
          nlinarith only [h2z]
        omega
    · -- **Branch 1 (`z < 1 ∧ y > 0`)**: explicit almost-uniform `π` with `α₀ = y / (1 - z)` → Theorem H!
      have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy0)
      have h1z_pos : 0 < 1 - z := sub_pos.mpr hz_lt1
      let α₀ : ℝ := y / (1 - z)
      have hα₀_pos : 0 < α₀ := div_pos hy_pos h1z_pos
      let π : Q → ℝ := fun q => if q = x₀ then α₀ else 1
      have hstat_ne : ∀ q : Q, q ≠ s →
          (∑ p : Q, π p * (∑ a : α, if A.step p a = q then β a else 0)) = π q := by
        intro q hqs
        by_cases hqx : q = x₀
        · rw [hqx]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x₀)]
          have h1 : π x₀ * (∑ a : α, if A.step x₀ a = x₀ then β a else 0) = α₀ * z := by
            simp [π, z]
          have h2 : (∑ p ∈ Finset.univ.erase x₀,
              π p * (∑ a : α, if A.step p a = x₀ then β a else 0)) = y := by
            dsimp only [y]
            refine Finset.sum_congr rfl fun p hp => ?_
            simp [π, Finset.ne_of_mem_erase hp]
          rw [h1, h2]
          simp only [π, ↓reduceIte, α₀]
          field_simp [h1z_pos.ne']
          ring
        · have hx₀_zero : (∑ a : α, if A.step x₀ a = q then β a else 0) = 0 := by
            refine Finset.sum_eq_zero fun a _ => ?_
            have hne : A.step x₀ a ≠ q := by
              rcases hx₀_out a with h | h
              · rw [h]; exact Ne.symm hqx
              · rw [h]; exact Ne.symm hqs
            simp [hne]
          have hrew : (∑ p : Q, π p * (∑ a : α, if A.step p a = q then β a else 0)) =
              ∑ p : Q, ∑ a : α, if A.step p a = q then β a else 0 := by
            refine Finset.sum_congr rfl fun p _ => ?_
            by_cases hpx : p = x₀
            · subst hpx; rw [hx₀_zero, mul_zero]
            · simp [π, hpx]
          rw [hrew, hin q hqx hqs]
          simp [π, hqx]
      let P : PositiveStationary A :=
        { β := β
          π := π
          hβ_pos := hβ_pos
          hβ_sum := hβ_sum
          hπ_pos := fun q => by dsimp only [π]; split_ifs; exact hα₀_pos; exact zero_lt_one
          hstat := by
            intro q
            by_cases hqs : q = s
            · rw [hqs]
              have htot :
                  (∑ r : Q, ∑ p : Q, π p * (∑ a : α, if A.step p a = r then β a else 0)) =
                    ∑ p : Q, π p := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun p _ => ?_
                rw [← Finset.mul_sum, Finset.sum_comm]
                have h1 : ∀ a : α, (∑ r : Q, if A.step p a = r then β a else 0) = β a := by
                  intro a
                  rw [Finset.sum_eq_single (A.step p a)]
                  · simp
                  · intro r _ hr; simp [Ne.symm hr]
                  · intro h; exact absurd (Finset.mem_univ _) h
                simp_rw [h1, hβ_sum, mul_one]
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
                  ← Finset.add_sum_erase _ π (Finset.mem_univ s)] at htot
              have hrest :
                  (∑ r ∈ Finset.univ.erase s,
                    ∑ p : Q, π p * (∑ a : α, if A.step p a = r then β a else 0)) =
                  ∑ r ∈ Finset.univ.erase s, π r :=
                Finset.sum_congr rfl fun r hr => hstat_ne r (Finset.ne_of_mem_erase hr)
              linarith
            · exact hstat_ne q hqs }
      exact almostUniform_cerny A hSync P x₀ 1 (fun q hqx => by simp [P, π, hqx])

/-! ### Section 5: Bonus Theorem H_k — Multi-Exception Rational Stationary Vectors -/

/-- **Theorem H_k (Multi-Exception Two-Value Rational Stationary Vector Bound)**:
If a synchronizing `n`-state DFA admits a positive stationary vector taking value `1` on `Q \ X`
and `(p : ℝ) / (q₀ : ℝ)` on `X` (`p, q₀ ≥ 1`, `1 ≤ |X| ≤ n - 1`), then:
`w.length ≤ (q₀ * (n - |X|) + |X| * p - max p q₀) * (n - 1)`. -/
theorem multiException_rational_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (X : Finset Q) (hX_pos : 1 ≤ X.card) (hX_lt : X.card < Fintype.card Q)
    (p q₀ : ℕ) (_hp : 0 < p) (hq₀ : 0 < q₀)
    (hπ_eq : ∀ q : Q, P.π q = if q ∈ X then (p : ℝ) / (q₀ : ℝ) else 1) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ (q₀ * (Fintype.card Q - X.card) + X.card * p - max p q₀) *
        (Fintype.card Q - 1) := by
  classical
  have hq₀_r : (0 : ℝ) < (q₀ : ℝ) := by exact_mod_cast hq₀
  let P' : PositiveStationary A := AlmostUniform.scaleStationary P (q₀ : ℝ) hq₀_r
  let w_int : Q → ℕ := fun q => if q ∈ X then p else q₀
  have hw_eq : ∀ q : Q, P'.π q = (w_int q : ℝ) := fun q => by
    dsimp only [P', AlmostUniform.scaleStationary, w_int]
    rw [hπ_eq q]
    split_ifs
    · exact mul_div_cancel₀ _ hq₀_r.ne'
    · ring
  -- Pick `q_max : Q` attaining `w_int q_max = max p q₀`
  have hex_max : ∃ q_max : Q, w_int q_max = max p q₀ := by
    by_cases hle : q₀ ≤ p
    · obtain ⟨x, hx⟩ := Finset.card_pos.mp hX_pos
      refine ⟨x, ?_⟩
      simp only [w_int, hx, ↓reduceIte, max_eq_left hle]
    · have hex_out : ∃ y : Q, y ∉ X := by
        by_contra hall; push Not at hall
        have := Finset.card_le_card (show (Finset.univ : Finset Q) ⊆ X from fun y _ => hall y)
        rw [Finset.card_univ] at this; omega
      obtain ⟨y, hy⟩ := hex_out
      refine ⟨y, ?_⟩
      simp only [w_int, hy, ↓reduceIte, max_eq_right (le_of_not_ge hle)]
  obtain ⟨q_max, hq_max⟩ := hex_max
  obtain ⟨v, hv_full, hv_len⟩ :=
    integerStationary_reset_bound hSync P' w_int hw_eq {q_max}
      (Finset.singleton_nonempty q_max)
  refine ⟨v, ⟨q_max, fun q => ?_⟩, ?_⟩
  · have hq : q ∈ A.preimage {q_max} v := hv_full ▸ Finset.mem_univ q
    simpa [DFA.mem_preimage] using hq
  · have hsum_tot : ∑ q : Q, w_int q = q₀ * (Fintype.card Q - X.card) + X.card * p := by
      have hdisj : Disjoint X (Finset.univ \ X) := Finset.disjoint_sdiff
      have hunion : X ∪ (Finset.univ \ X) = Finset.univ :=
        Finset.union_sdiff_of_subset (Finset.subset_univ X)
      rw [← hunion, Finset.sum_union hdisj]
      have h1 : ∑ q ∈ X, w_int q = X.card * p := by
        have hcongr : ∑ q ∈ X, w_int q = ∑ _q ∈ X, p :=
          Finset.sum_congr rfl fun q hq => by dsimp only [w_int]; simp only [hq, ↓reduceIte]
        rw [hcongr, Finset.sum_const, smul_eq_mul]
      have h2 : ∑ q ∈ Finset.univ \ X, w_int q = q₀ * (Fintype.card Q - X.card) := by
        have hcongr : ∑ q ∈ Finset.univ \ X, w_int q = ∑ _q ∈ Finset.univ \ X, q₀ :=
          Finset.sum_congr rfl fun q hq => by
            dsimp only [w_int]; simp only [(Finset.mem_sdiff.mp hq).2, ↓reduceIte]
        rw [hcongr, Finset.sum_const, smul_eq_mul, Finset.card_sdiff, Finset.inter_univ,
          Finset.card_univ, mul_comm]
      rw [h1, h2, add_comm]
    rw [hsum_tot, Finset.sum_singleton, hq_max] at hv_len
    exact hv_len

/-- **Corollary (`α = 1 / 2`, arbitrary multiplicity `1 ≤ k ≤ n - 1`)**:
For half-weight exceptional states of ANY multiplicity `k`,
`w.length ≤ (2 * n - k - 2) * (n - 1) < 2 * (n - 1) ^ 2` — uniformly quadratic in `n` and
independent of `k` (exponentially beating Berlinkov 2013's `2^k (n - k + 1)(n - 1)`!). -/
theorem multiException_half_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (X : Finset Q) (hX_pos : 1 ≤ X.card) (hX_lt : X.card < Fintype.card Q)
    (hπ_eq : ∀ q : Q, P.π q = if q ∈ X then (1 : ℝ) / 2 else 1) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ (2 * Fintype.card Q - X.card - 2) * (Fintype.card Q - 1) ∧
      w.length < 2 * (Fintype.card Q - 1) ^ 2 := by
  have hπ' : ∀ q : Q, P.π q = if q ∈ X then ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) else 1 := by
    simpa using hπ_eq
  obtain ⟨w, hw_sync, hw_len⟩ :=
    multiException_rational_bound A hSync P X hX_pos hX_lt 1 2 (by omega) (by omega) hπ'
  refine ⟨w, hw_sync, ?_, ?_⟩
  · have hcoeff : 2 * (Fintype.card Q - X.card) + X.card * 1 - max 1 2 =
        2 * Fintype.card Q - X.card - 2 := by omega
    rwa [hcoeff] at hw_len
  · have hcoeff : 2 * (Fintype.card Q - X.card) + X.card * 1 - max 1 2 =
        2 * Fintype.card Q - X.card - 2 := by omega
    rw [hcoeff] at hw_len
    have hn_ge2 : 2 ≤ Fintype.card Q := by omega
    have hlt_coeff : 2 * Fintype.card Q - X.card - 2 < 2 * (Fintype.card Q - 1) := by omega
    have hmul : (2 * Fintype.card Q - X.card - 2) * (Fintype.card Q - 1) <
        2 * (Fintype.card Q - 1) * (Fintype.card Q - 1) :=
      Nat.mul_lt_mul_of_pos_right hlt_coeff (by omega)
    have hsq : 2 * (Fintype.card Q - 1) * (Fintype.card Q - 1) = 2 * (Fintype.card Q - 1) ^ 2 := by
      ring
    omega

end Cerny
