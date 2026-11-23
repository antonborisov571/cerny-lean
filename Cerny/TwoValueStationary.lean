import Cerny.Defs
import Cerny.AlmostUniform
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Zify

/-!
# Two-Value Stationary Vectors over `ℝ_{>0}` (`Theorems H_two & H_real_k`) & Super-Eulerian Tier Exact Černý (`Lemma T.1 & Theorem T`)

This file formalizes Round 5's stationary-measure theorems (`docs/round5_two_cycle_closure.md` §2–3 & §5.2–5.3):

## Main Results
* `Cerny.subset_bfs_entry` & `Cerny.subset_bfs_escape` (**Lemma H.3**):
  Multi-state BFS entry (`≤ n - k - r + 1`) and escape (`≤ r + 1`) orbit bounds for any subset `X`.
* `Cerny.twoValue_k2_int_bound`, `Cerny.twoValue_k2_nonHalfInt_bound`,
  `Cerny.twoValue_k2_threeHalves_bound`, `Cerny.twoValue_k2_universal_bound` (**Theorem H_two**):
  Complete resolution of Goel's Open Frontier #1 (`|X| = 2`, arbitrary `α₀ ∈ ℝ_{>0}`):
  - `α₀ ∈ ℤ_{≥ 1}`: `2 * w.length ≤ (3 * n - 4) * (n - 1) < 3 * (n - 1)^2`;
  - `α₀ ∉ (1/2)ℤ`: `w.length ≤ 2 * n^2 - 6 * n + 5 < 2 * (n - 1)^2`;
  - `α₀ = 3/2`: `w.length < 2 * (n - 1)^2`;
  - ALL `α₀ ∈ ℝ_{>0}` unconditionally: `14 * w.length < 29 * (n - 1)^2`!
* `Cerny.twoValue_general_k_bound`, `Cerny.twoValue_general_k_nonSmallDenom_bound`,
  `Cerny.twoValue_general_k_irrational_bound` (**Theorem H_real_k**):
  General `k`-exception two-value stationary vectors over ALL `ℝ_{>0}`, exponentially beating
  Berlinkov (2013)'s `2^k (n - k + 1)(n - 1)` and removing denominator blowup.
* `Cerny.szykula_tier_lemma` (**Lemma T.1**):
  Self-contained dual-subspace proof that at most `2^j - 2` nonempty proper subsets `K ⊂ Q` have
  `∀ w, w.length ≤ n - j → π(K w⁻¹) = π(K)` (using affine-subspace `{0, 1}`-counting!).
* `Cerny.superEulerian_tier_bound`, `Cerny.superEulerian_const_excess_cerny`,
  `Cerny.superEulerian_excess_one_cerny`, `Cerny.superEulerian_excess_two_cerny`,
  `Cerny.superEulerian_excess_three_cerny`, `Cerny.superEulerian_log_excess_cerny` (**Theorem T**):
  Master tier bound `w.length ≤ J * (n - t) + 2^(t+1) - 2*t - 2` for every `1 ≤ t ≤ n`, yielding
  **EXACT Černý `(n - 1)^2`** for arbitrary constant excess `E` (`n ≥ 2^(E+3) - E^2 - 3*E - 5`)
  and logarithmic excess `J ≤ n + Nat.log 2 n - 4` (`n ≥ 32`)!
-/

namespace Cerny

universe u v w

namespace TwoValueStationary

section CoreHelpers

variable {Q : Type u} {α : Type v}

/-- Pullback linear operator `(pullbackR A w v) q = v (A.eval q w)` on `Q → ℝ`. -/
private def pullbackR (A : DFA Q α) (w : List α) : (Q → ℝ) →ₗ[ℝ] (Q → ℝ) where
  toFun v q := v (A.eval q w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma pullbackR_cons (A : DFA Q α) (a : α) (u : List α) (v : Q → ℝ) :
    pullbackR A (a :: u) v = pullbackR A [a] (pullbackR A u v) := by
  ext q; simp [pullbackR]

/-- Pushforward (row-vector action) linear operator `(pushR A w v) q = ∑_{p·w = q} v p`. -/
private def pushR [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) :
    (Q → ℝ) →ₗ[ℝ] (Q → ℝ) where
  toFun v q := ∑ p : Q, if A.eval p w = q then v p else 0
  map_add' x y := by
    ext q; simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
  map_smul' c x := by
    ext q; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp

private lemma pushR_nil [Fintype Q] [DecidableEq Q] (A : DFA Q α) (v : Q → ℝ) :
    pushR A [] v = v := by
  ext q
  simp only [pushR, LinearMap.coe_mk, AddHom.coe_mk, DFA.eval_nil]
  rw [Finset.sum_eq_single q]
  · simp
  · intro p _ hp; simp [hp]
  · intro h; exact absurd (Finset.mem_univ q) h

private lemma pushR_append [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w₁ w₂ : List α) (v : Q → ℝ) :
    pushR A (w₁ ++ w₂) v = pushR A w₂ (pushR A w₁ v) := by
  ext q
  simp only [pushR, LinearMap.coe_mk, AddHom.coe_mk]
  calc (∑ p : Q, if A.eval p (w₁ ++ w₂) = q then v p else 0)
      = ∑ p : Q, ∑ r : Q, if A.eval p w₁ = r then (if A.eval r w₂ = q then v p else 0) else 0 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_eq_single (A.eval p w₁)]
          · simp [DFA.eval_append]
          · intro r _ hr; simp [Ne.symm hr]
          · intro h; exact absurd (Finset.mem_univ _) h
    _ = ∑ r : Q, ∑ p : Q, if A.eval p w₁ = r then (if A.eval r w₂ = q then v p else 0) else 0 :=
          Finset.sum_comm
    _ = ∑ r : Q, if A.eval r w₂ = q then (∑ p : Q, if A.eval p w₁ = r then v p else 0) else 0 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          by_cases hr : A.eval r w₂ = q <;> simp [hr]

private lemma pushR_dot [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) (v f : Q → ℝ) :
    (∑ q : Q, pushR A w v q * f q) = ∑ p : Q, v p * f (A.eval p w) := by
  simp only [pushR, LinearMap.coe_mk, AddHom.coe_mk]
  calc (∑ q : Q, (∑ p : Q, if A.eval p w = q then v p else 0) * f q)
      = ∑ q : Q, ∑ p : Q, if A.eval p w = q then v p * f q else 0 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    _ = ∑ p : Q, ∑ q : Q, if A.eval p w = q then v p * f q else 0 := Finset.sum_comm
    _ = ∑ p : Q, v p * f (A.eval p w) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_eq_single (A.eval p w)]
          · simp
          · intro q _ hq; simp [Ne.symm hq]
          · intro h; exact absurd (Finset.mem_univ _) h

/-- Weighted inner-product linear functional `v ↦ ∑ q, π q * v q` on `Q → ℝ`. -/
private def dotLinR [Fintype Q] (π : Q → ℝ) : (Q → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ q : Q, π q * v q
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring

private lemma finrank_ker_dotLinR [Fintype Q] {π : Q → ℝ} (hπ_sum : ∑ q : Q, π q ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (dotLinR π)) = Fintype.card Q - 1 := by
  classical
  have hex_nz : ∃ q₀ : Q, π q₀ ≠ 0 := by
    by_contra hall; push Not at hall
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
            exact Finset.sum_congr rfl fun p _ => by ring
      _ = c * P.π q := by rw [h]

/-- Same-length positive-deviation extraction from `positiveStationary_word_avg`. -/
private lemma exists_gt_of_ne [Fintype Q] [Fintype α] [DecidableEq Q]
    {A : DFA Q α} (P : PositiveStationary A) (S : Finset Q) (u : List α)
    (hne : ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q) :
    ∃ w : List α, w.length = u.length ∧
      ∑ q ∈ S, P.π q < ∑ p ∈ A.preimage S w, P.π p := by
  set k := u.length
  obtain ⟨hsum1, havg⟩ := positiveStationary_word_avg P S k
  let f₀ : Fin k → α := fun i => u.get i
  have hf₀_ofFn : List.ofFn f₀ = u := List.ofFn_get u
  have hW_pos : ∀ f : Fin k → α, 0 < ∏ i : Fin k, P.β (f i) :=
    fun f => Finset.prod_pos fun i _ => P.hβ_pos (f i)
  have hzero :
      (∑ f : Fin k → α, (∏ i : Fin k, P.β (f i)) *
          ((∑ p ∈ A.preimage S (List.ofFn f), P.π p) - ∑ q ∈ S, P.π q)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    have h1 : (∑ f : Fin k → α, (∏ i : Fin k, P.β (f i)) *
        ∑ p ∈ A.preimage S (List.ofFn f), P.π p) = ∑ q ∈ S, P.π q := havg
    have h2 : (∑ f : Fin k → α, ∏ i : Fin k, P.β (f i)) = 1 := hsum1
    rw [h1, h2, one_mul, sub_self]
  have hex : ∃ f : Fin k → α, ∑ q ∈ S, P.π q < ∑ p ∈ A.preimage S (List.ofFn f), P.π p := by
    by_contra hall; push Not at hall
    have hle : ∀ f : Fin k → α,
        (∏ i : Fin k, P.β (f i)) *
          ((∑ p ∈ A.preimage S (List.ofFn f), P.π p) - ∑ q ∈ S, P.π q) ≤ 0 :=
      fun f => mul_nonpos_of_nonneg_of_nonpos (hW_pos f).le (sub_nonpos.mpr (hall f))
    have hlt₀ :
        (∏ i : Fin k, P.β (f₀ i)) *
          ((∑ p ∈ A.preimage S (List.ofFn f₀), P.π p) - ∑ q ∈ S, P.π q) < 0 := by
      refine mul_neg_of_pos_of_neg (hW_pos f₀) ?_
      rw [hf₀_ofFn]
      exact sub_neg.mpr (lt_of_le_of_ne (by simpa [hf₀_ofFn] using hall f₀) hne)
    have hsum_lt :
        (∑ f : Fin k → α, (∏ i : Fin k, P.β (f i)) *
            ((∑ p ∈ A.preimage S (List.ofFn f), P.π p) - ∑ q ∈ S, P.π q)) <
          ∑ _f : Fin k → α, (0 : ℝ) :=
      Finset.sum_lt_sum (fun f _ => hle f) ⟨f₀, Finset.mem_univ f₀, hlt₀⟩
    rw [hzero, Finset.sum_const_zero] at hsum_lt
    exact lt_irrefl _ hsum_lt
  rcases hex with ⟨f, hf⟩
  exact ⟨List.ofFn f, List.length_ofFn, hf⟩

/-- Steinberg hyperplane escape bound: for every nonempty proper `S ⊂ Q`, some `u` of length
`≤ n - 1` satisfies `π(S u⁻¹) ≠ π(S)`. -/
private lemma steinberg_exists_ne [Fintype Q] [Fintype α] [DecidableEq Q]
    {A : DFA Q α} (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (S : Finset Q) (hS_ne : S.Nonempty) (hS_lt : S.card < Fintype.card Q) :
    ∃ u : List α, u.length ≤ Fintype.card Q - 1 ∧
      ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q := by
  classical
  have : Nonempty Q := hSync.nonempty
  have hπ_total_pos : 0 < ∑ q : Q, P.π q :=
    Finset.sum_pos (fun q _ => P.hπ_pos q) Finset.univ_nonempty
  let tot : ℝ := ∑ q : Q, P.π q
  let cS : ℝ := (∑ q ∈ S, P.π q) / tot
  have hcS_pos : 0 < cS := div_pos (Finset.sum_pos (fun q _ => P.hπ_pos q) hS_ne) hπ_total_pos
  have hcS_lt1 : cS < 1 := by
    have hex_out : ∃ y : Q, y ∉ S := by
      by_contra hall; push Not at hall
      have hle := Finset.card_le_card (show (Finset.univ : Finset Q) ⊆ S from fun y _ => hall y)
      rw [Finset.card_univ] at hle; omega
    obtain ⟨y, hy⟩ := hex_out
    have hS_lt_tot : ∑ q ∈ S, P.π q < tot :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ S) (Finset.mem_univ y) hy (P.hπ_pos y)
        (fun q _ _ => (P.hπ_pos q).le)
    have hmul : cS * tot = ∑ q ∈ S, P.π q := div_mul_cancel₀ _ hπ_total_pos.ne'
    nlinarith
  let γ : Q → ℝ := fun q => (if q ∈ S then (1 : ℝ) else 0) - cS
  have hdot_eval : ∀ u : List α,
      dotLinR P.π (pullbackR A u γ) = (∑ p ∈ A.preimage S u, P.π p) - ∑ q ∈ S, P.π q := by
    intro u
    simp only [dotLinR, pullbackR, γ, LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    have h1 : (∑ p : Q, P.π p * if A.eval p u ∈ S then (1 : ℝ) else 0) =
        ∑ p ∈ A.preimage S u, P.π p := by
      rw [DFA.preimage, Finset.sum_filter]
      exact Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    have h2 : (∑ p : Q, P.π p) * cS = ∑ q ∈ S, P.π q := by
      dsimp only [cS, tot]; exact mul_div_cancel₀ _ hπ_total_pos.ne'
    rw [h1, h2]
  let H : Submodule ℝ (Q → ℝ) := LinearMap.ker (dotLinR P.π)
  let W : ℕ → Submodule ℝ (Q → ℝ) := fun k =>
    Submodule.span ℝ { v : Q → ℝ | ∃ u : List α, u.length ≤ k ∧ v = pullbackR A u γ }
  have hW_mono : ∀ {j k}, j ≤ k → W j ≤ W k := by
    intro j k hjk; apply Submodule.span_mono
    rintro v ⟨u, hu, rfl⟩; exact ⟨u, hu.trans hjk, rfl⟩
  have hW0_dim : 1 ≤ Module.finrank ℝ (W 0) := by
    have hγ_mem : γ ∈ W 0 := Submodule.subset_span ⟨[], le_rfl, rfl⟩
    have hγ_ne : γ ≠ 0 := by
      obtain ⟨p₀⟩ := hSync.nonempty
      intro h0; have hval := congrFun h0 p₀
      simp only [γ, Pi.zero_apply] at hval; split_ifs at hval <;> linarith
    have hbot : (⊥ : Submodule ℝ (Q → ℝ)) < W 0 := by
      rw [bot_lt_iff_ne_bot]; intro hb; rw [hb, Submodule.mem_bot] at hγ_mem; exact hγ_ne hγ_mem
    have hlt := Submodule.finrank_lt_finrank_of_lt hbot
    rw [finrank_bot] at hlt; omega
  rcases hSync with ⟨w_sync, q₀, hq₀⟩
  have hsync_notH : pullbackR A w_sync γ ∉ H := by
    intro hmem
    change dotLinR P.π (pullbackR A w_sync γ) = 0 at hmem
    have hconst : ∀ p : Q, pullbackR A w_sync γ p = γ q₀ := fun p => by
      simp only [pullbackR, LinearMap.coe_mk, AddHom.coe_mk, hq₀ p]
    simp only [dotLinR, LinearMap.coe_mk, AddHom.coe_mk] at hmem
    simp_rw [hconst, ← Finset.sum_mul] at hmem
    have hγq0 : γ q₀ = 0 := (mul_eq_zero.mp hmem).resolve_left hπ_total_pos.ne'
    simp only [γ] at hγq0; split_ifs at hγq0 <;> linarith
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
        have hclosed : ∀ (a : α) (v : Q → ℝ), v ∈ W j → pullbackR A [a] v ∈ W j := by
          intro a v hv; rw [heq]
          induction hv using Submodule.span_induction with
          | mem x hx =>
            rcases hx with ⟨u, hu, rfl⟩
            rw [← pullbackR_cons]
            exact Submodule.subset_span ⟨a :: u, by simp; omega, rfl⟩
          | zero => simp
          | add x y _ _ hx hy => rw [map_add]; exact (W (j + 1)).add_mem hx hy
          | smul c x _ hx => rw [map_smul]; exact (W (j + 1)).smul_mem c hx
        have hall : ∀ u : List α, pullbackR A u γ ∈ W j := by
          intro u; induction u with
          | nil => exact Submodule.subset_span ⟨[], Nat.zero_le j, rfl⟩
          | cons a u ih => rw [pullbackR_cons]; exact hclosed a _ ih
        exact hsync_notH (hk₀_min j (by omega) (hall w_sync))
      have hdim : ∀ j ≤ k₀ - 1, j + 1 ≤ Module.finrank ℝ (W j) := by
        intro j; induction j with
        | zero => intro _; exact hW0_dim
        | succ j ih =>
          intro hj; have ih' := ih (by omega)
          have hlt := Submodule.finrank_lt_finrank_of_lt (hstrict j (by omega)); omega
      have h1 := hdim (k₀ - 1) le_rfl
      have h2 : Module.finrank ℝ (W (k₀ - 1)) ≤ Module.finrank ℝ H :=
        Submodule.finrank_mono (hk₀_min (k₀ - 1) (by omega))
      rw [finrank_ker_dotLinR hπ_total_pos.ne'] at h2; omega
  have hex_u : ∃ u : List α, u.length ≤ k₀ ∧ dotLinR P.π (pullbackR A u γ) ≠ 0 := by
    by_contra hall; push Not at hall
    apply hk₀_not; rw [Submodule.span_le]
    rintro v ⟨u, hu, rfl⟩; exact hall u hu
  rcases hex_u with ⟨u, hu_len, hu_nz⟩
  rw [hdot_eval u] at hu_nz
  exact ⟨u, by omega, sub_ne_zero.mp hu_nz⟩

/-- Steinberg extending word: every nonempty proper `S ⊂ Q` has `w` with `|w| ≤ n - 1` and
`π(S w⁻¹) > π(S)`. -/
private lemma steinberg_exists_gt [Fintype Q] [Fintype α] [DecidableEq Q]
    {A : DFA Q α} (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (S : Finset Q) (hS_ne : S.Nonempty) (hS_lt : S.card < Fintype.card Q) :
    ∃ w : List α, w.length ≤ Fintype.card Q - 1 ∧
      ∑ q ∈ S, P.π q < ∑ p ∈ A.preimage S w, P.π p := by
  obtain ⟨u, hu_len, hu_ne⟩ := steinberg_exists_ne hSync P S hS_ne hS_lt
  obtain ⟨w, hw_len, hw_gt⟩ := exists_gt_of_ne P S u hu_ne
  exact ⟨w, by omega, hw_gt⟩

/-- **Generic Indexed Remaining-Level Potential Engine (ZERO injectivity required!)**:
Given any finite index set `I`, level map `val : ι → ℝ`, and budget `cost : ι → ℕ`,
if every nonempty proper `S ⊂ Q` with `π(S) ≥ π(S₀)` hits some `i ∈ I` with `val i = π(S)`,
`0 < cost i`, and an extending word `w` (`w.length ≤ cost i`, `π(S w⁻¹) > π(S)`), then `S₀`
reaches `Finset.univ` in total length `≤ ∑_{i ∈ I, π(S₀) ≤ val i} cost i`! -/
private lemma potential_reach_univ {ι : Type w} [Fintype Q] [Fintype α] [DecidableEq Q]
    [DecidableEq ι]
    {A : DFA Q α} (P : PositiveStationary A)
    (I : Finset ι) (val : ι → ℝ) (cost : ι → ℕ) (S₀ : Finset Q) (hS₀_ne : S₀.Nonempty)
    (hstep : ∀ S : Finset Q, S.Nonempty → S ≠ Finset.univ →
      ∑ q ∈ S₀, P.π q ≤ ∑ q ∈ S, P.π q →
      ∃ i ∈ I, val i = ∑ q ∈ S, P.π q ∧ 0 < cost i ∧
        ∃ w : List α, w.length ≤ cost i ∧ ∑ q ∈ S, P.π q < ∑ p ∈ A.preimage S w, P.π p) :
    ∃ v : List α, A.preimage S₀ v = Finset.univ ∧
      v.length ≤ ∑ i ∈ I.filter (fun i => by classical exact ∑ q ∈ S₀, P.π q ≤ val i), cost i := by
  classical
  let Ψ : Finset Q → ℕ := fun S =>
    ∑ i ∈ I.filter (fun i => ∑ q ∈ S, P.π q ≤ val i), cost i
  have hind : ∀ k : ℕ, ∀ S : Finset Q, S.Nonempty → ∑ q ∈ S₀, P.π q ≤ ∑ q ∈ S, P.π q →
      Ψ S = k → ∃ v : List α, A.preimage S v = Finset.univ ∧ v.length ≤ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro S hS_ne hS_ge hk
      by_cases hfull : S = Finset.univ
      · refine ⟨[], ?_, by simp⟩
        rw [hfull]; ext q; simp
      · obtain ⟨i, hiI, hval_i, hcost_pos, w, hw_len, hw_gt⟩ := hstep S hS_ne hfull hS_ge
        set S' := A.preimage S w
        have hS'_ne : S'.Nonempty := by
          by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
          rw [hemp, Finset.sum_empty] at hw_gt
          have hpos : 0 < ∑ q ∈ S, P.π q := Finset.sum_pos (fun q _ => P.hπ_pos q) hS_ne
          linarith
        let F₀ := I.filter (fun j => ∑ q ∈ S, P.π q ≤ val j)
        let F₁ := I.filter (fun j => ∑ q ∈ S', P.π q ≤ val j)
        have hi_F₀ : i ∈ F₀ := Finset.mem_filter.mpr ⟨hiI, hval_i.ge⟩
        have hF₁_sub : F₁ ⊆ F₀.erase i := by
          intro j hj
          rcases Finset.mem_filter.mp hj with ⟨hjI, hj_val⟩
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hjI, hw_gt.le.trans hj_val⟩⟩
          intro heq; rw [heq, hval_i] at hj_val; linarith
        have hdrop : Ψ S' + cost i ≤ Ψ S := by
          change (∑ j ∈ F₁, cost j) + cost i ≤ ∑ j ∈ F₀, cost j
          have h1 : ∑ j ∈ F₁, cost j ≤ ∑ j ∈ F₀.erase i, cost j :=
            Finset.sum_le_sum_of_subset hF₁_sub
          have h2 : (∑ j ∈ F₀.erase i, cost j) + cost i = ∑ j ∈ F₀, cost j :=
            Finset.sum_erase_add F₀ cost hi_F₀
          omega
        obtain ⟨v', hv'_full, hv'_len⟩ :=
          ih (Ψ S') (by omega) S' hS'_ne (hS_ge.trans hw_gt.le) rfl
        refine ⟨v' ++ w, ?_, ?_⟩
        · ext q
          simp only [DFA.mem_preimage, DFA.eval_append, Finset.mem_univ, iff_true]
          have hq' : q ∈ A.preimage S' v' := hv'_full ▸ Finset.mem_univ q
          exact (DFA.mem_preimage A S w _).mp ((DFA.mem_preimage A S' v' q).mp hq')
        · rw [List.length_append]; omega
  obtain ⟨v, hv_full, hv_len⟩ := hind (Ψ S₀) S₀ hS₀_ne le_rfl rfl
  refine ⟨v, hv_full, ?_⟩
  convert hv_len using 2

/-- Elementary triangular sum identity `2 * ∑ i ∈ range m, i = m * (m - 1)`. -/
private lemma two_mul_sum_range (m : ℕ) : 2 * (∑ i ∈ Finset.range m, i) = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    cases m with
    | zero => simp
    | succ m =>
      have : (m + 1) * (m + 1 - 1) = (m + 1) * m := rfl
      have : (m + 1 + 1) * (m + 1 + 1 - 1) = (m + 2) * (m + 1) := rfl
      linarith

/-- Elementary sum of `1 + ... + m`: `2 * ∑ i ∈ range m, (i + 1) = m * (m + 1)`. -/
private lemma two_mul_sum_range_succ (m : ℕ) :
    2 * (∑ i ∈ Finset.range m, (i + 1)) = m * (m + 1) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
    mul_add, two_mul_sum_range]
  cases m with
  | zero => simp
  | succ m =>
    have : (m + 1) * (m + 1 - 1) = (m + 1) * m := rfl
    linarith

/-- Exact two-value stationary weight formula `∑ q ∈ S, π q = |S \ X| + |S ∩ X| * α₀`. -/
private lemma twoValue_sum_eq [Fintype Q] [DecidableEq Q]
    (π : Q → ℝ) (X : Finset Q) (α₀ : ℝ)
    (hπ : ∀ q : Q, π q = if q ∈ X then α₀ else 1) (S : Finset Q) :
    ∑ q ∈ S, π q = ((S \ X).card : ℝ) + ((S ∩ X).card : ℝ) * α₀ := by
  have h1 : ∑ q ∈ S, π q = ∑ q ∈ S, if q ∈ X then α₀ else 1 :=
    Finset.sum_congr rfl fun q _ => hπ q
  rw [h1, Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  have hf1 : S.filter (fun q => q ∈ X) = S ∩ X := Finset.filter_mem_eq_inter
  have hf2 : S.filter (fun q => q ∉ X) = S \ X := by
    ext q; simp only [Finset.mem_filter, Finset.mem_sdiff]
  rw [hf1, hf2, add_comm]

private lemma card_sdiff_le_compl [Fintype Q] [DecidableEq Q] (S X : Finset Q) :
    (S \ X).card ≤ Fintype.card Q - X.card := by
  have h1 : (S \ X).card ≤ (Finset.univ \ X).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ S) subset_rfl)
  have h2 : (Finset.univ \ X).card = Fintype.card Q - X.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  omega

/-- Pure-`ℕ` arithmetic closure for the overlap regime (`2 * m ≤ n - 3`) of `Theorem H_two(3)`. -/
private lemma halfInt_overlap_arith (n m L : ℕ) (hn3 : 3 ≤ n) (hm : 1 ≤ m) (hov : 2 * m ≤ n - 3)
    (h1 : 2 * L ≤ 2 * (n - 1) ^ 2 +
      ((2 * m * (n - 1) - 3 * m ^ 2 - m) +
        2 * ((n - 2 * m - 2) * (n - 1)) +
        (4 * m * (n - 1) - 4 * m ^ 2 - 2 * m))) :
    (m = 1 → L < 2 * (n - 1) ^ 2) ∧ 14 * L < 29 * (n - 1) ^ 2 := by
  have h2m_le : 2 * m + 2 ≤ n - 1 := by omega
  have ha : 3 * m ^ 2 ≤ 2 * m * (n - 1) := by nlinarith
  have hab : 3 * m ^ 2 + m ≤ 2 * m * (n - 1) := by nlinarith
  have hb : m ≤ 2 * m * (n - 1) - 3 * m ^ 2 := by omega
  have hc : 4 * m ^ 2 ≤ 4 * m * (n - 1) := by nlinarith
  have hcd : 4 * m ^ 2 + 2 * m ≤ 4 * m * (n - 1) := by nlinarith
  have hd : 2 * m ≤ 4 * m * (n - 1) - 4 * m ^ 2 := by omega
  have h2v_z : 2 * (L : ℤ) ≤
      4 * ((n : ℤ) - 1) ^ 2 - 2 * ((n : ℤ) - 1) + 2 * (m : ℤ) * ((n : ℤ) - 1) -
      7 * (m : ℤ) ^ 2 - 3 * (m : ℤ) := by
    zify [show 1 ≤ n by omega, show 2 * m + 2 ≤ n by omega, show 2 * m ≤ n by omega,
      show 2 ≤ n - 2 * m by omega, ha, hb, hc, hd] at h1
    nlinarith only [h1]
  constructor
  · intro hm1
    subst hm1
    push_cast at h2v_z
    zify [show 1 ≤ n by omega]
    nlinarith only [h2v_z]
  · zify [show 1 ≤ n by omega]
    have hn3_z : (3 : ℤ) ≤ (n : ℤ) := by omega
    have hm1_z : (1 : ℤ) ≤ (m : ℤ) := by omega
    nlinarith only [h2v_z, hn3_z, hm1_z, sq_nonneg (((n : ℤ) - 1) - 7 * (m : ℤ))]

end CoreHelpers

end TwoValueStationary

/-! ### Section 1: Lemma H.3 — Multi-State BFS Entry & Escape Bounds -/

/-- **Lemma H.3(1) (Multi-State BFS Entry Bound)**:
In any strongly connected `n`-state DFA, for any nonempty `X, S ⊆ Q` with `Disjoint S X`,
some word `u` with `1 ≤ u.length ≤ n - |X| - |S| + 1` satisfies `(A.preimage S u ∩ X).Nonempty`. -/
theorem subset_bfs_entry {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} (hSC : A.IsStronglyConnected)
    (X S : Finset Q) (hX_ne : X.Nonempty) (hS_ne : S.Nonempty) (hdisj : Disjoint S X) :
    ∃ u : List α, 1 ≤ u.length ∧ u.length ≤ Fintype.card Q - X.card - S.card + 1 ∧
      (A.preimage S u ∩ X).Nonempty := by
  classical
  let R : ℕ → Finset Q := fun t =>
    Finset.univ.filter (fun y => ∃ x ∈ X, ∃ w : List α, w.length ≤ t ∧ A.eval x w = y)
  have hR0 : R 0 = X := by
    ext y
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, w, hw, rfl⟩
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hw)
      simpa [hw0] using hx
    · intro hy; exact ⟨y, hy, [], le_rfl, rfl⟩
  have hR_mono : ∀ t : ℕ, R t ⊆ R (t + 1) := by
    intro t y hy
    rcases (Finset.mem_filter.mp hy).2 with ⟨x, hx, w, hw, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, w, by omega, rfl⟩
  have hR_eq_univ : ∀ t : ℕ, R t = R (t + 1) → R t = Finset.univ := by
    intro t heq
    have hclosed : ∀ y ∈ R t, ∀ a : α, A.step y a ∈ R t := by
      intro y hy a
      rw [heq]
      rcases (Finset.mem_filter.mp hy).2 with ⟨x, hx, w, hw, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, w ++ [a], by simp; omega,
        by rw [DFA.eval_append, DFA.eval_singleton]⟩
    have heval : ∀ y ∈ R t, ∀ w : List α, A.eval y w ∈ R t := by
      intro y hy w
      induction w generalizing y with
      | nil => exact hy
      | cons a u ih => exact ih (A.step y a) (hclosed y hy a)
    obtain ⟨x₀, hx₀⟩ := hX_ne
    have hx₀R : x₀ ∈ R t := by
      have : X ⊆ R t := by
        intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, [], Nat.zero_le t, rfl⟩
      exact this hx₀
    ext y; simp only [Finset.mem_univ, iff_true]
    obtain ⟨w, rfl⟩ := hSC x₀ y
    exact heval x₀ hx₀R w
  have hex : ∃ t : ℕ, (R t ∩ S).Nonempty := by
    obtain ⟨x₀, hx₀⟩ := hX_ne
    obtain ⟨y₀, hy₀⟩ := hS_ne
    obtain ⟨w, hw⟩ := hSC x₀ y₀
    exact ⟨w.length, y₀, Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, x₀, hx₀, w, le_rfl, hw⟩, hy₀⟩⟩
  let tStar := Nat.find hex
  have ht_spec : (R tStar ∩ S).Nonempty := Nat.find_spec hex
  have ht_min : ∀ t < tStar, ¬ (R t ∩ S).Nonempty := fun t ht => Nat.find_min hex ht
  have ht_pos : 1 ≤ tStar := by
    by_contra h0
    have ht0 : tStar = 0 := by omega
    rw [ht0, hR0] at ht_spec
    rcases ht_spec with ⟨y, hy⟩
    rcases Finset.mem_inter.mp hy with ⟨hyX, hyS⟩
    exact Finset.disjoint_left.mp hdisj hyS hyX
  have hcard_grow : ∀ t ≤ tStar - 1, X.card + t ≤ (R t).card := by
    intro t
    induction t with
    | zero => intro _; rw [hR0]; omega
    | succ t ih =>
      intro ht
      have ih' := ih (by omega)
      have hss : R t ⊂ R (t + 1) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hR_mono t, fun heq => ?_⟩
        have huniv := hR_eq_univ t heq
        have hne_inter : (R t ∩ S).Nonempty := by rw [huniv, Finset.univ_inter]; exact hS_ne
        exact ht_min t (by omega) hne_inter
      have hlt := Finset.card_lt_card hss
      omega
  have hsub_compl : R (tStar - 1) ⊆ Finset.univ \ S := by
    intro y hy
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, fun hyS => ?_⟩
    exact ht_min (tStar - 1) (by omega) ⟨y, Finset.mem_inter.mpr ⟨hy, hyS⟩⟩
  have hcard_ub : (R (tStar - 1)).card ≤ Fintype.card Q - S.card := by
    have := Finset.card_le_card hsub_compl
    rwa [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ] at this
  have hcard_lb := hcard_grow (tStar - 1) le_rfl
  have ht_le : tStar ≤ Fintype.card Q - X.card - S.card + 1 := by omega
  rcases ht_spec with ⟨y, hy⟩
  rcases Finset.mem_inter.mp hy with ⟨hyR, hyS⟩
  rcases (Finset.mem_filter.mp hyR).2 with ⟨x, hxX, u, hu_len, hu_eq⟩
  have hu_pos : 1 ≤ u.length := by
    by_contra h0
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hu0, DFA.eval_nil] at hu_eq
    exact Finset.disjoint_left.mp hdisj (hu_eq ▸ hyS) hxX
  exact ⟨u, hu_pos, by omega, x, Finset.mem_inter.mpr ⟨by simp [DFA.mem_preimage, hu_eq, hyS], hxX⟩⟩

/-- **Lemma H.3(2) (Multi-State BFS Escape Bound)**:
In any strongly connected `n`-state DFA, for any nonempty `X ⊆ S ⊂ Q`,
some word `u` with `1 ≤ u.length ≤ (S \ X).card + 1` satisfies `¬ (X ⊆ A.preimage S u)`. -/
theorem subset_bfs_escape {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} (hSC : A.IsStronglyConnected)
    (X S : Finset Q) (hX_ne : X.Nonempty) (hXS : X ⊆ S) (hS_lt : S.card < Fintype.card Q) :
    ∃ u : List α, 1 ≤ u.length ∧ u.length ≤ (S \ X).card + 1 ∧ ¬ (X ⊆ A.preimage S u) := by
  -- Escape from `S` is literally Entry into `Finset.univ \ S`!
  let T := Finset.univ \ S
  have hT_ne : T.Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
    have := Finset.card_le_card hemp; rw [Finset.card_univ] at this; omega
  have hdisj : Disjoint T X :=
    Finset.disjoint_left.mpr fun q hqT hqX => (Finset.mem_sdiff.mp hqT).2 (hXS hqX)
  obtain ⟨u, hu_pos, hu_len, x, hx⟩ := subset_bfs_entry hSC X T hX_ne hT_ne hdisj
  have hT_card : T.card = Fintype.card Q - S.card := by
    dsimp only [T]; rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  have hSX_card : (S \ X).card = S.card - X.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hXS]
  have hS_le : S.card ≤ Fintype.card Q := Finset.card_le_univ S
  have hX_le : X.card ≤ S.card := Finset.card_le_card hXS
  refine ⟨u, hu_pos, by omega, fun hsub => ?_⟩
  rcases Finset.mem_inter.mp hx with ⟨hxT, hxX⟩
  have h1 : A.eval x u ∈ T := (DFA.mem_preimage A T u x).mp hxT
  have h2 : A.eval x u ∈ S := (DFA.mem_preimage A S u x).mp (hsub hxX)
  exact (Finset.mem_sdiff.mp h1).2 h2

/-! ### Section 2: Theorem H_two — Complete `O(n^2)` Resolution of Goel Open Frontier #1 (`|X| = 2`) -/

/-- **Theorem H_two(1) (Integer `α₀ = m ≥ 1`, `|X| = 2` → `< (3/2)(n - 1)^2`)**:
`2 * w.length ≤ (3 * n - 4) * (n - 1)` and `2 * w.length < 3 * (n - 1) ^ 2`! -/
theorem twoValue_k2_int_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (X : Finset Q) (hX : X.card = 2) (hn3 : 3 ≤ Fintype.card Q)
    (m : ℕ) (hm : 1 ≤ m)
    (hπ : ∀ q : Q, P.π q = if q ∈ X then (m : ℝ) else 1) :
    ∃ w : List α, A.IsSyncWord w ∧
      2 * w.length ≤ (3 * Fintype.card Q - 4) * (Fintype.card Q - 1) ∧
      2 * w.length < 3 * (Fintype.card Q - 1) ^ 2 := by
  classical
  set n := Fintype.card Q
  have hSC : A.IsStronglyConnected := positiveStationary_stronglyConnected hSync P
  obtain ⟨x₁, hx₁X⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  let A_set : Finset ℕ := (Finset.range (n - 1)).image (fun i => m + i)
  let B_set : Finset ℕ := (Finset.range (n - 2)).image (fun r => 2 * m + r)
  let I : Finset ℕ := A_set ∪ (B_set.filter (fun v => n - 2 + m < v))
  let val : ℕ → ℝ := fun v => (v : ℝ)
  let cost : ℕ → ℕ := fun v => if v ≤ n - 2 + m then n - 1 else v - 2 * m + 1
  have hS₀_pi : ∑ q ∈ ({x₁} : Finset Q), P.π q = (m : ℝ) := by simp [hπ x₁, hx₁X]
  obtain ⟨v, hv_full, hv_len⟩ :=
    TwoValueStationary.potential_reach_univ P I val cost {x₁} (Finset.singleton_nonempty x₁) (by
      intro S hS_ne hS_ne_univ hS_ge
      rw [hS₀_pi] at hS_ge
      have hS_lt : S.card < n := by
        simpa [n] using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS_ne_univ)
      set r := (S \ X).card
      set j := (S ∩ X).card
      have hj_le : j ≤ 2 := by rw [← hX]; exact Finset.card_le_card Finset.inter_subset_right
      have hr_le : r ≤ n - 2 := by
        have := TwoValueStationary.card_sdiff_le_compl S X; omega
      have hcard_split : r + j = S.card := by
        have h1 : (S \ X) ∪ (S ∩ X) = S := Finset.sdiff_union_inter S X
        have h2 : Disjoint (S \ X) (S ∩ X) := Finset.disjoint_sdiff_inter S X
        rw [← Finset.card_union_of_disjoint h2, h1]
      have hπS : ∑ q ∈ S, P.π q = ((r + j * m : ℕ) : ℝ) := by
        rw [TwoValueStationary.twoValue_sum_eq P.π X (m : ℝ) hπ S]
        push_cast; ring
      set v_nat := r + j * m
      have hv_ge : m ≤ v_nat := by
        rw [hπS] at hS_ge; exact_mod_cast hS_ge
      by_cases hv_le : v_nat ≤ n - 2 + m
      · have hv_mem : v_nat ∈ I := Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨v_nat - m, Finset.mem_range.mpr (by omega), by omega⟩)
        obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.steinberg_exists_gt hSync P S hS_ne hS_lt
        refine ⟨v_nat, hv_mem, hπS.symm, ?_, w, ?_, hw_gt⟩
        · dsimp only [cost]; simp only [hv_le, ↓reduceIte]; omega
        · dsimp only [cost]; simp only [hv_le, ↓reduceIte]; exact hw_len
      · -- `v_nat > n - 2 + m`: forces `j = 2` and `r ≤ n - 3`, so Lemma H.3(2) escapes in `≤ r + 1`!
        have hj2 : j = 2 := by
          have : r + j * m > n - 2 + m := by omega
          rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with h | h | h
          · rw [h] at this; omega
          · rw [h] at this; omega
          · exact h
        have hr_lt : r ≤ n - 3 := by omega
        have hXS : X ⊆ S := by
          have heq : S ∩ X = X := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
          intro q hq; rw [← heq] at hq; exact (Finset.mem_inter.mp hq).1
        have hv_mem : v_nat ∈ I := Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr (by omega), by dsimp only [v_nat]; rw [hj2]; ring⟩,
            by omega⟩)
        obtain ⟨u, _, hu_len, hu_esc⟩ :=
          subset_bfs_escape hSC X S (Finset.card_pos.mp (by omega)) hXS hS_lt
        have hj'_le : (A.preimage S u ∩ X).card ≤ 1 := by
          have hss : A.preimage S u ∩ X ⊂ X := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, fun heq => ?_⟩
            apply hu_esc; intro q hq; rw [← heq] at hq; exact (Finset.mem_inter.mp hq).1
          have := Finset.card_lt_card hss; omega
        have hr'_le : (A.preimage S u \ X).card ≤ n - 2 := by
          have := TwoValueStationary.card_sdiff_le_compl (A.preimage S u) X; omega
        have hne : ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q := by
          rw [TwoValueStationary.twoValue_sum_eq P.π X (m : ℝ) hπ (A.preimage S u), hπS]
          have hlt_nat : (A.preimage S u \ X).card + (A.preimage S u ∩ X).card * m < v_nat := by
            have h1 : (A.preimage S u ∩ X).card * m ≤ 1 * m := Nat.mul_le_mul_right m hj'_le
            omega
          have hlt_r : (((A.preimage S u \ X).card + (A.preimage S u ∩ X).card * m : ℕ) : ℝ) <
              (v_nat : ℝ) := by exact_mod_cast hlt_nat
          push_cast at hlt_r; linarith
        obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.exists_gt_of_ne P S u hne
        have hcost_eq : cost v_nat = r + 1 := by
          dsimp only [cost]
          simp only [hv_le, ↓reduceIte]
          have : v_nat = 2 * m + r := by dsimp only [v_nat]; rw [hj2]; ring
          omega
        refine ⟨v_nat, hv_mem, hπS.symm, by omega, w, by omega, hw_gt⟩)
  -- Upper bound total sum over `I`
  have hsum_le : ∑ i ∈ I, cost i ≤ (n - 1) ^ 2 + ∑ r ∈ Finset.range (n - 2), (r + 1) := by
    have h1 : ∑ i ∈ I, cost i ≤ (∑ i ∈ A_set, cost i) + ∑ i ∈ B_set.filter (fun v => n - 2 + m < v), cost i := by
      have hu := Finset.sum_union_inter (s₁ := A_set) (s₂ := B_set.filter (fun v => n - 2 + m < v)) (f := cost)
      dsimp only [I]; omega
    have hA : ∑ i ∈ A_set, cost i = (n - 1) ^ 2 := by
      have hinj : Set.InjOn (fun k => m + k) (Finset.range (n - 1) : Set ℕ) :=
        fun _ _ _ _ h => by dsimp only at h; omega
      dsimp only [A_set]
      rw [Finset.sum_image hinj]
      have hcongr : ∑ k ∈ Finset.range (n - 1), cost (m + k) = ∑ _k ∈ Finset.range (n - 1), (n - 1) :=
        Finset.sum_congr rfl fun k hk => by
          have hk_lt := Finset.mem_range.mp hk
          dsimp only [cost]; simp only [show m + k ≤ n - 2 + m by omega, ↓reduceIte]
      rw [hcongr, Finset.sum_const, Finset.card_range, smul_eq_mul, ← sq]
    have hB : ∑ i ∈ B_set.filter (fun v => n - 2 + m < v), cost i ≤
        ∑ r ∈ Finset.range (n - 2), (r + 1) := by
      have hinj : Set.InjOn (fun r => 2 * m + r) (Finset.range (n - 2) : Set ℕ) :=
        fun _ _ _ _ h => by dsimp only at h; omega
      have h2 : ∑ i ∈ B_set.filter (fun v => n - 2 + m < v), cost i ≤
          ∑ i ∈ B_set.filter (fun v => n - 2 + m < v), (i - 2 * m + 1) :=
        Finset.sum_le_sum fun i hi => by
          have hi_gt := (Finset.mem_filter.mp hi).2
          dsimp only [cost]; simp only [show ¬ (i ≤ n - 2 + m) by omega, ↓reduceIte]; exact le_rfl
      have h3 : ∑ i ∈ B_set.filter (fun v => n - 2 + m < v), (i - 2 * m + 1) ≤
          ∑ i ∈ B_set, (i - 2 * m + 1) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have h4 : ∑ i ∈ B_set, (i - 2 * m + 1) = ∑ r ∈ Finset.range (n - 2), (r + 1) := by
        dsimp only [B_set]
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl fun r _ => by omega
      omega
    omega
  have hv_le_tot : v.length ≤ (n - 1) ^ 2 + ∑ r ∈ Finset.range (n - 2), (r + 1) :=
    hv_len.trans ((Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hsum_le)
  have htri : 2 * ∑ r ∈ Finset.range (n - 2), (r + 1) = (n - 2) * (n - 1) := by
    have := TwoValueStationary.two_mul_sum_range_succ (n - 2)
    have hsub : n - 2 + 1 = n - 1 := by omega
    rwa [hsub] at this
  refine ⟨v, ⟨x₁, fun q => by
    have hq : q ∈ A.preimage {x₁} v := hv_full ▸ Finset.mem_univ q
    simpa [DFA.mem_preimage] using hq⟩, ?_, ?_⟩
  · have h2v : 2 * v.length ≤ 2 * (n - 1) ^ 2 + (n - 2) * (n - 1) := by omega
    zify [show 1 ≤ n by omega, show 2 ≤ n by omega, show 4 ≤ 3 * n by omega] at h2v ⊢
    nlinarith only [h2v]
  · have h2v : 2 * v.length ≤ 2 * (n - 1) ^ 2 + (n - 2) * (n - 1) := by omega
    zify [show 1 ≤ n by omega, show 2 ≤ n by omega] at h2v ⊢
    have hn3_z : (3 : ℤ) ≤ (n : ℤ) := by omega
    nlinarith only [h2v, hn3_z]

/-- **Theorem H_two(2) (Non-Half-Integer `α₀ ∉ (1/2)ℤ`, `|X| = 2` → `< 2(n - 1)^2`)**:
Covers ALL irrational `α₀` and ALL rational denominators `≥ 3`:
`w.length ≤ 2 * n ^ 2 - 6 * n + 5` and `w.length < 2 * (n - 1) ^ 2`! -/
theorem twoValue_k2_nonHalfInt_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (X : Finset Q) (hX : X.card = 2) (hn3 : 3 ≤ Fintype.card Q)
    (α₀ : ℝ) (_hα₀_pos : 0 < α₀) (hnotHalf : ∀ z : ℤ, 2 * α₀ ≠ (z : ℝ))
    (hπ : ∀ q : Q, P.π q = if q ∈ X then α₀ else 1) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 2 * Fintype.card Q ^ 2 - 6 * Fintype.card Q + 5 ∧
      w.length < 2 * (Fintype.card Q - 1) ^ 2 := by
  classical
  set n := Fintype.card Q
  have hSC : A.IsStronglyConnected := positiveStationary_stronglyConnected hSync P
  have hα₀_ne1 : α₀ ≠ 1 := fun h => hnotHalf 2 (by rw [h]; norm_num)
  have hnot1 : ∀ z : ℤ, α₀ ≠ (z : ℝ) := fun z h => hnotHalf (2 * z) (by push_cast; linarith)
  let Full : Finset (ℕ × ℕ) := Finset.range (n - 1) ×ˢ Finset.range 3
  let I : Finset (ℕ × ℕ) := (Full.erase (0, 0)).erase (n - 2, 2)
  let val : ℕ × ℕ → ℝ := fun rj => (rj.1 : ℝ) + (rj.2 : ℝ) * α₀
  let cost : ℕ × ℕ → ℕ := fun rj =>
    if rj.2 = 0 then n - 1 - rj.1 else if rj.2 = 2 then rj.1 + 1 else n - 1
  -- Exact sum over `I` equals `(2 * n - 3) * (n - 1)`
  have h00_mem : (0, 0) ∈ Full :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hn22_mem : (n - 2, 2) ∈ Full.erase (0, 0) := by
    refine Finset.mem_erase.mpr ⟨?_,
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩
    intro h; have := congrArg Prod.snd h; norm_num at this
  have hFull_sum : ∑ rj ∈ Full, cost rj = (2 * n - 3) * (n - 1) + (n - 1) + (n - 1) := by
    dsimp only [Full]
    rw [Finset.sum_product]
    have hinner : ∀ r ∈ Finset.range (n - 1),
        ∑ j ∈ Finset.range 3, cost (r, j) = (n - 1 - r) + (n - 1) + (r + 1) := by
      intro r _
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      dsimp only [cost]; simp only [↓reduceIte, OfNat.one_ne_ofNat,
        show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega]
    have hconst : ∑ r ∈ Finset.range (n - 1), ∑ j ∈ Finset.range 3, cost (r, j) =
        ∑ _r ∈ Finset.range (n - 1), (2 * n - 1) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [hinner r hr]
      have hr_lt := Finset.mem_range.mp hr
      omega
    rw [hconst, Finset.sum_const, Finset.card_range, smul_eq_mul]
    zify [show 1 ≤ n by omega, show 3 ≤ 2 * n by omega, show 1 ≤ 2 * n by omega]
    ring
  have hI_sum : ∑ rj ∈ I, cost rj = (2 * n - 3) * (n - 1) := by
    have h1 := Finset.sum_erase_add (Full.erase (0, 0)) cost hn22_mem
    have h2 := Finset.sum_erase_add Full cost h00_mem
    have hc1 : cost (0, 0) = n - 1 := by dsimp only [cost]; simp
    have hc2 : cost (n - 2, 2) = n - 1 := by dsimp only [cost]; simp; omega
    rw [hc2] at h1; rw [hc1, hFull_sum] at h2
    change ∑ rj ∈ (Full.erase (0, 0)).erase (n - 2, 2), cost rj = (2 * n - 3) * (n - 1)
    omega
  -- Common single-step descent verifier for any starting set `S₀`
  have hstep_all : ∀ S : Finset Q, S.Nonempty → S ≠ Finset.univ →
      ∃ rj ∈ I, val rj = ∑ q ∈ S, P.π q ∧ 0 < cost rj ∧
        ∃ w : List α, w.length ≤ cost rj ∧ ∑ q ∈ S, P.π q < ∑ p ∈ A.preimage S w, P.π p := by
    intro S hS_ne hS_ne_univ
    have hS_lt : S.card < n := by
      simpa [n] using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS_ne_univ)
    set r := (S \ X).card
    set j := (S ∩ X).card
    have hj_le : j ≤ 2 := by rw [← hX]; exact Finset.card_le_card Finset.inter_subset_right
    have hr_le : r ≤ n - 2 := by
      have := TwoValueStationary.card_sdiff_le_compl S X; omega
    have hcard_split : r + j = S.card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_sdiff_inter S X), Finset.sdiff_union_inter]
    have hS_pos : 0 < S.card := Finset.card_pos.mpr hS_ne
    have hrj_mem : (r, j) ∈ I := by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩⟩
      · intro h; have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h; omega
      · intro h; have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h; omega
    have hval_eq : val (r, j) = ∑ q ∈ S, P.π q :=
      (TwoValueStationary.twoValue_sum_eq P.π X α₀ hπ S).symm
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with hj0 | hj1 | hj2
    · -- `j = 0`: `Disjoint S X`, Lemma H.3(1) enters `X` in `≤ n - 1 - r`!
      have hdisj : Disjoint S X := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hj0)
      obtain ⟨u, _, hu_len, hu_in⟩ :=
        subset_bfs_entry hSC X S (Finset.card_pos.mp (by omega)) hS_ne hdisj
      have hj'_pos : 1 ≤ (A.preimage S u ∩ X).card := Finset.card_pos.mpr hu_in
      have hj'_le : (A.preimage S u ∩ X).card ≤ 2 := by
        rw [← hX]; exact Finset.card_le_card Finset.inter_subset_right
      have hne : ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q := by
        rw [TwoValueStationary.twoValue_sum_eq P.π X α₀ hπ (A.preimage S u), ← hval_eq]
        dsimp only [val]; rw [hj0, Nat.cast_zero, zero_mul, add_zero]
        intro heq
        rcases (by omega : (A.preimage S u ∩ X).card = 1 ∨ (A.preimage S u ∩ X).card = 2) with h1 | h2
        · rw [h1, Nat.cast_one, one_mul] at heq
          exact hnot1 ((r : ℤ) - ((A.preimage S u \ X).card : ℤ)) (by push_cast; linarith)
        · rw [h2, Nat.cast_ofNat] at heq
          exact hnotHalf ((r : ℤ) - ((A.preimage S u \ X).card : ℤ)) (by push_cast; linarith)
      obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.exists_gt_of_ne P S u hne
      have hcost : cost (r, j) = n - 1 - r := by dsimp only [cost]; simp [hj0]
      have hS_eq_r : S.card = r := by omega
      refine ⟨(r, j), hrj_mem, hval_eq, by omega, w, by omega, hw_gt⟩
    · -- `j = 1`: Steinberg bound `≤ n - 1`
      obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.steinberg_exists_gt hSync P S hS_ne hS_lt
      have hcost : cost (r, j) = n - 1 := by dsimp only [cost]; simp [hj1]
      refine ⟨(r, j), hrj_mem, hval_eq, by omega, w, by omega, hw_gt⟩
    · -- `j = 2`: `X ⊆ S`, Lemma H.3(2) escapes `X` in `≤ r + 1`!
      have hXS : X ⊆ S := by
        have heq : S ∩ X = X := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
        intro q hq; rw [← heq] at hq; exact (Finset.mem_inter.mp hq).1
      obtain ⟨u, _, hu_len, hu_esc⟩ :=
        subset_bfs_escape hSC X S (Finset.card_pos.mp (by omega)) hXS hS_lt
      have hj'_le : (A.preimage S u ∩ X).card ≤ 1 := by
        have hss : A.preimage S u ∩ X ⊂ X := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, fun heq => ?_⟩
          apply hu_esc; intro q hq; rw [← heq] at hq; exact (Finset.mem_inter.mp hq).1
        have := Finset.card_lt_card hss; omega
      have hne : ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q := by
        rw [TwoValueStationary.twoValue_sum_eq P.π X α₀ hπ (A.preimage S u), ← hval_eq]
        dsimp only [val]; rw [hj2, Nat.cast_ofNat]
        intro heq
        rcases (by omega : (A.preimage S u ∩ X).card = 0 ∨ (A.preimage S u ∩ X).card = 1) with h0 | h1
        · rw [h0, Nat.cast_zero, zero_mul, add_zero] at heq
          exact hnotHalf (((A.preimage S u \ X).card : ℤ) - (r : ℤ)) (by push_cast; linarith)
        · rw [h1, Nat.cast_one, one_mul] at heq
          exact hnot1 (((A.preimage S u \ X).card : ℤ) - (r : ℤ)) (by push_cast; linarith)
      obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.exists_gt_of_ne P S u hne
      have hcost : cost (r, j) = r + 1 := by dsimp only [cost]; simp [hj2]
      refine ⟨(r, j), hrj_mem, hval_eq, by omega, w, by omega, hw_gt⟩
  -- Pick starting singleton omitting `(1, 0)` (cost `n - 2`) if `1 < α₀`, or `(0, 1)` (cost `n - 1`) if `α₀ < 1`
  have h6n : 6 * n ≤ 2 * n ^ 2 := by nlinarith
  rcases lt_or_gt_of_ne hα₀_ne1 with hlt1 | hgt1
  · have hex_y : ∃ y₀ : Q, y₀ ∉ X := by
      by_contra hall; push Not at hall
      have := Finset.card_le_card (show (Finset.univ : Finset Q) ⊆ X from fun y _ => hall y)
      rw [Finset.card_univ] at this; omega
    obtain ⟨y₀, hy₀⟩ := hex_y
    obtain ⟨v, hv_full, hv_len⟩ :=
      TwoValueStationary.potential_reach_univ P I val cost {y₀} (Finset.singleton_nonempty y₀)
        (fun S h1 h2 _ => hstep_all S h1 h2)
    have h01_mem : (0, 1) ∈ I := by
      refine Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.snd h; norm_num at this,
        Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.snd h; norm_num at this,
          Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩⟩
    have hsub : I.filter (fun i => ∑ q ∈ ({y₀} : Finset Q), P.π q ≤ val i) ⊆ I.erase (0, 1) := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hiI, hival⟩
      refine Finset.mem_erase.mpr ⟨?_, hiI⟩
      intro heq; rw [heq] at hival
      simp only [Finset.sum_singleton, hπ y₀, hy₀, ↓reduceIte, val, Nat.cast_zero, Nat.cast_one,
        zero_add, one_mul] at hival
      linarith
    have hv_ub : v.length + (n - 1) ≤ (2 * n - 3) * (n - 1) := by
      have h1 := Finset.sum_le_sum_of_subset hsub (f := cost)
      have h2 := Finset.sum_erase_add I cost h01_mem
      have hc : cost (0, 1) = n - 1 := by dsimp only [cost]; simp
      rw [hc, hI_sum] at h2
      have hv_len' : v.length ≤ ∑ i ∈ I.filter (fun i => ∑ q ∈ ({y₀} : Finset Q), P.π q ≤ val i), cost i := by
        convert hv_len using 2
      omega
    refine ⟨v, ⟨y₀, fun q => by
      have hq : q ∈ A.preimage {y₀} v := hv_full ▸ Finset.mem_univ q
      simpa [DFA.mem_preimage] using hq⟩, ?_, ?_⟩
    · zify [show 1 ≤ n by omega, show 3 ≤ 2 * n by omega, h6n] at hv_ub ⊢; nlinarith only [hv_ub]
    · zify [show 1 ≤ n by omega, show 3 ≤ 2 * n by omega] at hv_ub ⊢
      have hn3_z : (3 : ℤ) ≤ (n : ℤ) := by omega
      nlinarith only [hv_ub, hn3_z]
  · obtain ⟨x₁, hx₁X⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
    obtain ⟨v, hv_full, hv_len⟩ :=
      TwoValueStationary.potential_reach_univ P I val cost {x₁} (Finset.singleton_nonempty x₁)
        (fun S h1 h2 _ => hstep_all S h1 h2)
    have h10_mem : (1, 0) ∈ I := by
      refine Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.snd h; norm_num at this,
        Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.fst h; norm_num at this,
          Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩⟩
    have hsub : I.filter (fun i => ∑ q ∈ ({x₁} : Finset Q), P.π q ≤ val i) ⊆ I.erase (1, 0) := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hiI, hival⟩
      refine Finset.mem_erase.mpr ⟨?_, hiI⟩
      intro heq; rw [heq] at hival
      simp only [Finset.sum_singleton, hπ x₁, hx₁X, ↓reduceIte, val, Nat.cast_one, Nat.cast_zero,
        zero_mul, add_zero] at hival
      linarith
    have hv_ub : v.length + (n - 2) ≤ (2 * n - 3) * (n - 1) := by
      have h1 := Finset.sum_le_sum_of_subset hsub (f := cost)
      have h2 := Finset.sum_erase_add I cost h10_mem
      have hc : cost (1, 0) = n - 2 := by dsimp only [cost]; simp; omega
      rw [hc, hI_sum] at h2
      have hv_len' : v.length ≤ ∑ i ∈ I.filter (fun i => ∑ q ∈ ({x₁} : Finset Q), P.π q ≤ val i), cost i := by
        convert hv_len using 2
      omega
    refine ⟨v, ⟨x₁, fun q => by
      have hq : q ∈ A.preimage {x₁} v := hv_full ▸ Finset.mem_univ q
      simpa [DFA.mem_preimage] using hq⟩, ?_, ?_⟩
    · zify [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ 2 * n by omega, h6n] at hv_ub ⊢
      nlinarith only [hv_ub]
    · zify [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ 2 * n by omega] at hv_ub ⊢
      have hn3_z : (3 : ℤ) ≤ (n : ℤ) := by omega
      nlinarith only [hv_ub, hn3_z]

/-- Helper for **Theorem H_two(3)** (`α₀ = m + 1/2`, `m ≥ 1`):
exact unified potential bound yielding `< 2(n - 1)^2` at `m = 1` AND `14 * w.length < 29 * (n - 1)^2`
for ALL `m ≥ 1`! -/
private lemma twoValue_k2_halfInt_pos_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (X : Finset Q) (hX : X.card = 2) (hn3 : 3 ≤ Fintype.card Q)
    (m : ℕ) (hm : 1 ≤ m)
    (hπ : ∀ q : Q, P.π q = if q ∈ X then (m : ℝ) + 1 / 2 else 1) :
    ∃ w : List α, A.IsSyncWord w ∧
      (m = 1 → w.length < 2 * (Fintype.card Q - 1) ^ 2) ∧
      14 * w.length < 29 * (Fintype.card Q - 1) ^ 2 := by
  classical
  set n := Fintype.card Q
  have hSC : A.IsStronglyConnected := positiveStationary_stronglyConnected hSync P
  obtain ⟨x₁, hx₁X⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  -- Index `ℕ ⊕ ℕ`: left = half-integers `r + m + 1/2`, right = achievable integers `v ∈ [m+1, n+2m-2]`
  -- omitting the unachievable gap `[n - 1, 2 * m]` when `2 * m ≥ n - 2`.
  let I_half : Finset (ℕ ⊕ ℕ) := (Finset.range (n - 1)).image Sum.inl
  let I_int_all : Finset (ℕ ⊕ ℕ) := (Finset.range (n + m - 2)).image (fun i => Sum.inr (m + 1 + i))
  let I_int : Finset (ℕ ⊕ ℕ) :=
    I_int_all.filter (fun x => match x with | Sum.inr v => v ≤ n - 2 ∨ 2 * m + 1 ≤ v | _ => False)
  let I : Finset (ℕ ⊕ ℕ) := I_half ∪ I_int
  let val : ℕ ⊕ ℕ → ℝ
    | Sum.inl r => (r : ℝ) + (m : ℝ) + 1 / 2
    | Sum.inr v => (v : ℝ)
  let cost : ℕ ⊕ ℕ → ℕ
    | Sum.inl _ => n - 1
    | Sum.inr v =>
      if v ≤ min (n - 2) (2 * m) then n - 1 - v
      else if max (n - 1) (2 * m + 1) ≤ v then v - 2 * m
      else n - 1
  have hS₀_pi : ∑ q ∈ ({x₁} : Finset Q), P.π q = (m : ℝ) + 1 / 2 := by simp [hπ x₁, hx₁X]
  obtain ⟨v, hv_full, hv_len⟩ :=
    TwoValueStationary.potential_reach_univ P I val cost {x₁} (Finset.singleton_nonempty x₁) (by
      intro S hS_ne hS_ne_univ hS_ge
      rw [hS₀_pi] at hS_ge
      have hS_lt : S.card < n := by
        simpa [n] using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS_ne_univ)
      set r := (S \ X).card
      set j := (S ∩ X).card
      have hj_le : j ≤ 2 := by rw [← hX]; exact Finset.card_le_card Finset.inter_subset_right
      have hr_le : r ≤ n - 2 := by
        have := TwoValueStationary.card_sdiff_le_compl S X; omega
      have hcard_split : r + j = S.card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_sdiff_inter S X), Finset.sdiff_union_inter]
      have hπS : ∑ q ∈ S, P.π q = (r : ℝ) + (j : ℝ) * ((m : ℝ) + 1 / 2) :=
        TwoValueStationary.twoValue_sum_eq P.π X ((m : ℝ) + 1 / 2) hπ S
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with hj0 | hj1 | hj2
      · -- `j = 0`: `π(S) = r ∈ [m + 1, n - 2]`
        have hπS' : ∑ q ∈ S, P.π q = (r : ℝ) := by rw [hπS, hj0]; ring
        have hr_ge : m + 1 ≤ r := by
          have : (m : ℝ) + 1 / 2 ≤ (r : ℝ) := by linarith
          have hlt : (m : ℝ) < (r : ℝ) := by linarith
          have : m < r := by exact_mod_cast hlt
          omega
        have hr_mem : Sum.inr r ∈ I := Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
            ⟨r - (m + 1), Finset.mem_range.mpr (by omega), by congr 1; omega⟩, Or.inl hr_le⟩)
        by_cases hlow : r ≤ min (n - 2) (2 * m)
        · have hdisj : Disjoint S X := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hj0)
          obtain ⟨u, _, hu_len, hu_in⟩ :=
            subset_bfs_entry hSC X S (Finset.card_pos.mp (by omega)) hS_ne hdisj
          have hj'_pos : 1 ≤ (A.preimage S u ∩ X).card := Finset.card_pos.mpr hu_in
          have hj'_le : (A.preimage S u ∩ X).card ≤ 2 := by
            rw [← hX]; exact Finset.card_le_card Finset.inter_subset_right
          have hne : ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q := by
            rw [TwoValueStationary.twoValue_sum_eq P.π X ((m : ℝ) + 1 / 2) hπ (A.preimage S u), hπS']
            intro heq
            rcases (by omega : (A.preimage S u ∩ X).card = 1 ∨ (A.preimage S u ∩ X).card = 2) with h1 | h2
            · rw [h1, Nat.cast_one, one_mul] at heq
              have h2int : ((2 * ((A.preimage S u \ X).card + m) + 1 : ℕ) : ℝ) = ((2 * r : ℕ) : ℝ) := by
                push_cast; linarith
              have h2nat : 2 * ((A.preimage S u \ X).card + m) + 1 = 2 * r := by exact_mod_cast h2int
              omega
            · rw [h2, Nat.cast_ofNat] at heq
              have h2m1 : (2 * m + 1 : ℕ) ≤ r := by
                have hle_r : ((2 * m + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
                  have hnn : (0 : ℝ) ≤ ((A.preimage S u \ X).card : ℝ) := Nat.cast_nonneg _
                  push_cast; linarith
                exact_mod_cast hle_r
              have : r ≤ 2 * m := le_trans hlow (min_le_right _ _)
              omega
          obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.exists_gt_of_ne P S u hne
          have hcost : cost (Sum.inr r) = n - 1 - r := by dsimp only [cost]; simp only [hlow, ↓reduceIte]
          have hS_eq_r : S.card = r := by omega
          refine ⟨Sum.inr r, hr_mem, hπS'.symm, by omega, w, by omega, hw_gt⟩
        · obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.steinberg_exists_gt hSync P S hS_ne hS_lt
          have hnot_high : ¬ (max (n - 1) (2 * m + 1) ≤ r) := by
            have := le_max_left (n - 1) (2 * m + 1); omega
          have hcost : cost (Sum.inr r) = n - 1 := by
            dsimp only [cost]; simp only [hlow, hnot_high, ↓reduceIte]
          refine ⟨Sum.inr r, hr_mem, hπS'.symm, by omega, w, by omega, hw_gt⟩
      · -- `j = 1`: half-integer `r + m + 1/2` (`r ≤ n - 2`), Steinberg cost `n - 1`
        have hπS' : ∑ q ∈ S, P.π q = (r : ℝ) + (m : ℝ) + 1 / 2 := by rw [hπS, hj1]; ring
        have hr_mem : Sum.inl r ∈ I := Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr (by omega), rfl⟩)
        obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.steinberg_exists_gt hSync P S hS_ne hS_lt
        refine ⟨Sum.inl r, hr_mem, hπS'.symm, by dsimp only [cost]; omega, w, hw_len, hw_gt⟩
      · -- `j = 2`: integer `v_nat = r + 2*m + 1 ∈ [2*m + 1, n + 2*m - 2]`
        set v_nat := r + 2 * m + 1
        have hπS' : ∑ q ∈ S, P.π q = (v_nat : ℝ) := by
          rw [hπS, hj2]; dsimp only [v_nat]; push_cast; ring
        have hr_lt : r ≤ n - 3 := by omega
        have hv_mem : Sum.inr v_nat ∈ I := Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
            ⟨v_nat - (m + 1), Finset.mem_range.mpr (by omega), by congr 1; omega⟩, Or.inr (by omega)⟩)
        have hnot_low : ¬ (v_nat ≤ min (n - 2) (2 * m)) := by
          have := min_le_right (n - 2) (2 * m); omega
        by_cases hhigh : max (n - 1) (2 * m + 1) ≤ v_nat
        · have hXS : X ⊆ S := by
            have heq : S ∩ X = X := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
            intro q hq; rw [← heq] at hq; exact (Finset.mem_inter.mp hq).1
          obtain ⟨u, _, hu_len, hu_esc⟩ :=
            subset_bfs_escape hSC X S (Finset.card_pos.mp (by omega)) hXS hS_lt
          have hj'_le : (A.preimage S u ∩ X).card ≤ 1 := by
            have hss : A.preimage S u ∩ X ⊂ X := by
              refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, fun heq => ?_⟩
              apply hu_esc; intro q hq; rw [← heq] at hq; exact (Finset.mem_inter.mp hq).1
            have := Finset.card_lt_card hss; omega
          have hr'_le : (A.preimage S u \ X).card ≤ n - 2 := by
            have := TwoValueStationary.card_sdiff_le_compl (A.preimage S u) X; omega
          have hne : ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q := by
            rw [TwoValueStationary.twoValue_sum_eq P.π X ((m : ℝ) + 1 / 2) hπ (A.preimage S u), hπS']
            intro heq
            rcases (by omega : (A.preimage S u ∩ X).card = 0 ∨ (A.preimage S u ∩ X).card = 1) with h0 | h1
            · rw [h0, Nat.cast_zero, zero_mul, add_zero] at heq
              have hnat : (A.preimage S u \ X).card = v_nat := by exact_mod_cast heq
              have : n - 1 ≤ v_nat := le_trans (le_max_left _ _) hhigh
              omega
            · rw [h1, Nat.cast_one, one_mul] at heq
              have h2int : ((2 * ((A.preimage S u \ X).card + m) + 1 : ℕ) : ℝ) = ((2 * v_nat : ℕ) : ℝ) := by
                push_cast; linarith
              have h2nat : 2 * ((A.preimage S u \ X).card + m) + 1 = 2 * v_nat := by exact_mod_cast h2int
              omega
          obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.exists_gt_of_ne P S u hne
          have hcost : cost (Sum.inr v_nat) = r + 1 := by
            dsimp only [cost]; simp only [hnot_low, hhigh, ↓reduceIte]; omega
          refine ⟨Sum.inr v_nat, hv_mem, hπS'.symm, by omega, w, by omega, hw_gt⟩
        · obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.steinberg_exists_gt hSync P S hS_ne hS_lt
          have hcost : cost (Sum.inr v_nat) = n - 1 := by
            dsimp only [cost]; simp only [hnot_low, hhigh, ↓reduceIte]
          refine ⟨Sum.inr v_nat, hv_mem, hπS'.symm, by omega, w, by omega, hw_gt⟩)
  -- Compute exact upper bound on `∑ i ∈ I, cost i`
  have hsum_half : ∑ i ∈ I_half, cost i = (n - 1) ^ 2 := by
    dsimp only [I_half]
    rw [Finset.sum_image (fun _ _ _ _ h => Sum.inl.inj h)]
    simp only [cost, Finset.sum_const, Finset.card_range, smul_eq_mul, ← sq]
  have hv_le_int : v.length ≤ (n - 1) ^ 2 + ∑ x ∈ I_int, cost x := by
    have h1 : v.length ≤ ∑ x ∈ I, cost x :=
      hv_len.trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    have h2 := Finset.sum_union_inter (s₁ := I_half) (s₂ := I_int) (f := cost)
    dsimp only [I] at h1
    omega
  refine ⟨v, ⟨x₁, fun q => by
    have hq : q ∈ A.preimage {x₁} v := hv_full ▸ Finset.mem_univ q
    simpa [DFA.mem_preimage] using hq⟩, ?_⟩
  by_cases hov : 2 * m ≤ n - 3
  · -- **Overlap present (`2 * m ≤ n - 3`)**: bound `I_int ⊆ I_int_all` and split into 3 intervals `[0, m)`, `[m, n - m - 2)`, `[n - m - 2, n + m - 2)`!
    have h2m_le : 2 * m + 2 ≤ n - 1 := by omega
    have hv_le_sum : v.length ≤ (n - 1) ^ 2 + ∑ i ∈ Finset.range (n + m - 2), cost (Sum.inr (m + 1 + i)) := by
      have hsub : ∑ x ∈ I_int, cost x ≤ ∑ x ∈ I_int_all, cost x :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have h3 : ∑ x ∈ I_int_all, cost x = ∑ i ∈ Finset.range (n + m - 2), cost (Sum.inr (m + 1 + i)) := by
        dsimp only [I_int_all]
        rw [Finset.sum_image (fun _ _ _ _ h => by have := Sum.inr.inj h; omega)]
      omega
    have hsplit_len : n + m - 2 = m + (n - 2 * m - 2) + 2 * m := by omega
    have hsum_int :
        2 * (∑ i ∈ Finset.range (n + m - 2), cost (Sum.inr (m + 1 + i))) =
          (2 * m * (n - 1) - 3 * m ^ 2 - m) +
          2 * ((n - 2 * m - 2) * (n - 1)) +
          (4 * m * (n - 1) - 4 * m ^ 2 - 2 * m) := by
      rw [hsplit_len, Finset.sum_range_add, Finset.sum_range_add]
      have hpart1 : 2 * (∑ i ∈ Finset.range m, cost (Sum.inr (m + 1 + i))) =
          2 * m * (n - 1) - 3 * m ^ 2 - m := by
        have hcongr : ∑ i ∈ Finset.range m, cost (Sum.inr (m + 1 + i)) =
            ∑ i ∈ Finset.range m, (n - 1 - (m + 1 + i)) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi_lt := Finset.mem_range.mp hi
          dsimp only [cost]
          simp only [show m + 1 + i ≤ min (n - 2) (2 * m) by omega, ↓reduceIte]
        rw [hcongr]
        have hadd : (∑ i ∈ Finset.range m, (n - 1 - (m + 1 + i))) +
            (∑ i ∈ Finset.range m, (m + 1 + i)) = m * (n - 1) := by
          rw [← Finset.sum_add_distrib]
          have hc : ∑ i ∈ Finset.range m, ((n - 1 - (m + 1 + i)) + (m + 1 + i)) =
              ∑ _i ∈ Finset.range m, (n - 1) :=
            Finset.sum_congr rfl fun i hi => by have := Finset.mem_range.mp hi; omega
          rw [hc, Finset.sum_const, Finset.card_range, smul_eq_mul]
        have hsub_sum : 2 * (∑ i ∈ Finset.range m, (m + 1 + i)) = 3 * m ^ 2 + m := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
            mul_add, TwoValueStationary.two_mul_sum_range]
          zify [hm]; ring
        have ha : 3 * m ^ 2 ≤ 2 * m * (n - 1) := by nlinarith
        have hab : 3 * m ^ 2 + m ≤ 2 * m * (n - 1) := by nlinarith
        have hb : m ≤ 2 * m * (n - 1) - 3 * m ^ 2 := by omega
        zify [show 1 ≤ n by omega, ha, hb] at hadd hsub_sum ⊢
        linarith
      have hpart2 : ∑ i ∈ Finset.range (n - 2 * m - 2), cost (Sum.inr (m + 1 + (m + i))) =
          (n - 2 * m - 2) * (n - 1) := by
        have hcongr : ∑ i ∈ Finset.range (n - 2 * m - 2), cost (Sum.inr (m + 1 + (m + i))) =
            ∑ _i ∈ Finset.range (n - 2 * m - 2), (n - 1) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi_lt := Finset.mem_range.mp hi
          dsimp only [cost]
          have h1 : ¬ (m + 1 + (m + i) ≤ min (n - 2) (2 * m)) := by
            have := min_le_right (n - 2) (2 * m); omega
          have h2 : ¬ (max (n - 1) (2 * m + 1) ≤ m + 1 + (m + i)) := by
            have := le_max_left (n - 1) (2 * m + 1); omega
          simp only [h1, h2, ↓reduceIte]
        rw [hcongr, Finset.sum_const, Finset.card_range, smul_eq_mul]
      have hpart3 : 2 * (∑ i ∈ Finset.range (2 * m), cost (Sum.inr (m + 1 + (m + (n - 2 * m - 2) + i)))) =
          4 * m * (n - 1) - 4 * m ^ 2 - 2 * m := by
        have hcongr : ∑ i ∈ Finset.range (2 * m), cost (Sum.inr (m + 1 + (m + (n - 2 * m - 2) + i))) =
            ∑ i ∈ Finset.range (2 * m), ((n - 1 - 2 * m) + i) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi_lt := Finset.mem_range.mp hi
          dsimp only [cost]
          have h1 : ¬ (m + 1 + (m + (n - 2 * m - 2) + i) ≤ min (n - 2) (2 * m)) := by
            have := min_le_right (n - 2) (2 * m); omega
          have h2 : max (n - 1) (2 * m + 1) ≤ m + 1 + (m + (n - 2 * m - 2) + i) := by omega
          simp only [h1, h2, ↓reduceIte]; omega
        rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
          mul_add, TwoValueStationary.two_mul_sum_range]
        have hle1 : 2 * m ≤ n - 1 := by omega
        have hc : 4 * m ^ 2 ≤ 4 * m * (n - 1) := by nlinarith
        have hcd : 4 * m ^ 2 + 2 * m ≤ 4 * m * (n - 1) := by nlinarith
        have hd : 2 * m ≤ 4 * m * (n - 1) - 4 * m ^ 2 := by omega
        zify [show 1 ≤ n by omega, hle1, show 1 ≤ 2 * m by omega, hc, hd]
        ring
      omega
    have h1 : 2 * v.length ≤ 2 * (n - 1) ^ 2 +
        ((2 * m * (n - 1) - 3 * m ^ 2 - m) +
          2 * ((n - 2 * m - 2) * (n - 1)) +
          (4 * m * (n - 1) - 4 * m ^ 2 - 2 * m)) := by omega
    exact TwoValueStationary.halfInt_overlap_arith n m v.length hn3 hm hov h1
  · -- **No overlap (`n - 2 ≤ 2 * m`)**: `I_int ⊆ I_lo ∪ I_hi`, each summing to `(n - 2) * (n - 1) / 2`!
    let I_lo : Finset (ℕ ⊕ ℕ) := (Finset.range (n - 2)).image (fun i => Sum.inr (i + 1))
    let I_hi : Finset (ℕ ⊕ ℕ) := (Finset.range (n - 2)).image (fun r => Sum.inr (2 * m + 1 + r))
    have hsub_union : I_int ⊆ I_lo ∪ I_hi := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxAll, hcond⟩
      rcases Finset.mem_image.mp hxAll with ⟨i, hi, rfl⟩
      have hi_lt := Finset.mem_range.mp hi
      rcases hcond with hlo | hhi
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨m + i, Finset.mem_range.mpr (by omega), by congr 1; omega⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨i - m, Finset.mem_range.mpr (by omega), by congr 1; omega⟩)
    have hsum_lo : 2 * (∑ x ∈ I_lo, cost x) = (n - 2) * (n - 1) := by
      dsimp only [I_lo]
      rw [Finset.sum_image (fun _ _ _ _ h => by have := Sum.inr.inj h; omega)]
      have hcongr : ∑ i ∈ Finset.range (n - 2), cost (Sum.inr (i + 1)) =
          ∑ i ∈ Finset.range (n - 2), (n - 2 - i) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi_lt := Finset.mem_range.mp hi
        dsimp only [cost]
        have h1 : i + 1 ≤ min (n - 2) (2 * m) := by omega
        simp only [h1, ↓reduceIte]; omega
      rw [hcongr]
      have hadd : (∑ i ∈ Finset.range (n - 2), (n - 2 - i)) +
          (∑ i ∈ Finset.range (n - 2), i) = (n - 2) * (n - 2) := by
        rw [← Finset.sum_add_distrib]
        have hc : ∑ i ∈ Finset.range (n - 2), ((n - 2 - i) + i) =
            ∑ _i ∈ Finset.range (n - 2), (n - 2) :=
          Finset.sum_congr rfl fun i hi => by have := Finset.mem_range.mp hi; omega
        rw [hc, Finset.sum_const, Finset.card_range, smul_eq_mul]
      have htri := TwoValueStationary.two_mul_sum_range (n - 2)
      zify [show 1 ≤ n by omega, show 2 ≤ n by omega, show 1 ≤ n - 2 by omega] at hadd htri ⊢
      nlinarith only [hadd, htri]
    have hsum_hi : 2 * (∑ x ∈ I_hi, cost x) = (n - 2) * (n - 1) := by
      dsimp only [I_hi]
      rw [Finset.sum_image (fun _ _ _ _ h => by have := Sum.inr.inj h; omega)]
      have hcongr : ∑ r ∈ Finset.range (n - 2), cost (Sum.inr (2 * m + 1 + r)) =
          ∑ r ∈ Finset.range (n - 2), (r + 1) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        dsimp only [cost]
        have h1 : ¬ (2 * m + 1 + r ≤ min (n - 2) (2 * m)) := by
          have := min_le_right (n - 2) (2 * m); omega
        have h2 : max (n - 1) (2 * m + 1) ≤ 2 * m + 1 + r := by omega
        simp only [h1, h2, ↓reduceIte]; omega
      rw [hcongr, TwoValueStationary.two_mul_sum_range_succ]
      congr 1; omega
    have hsum_int_le : ∑ x ∈ I_int, cost x ≤ (n - 2) * (n - 1) := by
      have h1 : ∑ x ∈ I_int, cost x ≤ ∑ x ∈ I_lo ∪ I_hi, cost x :=
        Finset.sum_le_sum_of_subset hsub_union
      have h2 := Finset.sum_union_inter (s₁ := I_lo) (s₂ := I_hi) (f := cost)
      omega
    have hv_lt2 : v.length < 2 * (n - 1) ^ 2 := by
      have hv_bound : v.length ≤ (n - 1) ^ 2 + (n - 2) * (n - 1) := by omega
      zify [show 1 ≤ n by omega, show 2 ≤ n by omega] at hv_bound ⊢
      have hn3_z : (3 : ℤ) ≤ (n : ℤ) := by omega
      nlinarith only [hv_bound, hn3_z]
    exact ⟨fun _ => hv_lt2, by
      have hsq : 1 ≤ (n - 1) ^ 2 := by nlinarith
      omega⟩

/-- **Theorem H_two(3b) (`α₀ = 3/2`, `|X| = 2` → `< 2(n - 1)^2`)**:
Exact `2(n - 1)^2` barrier beat for `α₀ = 3/2`! -/
theorem twoValue_k2_threeHalves_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (X : Finset Q) (hX : X.card = 2) (hn3 : 3 ≤ Fintype.card Q)
    (hπ : ∀ q : Q, P.π q = if q ∈ X then (3 : ℝ) / 2 else 1) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length < 2 * (Fintype.card Q - 1) ^ 2 := by
  have hπ' : ∀ q : Q, P.π q = if q ∈ X then ((1 : ℕ) : ℝ) + 1 / 2 else 1 := by
    intro q; rw [hπ q]; split_ifs <;> norm_num
  obtain ⟨w, hw_sync, hw_m1, _⟩ := twoValue_k2_halfInt_pos_bound A hSync P X hX hn3 1 le_rfl hπ'
  exact ⟨w, hw_sync, hw_m1 rfl⟩

/-- **Theorem H_two(4) (Universal Unconditional `< (29/14)(n - 1)^2` for ALL `α₀ ∈ ℝ_{>0}`, `|X| = 2`)**:
Resolves Goel's Open Frontier #1 completely: for EVERY synchronizing DFA on `n ≥ 3` states with
positive stationary vector `π = 1` outside a 2-state set `X` and `π = α₀ > 0` on `X`
(arbitrary rational OR irrational `α₀ > 0`), `14 * rt(A) < 29 * (n - 1)^2`! -/
theorem twoValue_k2_universal_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (X : Finset Q) (hX : X.card = 2) (hn3 : 3 ≤ Fintype.card Q)
    (α₀ : ℝ) (hα₀_pos : 0 < α₀)
    (hπ : ∀ q : Q, P.π q = if q ∈ X then α₀ else 1) :
    ∃ w : List α, A.IsSyncWord w ∧ 14 * w.length < 29 * (Fintype.card Q - 1) ^ 2 := by
  have hn1 : 2 ≤ Fintype.card Q - 1 := by omega
  have hsq_pos : 1 ≤ (Fintype.card Q - 1) ^ 2 := by nlinarith
  by_cases hhalf : ∃ z : ℤ, 2 * α₀ = (z : ℝ)
  · rcases hhalf with ⟨z, hz⟩
    have hz_pos : (0 : ℤ) < z := by
      have : (0 : ℝ) < (z : ℝ) := by linarith
      exact_mod_cast this
    let k : ℕ := z.toNat
    have hk_pos : 1 ≤ k := by omega
    have hk_eq : (k : ℝ) = 2 * α₀ := by
      have hzk : (k : ℤ) = z := Int.toNat_of_nonneg (by omega)
      have : ((k : ℤ) : ℝ) = (z : ℝ) := by exact_mod_cast hzk
      simpa using this.trans hz.symm
    by_cases heven : k % 2 = 0
    · let m : ℕ := k / 2
      have hm_pos : 1 ≤ m := by omega
      have hα_m : α₀ = (m : ℝ) := by
        have hkm : k = 2 * m := by omega
        have hkm_r : (k : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hkm
        linarith
      have hπ' : ∀ q : Q, P.π q = if q ∈ X then (m : ℝ) else 1 := by
        intro q; rw [hπ q, hα_m]
      obtain ⟨w, hw_sync, _, hw_lt⟩ := twoValue_k2_int_bound A hSync P X hX hn3 m hm_pos hπ'
      exact ⟨w, hw_sync, by omega⟩
    · by_cases hk1 : k = 1
      · have hα_half : α₀ = (1 : ℝ) / 2 := by
          rw [hk1, Nat.cast_one] at hk_eq; linarith
        have hπ' : ∀ q : Q, P.π q = if q ∈ X then (1 : ℝ) / 2 else 1 := by
          intro q; rw [hπ q, hα_half]
        obtain ⟨w, hw_sync, _, hw_lt⟩ :=
          multiException_half_bound A hSync P X (by omega) (by omega) hπ'
        exact ⟨w, hw_sync, by omega⟩
      · let m : ℕ := k / 2
        have hm_pos : 1 ≤ m := by omega
        have hα_hm : α₀ = (m : ℝ) + 1 / 2 := by
          have hkm : k = 2 * m + 1 := by omega
          have hkm_r : (k : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hkm
          linarith
        have hπ' : ∀ q : Q, P.π q = if q ∈ X then (m : ℝ) + 1 / 2 else 1 := by
          intro q; rw [hπ q, hα_hm]
        obtain ⟨w, hw_sync, _, hw_lt⟩ := twoValue_k2_halfInt_pos_bound A hSync P X hX hn3 m hm_pos hπ'
        exact ⟨w, hw_sync, hw_lt⟩
  · obtain ⟨w, hw_sync, _, hw_lt⟩ :=
      twoValue_k2_nonHalfInt_bound A hSync P X hX hn3 α₀ hα₀_pos (fun z hz => hhalf ⟨z, hz⟩) hπ
    exact ⟨w, hw_sync, by omega⟩

/-! ### Section 3: Theorem H_real_k — General `k`-Exception Two-Value Stationary Vectors over `ℝ_{>0}` -/

/-- **Theorem H_real_k(1) (General `k`-Exception Two-Value Stationary Bound over ALL `ℝ_{>0}`)**:
For ANY synchronizing `n`-state DFA (`n ≥ 2`) with positive stationary vector `π = α₀ > 0` on `X`
(`1 ≤ k := |X| < n`) and `π = 1` outside `X`, setting `k' := min k (n - k)`:
`rt(A) ≤ ((k' + 1) * (n - k' + 1) - 3) * (n - 1)` — completely independent of rationality or
denominators, exponentially beating Berlinkov (2013)'s `2^k (n - k + 1)(n - 1)`! -/
theorem twoValue_general_k_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (X : Finset Q) (hX_pos : 1 ≤ X.card) (hX_lt : X.card < Fintype.card Q)
    (α₀ : ℝ) (_hα₀_pos : 0 < α₀)
    (hπ : ∀ q : Q, P.π q = if q ∈ X then α₀ else 1) :
    ∃ w : List α, A.IsSyncWord w ∧
      let k' := min X.card (Fintype.card Q - X.card)
      w.length ≤ ((k' + 1) * (Fintype.card Q - k' + 1) - 3) * (Fintype.card Q - 1) := by
  classical
  set n := Fintype.card Q
  set k := X.card
  set k' := min k (n - k)
  have hsym : (k' + 1) * (n - k' + 1) = (k + 1) * (n - k + 1) := by
    dsimp only [k']
    by_cases h : k ≤ n - k
    · rw [min_eq_left h]
    · rw [min_eq_right (by omega)]
      have heq : n - (n - k) = k := by omega
      rw [heq, mul_comm]
  by_cases hα1 : α₀ = 1
  · obtain ⟨x₀, _⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
    obtain ⟨w, hw_sync, hw_len⟩ :=
      almostUniform_cerny A hSync P x₀ 1 (by
        intro q _; rw [hπ q, hα1]; split_ifs <;> rfl)
    refine ⟨w, hw_sync, ?_⟩
    dsimp only
    have hcoeff : n - 1 ≤ (k' + 1) * (n - k' + 1) - 3 := by
      rw [hsym]
      have hnk1 : 1 ≤ n - k := by omega
      have hge4 : 4 ≤ (k + 1) * (n - k + 1) := by nlinarith
      zify [show 1 ≤ n by omega, show k ≤ n by omega, show 3 ≤ (k + 1) * (n - k + 1) by omega]
      have hkn : (1 : ℤ) ≤ (k : ℤ) * ((n : ℤ) - (k : ℤ)) := by nlinarith
      nlinarith only [hkn]
    calc w.length ≤ (n - 1) ^ 2 := hw_len
      _ = (n - 1) * (n - 1) := sq (n - 1)
      _ ≤ ((k' + 1) * (n - k' + 1) - 3) * (n - 1) := Nat.mul_le_mul_right _ hcoeff
  · -- `α₀ ≠ 1`: index set `I = ({0..n-k} × {0..k}) \ {(0, 0), (n-k, k)}` with Steinberg cost `n - 1`
    let P_all : Finset (ℕ × ℕ) := Finset.range (n - k + 1) ×ˢ Finset.range (k + 1)
    let I : Finset (ℕ × ℕ) := (P_all.erase (0, 0)).erase (n - k, k)
    let val : ℕ × ℕ → ℝ := fun p => (p.1 : ℝ) + (p.2 : ℝ) * α₀
    let cost : ℕ × ℕ → ℕ := fun _ => n - 1
    have h00_mem : (0, 0) ∈ P_all :=
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
    have hnk_mem : (n - k, k) ∈ P_all.erase (0, 0) :=
      Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.snd h; omega,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩
    have hI_card : I.card = (k + 1) * (n - k + 1) - 2 := by
      have h1 : (P_all.erase (0, 0)).card = P_all.card - 1 := Finset.card_erase_of_mem h00_mem
      have h2 : I.card = (P_all.erase (0, 0)).card - 1 := Finset.card_erase_of_mem hnk_mem
      have h3 : P_all.card = (n - k + 1) * (k + 1) := by
        simp only [P_all, Finset.card_product, Finset.card_range]
      rw [h2, h1, h3, mul_comm]; omega
    have hstep_all : ∀ S : Finset Q, S.Nonempty → S ≠ Finset.univ →
        ∃ i ∈ I, val i = ∑ q ∈ S, P.π q ∧ 1 ≤ cost i ∧
          ∃ w : List α, w.length ≤ cost i ∧ ∑ q ∈ S, P.π q < ∑ p ∈ A.preimage S w, P.π p := by
      intro S hS_ne hS_ne_univ
      have hS_lt : S.card < n := by
        simpa [n] using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS_ne_univ)
      set r := (S \ X).card
      set j := (S ∩ X).card
      have hj_le : j ≤ k := Finset.card_le_card Finset.inter_subset_right
      have hr_le : r ≤ n - k := TwoValueStationary.card_sdiff_le_compl S X
      have hcard_split : r + j = S.card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_sdiff_inter S X), Finset.sdiff_union_inter]
      have hS_pos : 0 < S.card := Finset.card_pos.mpr hS_ne
      have hrj_mem : (r, j) ∈ I := by
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
          Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩⟩
        · intro h; have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h; omega
        · intro h; have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h; omega
      obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.steinberg_exists_gt hSync P S hS_ne hS_lt
      exact ⟨(r, j), hrj_mem, (TwoValueStationary.twoValue_sum_eq P.π X α₀ hπ S).symm,
        by dsimp only [cost]; omega, w, hw_len, hw_gt⟩
    rcases lt_or_gt_of_ne hα1 with hlt1 | hgt1
    · -- `α₀ < 1`: start at `{y₀}` (`y₀ ∉ X`), omitting `(0, 1) ∈ I`
      have hex_y : ∃ y₀ : Q, y₀ ∉ X := by
        by_contra hall; push Not at hall
        have := Finset.card_le_card (show (Finset.univ : Finset Q) ⊆ X from fun y _ => hall y)
        rw [Finset.card_univ] at this; omega
      obtain ⟨y₀, hy₀⟩ := hex_y
      obtain ⟨v, hv_full, hv_len⟩ :=
        TwoValueStationary.potential_reach_univ P I val cost {y₀} (Finset.singleton_nonempty y₀)
          (fun S h1 h2 _ => hstep_all S h1 h2)
      have h01_mem : (0, 1) ∈ I := by
        refine Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.fst h; omega,
          Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.snd h; norm_num at this,
            Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩⟩
      have hsub : I.filter (fun i => ∑ q ∈ ({y₀} : Finset Q), P.π q ≤ val i) ⊆ I.erase (0, 1) := by
        intro i hi
        rcases Finset.mem_filter.mp hi with ⟨hiI, hival⟩
        refine Finset.mem_erase.mpr ⟨?_, hiI⟩
        intro heq; rw [heq] at hival
        simp only [Finset.sum_singleton, hπ y₀, hy₀, ↓reduceIte, val, Nat.cast_zero, Nat.cast_one,
          zero_add, one_mul] at hival
        linarith
      refine ⟨v, ⟨y₀, fun q => by
        have hq : q ∈ A.preimage {y₀} v := hv_full ▸ Finset.mem_univ q
        simpa [DFA.mem_preimage] using hq⟩, ?_⟩
      dsimp only
      have h1 : v.length ≤ (I.erase (0, 1)).card * (n - 1) := by
        calc v.length
            ≤ ∑ i ∈ I.filter (fun i => ∑ q ∈ ({y₀} : Finset Q), P.π q ≤ val i), cost i := hv_len
          _ ≤ ∑ i ∈ I.erase (0, 1), cost i := Finset.sum_le_sum_of_subset hsub
          _ = (I.erase (0, 1)).card * (n - 1) := by
              simp only [cost, Finset.sum_const, smul_eq_mul]
      rw [Finset.card_erase_of_mem h01_mem, hI_card, ← hsym] at h1
      simpa only [Nat.sub_sub] using h1
    · -- `1 < α₀`: start at `{x₁}` (`x₁ ∈ X`), omitting `(1, 0) ∈ I`
      obtain ⟨x₁, hx₁X⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
      obtain ⟨v, hv_full, hv_len⟩ :=
        TwoValueStationary.potential_reach_univ P I val cost {x₁} (Finset.singleton_nonempty x₁)
          (fun S h1 h2 _ => hstep_all S h1 h2)
      have h10_mem : (1, 0) ∈ I := by
        refine Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.snd h; omega,
          Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.fst h; norm_num at this,
            Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩⟩
      have hsub : I.filter (fun i => ∑ q ∈ ({x₁} : Finset Q), P.π q ≤ val i) ⊆ I.erase (1, 0) := by
        intro i hi
        rcases Finset.mem_filter.mp hi with ⟨hiI, hival⟩
        refine Finset.mem_erase.mpr ⟨?_, hiI⟩
        intro heq; rw [heq] at hival
        simp only [Finset.sum_singleton, hπ x₁, hx₁X, ↓reduceIte, val, Nat.cast_one, Nat.cast_zero,
          zero_mul, add_zero] at hival
        linarith
      refine ⟨v, ⟨x₁, fun q => by
        have hq : q ∈ A.preimage {x₁} v := hv_full ▸ Finset.mem_univ q
        simpa [DFA.mem_preimage] using hq⟩, ?_⟩
      dsimp only
      have h1 : v.length ≤ (I.erase (1, 0)).card * (n - 1) := by
        calc v.length
            ≤ ∑ i ∈ I.filter (fun i => ∑ q ∈ ({x₁} : Finset Q), P.π q ≤ val i), cost i := hv_len
          _ ≤ ∑ i ∈ I.erase (1, 0), cost i := Finset.sum_le_sum_of_subset hsub
          _ = (I.erase (1, 0)).card * (n - 1) := by
              simp only [cost, Finset.sum_const, smul_eq_mul]
      rw [Finset.card_erase_of_mem h10_mem, hI_card, ← hsym] at h1
      simpa only [Nat.sub_sub] using h1

/-- **Theorem H_real_k(2) (BFS-Sharpened General `k`-Exception Bound for `α₀ ∉ ⋃_{d=1}^k (1/d)ℤ`)**:
Whenever `2 ≤ k := |X| < n` and `d * α₀ ∉ ℤ` for all `1 ≤ d ≤ k` (including all rationals `p/q₀`
with `q₀ > k` and all irrational `α₀`), multi-state BFS on `j ∈ {0, k}` yields:
`rt(A) ≤ (n - k + 1) * (k * n - 2 * k + 1) - (n - k) < k * (n - k + 1) * (n - 1)`. -/
theorem twoValue_general_k_nonSmallDenom_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (X : Finset Q) (hX_ge2 : 2 ≤ X.card) (hX_lt : X.card < Fintype.card Q)
    (α₀ : ℝ) (_hα₀_pos : 0 < α₀)
    (hnoDenom : ∀ d : ℕ, 1 ≤ d → d ≤ X.card → ∀ z : ℤ, (d : ℝ) * α₀ ≠ (z : ℝ))
    (hπ : ∀ q : Q, P.π q = if q ∈ X then α₀ else 1) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ (Fintype.card Q - X.card + 1) * (X.card * Fintype.card Q - 2 * X.card + 1) -
        (Fintype.card Q - X.card) ∧
      w.length < X.card * (Fintype.card Q - X.card + 1) * (Fintype.card Q - 1) := by
  classical
  set n := Fintype.card Q
  set k := X.card
  have hSC : A.IsStronglyConnected := positiveStationary_stronglyConnected hSync P
  have hα₀_ne1 : α₀ ≠ 1 := by
    intro h1
    exact hnoDenom 1 le_rfl (by omega) 1 (by simp [h1])
  let P_all : Finset (ℕ × ℕ) := Finset.range (n - k + 1) ×ˢ Finset.range (k + 1)
  let I : Finset (ℕ × ℕ) := (P_all.erase (0, 0)).erase (n - k, k)
  let val : ℕ × ℕ → ℝ := fun p => (p.1 : ℝ) + (p.2 : ℝ) * α₀
  let cost : ℕ × ℕ → ℕ := fun p =>
    if p.2 = 0 then n - k - p.1 + 1
    else if p.2 = k then p.1 + 1
    else n - 1
  -- Exact sum over `I`: `(n - k + 1) * (k * n - 2 * k + 1)`
  have hI_sum : ∑ p ∈ I, cost p = (n - k + 1) * (k * n - 2 * k + 1) := by
    have h00_mem : (0, 0) ∈ P_all :=
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
    have hnk_mem : (n - k, k) ∈ P_all.erase (0, 0) :=
      Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.snd h; omega,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩
    have hsum_erase : (∑ p ∈ I, cost p) + cost (n - k, k) + cost (0, 0) = ∑ p ∈ P_all, cost p := by
      have h1 := Finset.sum_erase_add (P_all.erase (0, 0)) cost hnk_mem
      have h2 := Finset.sum_erase_add P_all cost h00_mem
      dsimp only [I]
      omega
    have hc00 : cost (0, 0) = n - k + 1 := by dsimp only [cost]; simp
    have hcnk : cost (n - k, k) = n - k + 1 := by dsimp only [cost]; simp [show k ≠ 0 by omega]
    have hPall_sum : ∑ p ∈ P_all, cost p =
        ∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (n - k + 1), cost (r, j) := by
      dsimp only [P_all]; rw [Finset.sum_product_right]
    -- Split `range (k + 1)` = `{0} ∪ {1..k-1} ∪ {k}` via `sum_range_succ` and `sum_range_succ'`
    have hsplit : ∑ j ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (n - k + 1), cost (r, j) =
        (∑ r ∈ Finset.range (n - k + 1), cost (r, 0)) +
        (∑ i ∈ Finset.range (k - 1), ∑ r ∈ Finset.range (n - k + 1), cost (r, i + 1)) +
        (∑ r ∈ Finset.range (n - k + 1), cost (r, k)) := by
      rw [Finset.sum_range_succ]
      have hsub_k : ∑ j ∈ Finset.range k, ∑ r ∈ Finset.range (n - k + 1), cost (r, j) =
          (∑ i ∈ Finset.range (k - 1), ∑ r ∈ Finset.range (n - k + 1), cost (r, i + 1)) +
          (∑ r ∈ Finset.range (n - k + 1), cost (r, 0)) := by
        have hk1 : Finset.range k = Finset.range ((k - 1) + 1) := by congr 1; omega
        rw [hk1, Finset.sum_range_succ']
      omega
    have hj0_sum : 2 * (∑ r ∈ Finset.range (n - k + 1), cost (r, 0)) =
        (n - k + 1) * (n - k + 2) := by
      have hc : ∑ r ∈ Finset.range (n - k + 1), cost (r, 0) =
          ∑ r ∈ Finset.range (n - k + 1), (n - k + 1 - r) :=
        Finset.sum_congr rfl fun r hr => by
          have := Finset.mem_range.mp hr; dsimp only [cost]; simp; omega
      rw [hc]
      have hadd : (∑ r ∈ Finset.range (n - k + 1), (n - k + 1 - r)) +
          (∑ r ∈ Finset.range (n - k + 1), r) = (n - k + 1) * (n - k + 1) := by
        rw [← Finset.sum_add_distrib]
        have h1 : ∑ r ∈ Finset.range (n - k + 1), ((n - k + 1 - r) + r) =
            ∑ _r ∈ Finset.range (n - k + 1), (n - k + 1) :=
          Finset.sum_congr rfl fun r hr => by have := Finset.mem_range.mp hr; omega
        rw [h1, Finset.sum_const, Finset.card_range, smul_eq_mul]
      have htri := TwoValueStationary.two_mul_sum_range (n - k + 1)
      rw [Nat.add_sub_cancel] at htri
      zify [show k ≤ n by omega] at hadd htri ⊢
      nlinarith only [hadd, htri]
    have hjk_sum : 2 * (∑ r ∈ Finset.range (n - k + 1), cost (r, k)) =
        (n - k + 1) * (n - k + 2) := by
      have hc : ∑ r ∈ Finset.range (n - k + 1), cost (r, k) =
          ∑ r ∈ Finset.range (n - k + 1), (r + 1) :=
        Finset.sum_congr rfl fun r _ => by dsimp only [cost]; simp [show k ≠ 0 by omega]
      rw [hc, TwoValueStationary.two_mul_sum_range_succ]
    have hmid_sum : ∑ i ∈ Finset.range (k - 1), ∑ r ∈ Finset.range (n - k + 1), cost (r, i + 1) =
        (k - 1) * ((n - k + 1) * (n - 1)) := by
      have hc : ∑ i ∈ Finset.range (k - 1), ∑ r ∈ Finset.range (n - k + 1), cost (r, i + 1) =
          ∑ _i ∈ Finset.range (k - 1), ((n - k + 1) * (n - 1)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi_lt := Finset.mem_range.mp hi
        have hinner : ∑ r ∈ Finset.range (n - k + 1), cost (r, i + 1) =
            ∑ _r ∈ Finset.range (n - k + 1), (n - 1) :=
          Finset.sum_congr rfl fun r _ => by
            dsimp only [cost]; simp [show i + 1 ≠ k by omega]
        rw [hinner, Finset.sum_const, Finset.card_range, smul_eq_mul]
      rw [hc, Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [hPall_sum, hsplit, hmid_sum, hc00, hcnk] at hsum_erase
    have h2k_le : 2 * k ≤ k * n := by nlinarith
    zify [show 1 ≤ n by omega, show 1 ≤ k by omega, show k ≤ n by omega, h2k_le] at hsum_erase hj0_sum hjk_sum ⊢
    nlinarith only [hsum_erase, hj0_sum, hjk_sum]
  -- Step verification for every nonempty proper `S`
  have hstep_all : ∀ S : Finset Q, S.Nonempty → S ≠ Finset.univ →
      ∃ i ∈ I, val i = ∑ q ∈ S, P.π q ∧ 1 ≤ cost i ∧
        ∃ w : List α, w.length ≤ cost i ∧ ∑ q ∈ S, P.π q < ∑ p ∈ A.preimage S w, P.π p := by
    intro S hS_ne hS_ne_univ
    have hS_lt : S.card < n := by
      simpa [n] using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS_ne_univ)
    set r := (S \ X).card
    set j := (S ∩ X).card
    have hj_le : j ≤ k := Finset.card_le_card Finset.inter_subset_right
    have hr_le : r ≤ n - k := TwoValueStationary.card_sdiff_le_compl S X
    have hcard_split : r + j = S.card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_sdiff_inter S X), Finset.sdiff_union_inter]
    have hS_pos : 0 < S.card := Finset.card_pos.mpr hS_ne
    have hrj_mem : (r, j) ∈ I := by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩⟩
      · intro h; have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h; omega
      · intro h; have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h; omega
    have hval_eq : val (r, j) = ∑ q ∈ S, P.π q :=
      (TwoValueStationary.twoValue_sum_eq P.π X α₀ hπ S).symm
    by_cases hj0 : j = 0
    · -- `j = 0`: `Disjoint S X`, Lemma H.3(1) enters `X` in `≤ n - k - r + 1`!
      have hdisj : Disjoint S X := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hj0)
      obtain ⟨u, _, hu_len, hu_in⟩ :=
        subset_bfs_entry hSC X S (Finset.card_pos.mp (by omega)) hS_ne hdisj
      set j' := (A.preimage S u ∩ X).card
      have hj'_pos : 1 ≤ j' := Finset.card_pos.mpr hu_in
      have hj'_le : j' ≤ k := Finset.card_le_card Finset.inter_subset_right
      have hne : ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q := by
        rw [TwoValueStationary.twoValue_sum_eq P.π X α₀ hπ (A.preimage S u), ← hval_eq]
        dsimp only [val]; rw [hj0, Nat.cast_zero, zero_mul, add_zero]
        intro heq
        exact hnoDenom j' hj'_pos hj'_le ((r : ℤ) - ((A.preimage S u \ X).card : ℤ))
          (by push_cast; linarith)
      obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.exists_gt_of_ne P S u hne
      have hcost : cost (r, j) = n - k - r + 1 := by dsimp only [cost]; simp [hj0]
      have hS_eq_r : S.card = r := by omega
      refine ⟨(r, j), hrj_mem, hval_eq, by omega, w, by omega, hw_gt⟩
    · by_cases hjk : j = k
      · -- `j = k`: `X ⊆ S`, Lemma H.3(2) escapes `X` in `≤ r + 1`!
        have hXS : X ⊆ S := by
          have heq : S ∩ X = X := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
          intro q hq; rw [← heq] at hq; exact (Finset.mem_inter.mp hq).1
        obtain ⟨u, _, hu_len, hu_esc⟩ :=
          subset_bfs_escape hSC X S (Finset.card_pos.mp (by omega)) hXS hS_lt
        set j' := (A.preimage S u ∩ X).card
        have hj'_lt : j' < k := by
          have hss : A.preimage S u ∩ X ⊂ X := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, fun heq => ?_⟩
            apply hu_esc; intro q hq; rw [← heq] at hq; exact (Finset.mem_inter.mp hq).1
          exact Finset.card_lt_card hss
        have hne : ∑ p ∈ A.preimage S u, P.π p ≠ ∑ q ∈ S, P.π q := by
          rw [TwoValueStationary.twoValue_sum_eq P.π X α₀ hπ (A.preimage S u), ← hval_eq]
          dsimp only [val]; rw [hjk]
          intro heq
          have hd_eq : ((k - j' : ℕ) : ℝ) * α₀ = (((A.preimage S u \ X).card : ℤ) - (r : ℤ) : ℤ) := by
            have hkj : (k - j' : ℕ) + j' = k := Nat.sub_add_cancel (by omega)
            have hkj_r : ((k - j' : ℕ) : ℝ) + (j' : ℝ) = (k : ℝ) := by exact_mod_cast hkj
            push_cast; nlinarith
          exact hnoDenom (k - j') (by omega) (by omega) (((A.preimage S u \ X).card : ℤ) - (r : ℤ)) hd_eq
        obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.exists_gt_of_ne P S u hne
        have hcost : cost (r, j) = r + 1 := by dsimp only [cost]; simp [hjk, show k ≠ 0 by omega]
        refine ⟨(r, j), hrj_mem, hval_eq, by omega, w, by omega, hw_gt⟩
      · -- `1 ≤ j ≤ k - 1`: Steinberg bound `≤ n - 1`
        obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.steinberg_exists_gt hSync P S hS_ne hS_lt
        have hcost : cost (r, j) = n - 1 := by dsimp only [cost]; simp [hj0, hjk]
        refine ⟨(r, j), hrj_mem, hval_eq, by omega, w, by omega, hw_gt⟩
  -- Pick starting singleton omitting `(0, 1)` (cost `n - 1 ≥ n - k`) if `α₀ < 1`, or `(1, 0)` (cost `n - k`) if `1 < α₀`
  have hstrict_arith : (n - k + 1) * (k * n - 2 * k + 1) - (n - k) < k * (n - k + 1) * (n - 1) := by
    have h2k_le : 2 * k ≤ k * n := by nlinarith
    have hsub_le : n - k ≤ (n - k + 1) * (k * n - 2 * k + 1) := by nlinarith
    zify [show 1 ≤ n by omega, show k ≤ n by omega, h2k_le, hsub_le]
    have hnk1 : (1 : ℤ) ≤ (n : ℤ) - (k : ℤ) := by omega
    have hk2 : (2 : ℤ) ≤ (k : ℤ) := by omega
    nlinarith only [hnk1, hk2]
  rcases lt_or_gt_of_ne hα₀_ne1 with hlt1 | hgt1
  · have hex_y : ∃ y₀ : Q, y₀ ∉ X := by
      by_contra hall; push Not at hall
      have := Finset.card_le_card (show (Finset.univ : Finset Q) ⊆ X from fun y _ => hall y)
      rw [Finset.card_univ] at this; omega
    obtain ⟨y₀, hy₀⟩ := hex_y
    obtain ⟨v, hv_full, hv_len⟩ :=
      TwoValueStationary.potential_reach_univ P I val cost {y₀} (Finset.singleton_nonempty y₀)
        (fun S h1 h2 _ => hstep_all S h1 h2)
    have h01_mem : (0, 1) ∈ I := by
      refine Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.fst h; omega,
        Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.snd h; norm_num at this,
          Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩⟩
    have hsub : I.filter (fun i => ∑ q ∈ ({y₀} : Finset Q), P.π q ≤ val i) ⊆ I.erase (0, 1) := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hiI, hival⟩
      refine Finset.mem_erase.mpr ⟨?_, hiI⟩
      intro heq; rw [heq] at hival
      simp only [Finset.sum_singleton, hπ y₀, hy₀, ↓reduceIte, val, Nat.cast_zero, Nat.cast_one,
        zero_add, one_mul] at hival
      linarith
    have hv_ub : v.length ≤ (n - k + 1) * (k * n - 2 * k + 1) - (n - k) := by
      have h1 := Finset.sum_le_sum_of_subset hsub (f := cost)
      have h2 := Finset.sum_erase_add I cost h01_mem
      have hc : cost (0, 1) = n - 1 := by dsimp only [cost]; simp [show 1 ≠ k by omega]
      rw [hc, hI_sum] at h2
      have hv_len' : v.length ≤ ∑ i ∈ I.filter (fun i => ∑ q ∈ ({y₀} : Finset Q), P.π q ≤ val i), cost i := by
        convert hv_len using 2
      omega
    exact ⟨v, ⟨y₀, fun q => by
      have hq : q ∈ A.preimage {y₀} v := hv_full ▸ Finset.mem_univ q
      simpa [DFA.mem_preimage] using hq⟩, hv_ub, lt_of_le_of_lt hv_ub hstrict_arith⟩
  · obtain ⟨x₁, hx₁X⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
    obtain ⟨v, hv_full, hv_len⟩ :=
      TwoValueStationary.potential_reach_univ P I val cost {x₁} (Finset.singleton_nonempty x₁)
        (fun S h1 h2 _ => hstep_all S h1 h2)
    have h10_mem : (1, 0) ∈ I := by
      refine Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.snd h; omega,
        Finset.mem_erase.mpr ⟨by intro h; have := congrArg Prod.fst h; norm_num at this,
          Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩⟩
    have hsub : I.filter (fun i => ∑ q ∈ ({x₁} : Finset Q), P.π q ≤ val i) ⊆ I.erase (1, 0) := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hiI, hival⟩
      refine Finset.mem_erase.mpr ⟨?_, hiI⟩
      intro heq; rw [heq] at hival
      simp only [Finset.sum_singleton, hπ x₁, hx₁X, ↓reduceIte, val, Nat.cast_one, Nat.cast_zero,
        zero_mul, add_zero] at hival
      linarith
    have hv_ub : v.length ≤ (n - k + 1) * (k * n - 2 * k + 1) - (n - k) := by
      have h1 := Finset.sum_le_sum_of_subset hsub (f := cost)
      have h2 := Finset.sum_erase_add I cost h10_mem
      have hc : cost (1, 0) = n - k := by dsimp only [cost]; simp; omega
      rw [hc, hI_sum] at h2
      have hv_len' : v.length ≤ ∑ i ∈ I.filter (fun i => ∑ q ∈ ({x₁} : Finset Q), P.π q ≤ val i), cost i := by
        convert hv_len using 2
      omega
    exact ⟨v, ⟨x₁, fun q => by
      have hq : q ∈ A.preimage {x₁} v := hv_full ▸ Finset.mem_univ q
      simpa [DFA.mem_preimage] using hq⟩, hv_ub, lt_of_le_of_lt hv_ub hstrict_arith⟩

/-- **Theorem H_real_k(2-Corollary) (Irrational `α₀ > 0` with `k' := min(k, n - k) ≥ 2`)**:
Because `α₀⁻¹` is also irrational, swapping `X ↔ Q \ X` when `k > n - k` replaces `k` by
`k' = min k (n - k)` in `twoValue_general_k_nonSmallDenom_bound`! -/
theorem twoValue_general_k_irrational_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (X : Finset Q) (hX_ge2 : 2 ≤ X.card) (hX_le : X.card + 2 ≤ Fintype.card Q)
    (α₀ : ℝ) (hα₀_pos : 0 < α₀)
    (hirr : ∀ (d : ℕ) (z : ℤ), 1 ≤ d → (d : ℝ) * α₀ ≠ (z : ℝ))
    (hπ : ∀ q : Q, P.π q = if q ∈ X then α₀ else 1) :
    ∃ w : List α, A.IsSyncWord w ∧
      let k' := min X.card (Fintype.card Q - X.card)
      w.length ≤ (Fintype.card Q - k' + 1) * (k' * Fintype.card Q - 2 * k' + 1) -
        (Fintype.card Q - k') := by
  by_cases hk : X.card ≤ Fintype.card Q - X.card
  · obtain ⟨w, hw_sync, hw_len, _⟩ :=
      twoValue_general_k_nonSmallDenom_bound A hSync P X hX_ge2 (by omega) α₀ hα₀_pos
        (fun d hd _ z => hirr d z hd) hπ
    refine ⟨w, hw_sync, ?_⟩
    dsimp only; rwa [min_eq_left hk]
  · let X' : Finset Q := Finset.univ \ X
    have hX'_card : X'.card = Fintype.card Q - X.card := by
      dsimp only [X']; rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    let P' : PositiveStationary A := TwoValueStationary.scaleStationary P α₀⁻¹ (inv_pos.mpr hα₀_pos)
    have hπ' : ∀ q : Q, P'.π q = if q ∈ X' then α₀⁻¹ else 1 := by
      intro q
      simp only [P', TwoValueStationary.scaleStationary, hπ q, X', Finset.mem_sdiff,
        Finset.mem_univ, true_and]
      by_cases hq : q ∈ X
      · simp [hq, inv_mul_cancel₀ (ne_of_gt hα₀_pos)]
      · simp [hq]
    have hirr_inv : ∀ d : ℕ, 1 ≤ d → d ≤ X'.card → ∀ z : ℤ, (d : ℝ) * α₀⁻¹ ≠ (z : ℝ) := by
      intro d hd _ z heq
      have hz_pos : (0 : ℤ) < z := by
        have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hpos : (0 : ℝ) < (z : ℝ) := by
          rw [← heq]; exact mul_pos hd_pos (inv_pos.mpr hα₀_pos)
        exact_mod_cast hpos
      have hmul : (z.toNat : ℝ) * α₀ = ((d : ℤ) : ℝ) := by
        have hzk : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
        have hzr : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hzk
        rw [hzr, ← heq, mul_assoc, inv_mul_cancel₀ (ne_of_gt hα₀_pos), mul_one]
        simp
      exact hirr z.toNat (d : ℤ) (by omega) hmul
    obtain ⟨w, hw_sync, hw_len, _⟩ :=
      twoValue_general_k_nonSmallDenom_bound A hSync P' X' (by omega) (by omega) α₀⁻¹
        (inv_pos.mpr hα₀_pos) hirr_inv hπ'
    refine ⟨w, hw_sync, ?_⟩
    dsimp only
    rw [min_eq_right (by omega), ← hX'_card]
    exact hw_len

/-! ### Section 4: Lemma T.1 (Szykuła Tier Lemma) & Theorem T (Super-Eulerian Exact Černý) -/

namespace TwoValueStationary

/-- Real `{0, 1}`-indicator function of a subset `K : Finset Q`. -/
private def indR {Q : Type u} [DecidableEq Q] (K : Finset Q) : Q → ℝ :=
  fun q => if q ∈ K then 1 else 0

private lemma indR_injective {Q : Type u} [DecidableEq Q] :
    Function.Injective (indR (Q := Q)) := by
  intro K₁ K₂ h
  ext q
  have hq := congrFun h q
  dsimp only [indR] at hq
  by_cases h1 : q ∈ K₁ <;> by_cases h2 : q ∈ K₂ <;> simp [h1, h2] at hq ⊢

open Classical in
/-- **Affine-Subspace `{0, 1}`-Counting Lemma (Matrix-Free Induction on `finrank U`)**:
For any `U : Submodule ℝ (Q → ℝ)` of dimension `≤ d` and any translate `v₀ : Q → ℝ`,
at most `2 ^ d` subsets `K : Finset Q` satisfy `indR K - v₀ ∈ U`! -/
private lemma subspace_zeroOne_card_le {Q : Type u} [Fintype Q] [DecidableEq Q] :
    ∀ (d : ℕ) (U : Submodule ℝ (Q → ℝ)) (v₀ : Q → ℝ),
      Module.finrank ℝ U ≤ d →
      ((Finset.univ : Finset (Finset Q)).filter (fun K => indR K - v₀ ∈ U)).card ≤ 2 ^ d := by
  intro d
  induction d with
  | zero =>
      intro U v₀ hU
      have hU_bot : U = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)
      have hle1 : ((Finset.univ : Finset (Finset Q)).filter (fun K => indR K - v₀ ∈ U)).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun K₁ hK₁ K₂ hK₂ => ?_
        have h1 : indR K₁ - v₀ = 0 := by
          have := (Finset.mem_filter.mp hK₁).2; rwa [hU_bot, Submodule.mem_bot] at this
        have h2 : indR K₂ - v₀ = 0 := by
          have := (Finset.mem_filter.mp hK₂).2; rwa [hU_bot, Submodule.mem_bot] at this
        exact indR_injective (by rw [sub_eq_zero.mp h1, sub_eq_zero.mp h2])
      simpa using hle1
  | succ d ih =>
      intro U v₀ hU
      let F : Finset (Finset Q) := Finset.univ.filter (fun K => indR K - v₀ ∈ U)
      by_cases hF1 : F.card ≤ 1
      · exact hF1.trans (Nat.one_le_two_pow)
      · obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
        have hdiff_q : ∃ q₀ : Q, (q₀ ∈ K₁) ≠ (q₀ ∈ K₂) := by
          by_contra hall; push Not at hall
          exact hne (Finset.ext fun q => eq_iff_iff.mp (hall q))
        obtain ⟨q₀, hq₀⟩ := hdiff_q
        let u : Q → ℝ := indR K₁ - indR K₂
        have huU : u ∈ U := by
          have h1 := (Finset.mem_filter.mp hK₁).2
          have h2 := (Finset.mem_filter.mp hK₂).2
          have heq : u = (indR K₁ - v₀) - (indR K₂ - v₀) := by ext q; simp [u]
          rw [heq]; exact U.sub_mem h1 h2
        have huq₀ : u q₀ ≠ 0 := by
          by_cases h1 : q₀ ∈ K₁ <;> by_cases h2 : q₀ ∈ K₂ <;> simp [u, indR, h1, h2] at hq₀ ⊢
        let U₀ : Submodule ℝ (Q → ℝ) := U ⊓ LinearMap.ker (LinearMap.proj q₀)
        have hU₀_lt : U₀ < U := lt_of_le_of_ne inf_le_left fun heq => by
          have hu_U₀ : u ∈ U₀ := heq.symm ▸ huU
          have hu_ker : u ∈ LinearMap.ker (LinearMap.proj q₀) := hu_U₀.2
          exact huq₀ (by simpa [LinearMap.mem_ker] using hu_ker)
        have hU₀_dim : Module.finrank ℝ U₀ ≤ d := by
          have hlt := Submodule.finrank_lt_finrank_of_lt hU₀_lt
          omega
        let F_in : Finset (Finset Q) := F.filter (fun K => q₀ ∈ K)
        let F_out : Finset (Finset Q) := F.filter (fun K => q₀ ∉ K)
        have hsplit : F_in.card + F_out.card = F.card := by
          have hdisj : Disjoint F_in F_out :=
            Finset.disjoint_left.mpr fun K h1 h2 => (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
          have hunion : F_in ∪ F_out = F := by
            ext K; simp only [F_in, F_out, Finset.mem_union, Finset.mem_filter]
            by_cases h : q₀ ∈ K <;> simp [h]
          rw [← Finset.card_union_of_disjoint hdisj, hunion]
        have hFin_le : F_in.card ≤ 2 ^ d := by
          rcases F_in.eq_empty_or_nonempty with hemp | ⟨K_in, hKin⟩
          · rw [hemp, Finset.card_empty]; exact Nat.zero_le _
          · have hsub : F_in ⊆ Finset.univ.filter (fun K => indR K - indR K_in ∈ U₀) := by
              intro K hK
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ K, ?_, ?_⟩
              · have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hK).1).2
                have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hKin).1).2
                have heq : indR K - indR K_in = (indR K - v₀) - (indR K_in - v₀) := by ext q; simp
                rw [heq]; exact U.sub_mem h1 h2
              · simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, Pi.sub_apply,
                  indR, (Finset.mem_filter.mp hK).2, (Finset.mem_filter.mp hKin).2, ↓reduceIte, sub_self]
            exact (Finset.card_le_card hsub).trans (ih U₀ (indR K_in) hU₀_dim)
        have hFout_le : F_out.card ≤ 2 ^ d := by
          rcases F_out.eq_empty_or_nonempty with hemp | ⟨K_out, hKout⟩
          · rw [hemp, Finset.card_empty]; exact Nat.zero_le _
          · have hsub : F_out ⊆ Finset.univ.filter (fun K => indR K - indR K_out ∈ U₀) := by
              intro K hK
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ K, ?_, ?_⟩
              · have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hK).1).2
                have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hKout).1).2
                have heq : indR K - indR K_out = (indR K - v₀) - (indR K_out - v₀) := by ext q; simp
                rw [heq]; exact U.sub_mem h1 h2
              · simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, Pi.sub_apply,
                  indR, (Finset.mem_filter.mp hK).2, (Finset.mem_filter.mp hKout).2, ↓reduceIte, sub_self]
            exact (Finset.card_le_card hsub).trans (ih U₀ (indR K_out) hU₀_dim)
        calc F.card = F_in.card + F_out.card := hsplit.symm
          _ ≤ 2 ^ d + 2 ^ d := Nat.add_le_add hFin_le hFout_le
          _ = 2 ^ (d + 1) := by ring

/-- Telescoping indicator bound for `c ≤ n - 1` and `1 ≤ t ≤ n`. -/
private lemma tier_telescope_le (n : ℕ) :
    ∀ t : ℕ, 1 ≤ t → t ≤ n → ∀ c : ℕ, c ≤ n - 1 →
      c ≤ (n - t) + ∑ j ∈ Finset.Icc 2 t, if n - j + 1 ≤ c then 1 else 0 := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ t ih =>
      intro _ htn c hc
      by_cases ht0 : t = 0
      · subst ht0; simp; omega
      · have hih := ih (by omega) (by omega) c hc
        have hIcc : Finset.Icc 2 (t + 1) = insert (t + 1) (Finset.Icc 2 t) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnotmem : t + 1 ∉ Finset.Icc 2 t := by simp
        rw [hIcc, Finset.sum_insert hnotmem]
        by_cases hge : n - (t + 1) + 1 ≤ c
        · simp only [hge, ↓reduceIte]; omega
        · omega

private lemma two_mul_add_two_le_pow (t : ℕ) (ht : 1 ≤ t) : 2 * t + 2 ≤ 2 ^ (t + 1) := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases ht0 : t = 0
      · subst ht0; norm_num
      · have h := ih (by omega)
        have hpow : 2 ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := by ring
        omega

private lemma sum_Icc_two_pow_sub_two (t : ℕ) (ht : 1 ≤ t) :
    ∑ j ∈ Finset.Icc 2 t, (2 ^ j - 2) = 2 ^ (t + 1) - 2 * t - 2 := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases ht0 : t = 0
      · subst ht0; norm_num
      · have hih := ih (by omega)
        have hIcc : Finset.Icc 2 (t + 1) = insert (t + 1) (Finset.Icc 2 t) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnotmem : t + 1 ∉ Finset.Icc 2 t := by simp
        rw [hIcc, Finset.sum_insert hnotmem, hih]
        have hge := two_mul_add_two_le_pow t (by omega)
        have hpow : 2 ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := by ring
        omega

private lemma const_excess_pow_ge (E : ℕ) (hE : 1 ≤ E) :
    E ^ 2 + 4 * E + 7 ≤ 2 ^ (E + 3) := by
  induction E with
  | zero => omega
  | succ E ih =>
      by_cases hE0 : E = 0
      · subst hE0; norm_num
      · have h := ih (by omega)
        have hpow : 2 ^ (E + 1 + 3) = 2 * 2 ^ (E + 3) := by ring
        nlinarith

end TwoValueStationary

open Classical in
/-- **Lemma T.1 (Self-Contained Dual-Subspace Proof of Szykuła's Tier Lemma)**:
In any synchronizing `n`-state DFA (`n ≥ 2`) with positive stationary vector `P`, for every
`1 ≤ j ≤ n`, at most `2 ^ j - 2` nonempty proper subsets `K ⊂ Q` have `π(K w⁻¹) = π(K)` for all
words `w` of length `≤ n - j`! -/
theorem szykula_tier_lemma {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (hn2 : 2 ≤ Fintype.card Q) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ Fintype.card Q) :
    ((Finset.univ : Finset (Finset Q)).filter (fun K =>
      K.Nonempty ∧ K ≠ Finset.univ ∧
      ∀ w : List α, w.length ≤ Fintype.card Q - j →
        ∑ p ∈ A.preimage K w, P.π p = ∑ q ∈ K, P.π q)).card ≤ 2 ^ j - 2 := by
  classical
  set n := Fintype.card Q
  have hSC : A.IsStronglyConnected := positiveStationary_stronglyConnected hSync P
  -- Step 1: Ascending pushforward span `V d = span { pushR A w P.π | w.length ≤ d }`
  let V : ℕ → Submodule ℝ (Q → ℝ) := fun d =>
    Submodule.span ℝ { v : Q → ℝ | ∃ w : List α, w.length ≤ d ∧ v = TwoValueStationary.pushR A w P.π }
  have hV_mono : ∀ d : ℕ, V d ≤ V (d + 1) := fun d =>
    Submodule.span_mono fun _ ⟨w, hw, hv⟩ => ⟨w, by omega, hv⟩
  have hV0_pos : 1 ≤ Module.finrank ℝ (V 0) := by
    have hπ_mem : P.π ∈ V 0 :=
      Submodule.subset_span ⟨[], le_rfl, (TwoValueStationary.pushR_nil A P.π).symm⟩
    have hπ_ne : P.π ≠ 0 := by
      obtain ⟨q₀⟩ := hSync.nonempty
      intro h0
      have hq := congrFun h0 q₀
      simp only [Pi.zero_apply] at hq
      linarith [P.hπ_pos q₀]
    have hbot_lt : (⊥ : Submodule ℝ (Q → ℝ)) < V 0 :=
      lt_of_le_of_ne bot_le fun heq => hπ_ne (by rwa [← heq, Submodule.mem_bot] at hπ_mem)
    have hlt := Submodule.finrank_lt_finrank_of_lt hbot_lt
    simp only [finrank_bot] at hlt
    omega
  have hV_top_of_eq : ∀ d : ℕ, V d = V (d + 1) → V d = ⊤ := by
    intro d heq
    have hstep_closed : ∀ (a : α), Submodule.map (TwoValueStationary.pushR A [a]) (V d) ≤ V d := by
      intro a
      rw [Submodule.map_span_le]
      rintro v ⟨w, hw, rfl⟩
      rw [← TwoValueStationary.pushR_append A w [a] P.π, heq]
      exact Submodule.subset_span ⟨w ++ [a], by simp; omega, rfl⟩
    have hword_closed : ∀ (w : List α) (u : Q → ℝ), u ∈ V d → TwoValueStationary.pushR A w u ∈ V d := by
      intro w
      induction w with
      | nil => intro u hu; rwa [TwoValueStationary.pushR_nil]
      | cons a t ih =>
          intro u hu
          have hcons : a :: t = [a] ++ t := rfl
          rw [hcons, TwoValueStationary.pushR_append]
          exact ih _ (hstep_closed a ⟨u, hu, rfl⟩)
    have hπ_mem : P.π ∈ V d :=
      Submodule.subset_span ⟨[], Nat.zero_le d, (TwoValueStationary.pushR_nil A P.π).symm⟩
    rcases hSync with ⟨wStar, r₀, hr₀⟩
    have hsum_pos : 0 < ∑ p : Q, P.π p :=
      Finset.sum_pos (fun p _ => P.hπ_pos p) (Finset.univ_nonempty_iff.mpr ⟨r₀⟩)
    have hsingle_mem : ∀ q : Q, Pi.single q (1 : ℝ) ∈ V d := by
      intro q
      obtain ⟨uq, huq⟩ := hSC r₀ q
      have hwq_eval : ∀ p : Q, A.eval p (wStar ++ uq) = q := by
        intro p; rw [DFA.eval_append, hr₀ p, huq]
      have hpush_eq : TwoValueStationary.pushR A (wStar ++ uq) P.π =
          (∑ p : Q, P.π p) • Pi.single q (1 : ℝ) := by
        ext x
        simp only [TwoValueStationary.pushR, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
          smul_eq_mul, Pi.single_apply, hwq_eval]
        by_cases hxq : x = q
        · subst hxq; simp
        · simp [Ne.symm hxq, hxq]
      have hmem := hword_closed (wStar ++ uq) P.π hπ_mem
      rw [hpush_eq] at hmem
      have hscaled := (V d).smul_mem (∑ p : Q, P.π p)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hsum_pos), one_smul] at hscaled
    rw [eq_top_iff]
    intro f _
    have hf_eq : f = ∑ q : Q, f q • Pi.single q (1 : ℝ) := by
      ext x; simp [Pi.single_apply]
    rw [hf_eq]
    exact Submodule.sum_mem (V d) fun q _ => (V d).smul_mem (f q) (hsingle_mem q)
  have hV_dim : ∀ d : ℕ, min (d + 1) n ≤ Module.finrank ℝ (V d) := by
    intro d
    induction d with
    | zero => exact le_trans (min_le_left 1 n) hV0_pos
    | succ d ih =>
        by_cases heq : V d = V (d + 1)
        · have htop : V (d + 1) = ⊤ := heq ▸ hV_top_of_eq d heq
          rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card]
          exact min_le_right _ _
        · have hlt : V d < V (d + 1) := lt_of_le_of_ne (hV_mono d) heq
          have hdim_lt := Submodule.finrank_lt_finrank_of_lt hlt
          have hle_n : Module.finrank ℝ (V (d + 1)) ≤ n := by
            simpa [n, Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le (V (d + 1))
          omega
  -- Step 2: Orthocomplement `ker L` of `V (n - j)` has `finrank ≤ j - 1`
  set d := n - j
  set r := Module.finrank ℝ (V d)
  have hr_ge : n - j + 1 ≤ r := by
    have h := hV_dim d
    have : min (d + 1) n = n - j + 1 := by omega
    rwa [this] at h
  let b := Module.finBasis ℝ (V d)
  let L : (Q → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
    { toFun := fun f i => ∑ q : Q, (b i).1 q * f q
      map_add' := fun x y => by
        ext i; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => by ring }
  let T : (Fin r → ℝ) →ₗ[ℝ] (Q → ℝ) :=
    { toFun := fun c => ∑ i : Fin r, c i • (b i).1
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun s x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul] }
  have hLT_inj : Function.Injective (L.comp T) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hsum_sq : ∑ q : Q, (T c q) ^ 2 = 0 := by
      calc ∑ q : Q, (T c q) ^ 2
          = ∑ q : Q, (∑ i : Fin r, c i * (b i).1 q) * T c q := by
              refine Finset.sum_congr rfl fun q _ => ?_
              have hTc : T c q = ∑ i : Fin r, c i * (b i).1 q := by
                simp [T, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
              rw [sq, ← hTc]
        _ = ∑ q : Q, ∑ i : Fin r, c i * ((b i).1 q * T c q) := by
              refine Finset.sum_congr rfl fun q _ => ?_
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i : Fin r, ∑ q : Q, c i * ((b i).1 q * T c q) := Finset.sum_comm
        _ = ∑ i : Fin r, c i * (L (T c) i) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← Finset.mul_sum]; rfl
        _ = 0 := by
              have h0 : ∀ i : Fin r, L (T c) i = 0 := fun i => congrFun hc i
              simp [h0]
    have hTc0 : T c = 0 := by
      ext q
      have hsq0 : (T c q) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun p _ => sq_nonneg (T c p)).mp hsum_sq q (Finset.mem_univ q)
      exact sq_eq_zero_iff.mp hsq0
    have hlin0 : ∑ i : Fin r, c i • b i = 0 := by
      apply Subtype.ext
      simpa [T, Submodule.coe_sum, Submodule.coe_smul] using hTc0
    exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hlin0)
  have hL_surj : Function.Surjective L :=
    Function.Surjective.of_comp (LinearMap.surjective_of_injective hLT_inj)
  have hker_dim : Module.finrank ℝ (LinearMap.ker L) ≤ j - 1 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker L
    rw [LinearMap.range_eq_top.mpr hL_surj, finrank_top,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrk
    omega
  -- Step 3: `U_j := ker L ⊔ ℝ · 1` has `finrank ≤ j` and contains `indR K` for all tier-`j` subsets `K`
  let oneVec : Q → ℝ := fun _ => 1
  let U_j : Submodule ℝ (Q → ℝ) := LinearMap.ker L ⊔ Submodule.span ℝ {oneVec}
  have hUj_dim : Module.finrank ℝ U_j ≤ j := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker L) (Submodule.span ℝ {oneVec})
    have h1 : Module.finrank ℝ (Submodule.span ℝ {oneVec}) ≤ 1 := by
      simpa using finrank_span_le_card ({oneVec} : Set (Q → ℝ))
    dsimp only [U_j]
    omega
  let Tset : Finset (Finset Q) := Finset.univ.filter (fun K =>
    K.Nonempty ∧ K ≠ Finset.univ ∧
    ∀ w : List α, w.length ≤ n - j → ∑ p ∈ A.preimage K w, P.π p = ∑ q ∈ K, P.π q)
  let Gset : Finset (Finset Q) := Finset.univ.filter (fun K => TwoValueStationary.indR K - 0 ∈ U_j)
  have hG_le : Gset.card ≤ 2 ^ j := TwoValueStationary.subspace_zeroOne_card_le j U_j 0 hUj_dim
  have hsum_pos : 0 < ∑ q : Q, P.π q :=
    Finset.sum_pos (fun q _ => P.hπ_pos q) (Finset.univ_nonempty_iff.mpr hSync.nonempty)
  have hT_sub_G : Tset ⊆ Gset := by
    intro K hK
    rcases (Finset.mem_filter.mp hK).2 with ⟨_, _, hinv⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ K, ?_⟩
    rw [sub_zero]
    let c : ℝ := (∑ q ∈ K, P.π q) / (∑ q : Q, P.π q)
    let f : Q → ℝ := TwoValueStationary.indR K - c • oneVec
    have hf_ker : f ∈ LinearMap.ker L := by
      have hVd_sub : V d ≤ LinearMap.ker (TwoValueStationary.dotLinR f) := by
        rw [Submodule.span_le]
        rintro v ⟨w, hw, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        dsimp only [TwoValueStationary.dotLinR, LinearMap.coe_mk, AddHom.coe_mk]
        have hcomm : (∑ q : Q, f q * TwoValueStationary.pushR A w P.π q) =
            ∑ q : Q, TwoValueStationary.pushR A w P.π q * f q :=
          Finset.sum_congr rfl fun q _ => mul_comm _ _
        rw [hcomm, TwoValueStationary.pushR_dot]
        have hsplit_f : (∑ p : Q, P.π p * f (A.eval p w)) =
            (∑ p ∈ A.preimage K w, P.π p) - c * (∑ p : Q, P.π p) := by
          have h1 : (∑ p : Q, P.π p * f (A.eval p w)) =
              (∑ p : Q, if A.eval p w ∈ K then P.π p else 0) -
              ∑ p : Q, P.π p * c := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun p _ => ?_
            dsimp only [f, TwoValueStationary.indR, oneVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            split_ifs <;> ring
          rw [h1, ← Finset.sum_filter, ← Finset.sum_mul, mul_comm _ c]
          congr 1
        rw [hsplit_f, hinv w hw]
        dsimp only [c]
        rw [div_mul_cancel₀ _ (ne_of_gt hsum_pos), sub_self]
      rw [LinearMap.mem_ker]
      ext i
      have hbi := hVd_sub (b i).2
      rw [LinearMap.mem_ker] at hbi
      dsimp only [L, TwoValueStationary.dotLinR, LinearMap.coe_mk, AddHom.coe_mk] at hbi ⊢
      calc ∑ q : Q, (b i).1 q * f q
          = ∑ q : Q, f q * (b i).1 q := Finset.sum_congr rfl fun q _ => mul_comm _ _
        _ = 0 := hbi
    have hdecomp : TwoValueStationary.indR K = f + c • oneVec := by
      ext q; simp [f]
    rw [hdecomp]
    exact Submodule.add_mem_sup hf_ker (Submodule.smul_mem _ c (Submodule.subset_span rfl))
  have hemp_G : (∅ : Finset Q) ∈ Gset := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h0 : TwoValueStationary.indR (∅ : Finset Q) - 0 = 0 := by ext q; simp [TwoValueStationary.indR]
    rw [h0]; exact U_j.zero_mem
  have huniv_G : (Finset.univ : Finset Q) ∈ Gset := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h1 : TwoValueStationary.indR (Finset.univ : Finset Q) - 0 = oneVec := by
      ext q; simp [TwoValueStationary.indR, oneVec]
    rw [h1]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  have hemp_ne_univ : (∅ : Finset Q) ≠ Finset.univ := by
    intro h; have := congrArg Finset.card h
    simp only [Finset.card_empty, Finset.card_univ] at this; omega
  have hdisj : Disjoint Tset ({∅, Finset.univ} : Finset (Finset Q)) := by
    refine Finset.disjoint_right.mpr fun K hK hKT => ?_
    rcases (Finset.mem_filter.mp hKT).2 with ⟨hKne, hKnu, _⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl
    · exact Finset.not_nonempty_empty hKne
    · exact hKnu rfl
  have hunion_sub : Tset ∪ ({∅, Finset.univ} : Finset (Finset Q)) ⊆ Gset := by
    refine Finset.union_subset hT_sub_G ?_
    intro K hK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl
    · exact hemp_G
    · exact huniv_G
  have hcard := Finset.card_le_card hunion_sub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair hemp_ne_univ] at hcard
  have hT_le : Tset.card ≤ 2 ^ j - 2 := by omega
  simpa only [Tset, n] using hT_le

/-- **Theorem T(1) (Master Super-Eulerian Tier Inequality)**:
For ANY synchronizing `n`-state DFA (`n ≥ 2`) admitting positive letter weights and a positive
**integer** stationary vector `w_int : Q → ℕ` (`∀ q, 1 ≤ w_int q`, `P.π q = w_int q`), letting
`J := (∑ q, w_int q) - Finset.univ.sup w_int`, for EVERY `1 ≤ t ≤ n`:
`rt(A) ≤ J * (n - t) + 2^(t + 1) - 2*t - 2`! -/
theorem superEulerian_tier_bound {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (hn2 : 2 ≤ Fintype.card Q)
    (w_int : Q → ℕ) (_hw_pos : ∀ q : Q, 1 ≤ w_int q)
    (hπ : ∀ q : Q, P.π q = (w_int q : ℝ))
    (t : ℕ) (ht1 : 1 ≤ t) (htn : t ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ ((∑ q : Q, w_int q) - Finset.univ.sup w_int) * (Fintype.card Q - t) +
        2 ^ (t + 1) - 2 * t - 2 := by
  classical
  set n := Fintype.card Q
  let hasNe : Finset Q → Prop := fun K =>
    ∃ d : ℕ, ∃ w : List α, w.length = d ∧ ∑ p ∈ A.preimage K w, P.π p ≠ ∑ q ∈ K, P.π q
  let mPi : Finset Q → ℕ := fun K => if h : hasNe K then Nat.find h else 0
  have hmPi_spec : ∀ K : Finset Q, K.Nonempty → K ≠ Finset.univ →
      mPi K ≤ n - 1 ∧
      (∃ w : List α, w.length ≤ mPi K ∧ ∑ q ∈ K, P.π q < ∑ p ∈ A.preimage K w, P.π p) ∧
      (∀ w : List α, w.length < mPi K → ∑ p ∈ A.preimage K w, P.π p = ∑ q ∈ K, P.π q) := by
    intro K hKne hKnu
    have hKlt : K.card < n := by
      simpa [n] using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hKnu)
    obtain ⟨u0, hu0_len, hu0_ne⟩ := TwoValueStationary.steinberg_exists_ne hSync P K hKne hKlt
    have hEx : hasNe K := ⟨u0.length, u0, rfl, hu0_ne⟩
    have hm_eq : mPi K = Nat.find hEx := by simp only [mPi, hEx, ↓reduceDIte]
    have hm_le : mPi K ≤ n - 1 := by
      rw [hm_eq]; exact (Nat.find_min' hEx ⟨u0, rfl, hu0_ne⟩).trans hu0_len
    obtain ⟨u, hu_len, hu_ne⟩ := Nat.find_spec hEx
    obtain ⟨w, hw_len, hw_gt⟩ := TwoValueStationary.exists_gt_of_ne P K u hu_ne
    refine ⟨hm_le, ⟨w, by omega, hw_gt⟩, fun v hv => ?_⟩
    by_contra hne
    rw [hm_eq] at hv
    exact Nat.find_min hEx hv ⟨v, rfl, hne⟩
  -- Strong induction on remaining integer measure `(∑ q, w_int q) - (∑ q ∈ S, w_int q)`
  let totalW : ℕ := ∑ q : Q, w_int q
  have hpi_nat : ∀ S : Finset Q, ∑ q ∈ S, P.π q = ((∑ q ∈ S, w_int q : ℕ) : ℝ) := by
    intro S; simp only [hπ, Nat.cast_sum]
  have hreach : ∀ (rem : ℕ) (S : Finset Q), S.Nonempty →
      totalW - (∑ q ∈ S, w_int q) ≤ rem →
      ∃ (v : List α) (seq : Finset (Finset Q)),
        A.preimage S v = Finset.univ ∧
        seq.card ≤ totalW - (∑ q ∈ S, w_int q) ∧
        (∀ K ∈ seq, K.Nonempty ∧ K ≠ Finset.univ ∧ ∑ q ∈ S, w_int q ≤ ∑ q ∈ K, w_int q) ∧
        v.length ≤ ∑ K ∈ seq, mPi K := by
    intro rem
    induction rem with
    | zero =>
        intro S hSne hrem
        have hS_univ : S = Finset.univ := by
          by_contra hnu
          have hsub : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hnu
          obtain ⟨q₀, _, hq₀S⟩ := Finset.exists_of_ssubset hsub
          have hle : ∑ q ∈ S, w_int q + w_int q₀ ≤ totalW := by
            have h1 := Finset.sum_le_sum_of_subset (f := w_int)
              (Finset.insert_subset (Finset.mem_univ q₀) (Finset.subset_univ S))
            rw [Finset.sum_insert hq₀S] at h1
            dsimp only [totalW]; omega
          have := _hw_pos q₀
          omega
        exact ⟨[], ∅, by simp [hS_univ, DFA.preimage_nil], by simp, by simp, by simp⟩
    | succ rem ih =>
        intro S hSne hrem
        by_cases hS_univ : S = Finset.univ
        · exact ⟨[], ∅, by simp [hS_univ, DFA.preimage_nil], by simp, by simp, by simp⟩
        · obtain ⟨_, ⟨w, hw_len, hw_gt⟩, _⟩ := hmPi_spec S hSne hS_univ
          set S' := A.preimage S w
          have hS'_gt_nat : ∑ q ∈ S, w_int q < ∑ q ∈ S', w_int q := by
            rw [hpi_nat S, hpi_nat S'] at hw_gt
            exact_mod_cast hw_gt
          have hS'_ne : S'.Nonempty := by
            by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
            rw [hemp, Finset.sum_empty] at hS'_gt_nat; omega
          have hS'_le_tot : ∑ q ∈ S', w_int q ≤ totalW :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ S')
          obtain ⟨v', seq', hv'_full, hseq'_card, hseq'_prop, hv'_len⟩ :=
            ih S' hS'_ne (by omega)
          have hS_notmem : S ∉ seq' := fun hmem => by
            have := (hseq'_prop S hmem).2.2; omega
          refine ⟨v' ++ w, insert S seq', ?_, ?_, ?_, ?_⟩
          · rw [DFA.preimage_append]; exact hv'_full
          · rw [Finset.card_insert_of_notMem hS_notmem]; omega
          · intro K hK
            rcases Finset.mem_insert.mp hK with rfl | hK'
            · exact ⟨hSne, hS_univ, le_rfl⟩
            · have hp := hseq'_prop K hK'
              exact ⟨hp.1, hp.2.1, by omega⟩
          · rw [List.length_append, Finset.sum_insert hS_notmem]; omega
  -- Start from `{qStar}` maximizing `w_int`
  obtain ⟨qStar, _, hqStar⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset Q) (Finset.univ_nonempty_iff.mpr hSync.nonempty) w_int
  have hJ_eq : totalW - (∑ q ∈ ({qStar} : Finset Q), w_int q) = totalW - Finset.univ.sup w_int := by
    rw [Finset.sum_singleton, hqStar]
  obtain ⟨v, seq, hv_full, hseq_card, hseq_prop, hv_len⟩ :=
    hreach (totalW - Finset.univ.sup w_int) {qStar} (Finset.singleton_nonempty qStar) (by omega)
  -- Swap sums via `tier_telescope_le` + `szykula_tier_lemma`!
  have hsum_bound : ∑ K ∈ seq, mPi K ≤
      seq.card * (n - t) + ∑ j ∈ Finset.Icc 2 t, (2 ^ j - 2) := by
    calc ∑ K ∈ seq, mPi K
        ≤ ∑ K ∈ seq, ((n - t) + ∑ j ∈ Finset.Icc 2 t, if n - j + 1 ≤ mPi K then 1 else 0) :=
            Finset.sum_le_sum fun K hK =>
              TwoValueStationary.tier_telescope_le n t ht1 htn (mPi K)
                (hmPi_spec K (hseq_prop K hK).1 (hseq_prop K hK).2.1).1
      _ = seq.card * (n - t) +
            ∑ K ∈ seq, ∑ j ∈ Finset.Icc 2 t, if n - j + 1 ≤ mPi K then 1 else 0 := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      _ = seq.card * (n - t) +
            ∑ j ∈ Finset.Icc 2 t, ∑ K ∈ seq, if n - j + 1 ≤ mPi K then 1 else 0 := by
            rw [Finset.sum_comm]
      _ ≤ seq.card * (n - t) + ∑ j ∈ Finset.Icc 2 t, (2 ^ j - 2) := by
            refine Nat.add_le_add_left (Finset.sum_le_sum fun j hj => ?_) _
            have hj_bounds := Finset.mem_Icc.mp hj
            rw [Finset.sum_boole, Nat.cast_id]
            have hsub : seq.filter (fun K => n - j + 1 ≤ mPi K) ⊆
                Finset.univ.filter (fun K : Finset Q =>
                  K.Nonempty ∧ K ≠ Finset.univ ∧
                  ∀ w : List α, w.length ≤ n - j → ∑ p ∈ A.preimage K w, P.π p = ∑ q ∈ K, P.π q) := by
              intro K hK
              rcases Finset.mem_filter.mp hK with ⟨hKseq, hKm⟩
              have hp := hseq_prop K hKseq
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ K, hp.1, hp.2.1, fun w hw => ?_⟩
              exact (hmPi_spec K hp.1 hp.2.1).2.2 w (by omega)
            exact (Finset.card_le_card hsub).trans
              (szykula_tier_lemma A hSync P hn2 j (by omega) (by omega))
  rw [TwoValueStationary.sum_Icc_two_pow_sub_two t ht1] at hsum_bound
  have hpow_ge := TwoValueStationary.two_mul_add_two_le_pow t ht1
  have hcard_J : seq.card ≤ totalW - Finset.univ.sup w_int := by omega
  have hmul_le : seq.card * (n - t) ≤ (totalW - Finset.univ.sup w_int) * (n - t) :=
    Nat.mul_le_mul_right _ hcard_J
  refine ⟨v, ⟨qStar, fun q => by
    have hq : q ∈ A.preimage {qStar} v := hv_full ▸ Finset.mem_univ q
    simpa [DFA.mem_preimage] using hq⟩, ?_⟩
  dsimp only [totalW, n] at hsum_bound hmul_le ⊢
  omega

/-- **Theorem T(2) (EXACT Černý Conjecture `(n - 1)^2` for Arbitrary Constant Excess `E ≥ 1`)**:
Whenever `J := (∑ q, w_int q) - max_q w_int q ≤ n - 1 + E` (`E ≥ 1`) and
`n ≥ 2 ^ (E + 3) - E ^ 2 - 3 * E - 5`, setting `t := E + 2` in `superEulerian_tier_bound`
proves the **exact Černý bound `rt(A) ≤ (n - 1)^2`**! -/
theorem superEulerian_const_excess_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (w_int : Q → ℕ) (hw_pos : ∀ q : Q, 1 ≤ w_int q)
    (hπ : ∀ q : Q, P.π q = (w_int q : ℝ))
    (E : ℕ) (hE : 1 ≤ E)
    (hJ : (∑ q : Q, w_int q) - Finset.univ.sup w_int ≤ Fintype.card Q - 1 + E)
    (hn : 2 ^ (E + 3) - E ^ 2 - 3 * E - 5 ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  set n := Fintype.card Q
  have hpow_ge := TwoValueStationary.const_excess_pow_ge E hE
  have htn : E + 2 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨w, hw_sync, hw_len⟩ :=
    superEulerian_tier_bound A hSync P hn2 w_int hw_pos hπ (E + 2) (by omega) htn
  refine ⟨w, hw_sync, ?_⟩
  have hJ_mul : ((∑ q : Q, w_int q) - Finset.univ.sup w_int) * (n - (E + 2)) ≤
      (n - 1 + E) * (n - (E + 2)) := Nat.mul_le_mul_right _ hJ
  have hpow_t := TwoValueStationary.two_mul_add_two_le_pow (E + 2) (by omega)
  have hstep1 : w.length ≤ (n - 1 + E) * (n - (E + 2)) + 2 ^ (E + 3) - 2 * (E + 2) - 2 := by
    have : E + 2 + 1 = E + 3 := by omega
    rw [this] at hw_len
    change w.length ≤ ((∑ q : Q, w_int q) - Finset.univ.sup w_int) * (n - (E + 2)) +
      2 ^ (E + 3) - 2 * (E + 2) - 2 at hw_len
    omega
  have hle1 : E ^ 2 + 3 * E + 5 ≤ 2 ^ (E + 3) := by omega
  have hle2 : 2 * (E + 2) + 2 ≤ 2 ^ (E + 3) := by omega
  zify [show 1 ≤ n by omega, htn, show E ^ 2 ≤ 2 ^ (E + 3) by omega,
    show 3 * E ≤ 2 ^ (E + 3) - E ^ 2 by omega,
    show 5 ≤ 2 ^ (E + 3) - E ^ 2 - 3 * E by omega,
    show 2 * (E + 2) ≤ (n - 1 + E) * (n - (E + 2)) + 2 ^ (E + 3) by omega,
    show 2 ≤ (n - 1 + E) * (n - (E + 2)) + 2 ^ (E + 3) - 2 * (E + 2) by omega] at hn hstep1 ⊢
  nlinarith only [hn, hstep1]

/-- **Theorem T(2a) (`E = 1`, `J ≤ n`, `n ≥ 7`, incl. Goel `cor:integer` & `k = 2, α₀ = 2`)**:
`rt(A) ≤ n ^ 2 - 3 * n + 8 ≤ (n - 1) ^ 2`! -/
theorem superEulerian_excess_one_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (w_int : Q → ℕ) (hw_pos : ∀ q : Q, 1 ≤ w_int q)
    (hπ : ∀ q : Q, P.π q = (w_int q : ℝ))
    (hJ : (∑ q : Q, w_int q) - Finset.univ.sup w_int ≤ Fintype.card Q)
    (hn7 : 7 ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ Fintype.card Q ^ 2 - 3 * Fintype.card Q + 8 ∧
      w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  set n := Fintype.card Q
  obtain ⟨w, hw_sync, hw_len⟩ :=
    superEulerian_tier_bound A hSync P (by omega) w_int hw_pos hπ 3 (by omega) (by omega)
  have hmul : ((∑ q : Q, w_int q) - Finset.univ.sup w_int) * (n - 3) ≤ n * (n - 3) :=
    Nat.mul_le_mul_right _ hJ
  have h1 : w.length ≤ n * (n - 3) + 8 := by
    change w.length ≤ ((∑ q : Q, w_int q) - Finset.univ.sup w_int) * (n - 3) + 2 ^ (3 + 1) - 2 * 3 - 2 at hw_len
    norm_num at hw_len; omega
  have h3n : 3 * n ≤ n ^ 2 := by nlinarith
  refine ⟨w, hw_sync, ?_, ?_⟩
  · zify [show 3 ≤ n by omega, h3n] at h1 ⊢; nlinarith only [h1]
  · zify [show 1 ≤ n by omega, show 3 ≤ n by omega] at h1 ⊢
    have hn7_z : (7 : ℤ) ≤ (n : ℤ) := by omega
    nlinarith only [h1, hn7_z]

/-- **Theorem T(2b) (`E = 2`, `J ≤ n + 1`, `n ≥ 17`, incl. `k = 2, α₀ = 3` & `k = 3, α₀ = 2`)**:
Exact Černý `rt(A) ≤ (n - 1) ^ 2`! -/
theorem superEulerian_excess_two_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (w_int : Q → ℕ) (hw_pos : ∀ q : Q, 1 ≤ w_int q)
    (hπ : ∀ q : Q, P.π q = (w_int q : ℝ))
    (hJ : (∑ q : Q, w_int q) - Finset.univ.sup w_int ≤ Fintype.card Q + 1)
    (hn17 : 17 ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  superEulerian_const_excess_cerny A hSync P w_int hw_pos hπ 2 (by omega) (by omega) (by norm_num; omega)

/-- **Theorem T(2c) (`E = 3`, `J ≤ n + 2`, `n ≥ 41`, incl. `k = 2, α₀ = 4` & `k = 4, α₀ = 2`)**:
Exact Černý `rt(A) ≤ (n - 1) ^ 2`! -/
theorem superEulerian_excess_three_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (w_int : Q → ℕ) (hw_pos : ∀ q : Q, 1 ≤ w_int q)
    (hπ : ∀ q : Q, P.π q = (w_int q : ℝ))
    (hJ : (∑ q : Q, w_int q) - Finset.univ.sup w_int ≤ Fintype.card Q + 2)
    (hn41 : 41 ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  superEulerian_const_excess_cerny A hSync P w_int hw_pos hπ 3 (by omega) (by omega) (by norm_num; omega)

/-- **Theorem T(3) (EXACT Černý `(n - 1)^2` up to Logarithmic Excess `J ≤ n + ⌊log₂ n⌋ - 4`)**:
For EVERY synchronizing `n`-state DFA (`n ≥ 32`) with positive integer stationary vector `w_int`
satisfying `(∑ q, w_int q) - max_q w_int q ≤ n + Nat.log 2 n - 4`, setting `t := Nat.log 2 n - 1`
in `superEulerian_tier_bound` proves the **EXACT Černý Conjecture `rt(A) ≤ (n - 1) ^ 2`**! -/
theorem superEulerian_log_excess_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [Fintype α] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (P : PositiveStationary A)
    (w_int : Q → ℕ) (hw_pos : ∀ q : Q, 1 ≤ w_int q)
    (hπ : ∀ q : Q, P.π q = (w_int q : ℝ))
    (hn32 : 32 ≤ Fintype.card Q)
    (hJ : (∑ q : Q, w_int q) - Finset.univ.sup w_int ≤ Fintype.card Q + Nat.log 2 (Fintype.card Q) - 4) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  set n := Fintype.card Q
  have hlog5 : 5 ≤ Nat.log 2 n := by
    have h1 : Nat.log 2 32 ≤ Nat.log 2 n := Nat.log_mono_right hn32
    have h2 : Nat.log 2 32 = 5 := by decide
    omega
  set t := Nat.log 2 n - 1
  have ht4 : 4 ≤ t := by omega
  have hpow_le_n : 2 ^ (t + 1) ≤ n := by
    have ht1 : t + 1 = Nat.log 2 n := by omega
    rw [ht1]
    exact Nat.pow_log_le_self 2 (by omega)
  have ht_lt_pow := TwoValueStationary.two_mul_add_two_le_pow t (by omega)
  have htn : t ≤ n := by omega
  obtain ⟨w, hw_sync, hw_len⟩ :=
    superEulerian_tier_bound A hSync P (by omega) w_int hw_pos hπ t (by omega) htn
  refine ⟨w, hw_sync, ?_⟩
  have hJ' : (∑ q : Q, w_int q) - Finset.univ.sup w_int ≤ n + t - 3 := by omega
  have hmul : ((∑ q : Q, w_int q) - Finset.univ.sup w_int) * (n - t) ≤ (n + t - 3) * (n - t) :=
    Nat.mul_le_mul_right _ hJ'
  have h1 : w.length ≤ (n + t - 3) * (n - t) + n - 2 * t - 2 := by
    change w.length ≤ ((∑ q : Q, w_int q) - Finset.univ.sup w_int) * (n - t) +
      2 ^ (t + 1) - 2 * t - 2 at hw_len
    omega
  zify [show 1 ≤ n by omega, htn, show 3 ≤ n + t by omega,
    show 2 * t ≤ (n + t - 3) * (n - t) + n by omega,
    show 2 ≤ (n + t - 3) * (n - t) + n - 2 * t by omega] at h1 ⊢
  have ht4_z : (4 : ℤ) ≤ (t : ℤ) := by omega
  nlinarith only [h1, ht4_z]

end Cerny
