import Cerny.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Alpöge-Method Two-Letter Spectral Theta Lifts (Theorems D₀ & D — Breaching Obstruction O.3!)

This file formalizes our pure `ℚ`-linear rank-1 distribution engine (`Theorem D₀`) and its
flagship application (`Theorem D`), which **breaches Obstruction O.3** by proving quadratic
reset bounds (`≤ 3(n - 1)^2` for arbitrary cycle lengths `m₁, m₂` and `≤ 2(n - 1)^2` for equal
cycles `m₁ = m₂`) for **mixing 2-cluster synchronizing automata with arbitrary tree height `ℓ ≥ 0`**
— with ZERO strong-connectivity assumption, ZERO Perron–Frobenius, ZERO complex numbers,
and completely arbitrary additional letters in `α`!

## Main Results
* `Cerny.rankOne_exists_extending_word`: Theorem D₀(2) — any exact rank-1 word distribution `Q_μ = 1 · π`
  of max length `L₁` forces `π`-extension in length `≤ n - 1 + L₁`.
* `Cerny.rankOne_exists_extending_word_ne_half`: Lemma D₀' — universal `dim W₀ ≥ 2` upgrade
  sharpening `rankOne_exists_extending_word` to `≤ n - 2 + L₁` whenever `π(S) ≠ 1 / 2`.
* `Cerny.rankOne_uniform_reset_bound`: Theorem D₀(3) — when `π` is uniform on `C`,
  `rt(A) ≤ ℓ + (|C| - 1) * (n - 1 + L₁)`.
* `Cerny.twoCluster_mixing_reset_bound` & `Cerny.twoCluster_mixing_quadratic_bound`:
  **Theorem D (General `(m₁, m₂)`, arbitrary `ℓ ≥ 0`)**: `rt(A) ≤ ℓ + (m - 1)(n + 2ℓ + 2m - 4) ≤ 3(n - 1)^2`.
* `Cerny.twoCluster_equalCycle_mixing_bound`:
  **Theorem D (Equal cycles `m₁ = m₂`, arbitrary `ℓ ≥ 0`)**: `rt(A) ≤ ℓ + (m - 1)(n + 2ℓ + m - 2) ≤ 2(n - 1)^2`.
-/

namespace Cerny

universe u v w

namespace AlpogeThetaLift

section RankOneEngine

variable {Q : Type u} {α : Type v}

/-- Pullback linear operator `(pullback A w v) q = v (A.eval q w)` on `Q → ℚ`. -/
def pullback (A : DFA Q α) (w : List α) : (Q → ℚ) →ₗ[ℚ] (Q → ℚ) where
  toFun v q := v (A.eval q w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma pullback_nil (A : DFA Q α) (v : Q → ℚ) : pullback A [] v = v := rfl

lemma pullback_append (A : DFA Q α) (u₁ u₂ : List α) (v : Q → ℚ) :
    pullback A (u₁ ++ u₂) v = pullback A u₁ (pullback A u₂ v) := by
  ext q; simp [pullback]

lemma pullback_cons (A : DFA Q α) (a : α) (u : List α) (v : Q → ℚ) :
    pullback A (a :: u) v = pullback A [a] (pullback A u v) :=
  pullback_append A [a] u v

/-- Weighted inner-product linear functional `v ↦ ∑ q, π q * v q` on `Q → ℚ`. -/
def dotLin [Fintype Q] (π : Q → ℚ) : (Q → ℚ) →ₗ[ℚ] ℚ where
  toFun v := ∑ q : Q, π q * v q
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => by ring

lemma finrank_ker_dotLin [Fintype Q] {π : Q → ℚ} (hπ_sum : ∑ q : Q, π q = 1) :
    Module.finrank ℚ (LinearMap.ker (dotLin π)) = Fintype.card Q - 1 := by
  classical
  have hex_nz : ∃ q₀ : Q, π q₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : ∑ q : Q, π q = 0 := Finset.sum_eq_zero fun q _ => hall q
    linarith
  obtain ⟨q₀, hq₀⟩ := hex_nz
  have hsurj : Function.Surjective (dotLin π) := by
    intro c
    refine ⟨Pi.single q₀ (c / π q₀), ?_⟩
    simp only [dotLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single q₀]
    · simp [Pi.single_eq_same, mul_div_cancel₀ _ hq₀]
    · intro q _ hq; simp [Pi.single_eq_of_ne hq]
    · intro h; exact absurd (Finset.mem_univ q₀) h
  have hrn := LinearMap.finrank_range_add_finrank_ker (dotLin π)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, Module.finrank_pi] at hrn
  omega

/-- Centered indicator column vector `γ_S(q) = 1_{q ∈ S} - π(S)`. -/
def centered [DecidableEq Q] (π : Q → ℚ) (S : Finset Q) : Q → ℚ :=
  fun q => (if q ∈ S then (1 : ℚ) else 0) - ∑ x ∈ S, π x

lemma dotLin_pullback_centered [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (π : Q → ℚ) (hπ_sum : ∑ q : Q, π q = 1) (S : Finset Q) (u : List α) :
    dotLin π (pullback A u (centered π S)) =
      (∑ q ∈ A.preimage S u, π q) - ∑ x ∈ S, π x := by
  simp only [dotLin, pullback, centered, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ_sum, one_mul]
  congr 1
  rw [DFA.preimage, Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => by split_ifs <;> ring

lemma dotLin_centered_eq_zero [Fintype Q] [DecidableEq Q]
    (π : Q → ℚ) (hπ_sum : ∑ q : Q, π q = 1) (S : Finset Q) :
    dotLin π (centered π S) = 0 := by
  have h := dotLin_pullback_centered (⟨fun q (_ : Empty) => q⟩ : DFA Q Empty) π hπ_sum S []
  simpa [pullback_nil] using h

end RankOneEngine

end AlpogeThetaLift

/-- **Theorem D₀(2) (Exact Rank-1 Distribution Short `π`-Extension)**:
In any synchronizing `n`-state DFA (NO strong connectivity needed!), if an indexed probability
distribution `(μ, word)` of max length `L₁` has exact rank-1 matrix `Q_μ = 1 · π` with
`supp(π) = C`, then every nonempty proper `S ⊂ C` admits `w` with `|w| ≤ n - 1 + L₁` and
`π(S w⁻¹) > π(S)`. -/
theorem rankOne_exists_extending_word {Q : Type u} {α : Type v} {ι : Type w}
    [Fintype Q] [DecidableEq Q] [Fintype ι]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (C : Finset Q) (π : Q → ℚ) (μ : ι → ℚ) (word : ι → List α) (L₁ : ℕ)
    (hπ_nonneg : ∀ q : Q, 0 ≤ π q)
    (hπ_supp : ∀ q : Q, 0 < π q ↔ q ∈ C)
    (hπ_sum : ∑ q : Q, π q = 1)
    (hμ_nonneg : ∀ i : ι, 0 ≤ μ i)
    (hμ_sum : ∑ i : ι, μ i = 1)
    (hL₁ : ∀ i : ι, 0 < μ i → (word i).length ≤ L₁)
    (hRankOne : ∀ p q : Q, (∑ i : ι, if A.eval p (word i) = q then μ i else 0) = π q)
    {S : Finset Q} (hS_ne : S.Nonempty) (hS_ssub : S ⊂ C) :
    ∃ w : List α, w.length ≤ Fintype.card Q - 1 + L₁ ∧
      (∑ x ∈ S, π x) < ∑ q ∈ A.preimage S w, π q := by
  classical
  -- Step 1: 0 < π(S) < 1
  have hπS_pos : 0 < ∑ x ∈ S, π x := by
    rcases hS_ne with ⟨s₀, hs₀⟩
    have h0 : 0 < π s₀ := (hπ_supp s₀).mpr (hS_ssub.1 hs₀)
    have hle : π s₀ ≤ ∑ x ∈ S, π x :=
      Finset.single_le_sum (fun x _ => hπ_nonneg x) hs₀
    linarith
  have hπS_lt1 : ∑ x ∈ S, π x < 1 := by
    obtain ⟨c₀, hc₀C, hc₀NotS⟩ := Finset.exists_of_ssubset hS_ssub
    have hc₀_pos : 0 < π c₀ := (hπ_supp c₀).mpr hc₀C
    have hsub : insert c₀ S ⊆ Finset.univ := Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hπ_nonneg q)
    rw [Finset.sum_insert hc₀NotS, hπ_sum] at hle
    linarith
  -- Step 2: Pick an active index i₀ with 0 < μ i₀
  have hex_i₀ : ∃ i₀ : ι, 0 < μ i₀ := by
    by_contra hall
    push Not at hall
    have h0 : ∑ i : ι, μ i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (hall i) (hμ_nonneg i)
    linarith
  obtain ⟨i₀, hi₀⟩ := hex_i₀
  -- Step 3: Exact zero expectation for every u : List α!
  have hzero_exp : ∀ u : List α,
      ∑ i : ι, μ i * AlpogeThetaLift.dotLin π
        (AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S)) = 0 := by
    intro u
    have hrew : ∀ i : ι,
        μ i * AlpogeThetaLift.dotLin π
          (AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S)) =
        ∑ p : Q, π p * (μ i * AlpogeThetaLift.centered π S (A.eval (A.eval p u) (word i))) := by
      intro i
      simp only [AlpogeThetaLift.dotLin, AlpogeThetaLift.pullback, LinearMap.coe_mk,
        AddHom.coe_mk, DFA.eval_append, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    simp_rw [hrew]
    rw [Finset.sum_comm]
    have hinner : ∀ p : Q,
        ∑ i : ι, π p * (μ i * AlpogeThetaLift.centered π S (A.eval (A.eval p u) (word i))) = 0 := by
      intro p
      rw [← Finset.mul_sum]
      have hmid :
          ∑ i : ι, μ i * AlpogeThetaLift.centered π S (A.eval (A.eval p u) (word i)) =
          ∑ q : Q, (∑ i : ι, if A.eval (A.eval p u) (word i) = q then μ i else 0) *
            AlpogeThetaLift.centered π S q := by
        have hstep : ∀ i : ι,
            μ i * AlpogeThetaLift.centered π S (A.eval (A.eval p u) (word i)) =
            ∑ q : Q, (if A.eval (A.eval p u) (word i) = q then μ i else 0) *
              AlpogeThetaLift.centered π S q := by
          intro i
          rw [Finset.sum_eq_single (A.eval (A.eval p u) (word i))]
          · simp
          · intro q _ hq; simp [Ne.symm hq]
          · intro h; exact absurd (Finset.mem_univ _) h
        simp_rw [hstep]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => by rw [← Finset.sum_mul]
      rw [hmid]
      have hsum_q :
          ∑ q : Q, (∑ i : ι, if A.eval (A.eval p u) (word i) = q then μ i else 0) *
            AlpogeThetaLift.centered π S q =
          AlpogeThetaLift.dotLin π (AlpogeThetaLift.centered π S) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hRankOne (A.eval p u) q]
      rw [hsum_q, AlpogeThetaLift.dotLin_centered_eq_zero π hπ_sum S, mul_zero]
    exact Finset.sum_eq_zero fun p _ => hinner p
  -- Step 4: Ascending subspace chain in Q → ℚ escaping H = ker (dotLin π)
  let H : Submodule ℚ (Q → ℚ) := LinearMap.ker (AlpogeThetaLift.dotLin π)
  let W : ℕ → Submodule ℚ (Q → ℚ) := fun k =>
    Submodule.span ℚ { v : Q → ℚ | ∃ (u : List α) (i : ι), u.length ≤ k ∧ 0 < μ i ∧
      v = AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S) }
  have hW_mono : ∀ {j k}, j ≤ k → W j ≤ W k := by
    intro j k hjk
    apply Submodule.span_mono
    rintro v ⟨u, i, hu, hi, rfl⟩
    exact ⟨u, i, hu.trans hjk, hi, rfl⟩
  have hW0_dim : 1 ≤ Module.finrank ℚ (W 0) := by
    let v₀ := AlpogeThetaLift.pullback A ([] ++ word i₀) (AlpogeThetaLift.centered π S)
    have hv₀_mem : v₀ ∈ W 0 := Submodule.subset_span ⟨[], i₀, le_rfl, hi₀, rfl⟩
    have hv₀_ne : v₀ ≠ 0 := by
      obtain ⟨p₀⟩ := hSync.nonempty
      intro hzero
      have hval := congrFun hzero p₀
      simp only [v₀, AlpogeThetaLift.pullback, AlpogeThetaLift.centered, LinearMap.coe_mk,
        AddHom.coe_mk, Pi.zero_apply] at hval
      split_ifs at hval <;> linarith
    have hbot : (⊥ : Submodule ℚ (Q → ℚ)) < W 0 := by
      rw [bot_lt_iff_ne_bot]
      intro hb; rw [hb, Submodule.mem_bot] at hv₀_mem; exact hv₀_ne hv₀_mem
    have hlt := Submodule.finrank_lt_finrank_of_lt hbot
    rw [finrank_bot] at hlt
    omega
  -- Escape from H via synchronization (NO strong connectivity needed!)
  rcases hSync with ⟨w_sync, q₀, hq₀⟩
  have hsync_notH :
      AlpogeThetaLift.pullback A (w_sync ++ word i₀) (AlpogeThetaLift.centered π S) ∉ H := by
    intro hmem
    change AlpogeThetaLift.dotLin π
      (AlpogeThetaLift.pullback A (w_sync ++ word i₀) (AlpogeThetaLift.centered π S)) = 0 at hmem
    have hconst : ∀ p : Q,
        AlpogeThetaLift.pullback A (w_sync ++ word i₀) (AlpogeThetaLift.centered π S) p =
        AlpogeThetaLift.centered π S (A.eval q₀ (word i₀)) := by
      intro p
      simp only [AlpogeThetaLift.pullback, LinearMap.coe_mk, AddHom.coe_mk, DFA.eval_append, hq₀ p]
    simp only [AlpogeThetaLift.dotLin, LinearMap.coe_mk, AddHom.coe_mk] at hmem
    simp_rw [hconst, ← Finset.sum_mul, hπ_sum, one_mul] at hmem
    simp only [AlpogeThetaLift.centered] at hmem
    split_ifs at hmem <;> linarith
  have hex_esc : ∃ k : ℕ, ¬ (W k ≤ H) :=
    ⟨w_sync.length, fun hle => hsync_notH (hle (Submodule.subset_span ⟨w_sync, i₀, le_rfl, hi₀, rfl⟩))⟩
  let k₀ := Nat.find hex_esc
  have hk₀_not : ¬ (W k₀ ≤ H) := Nat.find_spec hex_esc
  have hk₀_min : ∀ j < k₀, W j ≤ H := fun j hj => not_not.mp (Nat.find_min hex_esc hj)
  have hk₀_le : k₀ ≤ Fintype.card Q - 1 := by
    by_cases hk0 : k₀ = 0
    · omega
    · have hstrict : ∀ j, j + 1 < k₀ → W j < W (j + 1) := by
        intro j hj
        refine lt_of_le_of_ne (hW_mono (Nat.le_succ j)) fun heq => ?_
        have hclosed : ∀ (g : α) (v : Q → ℚ), v ∈ W j → AlpogeThetaLift.pullback A [g] v ∈ W j := by
          intro g v hv
          rw [heq]
          induction hv using Submodule.span_induction with
          | mem x hx =>
            rcases hx with ⟨u, i, hu, hi, rfl⟩
            rw [← AlpogeThetaLift.pullback_cons]
            exact Submodule.subset_span ⟨g :: u, i, by simp; omega, hi, rfl⟩
          | zero => simp
          | add x y _ _ hx hy => rw [map_add]; exact (W (j + 1)).add_mem hx hy
          | smul c x _ hx => rw [map_smul]; exact (W (j + 1)).smul_mem c hx
        have hall : ∀ (u : List α) (i : ι), 0 < μ i →
            AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S) ∈ W j := by
          intro u
          induction u with
          | nil =>
            intro i hi
            exact Submodule.subset_span ⟨[], i, Nat.zero_le j, hi, rfl⟩
          | cons g u ih =>
            intro i hi
            rw [List.cons_append, AlpogeThetaLift.pullback_cons]
            exact hclosed g _ (ih i hi)
        exact hsync_notH (hk₀_min j (by omega) (hall w_sync i₀ hi₀))
      have hdim : ∀ j ≤ k₀ - 1, j + 1 ≤ Module.finrank ℚ (W j) := by
        intro j
        induction j with
        | zero => intro _; exact hW0_dim
        | succ j ih =>
          intro hj
          have ih' := ih (by omega)
          have hlt := Submodule.finrank_lt_finrank_of_lt (hstrict j (by omega))
          omega
      have h1 := hdim (k₀ - 1) le_rfl
      have h2 : Module.finrank ℚ (W (k₀ - 1)) ≤ Module.finrank ℚ H :=
        Submodule.finrank_mono (hk₀_min (k₀ - 1) (by omega))
      rw [AlpogeThetaLift.finrank_ker_dotLin hπ_sum] at h2
      omega
  -- Step 5: Extract generator (u, i₁) outside H, then use zero expectation to get > 0!
  have hex_gen : ∃ (u : List α) (i₁ : ι), u.length ≤ k₀ ∧ 0 < μ i₁ ∧
      AlpogeThetaLift.dotLin π
        (AlpogeThetaLift.pullback A (u ++ word i₁) (AlpogeThetaLift.centered π S)) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hk₀_not
    rw [Submodule.span_le]
    rintro v ⟨u, i, hu, hi, rfl⟩
    exact hall u i hu hi
  rcases hex_gen with ⟨u, i₁, hulen, hi₁_pos, hi₁_nz⟩
  have hex_pos : ∃ i' : ι, 0 < μ i' ∧
      0 < AlpogeThetaLift.dotLin π
        (AlpogeThetaLift.pullback A (u ++ word i') (AlpogeThetaLift.centered π S)) := by
    by_contra hall
    push Not at hall
    have hnonpos : ∀ i : ι,
        μ i * AlpogeThetaLift.dotLin π
          (AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S)) ≤ 0 := by
      intro i
      by_cases hi : 0 < μ i
      · exact mul_nonpos_of_nonneg_of_nonpos hi.le (hall i hi)
      · have h0 : μ i = 0 := le_antisymm (not_lt.mp hi) (hμ_nonneg i)
        rw [h0, zero_mul]
    have hlt_i₁ :
        μ i₁ * AlpogeThetaLift.dotLin π
          (AlpogeThetaLift.pullback A (u ++ word i₁) (AlpogeThetaLift.centered π S)) < 0 :=
      mul_neg_of_pos_of_neg hi₁_pos (lt_of_le_of_ne (hall i₁ hi₁_pos) hi₁_nz)
    have hsum_lt :
        ∑ i : ι, μ i * AlpogeThetaLift.dotLin π
          (AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S)) <
        ∑ _i : ι, (0 : ℚ) :=
      Finset.sum_lt_sum (fun i _ => hnonpos i) ⟨i₁, Finset.mem_univ i₁, hlt_i₁⟩
    rw [hzero_exp u, Finset.sum_const_zero] at hsum_lt
    exact lt_irrefl _ hsum_lt
  rcases hex_pos with ⟨i', hi'_pos, hi'_gt⟩
  rw [AlpogeThetaLift.dotLin_pullback_centered A π hπ_sum S (u ++ word i')] at hi'_gt
  refine ⟨u ++ word i', ?_, by linarith⟩
  rw [List.length_append]
  have hli' := hL₁ i' hi'_pos
  omega

/-- **Lemma D₀' (Universal `π(S) ≠ 1/2` Dimension-2 Upgrade for Exact Rank-1 Theta Lifts)**:
Under the exact hypotheses of `rankOne_exists_extending_word`, whenever `∑ x ∈ S, π x ≠ 1 / 2`,
the initial subspace `W 0 ⊆ ker (dotLin π)` has `finrank ≥ 2`, strictly sharpening the
extending-word bound from `n - 1 + L₁` to **`n - 2 + L₁`**! -/
theorem rankOne_exists_extending_word_ne_half {Q : Type u} {α : Type v} {ι : Type w}
    [Fintype Q] [DecidableEq Q] [Fintype ι]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (C : Finset Q) (π : Q → ℚ) (μ : ι → ℚ) (word : ι → List α) (L₁ : ℕ)
    (hπ_nonneg : ∀ q : Q, 0 ≤ π q)
    (hπ_supp : ∀ q : Q, 0 < π q ↔ q ∈ C)
    (hπ_sum : ∑ q : Q, π q = 1)
    (hμ_nonneg : ∀ i : ι, 0 ≤ μ i)
    (hμ_sum : ∑ i : ι, μ i = 1)
    (hL₁ : ∀ i : ι, 0 < μ i → (word i).length ≤ L₁)
    (hRankOne : ∀ p q : Q, (∑ i : ι, if A.eval p (word i) = q then μ i else 0) = π q)
    {S : Finset Q} (hS_ne : S.Nonempty) (hS_ssub : S ⊂ C)
    (hπS_ne_half : ∑ x ∈ S, π x ≠ (1 : ℚ) / 2) :
    ∃ w : List α, w.length ≤ Fintype.card Q - 2 + L₁ ∧
      (∑ x ∈ S, π x) < ∑ q ∈ A.preimage S w, π q := by
  classical
  set p : ℚ := ∑ x ∈ S, π x
  have hπS_pos : 0 < p := by
    rcases hS_ne with ⟨s₀, hs₀⟩
    have h0 : 0 < π s₀ := (hπ_supp s₀).mpr (hS_ssub.1 hs₀)
    have hle : π s₀ ≤ p := Finset.single_le_sum (fun x _ => hπ_nonneg x) hs₀
    linarith
  have hπS_lt1 : p < 1 := by
    obtain ⟨c₀, hc₀C, hc₀NotS⟩ := Finset.exists_of_ssubset hS_ssub
    have hc₀_pos : 0 < π c₀ := (hπ_supp c₀).mpr hc₀C
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (insert c₀ S)) (fun q _ _ => hπ_nonneg q)
    rw [Finset.sum_insert hc₀NotS, hπ_sum] at hle
    linarith
  have hex_i₀ : ∃ i₀ : ι, 0 < μ i₀ := by
    by_contra hall
    push Not at hall
    have h0 : ∑ i : ι, μ i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (hall i) (hμ_nonneg i)
    linarith
  obtain ⟨i₀, hi₀⟩ := hex_i₀
  -- Pointwise zero expectation at every state `q`
  have hpt_zero : ∀ q : Q,
      ∑ i : ι, μ i * AlpogeThetaLift.centered π S (A.eval q (word i)) = 0 := by
    intro q
    have hmid :
        ∑ i : ι, μ i * AlpogeThetaLift.centered π S (A.eval q (word i)) =
        ∑ r : Q, (∑ i : ι, if A.eval q (word i) = r then μ i else 0) *
          AlpogeThetaLift.centered π S r := by
      have hstep : ∀ i : ι,
          μ i * AlpogeThetaLift.centered π S (A.eval q (word i)) =
          ∑ r : Q, (if A.eval q (word i) = r then μ i else 0) *
            AlpogeThetaLift.centered π S r := by
        intro i
        rw [Finset.sum_eq_single (A.eval q (word i))]
        · simp
        · intro r _ hr; simp [Ne.symm hr]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [hstep]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => by rw [← Finset.sum_mul]
    rw [hmid]
    have hsum_r :
        ∑ r : Q, (∑ i : ι, if A.eval q (word i) = r then μ i else 0) *
          AlpogeThetaLift.centered π S r =
        AlpogeThetaLift.dotLin π (AlpogeThetaLift.centered π S) :=
      Finset.sum_congr rfl fun r _ => by rw [hRankOne q r]
    rw [hsum_r, AlpogeThetaLift.dotLin_centered_eq_zero π hπ_sum S]
  have hzero_exp : ∀ u : List α,
      ∑ i : ι, μ i * AlpogeThetaLift.dotLin π
        (AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S)) = 0 := by
    intro u
    have hrew : ∀ i : ι,
        μ i * AlpogeThetaLift.dotLin π
          (AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S)) =
        ∑ q : Q, π q * (μ i * AlpogeThetaLift.centered π S (A.eval (A.eval q u) (word i))) := by
      intro i
      simp only [AlpogeThetaLift.dotLin, AlpogeThetaLift.pullback, LinearMap.coe_mk,
        AddHom.coe_mk, DFA.eval_append, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => by ring
    simp_rw [hrew]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [← Finset.mul_sum, hpt_zero (A.eval q u), mul_zero]
  let H : Submodule ℚ (Q → ℚ) := LinearMap.ker (AlpogeThetaLift.dotLin π)
  let W : ℕ → Submodule ℚ (Q → ℚ) := fun k =>
    Submodule.span ℚ { v : Q → ℚ | ∃ (u : List α) (i : ι), u.length ≤ k ∧ 0 < μ i ∧
      v = AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S) }
  have hW_mono : ∀ {j k}, j ≤ k → W j ≤ W k := by
    intro j k hjk
    apply Submodule.span_mono
    rintro v ⟨u, i, hu, hi, rfl⟩
    exact ⟨u, i, hu.trans hjk, hi, rfl⟩
  rcases hSync with ⟨w_sync, q₀, hq₀⟩
  have hsync_notH :
      AlpogeThetaLift.pullback A (w_sync ++ word i₀) (AlpogeThetaLift.centered π S) ∉ H := by
    intro hmem
    change AlpogeThetaLift.dotLin π
      (AlpogeThetaLift.pullback A (w_sync ++ word i₀) (AlpogeThetaLift.centered π S)) = 0 at hmem
    have hconst : ∀ q : Q,
        AlpogeThetaLift.pullback A (w_sync ++ word i₀) (AlpogeThetaLift.centered π S) q =
        AlpogeThetaLift.centered π S (A.eval q₀ (word i₀)) := by
      intro q
      simp only [AlpogeThetaLift.pullback, LinearMap.coe_mk, AddHom.coe_mk, DFA.eval_append, hq₀ q]
    simp only [AlpogeThetaLift.dotLin, LinearMap.coe_mk, AddHom.coe_mk] at hmem
    simp_rw [hconst, ← Finset.sum_mul, hπ_sum, one_mul] at hmem
    simp only [AlpogeThetaLift.centered] at hmem
    split_ifs at hmem <;> linarith
  have hex_esc : ∃ k : ℕ, ¬ (W k ≤ H) :=
    ⟨w_sync.length, fun hle => hsync_notH (hle (Submodule.subset_span ⟨w_sync, i₀, le_rfl, hi₀, rfl⟩))⟩
  let k₀ := Nat.find hex_esc
  have hk₀_not : ¬ (W k₀ ≤ H) := Nat.find_spec hex_esc
  have hk₀_min : ∀ j < k₀, W j ≤ H := fun j hj => not_not.mp (Nat.find_min hex_esc hj)
  have hk₀_le : k₀ ≤ Fintype.card Q - 2 := by
    by_cases hk0 : k₀ = 0
    · omega
    · -- Since `k₀ ≥ 1`, `W 0 ≤ H`. Prove `2 ≤ Module.finrank ℚ (W 0)` using `p ≠ 1 / 2`!
      have hW0_leH : W 0 ≤ H := hk₀_min 0 (by omega)
      have hW0_dim2 : 2 ≤ Module.finrank ℚ (W 0) := by
        by_contra hlt2
        have hle1 : Module.finrank ℚ (W 0) ≤ 1 := by omega
        let v₀ := AlpogeThetaLift.pullback A ([] ++ word i₀) (AlpogeThetaLift.centered π S)
        have hv₀_mem : v₀ ∈ W 0 := Submodule.subset_span ⟨[], i₀, le_rfl, hi₀, rfl⟩
        have hv₀_ne : v₀ ≠ 0 := by
          intro hzero
          have hval := congrFun hzero q₀
          simp only [v₀, AlpogeThetaLift.pullback, AlpogeThetaLift.centered, LinearMap.coe_mk,
            AddHom.coe_mk, Pi.zero_apply] at hval
          split_ifs at hval <;> linarith
        have hspan_le : Submodule.span ℚ ({v₀} : Set (Q → ℚ)) ≤ W 0 :=
          Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv₀_mem)
        have hspan_rank : Module.finrank ℚ (Submodule.span ℚ ({v₀} : Set (Q → ℚ))) = 1 :=
          finrank_span_singleton hv₀_ne
        have hW0_eq : Submodule.span ℚ ({v₀} : Set (Q → ℚ)) = W 0 :=
          Submodule.eq_of_le_of_finrank_le hspan_le (by omega)
        have hvals : ∀ (i : ι) (q : Q),
            AlpogeThetaLift.pullback A ([] ++ word i) (AlpogeThetaLift.centered π S) q = 1 - p ∨
            AlpogeThetaLift.pullback A ([] ++ word i) (AlpogeThetaLift.centered π S) q = -p := by
          intro i q
          simp only [AlpogeThetaLift.pullback, AlpogeThetaLift.centered, LinearMap.coe_mk,
            AddHom.coe_mk, List.nil_append]
          split_ifs
          · left; ring
          · right; ring
        have hv₀_H : ∑ q : Q, π q * v₀ q = 0 := hW0_leH hv₀_mem
        have hex_q1 : ∃ q₁ : Q, v₀ q₁ = 1 - p := by
          by_contra hall
          push Not at hall
          have hall_neg : ∀ q : Q, v₀ q = -p := fun q =>
            (hvals i₀ q).resolve_left (hall q)
          have hsum : ∑ q : Q, π q * v₀ q = -p := by
            simp_rw [hall_neg, ← Finset.sum_mul, hπ_sum, one_mul]
          linarith
        have hex_q2 : ∃ q₂ : Q, v₀ q₂ = -p := by
          by_contra hall
          push Not at hall
          have hall_pos : ∀ q : Q, v₀ q = 1 - p := fun q =>
            (hvals i₀ q).resolve_right (hall q)
          have hsum : ∑ q : Q, π q * v₀ q = 1 - p := by
            simp_rw [hall_pos, ← Finset.sum_mul, hπ_sum, one_mul]
          linarith
        obtain ⟨q₁, hq₁⟩ := hex_q1
        obtain ⟨q₂, hq₂⟩ := hex_q2
        have hall_eq_q1 : ∀ i : ι, 0 < μ i →
            AlpogeThetaLift.centered π S (A.eval q₁ (word i)) = 1 - p := by
          intro i hi
          have hvi_mem : AlpogeThetaLift.pullback A ([] ++ word i) (AlpogeThetaLift.centered π S) ∈
              Submodule.span ℚ ({v₀} : Set (Q → ℚ)) := by
            rw [hW0_eq]
            exact Submodule.subset_span ⟨[], i, le_rfl, hi, rfl⟩
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvi_mem
          have hc1 : c * (1 - p) =
              AlpogeThetaLift.pullback A ([] ++ word i) (AlpogeThetaLift.centered π S) q₁ := by
            have := congrFun hc q₁
            simpa only [Pi.smul_apply, smul_eq_mul, hq₁] using this
          have hc2 : c * (-p) =
              AlpogeThetaLift.pullback A ([] ++ word i) (AlpogeThetaLift.centered π S) q₂ := by
            have := congrFun hc q₂
            simpa only [Pi.smul_apply, smul_eq_mul, hq₂] using this
          have hc_eq1 : c = 1 := by
            rcases hvals i q₁ with h1 | h1 <;> rcases hvals i q₂ with h2 | h2
            · nlinarith
            · nlinarith
            · exfalso
              have hsq : (-p) * (-p) = (1 - p) * (1 - p) := by
                calc (-p) * (-p) = (c * (1 - p)) * (-p) := by rw [hc1, h1]
                  _ = (c * (-p)) * (1 - p) := by ring
                  _ = (1 - p) * (1 - p) := by rw [hc2, h2]
              have hp_half : p = (1 : ℚ) / 2 := by linarith
              exact hπS_ne_half hp_half
            · nlinarith
          rw [hc_eq1, one_mul] at hc1
          simpa only [AlpogeThetaLift.pullback, LinearMap.coe_mk, AddHom.coe_mk,
            List.nil_append] using hc1.symm
        have hsum_pos :
            ∑ i : ι, μ i * AlpogeThetaLift.centered π S (A.eval q₁ (word i)) = 1 - p := by
          have hterm : ∀ i : ι,
              μ i * AlpogeThetaLift.centered π S (A.eval q₁ (word i)) = μ i * (1 - p) := by
            intro i
            by_cases hi : 0 < μ i
            · rw [hall_eq_q1 i hi]
            · have h0 : μ i = 0 := le_antisymm (not_lt.mp hi) (hμ_nonneg i)
              rw [h0, zero_mul, zero_mul]
          simp_rw [hterm, ← Finset.sum_mul, hμ_sum, one_mul]
        have hsum_zero := hpt_zero q₁
        linarith
      have hstrict : ∀ j, j + 1 < k₀ → W j < W (j + 1) := by
        intro j hj
        refine lt_of_le_of_ne (hW_mono (Nat.le_succ j)) fun heq => ?_
        have hclosed : ∀ (g : α) (v : Q → ℚ), v ∈ W j → AlpogeThetaLift.pullback A [g] v ∈ W j := by
          intro g v hv
          rw [heq]
          induction hv using Submodule.span_induction with
          | mem x hx =>
            rcases hx with ⟨u, i, hu, hi, rfl⟩
            rw [← AlpogeThetaLift.pullback_cons]
            exact Submodule.subset_span ⟨g :: u, i, by simp; omega, hi, rfl⟩
          | zero => simp
          | add x y _ _ hx hy => rw [map_add]; exact (W (j + 1)).add_mem hx hy
          | smul c x _ hx => rw [map_smul]; exact (W (j + 1)).smul_mem c hx
        have hall : ∀ (u : List α) (i : ι), 0 < μ i →
            AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S) ∈ W j := by
          intro u
          induction u with
          | nil =>
            intro i hi
            exact Submodule.subset_span ⟨[], i, Nat.zero_le j, hi, rfl⟩
          | cons g u ih =>
            intro i hi
            rw [List.cons_append, AlpogeThetaLift.pullback_cons]
            exact hclosed g _ (ih i hi)
        exact hsync_notH (hk₀_min j (by omega) (hall w_sync i₀ hi₀))
      have hdim : ∀ j ≤ k₀ - 1, j + 2 ≤ Module.finrank ℚ (W j) := by
        intro j
        induction j with
        | zero => intro _; exact hW0_dim2
        | succ j ih =>
          intro hj
          have ih' := ih (by omega)
          have hlt := Submodule.finrank_lt_finrank_of_lt (hstrict j (by omega))
          omega
      have h1 := hdim (k₀ - 1) le_rfl
      have h2 : Module.finrank ℚ (W (k₀ - 1)) ≤ Module.finrank ℚ H :=
        Submodule.finrank_mono (hk₀_min (k₀ - 1) (by omega))
      rw [AlpogeThetaLift.finrank_ker_dotLin hπ_sum] at h2
      omega
  have hex_gen : ∃ (u : List α) (i₁ : ι), u.length ≤ k₀ ∧ 0 < μ i₁ ∧
      AlpogeThetaLift.dotLin π
        (AlpogeThetaLift.pullback A (u ++ word i₁) (AlpogeThetaLift.centered π S)) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hk₀_not
    rw [Submodule.span_le]
    rintro v ⟨u, i, hu, hi, rfl⟩
    exact hall u i hu hi
  rcases hex_gen with ⟨u, i₁, hulen, hi₁_pos, hi₁_nz⟩
  have hex_pos : ∃ i' : ι, 0 < μ i' ∧
      0 < AlpogeThetaLift.dotLin π
        (AlpogeThetaLift.pullback A (u ++ word i') (AlpogeThetaLift.centered π S)) := by
    by_contra hall
    push Not at hall
    have hnonpos : ∀ i : ι,
        μ i * AlpogeThetaLift.dotLin π
          (AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S)) ≤ 0 := by
      intro i
      by_cases hi : 0 < μ i
      · exact mul_nonpos_of_nonneg_of_nonpos hi.le (hall i hi)
      · have h0 : μ i = 0 := le_antisymm (not_lt.mp hi) (hμ_nonneg i)
        rw [h0, zero_mul]
    have hlt_i₁ :
        μ i₁ * AlpogeThetaLift.dotLin π
          (AlpogeThetaLift.pullback A (u ++ word i₁) (AlpogeThetaLift.centered π S)) < 0 :=
      mul_neg_of_pos_of_neg hi₁_pos (lt_of_le_of_ne (hall i₁ hi₁_pos) hi₁_nz)
    have hsum_lt :
        ∑ i : ι, μ i * AlpogeThetaLift.dotLin π
          (AlpogeThetaLift.pullback A (u ++ word i) (AlpogeThetaLift.centered π S)) <
        ∑ _i : ι, (0 : ℚ) :=
      Finset.sum_lt_sum (fun i _ => hnonpos i) ⟨i₁, Finset.mem_univ i₁, hlt_i₁⟩
    rw [hzero_exp u, Finset.sum_const_zero] at hsum_lt
    exact lt_irrefl _ hsum_lt
  rcases hex_pos with ⟨i', hi'_pos, hi'_gt⟩
  rw [AlpogeThetaLift.dotLin_pullback_centered A π hπ_sum S (u ++ word i')] at hi'_gt
  refine ⟨u ++ word i', ?_, by linarith⟩
  rw [List.length_append]
  have hli' := hL₁ i' hi'_pos
  omega

/-- **Theorem D₀(3) (Uniform-on-`C` Quadratic Reset Bound)**:
When `π` is uniform (`1 / |C|`) on `C` and `w_in` (`|w_in| ≤ ℓ`) maps all of `Q` into `C`,
`A` admits a synchronizing word of length at most `ℓ + (|C| - 1) * (n - 1 + L₁)`. -/
theorem rankOne_uniform_reset_bound {Q : Type u} {α : Type v} {ι : Type w}
    [Fintype Q] [DecidableEq Q] [Fintype ι]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (C : Finset Q) (hC_ne : C.Nonempty)
    (μ : ι → ℚ) (word : ι → List α) (L₁ : ℕ)
    (w_in : List α) (ℓ : ℕ) (hw_in_len : w_in.length ≤ ℓ)
    (hw_in : ∀ q : Q, A.eval q w_in ∈ C)
    (hμ_nonneg : ∀ i : ι, 0 ≤ μ i)
    (hμ_sum : ∑ i : ι, μ i = 1)
    (hL₁ : ∀ i : ι, 0 < μ i → (word i).length ≤ L₁)
    (hRankOne : ∀ p q : Q,
      (∑ i : ι, if A.eval p (word i) = q then μ i else 0) =
        if q ∈ C then (1 : ℚ) / (C.card : ℚ) else 0) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ ℓ + (C.card - 1) * (Fintype.card Q - 1 + L₁) := by
  let π : Q → ℚ := fun q => if q ∈ C then (1 : ℚ) / (C.card : ℚ) else 0
  have hC_pos : (0 : ℚ) < (C.card : ℚ) := by exact_mod_cast Finset.card_pos.mpr hC_ne
  have hπ_nonneg : ∀ q : Q, 0 ≤ π q := fun q => by
    dsimp [π]; split_ifs
    · exact div_nonneg zero_le_one hC_pos.le
    · exact le_rfl
  have hπ_supp : ∀ q : Q, 0 < π q ↔ q ∈ C := fun q => by
    dsimp [π]; split_ifs with hq
    · exact ⟨fun _ => hq, fun _ => div_pos zero_lt_one hC_pos⟩
    · exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h hq⟩
  have hπ_sum : ∑ q : Q, π q = 1 := by
    dsimp [π]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_mem_eq_inter,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one_div_cancel (ne_of_gt hC_pos)]
  have hex_chain : ∀ k : ℕ, ∀ S : Finset Q, S ⊆ C → S.Nonempty → C.card - S.card ≤ k →
      ∃ X : List α, C ⊆ A.preimage S X ∧ X.length ≤ k * (Fintype.card Q - 1 + L₁) := by
    intro k
    induction k with
    | zero =>
      intro S hSC _ hk
      have hcard := Finset.card_le_card hSC
      have heq := Finset.eq_of_subset_of_card_le hSC (by omega)
      exact ⟨[], by rw [DFA.preimage_nil, heq], by simp⟩
    | succ k ih =>
      intro S hSC hSne hk
      by_cases heq : S = C
      · exact ⟨[], by rw [DFA.preimage_nil, heq], by simp⟩
      · have hssub : S ⊂ C := Finset.ssubset_iff_subset_ne.mpr ⟨hSC, heq⟩
        obtain ⟨u, hulen, hugt⟩ :=
          rankOne_exists_extending_word A hSync C π μ word L₁ hπ_nonneg hπ_supp hπ_sum
            hμ_nonneg hμ_sum hL₁ hRankOne hSne hssub
        -- Convert π-increase into cardinality increase on `(A.preimage S u) ∩ C`!
        have hπS : ∑ x ∈ S, π x = (S.card : ℚ) / (C.card : ℚ) := by
          have : ∀ x ∈ S, π x = 1 / (C.card : ℚ) := fun x hx => by simp [π, hSC hx]
          rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one_div]
        have hπ_pre : ∑ q ∈ A.preimage S u, π q =
            (((A.preimage S u) ∩ C).card : ℚ) / (C.card : ℚ) := by
          dsimp [π]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_one_div, Finset.filter_mem_eq_inter]
        rw [hπS, hπ_pre, div_lt_div_iff_of_pos_right hC_pos] at hugt
        have hcard_gt : S.card < ((A.preimage S u) ∩ C).card := by exact_mod_cast hugt
        let S' := (A.preimage S u) ∩ C
        have hS'card : S'.card = ((A.preimage S u) ∩ C).card := rfl
        have hS'ne : S'.Nonempty := Finset.card_pos.mp (lt_trans (Finset.card_pos.mpr hSne) hcard_gt)
        obtain ⟨X', hX'sub, hX'len⟩ := ih S' Finset.inter_subset_right hS'ne (by omega)
        refine ⟨X' ++ u, ?_, ?_⟩
        · rw [DFA.preimage_append]
          exact hX'sub.trans (A.preimage_mono Finset.inter_subset_left X')
        · rw [List.length_append]
          calc X'.length + u.length ≤ k * (Fintype.card Q - 1 + L₁) + (Fintype.card Q - 1 + L₁) :=
                Nat.add_le_add hX'len hulen
            _ = (k + 1) * (Fintype.card Q - 1 + L₁) := by ring
  rcases hC_ne with ⟨q₀, hq₀C⟩
  obtain ⟨X, hXsub, hXlen⟩ := hex_chain (C.card - 1) {q₀}
    (Finset.singleton_subset_iff.mpr hq₀C) ⟨q₀, by simp⟩ (by simp)
  refine ⟨w_in ++ X, ⟨q₀, fun q => ?_⟩, ?_⟩
  · rw [DFA.eval_append]
    have hmem : A.eval q w_in ∈ A.preimage {q₀} X := hXsub (hw_in q)
    simpa [DFA.mem_preimage] using hmem
  · rw [List.length_append]
    omega

/-! ### Section 2: Two-Cluster Mixing Theta Lift (Theorem D — Breaching Obstruction O.3!) -/

/-- Witness data for a 2-cluster letter `a` with disjoint directed cycles `C₁, C₂`,
disjoint basins `B₁ ⊔ B₂ = univ`, and arbitrary tree height `ℓ` (`Bᵢ · a^ℓ ⊆ Cᵢ`). -/
structure TwoClusterData {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q] (A : DFA Q α) where
  a : α
  C₁ : Finset Q
  C₂ : Finset Q
  B₁ : Finset Q
  B₂ : Finset Q
  ℓ : ℕ
  hC₁_ne : C₁.Nonempty
  hC₂_ne : C₂.Nonempty
  hC_disj : Disjoint C₁ C₂
  hB_disj : Disjoint B₁ B₂
  hB_union : B₁ ∪ B₂ = Finset.univ
  hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁
  hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q
  hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂
  hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q
  hB₁_enter : ∀ q ∈ B₁, (fun x => A.step x a)^[ℓ] q ∈ C₁
  hB₂_enter : ∀ q ∈ B₂, (fun x => A.step x a)^[ℓ] q ∈ C₂
  hℓ_le : ℓ + C₁.card + C₂.card ≤ Fintype.card Q

namespace TwoClusterData

/-- On a finite invariant transitive cycle `C`, iterating `step · a` for `0 ≤ j < |C|`
visits every state of `C` exactly once. -/
private lemma cycle_sum_indicator {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a : α) (C : Finset Q) (hC_inv : ∀ q ∈ C, A.step q a ∈ C)
    (hC_trans : ∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    {c₀ : Q} (hc₀ : c₀ ∈ C) (q : Q) :
    (∑ j : Fin C.card, if (fun x => A.step x a)^[j.val] c₀ = q then (1 : ℚ) else 0) =
      if q ∈ C then 1 else 0 := by
  let f : Q → Q := fun x => A.step x a
  have hiter_mem : ∀ k : ℕ, f^[k] c₀ ∈ C := by
    intro k
    induction k with
    | zero => exact hc₀
    | succ k ih => rw [Function.iterate_succ_apply']; exact hC_inv _ ih
  -- `f` restricted to `C` is surjective, hence bijective on finite `C`.
  let fC : C → C := fun x => ⟨f x.1, hC_inv x.1 x.2⟩
  have hfC_iter : ∀ (k : ℕ) (x : C), (fC^[k] x).1 = f^[k] x.1 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply, ih]; rfl
  have hfC_surj : Function.Surjective fC := by
    intro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hC_trans (f y) (hC_inv y hy) y hy
    refine ⟨⟨f^[k] y, ?_⟩, Subtype.ext ?_⟩
    · clear hk; induction k with
      | zero => exact hy
      | succ k ih => rw [Function.iterate_succ_apply']; exact hC_inv _ ih
    · change f (f^[k] y) = y
      rw [← Function.iterate_succ_apply' f k y, Function.iterate_succ_apply]
      exact hk
  have hfC_inj : Function.Injective fC :=
    (Fintype.bijective_iff_surjective_and_card fC).mpr ⟨hfC_surj, rfl⟩ |>.1
  -- No period `0 < k < C.card` fixes `c₀` (else orbit has size ≤ k < C.card).
  have hmin : ∀ k : ℕ, 0 < k → k < C.card → f^[k] c₀ ≠ c₀ := by
    intro k hk0 hkc hfix
    have hmul : ∀ t : ℕ, f^[k * t] c₀ = c₀ := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hfix]
    have hmod : ∀ t : ℕ, f^[t] c₀ = f^[t % k] c₀ := by
      intro t
      have hdiv : t = t % k + k * (t / k) := by have := Nat.div_add_mod t k; omega
      conv_lhs => rw [hdiv, Function.iterate_add_apply, hmul]
    have hsub : C ⊆ (Finset.range k).image (fun j => f^[j] c₀) := by
      intro y hy
      obtain ⟨t, rfl⟩ := hC_trans c₀ hc₀ y hy
      rw [Finset.mem_image]
      exact ⟨t % k, Finset.mem_range.mpr (Nat.mod_lt t hk0), (hmod t).symm⟩
    have hle := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_range] at hle
    omega
  -- Therefore `j : Fin C.card ↦ ⟨f^[j] c₀, ...⟩` is a bijection `Fin C.card ≃ C`!
  let g : Fin C.card → C := fun j => ⟨f^[j.val] c₀, hiter_mem j.val⟩
  have hg_inj : Function.Injective g := by
    intro i j hij
    have hval : f^[i.val] c₀ = f^[j.val] c₀ := congrArg Subtype.val hij
    by_contra hne
    have hstep : ∀ x y : ℕ, x < y → y < C.card → f^[x] c₀ = f^[y] c₀ → False := by
      intro x y hxy hyc heq
      have hsub : fC^[x] ⟨c₀, hc₀⟩ = fC^[y] ⟨c₀, hc₀⟩ := Subtype.ext (by rw [hfC_iter, hfC_iter]; exact heq)
      have hsplit : y = x + (y - x) := by omega
      rw [hsplit, Function.iterate_add_apply] at hsub
      have hfixC : fC^[y - x] ⟨c₀, hc₀⟩ = ⟨c₀, hc₀⟩ := (hfC_inj.iterate x) hsub.symm
      have hfix : f^[y - x] c₀ = c₀ := by
        have := congrArg Subtype.val hfixC; rwa [hfC_iter] at this
      exact hmin (y - x) (by omega) (by omega) hfix
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hstep i.val j.val hlt j.isLt hval
    · exact hstep j.val i.val hgt i.isLt hval.symm
  have hg_surj : Function.Surjective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_inj, by simp⟩ |>.2
  change (∑ j : Fin C.card, if f^[j.val] c₀ = q then (1 : ℚ) else 0) = if q ∈ C then 1 else 0
  by_cases hqC : q ∈ C
  · simp only [hqC, ↓reduceIte]
    obtain ⟨j₀, hj₀⟩ := hg_surj ⟨q, hqC⟩
    have hj₀_val : f^[j₀.val] c₀ = q := congrArg Subtype.val hj₀
    rw [Finset.sum_eq_single j₀]
    · simp only [hj₀_val, ↓reduceIte]
    · intro j _ hne
      have hne_val : f^[j.val] c₀ ≠ q := fun h => hne (hg_inj (Subtype.ext (h.trans hj₀_val.symm)))
      simp only [hne_val, ↓reduceIte]
    · intro h; exact absurd (Finset.mem_univ j₀) h
  · simp only [hqC, ↓reduceIte]
    exact Finset.sum_eq_zero fun j _ => by
      simp only [show f^[j.val] c₀ ≠ q from fun h => hqC (h ▸ hiter_mem j.val), ↓reduceIte]

/-- Double-cycle ergodic projector `E₁(a)` indexed by `Fin m₁ × Fin m₂`:
for `p ∈ B₁` gives `1 / m₁` on `C₁`, and for `p ∈ B₂` gives `1 / m₂` on `C₂`. -/
private lemma ergodic_double_matrix {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} (D : TwoClusterData A) (p q : Q) :
    (∑ idx : Fin D.C₁.card × Fin D.C₂.card,
      if A.eval p (List.replicate (D.ℓ + idx.1.val + idx.2.val) D.a) = q
      then (1 : ℚ) / ((D.C₁.card : ℚ) * (D.C₂.card : ℚ)) else 0) =
    if p ∈ D.B₁ then (if q ∈ D.C₁ then (1 : ℚ) / (D.C₁.card : ℚ) else 0)
    else (if q ∈ D.C₂ then (1 : ℚ) / (D.C₂.card : ℚ) else 0) := by
  have hm₁ : (D.C₁.card : ℚ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr D.hC₁_ne).ne'
  have hm₂ : (D.C₂.card : ℚ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr D.hC₂_ne).ne'
  have hfactor : ∀ (f : Fin D.C₁.card × Fin D.C₂.card → Prop) [DecidablePred f] (c : ℚ),
      (∑ x, if f x then c else 0) = c * ∑ x, if f x then (1 : ℚ) else 0 := by
    intro f _ c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
  rw [hfactor]
  by_cases hp1 : p ∈ D.B₁
  · simp only [hp1, ↓reduceIte]
    rw [Fintype.sum_prod_type_right]
    have hinner : ∀ j₂ : Fin D.C₂.card,
        (∑ j₁ : Fin D.C₁.card,
          if A.eval p (List.replicate (D.ℓ + j₁.val + j₂.val) D.a) = q then (1 : ℚ) else 0) =
        if q ∈ D.C₁ then 1 else 0 := by
      intro j₂
      let c₀ := (fun x => A.step x D.a)^[D.ℓ + j₂.val] p
      have hc₀ : c₀ ∈ D.C₁ := by
        dsimp [c₀]
        rw [add_comm, Function.iterate_add_apply]
        have hstart := D.hB₁_enter p hp1
        clear hp1
        induction j₂.val with
        | zero => exact hstart
        | succ k ih => rw [Function.iterate_succ_apply']; exact D.hC₁_inv _ ih
      have hrew : ∀ j₁ : Fin D.C₁.card,
          A.eval p (List.replicate (D.ℓ + j₁.val + j₂.val) D.a) =
            (fun x => A.step x D.a)^[j₁.val] c₀ := by
        intro j₁
        rw [DFA.eval_replicate]
        dsimp [c₀]
        rw [← Function.iterate_add_apply]
        congr 1; omega
      simp_rw [hrew]
      exact cycle_sum_indicator A D.a D.C₁ D.hC₁_inv D.hC₁_trans hc₀ q
    simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    split_ifs
    · field_simp
    · simp
  · simp only [hp1, ↓reduceIte]
    have hp2 : p ∈ D.B₂ := by
      have : p ∈ D.B₁ ∪ D.B₂ := by rw [D.hB_union]; exact Finset.mem_univ p
      exact (Finset.mem_union.mp this).resolve_left hp1
    rw [Fintype.sum_prod_type]
    have hinner : ∀ j₁ : Fin D.C₁.card,
        (∑ j₂ : Fin D.C₂.card,
          if A.eval p (List.replicate (D.ℓ + j₁.val + j₂.val) D.a) = q then (1 : ℚ) else 0) =
        if q ∈ D.C₂ then 1 else 0 := by
      intro j₁
      let c₀ := (fun x => A.step x D.a)^[D.ℓ + j₁.val] p
      have hc₀ : c₀ ∈ D.C₂ := by
        dsimp [c₀]
        rw [add_comm, Function.iterate_add_apply]
        have hstart := D.hB₂_enter p hp2
        clear hp2 hp1
        induction j₁.val with
        | zero => exact hstart
        | succ k ih => rw [Function.iterate_succ_apply']; exact D.hC₂_inv _ ih
      have hrew : ∀ j₂ : Fin D.C₂.card,
          A.eval p (List.replicate (D.ℓ + j₁.val + j₂.val) D.a) =
            (fun x => A.step x D.a)^[j₂.val] c₀ := by
        intro j₂
        rw [DFA.eval_replicate]
        dsimp [c₀]
        rw [← Function.iterate_add_apply]
        congr 1; omega
      simp_rw [hrew]
      exact cycle_sum_indicator A D.a D.C₂ D.hC₂_inv D.hC₂_trans hc₀ q
    simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    split_ifs
    · field_simp
    · simp

/-- Single-cycle ergodic projector `E₁(a)` for equal-cycle 2-cluster (`m₁ = m₂ = m₀`):
indexed by `Fin m₀`, max length `ℓ + m₀ - 1`. -/
private lemma ergodic_equal_matrix {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} (D : TwoClusterData A) (heq : D.C₁.card = D.C₂.card) (p q : Q) :
    (∑ j : Fin D.C₁.card,
      if A.eval p (List.replicate (D.ℓ + j.val) D.a) = q
      then (1 : ℚ) / (D.C₁.card : ℚ) else 0) =
    if p ∈ D.B₁ then (if q ∈ D.C₁ then (1 : ℚ) / (D.C₁.card : ℚ) else 0)
    else (if q ∈ D.C₂ then (1 : ℚ) / (D.C₂.card : ℚ) else 0) := by
  have hfactor : ∀ (f : Fin D.C₁.card → Prop) [DecidablePred f] (c : ℚ),
      (∑ x, if f x then c else 0) = c * ∑ x, if f x then (1 : ℚ) else 0 := by
    intro f _ c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
  rw [hfactor]
  by_cases hp1 : p ∈ D.B₁
  · simp only [hp1, ↓reduceIte]
    have hrew : ∀ j : Fin D.C₁.card,
        A.eval p (List.replicate (D.ℓ + j.val) D.a) =
          (fun x => A.step x D.a)^[j.val] ((fun x => A.step x D.a)^[D.ℓ] p) := by
      intro j
      rw [DFA.eval_replicate, add_comm, Function.iterate_add_apply]
    simp_rw [hrew]
    rw [cycle_sum_indicator A D.a D.C₁ D.hC₁_inv D.hC₁_trans (D.hB₁_enter p hp1) q]
    split_ifs <;> ring
  · simp only [hp1, ↓reduceIte]
    have hp2 : p ∈ D.B₂ := by
      have : p ∈ D.B₁ ∪ D.B₂ := by rw [D.hB_union]; exact Finset.mem_univ p
      exact (Finset.mem_union.mp this).resolve_left hp1
    let e : Fin D.C₁.card ≃ Fin D.C₂.card := finCongr heq
    rw [Fintype.sum_equiv e
      (fun j : Fin D.C₁.card => if A.eval p (List.replicate (D.ℓ + j.val) D.a) = q then (1 : ℚ) else 0)
      (fun j : Fin D.C₂.card => if A.eval p (List.replicate (D.ℓ + j.val) D.a) = q then (1 : ℚ) else 0)
      (fun j => by simp [e])]
    have hrew : ∀ j : Fin D.C₂.card,
        A.eval p (List.replicate (D.ℓ + j.val) D.a) =
          (fun x => A.step x D.a)^[j.val] ((fun x => A.step x D.a)^[D.ℓ] p) := by
      intro j
      rw [DFA.eval_replicate, add_comm, Function.iterate_add_apply]
    simp_rw [hrew]
    rw [cycle_sum_indicator A D.a D.C₂ D.hC₂_inv D.hC₂_trans (D.hB₂_enter p hp2) q, heq]
    split_ifs <;> ring

/-- Abstract two-letter theta-lift assembly: given ANY indexed representation `(η, eword)` of `E₁(a)`
of max length `L_E`, and a letter `b` satisfying balanced cross-cluster mixing `k₁₂ = k₂₁ > 0`
and `k₁₂ / m₁ + k₂₁ / m₂ ≥ 1`, constructs an exact rank-1 uniform distribution on `C₁ ∪ C₂`
of max length `2 * L_E + 1` and deduces `rt(A) ≤ ℓ + (m - 1) * (n + 2 * L_E)`. -/
private lemma thetaLift_of_ergodic {Q : Type u} {α : Type v} {ιE : Type w}
    [Fintype Q] [DecidableEq Q] [Fintype ιE]
    {A : DFA Q α} (D : TwoClusterData A) (hSync : A.IsSynchronizing)
    (η : ιE → ℚ) (eword : ιE → List α) (L_E : ℕ)
    (hη_nonneg : ∀ i, 0 ≤ η i)
    (hη_sum : ∑ i, η i = 1)
    (hL_E : ∀ i, (eword i).length ≤ L_E)
    (hE₁ : ∀ p q : Q, (∑ i : ιE, if A.eval p (eword i) = q then η i else 0) =
      if p ∈ D.B₁ then (if q ∈ D.C₁ then (1 : ℚ) / (D.C₁.card : ℚ) else 0)
      else (if q ∈ D.C₂ then (1 : ℚ) / (D.C₂.card : ℚ) else 0))
    (b : α)
    (hbal : (D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card =
            (D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card)
    (hmix : ((D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card : ℚ) / (D.C₁.card : ℚ) +
            ((D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card : ℚ) / (D.C₂.card : ℚ) ≥ 1) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ D.ℓ + (D.C₁.card + D.C₂.card - 1) * (Fintype.card Q + 2 * L_E) := by
  let k : ℕ := (D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card
  let m₁ : ℚ := D.C₁.card
  let m₂ : ℚ := D.C₂.card
  have hm₁_pos : (0 : ℚ) < m₁ := by dsimp [m₁]; exact_mod_cast Finset.card_pos.mpr D.hC₁_ne
  have hm₂_pos : (0 : ℚ) < m₂ := by dsimp [m₂]; exact_mod_cast Finset.card_pos.mpr D.hC₂_ne
  let p₁₂ : ℚ := (k : ℚ) / m₁
  let p₂₁ : ℚ := (k : ℚ) / m₂
  have hp_sum : 1 ≤ p₁₂ + p₂₁ := by
    have hbalQ : ((D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card : ℚ) =
        ((D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card : ℚ) := by exact_mod_cast hbal
    calc (1 : ℚ)
        ≤ ((D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card : ℚ) / (D.C₁.card : ℚ) +
          ((D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card : ℚ) / (D.C₂.card : ℚ) := hmix
      _ = p₁₂ + p₂₁ := by dsimp [p₁₂, p₂₁, k, m₁, m₂]; rw [hbalQ]
  have hp_pos : 0 < p₁₂ + p₂₁ := by linarith
  have hk_pos : (0 : ℚ) < (k : ℚ) := by
    by_contra hle
    have hk0 : (k : ℚ) = 0 := le_antisymm (not_lt.mp hle) (Nat.cast_nonneg k)
    have : p₁₂ + p₂₁ = 0 := by simp [p₁₂, p₂₁, hk0]
    linarith
  let αc : ℚ := (p₁₂ + p₂₁ - 1) / (p₁₂ + p₂₁)
  let βc : ℚ := 1 / (p₁₂ + p₂₁)
  have hα_nn : 0 ≤ αc := div_nonneg (by linarith) hp_pos.le
  have hβ_nn : 0 ≤ βc := div_nonneg zero_le_one hp_pos.le
  have hαβ : αc + βc = 1 := by dsimp [αc, βc]; field_simp; ring
  -- Indexed family `ι := ιE ⊕ (ιE × ιE)` representing `αc * E₁ + βc * E₁ P_b E₁`!
  let μ : ιE ⊕ (ιE × ιE) → ℚ
    | Sum.inl i => αc * η i
    | Sum.inr (i, j) => βc * (η i * η j)
  let word : ιE ⊕ (ιE × ιE) → List α
    | Sum.inl i => eword i
    | Sum.inr (i, j) => eword i ++ [b] ++ eword j
  have hμ_nn : ∀ x, 0 ≤ μ x := by
    rintro (i | ⟨i, j⟩)
    · exact mul_nonneg hα_nn (hη_nonneg i)
    · exact mul_nonneg hβ_nn (mul_nonneg (hη_nonneg i) (hη_nonneg j))
  have hμ_sum : ∑ x : ιE ⊕ (ιE × ιE), μ x = 1 := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    dsimp only [μ]
    have h1 : ∑ i : ιE, αc * η i = αc := by rw [← Finset.mul_sum, hη_sum, mul_one]
    have h2 : ∑ i : ιE, ∑ j : ιE, βc * (η i * η j) = βc := by
      calc ∑ i : ιE, ∑ j : ιE, βc * (η i * η j)
          = ∑ i : ιE, ∑ j : ιE, (βc * η i) * η j :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ i : ιE, (βc * η i) * ∑ j : ιE, η j :=
            Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
        _ = ∑ i : ιE, βc * η i := Finset.sum_congr rfl fun i _ => by rw [hη_sum, mul_one]
        _ = βc := by rw [← Finset.mul_sum, hη_sum, mul_one]
    rw [h1, h2]
    exact hαβ
  have hL : ∀ x, 0 < μ x → (word x).length ≤ 2 * L_E + 1 := by
    rintro (i | ⟨i, j⟩) _
    · exact (hL_E i).trans (by omega)
    · dsimp only [word]
      rw [List.length_append, List.length_append, List.length_singleton]
      have hi := hL_E i; have hj := hL_E j; omega
  -- Compute `(E₁ P_b E₁)_{p, q}`!
  have hEPE : ∀ p q : Q,
      (∑ x : ιE × ιE, if A.eval p (eword x.1 ++ [b] ++ eword x.2) = q then η x.1 * η x.2 else 0) =
      if p ∈ D.B₁ then
        (if q ∈ D.C₁ then (1 - p₁₂) / m₁ else if q ∈ D.C₂ then p₁₂ / m₂ else 0)
      else
        (if q ∈ D.C₁ then p₂₁ / m₁ else if q ∈ D.C₂ then (1 - p₂₁) / m₂ else 0) := by
    intro p q
    rw [Fintype.sum_prod_type]
    have hinner : ∀ i : ιE,
        (∑ j : ιE, if A.eval p (eword i ++ [b] ++ eword j) = q then η i * η j else 0) =
        η i * (if A.step (A.eval p (eword i)) b ∈ D.B₁ then
          (if q ∈ D.C₁ then 1 / m₁ else 0) else (if q ∈ D.C₂ then 1 / m₂ else 0)) := by
      intro i
      rw [← hE₁ (A.step (A.eval p (eword i)) b) q, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [DFA.eval_append, DFA.eval_singleton]
      split_ifs <;> ring
    simp_rw [hinner]
    -- Group over intermediate state `c = A.eval p (eword i)`!
    let G : Q → ℚ := fun c =>
      if A.step c b ∈ D.B₁ then (if q ∈ D.C₁ then 1 / m₁ else 0)
      else (if q ∈ D.C₂ then 1 / m₂ else 0)
    have hgroup : (∑ i : ιE, η i * G (A.eval p (eword i))) =
        ∑ c : Q, (∑ i : ιE, if A.eval p (eword i) = c then η i else 0) * G c := by
      have hstep : ∀ i : ιE,
          η i * G (A.eval p (eword i)) =
          ∑ c : Q, (if A.eval p (eword i) = c then η i else 0) * G c := by
        intro i
        rw [Finset.sum_eq_single (A.eval p (eword i))]
        · simp
        · intro c _ hc; simp [Ne.symm hc]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [hstep]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => by rw [← Finset.sum_mul]
    change ∑ i : ιE, η i * G (A.eval p (eword i)) = _
    rw [hgroup]
    simp_rw [hE₁ p]
    have hB_iff : ∀ x : Q, x ∈ D.B₁ ↔ x ∉ D.B₂ := fun x => by
      constructor
      · exact fun h1 h2 => Finset.disjoint_left.mp D.hB_disj h1 h2
      · intro h2
        have : x ∈ D.B₁ ∪ D.B₂ := by rw [D.hB_union]; exact Finset.mem_univ x
        exact (Finset.mem_union.mp this).resolve_right h2
    by_cases hp1 : p ∈ D.B₁
    · simp only [hp1, ↓reduceIte]
      have hsumC₁' :
          (∑ c : Q, (if c ∈ D.C₁ then 1 / m₁ else 0) * G c) =
          (1 / m₁) * ∑ c ∈ D.C₁, G c := by
        rw [Finset.mul_sum]
        calc ∑ c : Q, (if c ∈ D.C₁ then 1 / m₁ else 0) * G c
            = ∑ c : Q, if c ∈ D.C₁ then 1 / m₁ * G c else 0 :=
              Finset.sum_congr rfl fun c _ => by split_ifs <;> ring
          _ = ∑ c ∈ D.C₁, 1 / m₁ * G c := by
              rw [← Finset.sum_filter]; congr 1; ext x; simp
      rw [hsumC₁']
      have hcard_split :
          (D.C₁.filter (fun c => A.step c b ∈ D.B₁)).card + k = D.C₁.card := by
        dsimp [k]
        have hdisj : Disjoint (D.C₁.filter (fun c => A.step c b ∈ D.B₁))
            (D.C₁.filter (fun c => A.step c b ∈ D.B₂)) := by
          rw [Finset.disjoint_left]
          intro c hc1 hc2
          exact (hB_iff (A.step c b)).mp (Finset.mem_filter.mp hc1).2 (Finset.mem_filter.mp hc2).2
        have hunion : D.C₁.filter (fun c => A.step c b ∈ D.B₁) ∪
            D.C₁.filter (fun c => A.step c b ∈ D.B₂) = D.C₁ := by
          ext c
          simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro hc
            by_cases h1 : A.step c b ∈ D.B₁
            · exact Or.inl ⟨hc, h1⟩
            · exact Or.inr ⟨hc, by have := (hB_iff (A.step c b)).not.mp h1; push Not at this; exact this⟩
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      have hGsum : ∑ c ∈ D.C₁, G c =
          ((D.C₁.filter (fun c => A.step c b ∈ D.B₁)).card : ℚ) * (if q ∈ D.C₁ then 1 / m₁ else 0) +
          (k : ℚ) * (if q ∈ D.C₂ then 1 / m₂ else 0) := by
        have hfilt_eq : D.C₁.filter (fun c => ¬ A.step c b ∈ D.B₁) =
            D.C₁.filter (fun c => A.step c b ∈ D.B₂) := by
          ext c; simp [hB_iff]
        dsimp [G, k]
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hfilt_eq]
      rw [hGsum]
      have hcs : ((D.C₁.filter (fun c => A.step c b ∈ D.B₁)).card : ℚ) = m₁ - (k : ℚ) := by
        have h' : ((D.C₁.filter (fun c => A.step c b ∈ D.B₁)).card : ℚ) + (k : ℚ) = m₁ := by
          dsimp [m₁]; exact_mod_cast hcard_split
        linarith
      rw [hcs]
      by_cases hq1 : q ∈ D.C₁
      · have hq2 : q ∉ D.C₂ := Finset.disjoint_left.mp D.hC_disj hq1
        simp only [hq1, hq2, ↓reduceIte, mul_zero, add_zero, p₁₂]
        field_simp
      · by_cases hq2 : q ∈ D.C₂
        · simp only [hq1, hq2, ↓reduceIte, mul_zero, zero_add, p₁₂]
          field_simp
        · simp [hq1, hq2]
    · simp only [hp1, ↓reduceIte]
      have hsumC₂ :
          (∑ c : Q, (if c ∈ D.C₂ then 1 / m₂ else 0) * G c) =
          (1 / m₂) * ∑ c ∈ D.C₂, G c := by
        rw [Finset.mul_sum]
        calc ∑ c : Q, (if c ∈ D.C₂ then 1 / m₂ else 0) * G c
            = ∑ c : Q, if c ∈ D.C₂ then 1 / m₂ * G c else 0 :=
              Finset.sum_congr rfl fun c _ => by split_ifs <;> ring
          _ = ∑ c ∈ D.C₂, 1 / m₂ * G c := by
              rw [← Finset.sum_filter]; congr 1; ext x; simp
      rw [hsumC₂]
      have hcard_split :
          k + (D.C₂.filter (fun c => ¬ A.step c b ∈ D.B₁)).card = D.C₂.card := by
        dsimp [k]; rw [hbal]
        have hdisj : Disjoint (D.C₂.filter (fun c => A.step c b ∈ D.B₁))
            (D.C₂.filter (fun c => ¬ A.step c b ∈ D.B₁)) := by
          rw [Finset.disjoint_left]
          intro c hc1 hc2
          exact (Finset.mem_filter.mp hc2).2 (Finset.mem_filter.mp hc1).2
        have hunion : D.C₂.filter (fun c => A.step c b ∈ D.B₁) ∪
            D.C₂.filter (fun c => ¬ A.step c b ∈ D.B₁) = D.C₂ := by
          ext c
          simp only [Finset.mem_union, Finset.mem_filter]
          tauto
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      have hGsum : ∑ c ∈ D.C₂, G c =
          (k : ℚ) * (if q ∈ D.C₁ then 1 / m₁ else 0) +
          ((D.C₂.filter (fun c => ¬ A.step c b ∈ D.B₁)).card : ℚ) * (if q ∈ D.C₂ then 1 / m₂ else 0) := by
        dsimp [G, k]
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hbal]
      rw [hGsum]
      have hcs : ((D.C₂.filter (fun c => ¬ A.step c b ∈ D.B₁)).card : ℚ) = m₂ - (k : ℚ) := by
        have h' : (k : ℚ) + ((D.C₂.filter (fun c => ¬ A.step c b ∈ D.B₁)).card : ℚ) = m₂ := by
          dsimp [m₂]; exact_mod_cast hcard_split
        linarith
      rw [hcs]
      by_cases hq1 : q ∈ D.C₁
      · have hq2 : q ∉ D.C₂ := Finset.disjoint_left.mp D.hC_disj hq1
        simp only [hq1, hq2, ↓reduceIte, mul_zero, add_zero, p₂₁]
        field_simp
      · by_cases hq2 : q ∈ D.C₂
        · simp only [hq1, hq2, ↓reduceIte, mul_zero, zero_add, p₂₁]
          field_simp
        · simp [hq1, hq2]
  -- Verify `hRankOne` with uniform `π = 1 / (m₁ + m₂)` on `C := C₁ ∪ C₂`!
  let C := D.C₁ ∪ D.C₂
  have hC_card : C.card = D.C₁.card + D.C₂.card := Finset.card_union_of_disjoint D.hC_disj
  have hC_ne : C.Nonempty := D.hC₁_ne.mono Finset.subset_union_left
  have hm_pos : (0 : ℚ) < m₁ + m₂ := by linarith
  have hRankOne : ∀ p q : Q,
      (∑ x : ιE ⊕ (ιE × ιE), if A.eval p (word x) = q then μ x else 0) =
        if q ∈ C then (1 : ℚ) / (C.card : ℚ) else 0 := by
    intro p q
    rw [Fintype.sum_sum_type]
    have hL1 : (∑ i : ιE, if A.eval p (eword i) = q then αc * η i else 0) =
        αc * ∑ i : ιE, if A.eval p (eword i) = q then η i else 0 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
    have hR1 : (∑ x : ιE × ιE,
        if A.eval p (eword x.1 ++ [b] ++ eword x.2) = q then βc * (η x.1 * η x.2) else 0) =
        βc * ∑ x : ιE × ιE,
          if A.eval p (eword x.1 ++ [b] ++ eword x.2) = q then η x.1 * η x.2 else 0 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
    dsimp only [μ, word]
    rw [hL1, hR1, hE₁ p q, hEPE p q]
    have hCcast : (C.card : ℚ) = m₁ + m₂ := by dsimp [m₁, m₂]; exact_mod_cast hC_card
    have hm₁_def : (D.C₁.card : ℚ) = m₁ := rfl
    have hm₂_def : (D.C₂.card : ℚ) = m₂ := rfl
    rw [hCcast, hm₁_def, hm₂_def]
    by_cases hp1 : p ∈ D.B₁
    · simp only [hp1, ↓reduceIte]
      by_cases hq1 : q ∈ D.C₁
      · have hq2 : q ∉ D.C₂ := Finset.disjoint_left.mp D.hC_disj hq1
        have hqC : q ∈ C := Finset.mem_union_left _ hq1
        simp only [hq1, hqC, ↓reduceIte]
        dsimp only [αc, βc, p₁₂, p₂₁]
        field_simp
        ring
      · by_cases hq2 : q ∈ D.C₂
        · have hqC : q ∈ C := Finset.mem_union_right _ hq2
          simp only [hq1, hq2, hqC, ↓reduceIte, mul_zero, zero_add]
          dsimp only [βc, p₁₂, p₂₁]
          field_simp
          ring
        · have hqC : q ∉ C := fun h => (Finset.mem_union.mp h).elim hq1 hq2
          simp [hq1, hq2, hqC]
    · simp only [hp1, ↓reduceIte]
      by_cases hq1 : q ∈ D.C₁
      · have hq2 : q ∉ D.C₂ := Finset.disjoint_left.mp D.hC_disj hq1
        have hqC : q ∈ C := Finset.mem_union_left _ hq1
        simp only [hq1, hq2, hqC, ↓reduceIte, mul_zero, zero_add]
        dsimp only [βc, p₁₂, p₂₁]
        field_simp
        ring
      · by_cases hq2 : q ∈ D.C₂
        · have hqC : q ∈ C := Finset.mem_union_right _ hq2
          simp only [hq1, hq2, hqC, ↓reduceIte]
          dsimp only [αc, βc, p₁₂, p₂₁]
          field_simp
          ring
        · have hqC : q ∉ C := fun h => (Finset.mem_union.mp h).elim hq1 hq2
          simp [hq1, hq2, hqC]
  have hw_in : ∀ q : Q, A.eval q (List.replicate D.ℓ D.a) ∈ C := by
    intro q
    rw [DFA.eval_replicate]
    have hqU : q ∈ D.B₁ ∪ D.B₂ := by rw [D.hB_union]; exact Finset.mem_univ q
    rcases Finset.mem_union.mp hqU with h1 | h2
    · exact Finset.mem_union_left _ (D.hB₁_enter q h1)
    · exact Finset.mem_union_right _ (D.hB₂_enter q h2)
  obtain ⟨w, hw, hlen⟩ := rankOne_uniform_reset_bound A hSync C hC_ne μ word (2 * L_E + 1)
    (List.replicate D.ℓ D.a) D.ℓ (by simp) hw_in hμ_nn hμ_sum hL hRankOne
  refine ⟨w, hw, le_trans hlen ?_⟩
  rw [hC_card]
  have hn1 : 1 ≤ Fintype.card Q := by
    have := D.hℓ_le; have := Finset.card_pos.mpr D.hC₁_ne; omega
  have hrew : Fintype.card Q - 1 + (2 * L_E + 1) = Fintype.card Q + 2 * L_E := by omega
  rw [hrew]

end TwoClusterData

/-- **Theorem D (General Mixing 2-Cluster Reset Bound, arbitrary `m₁, m₂` and arbitrary `ℓ ≥ 0`)**:
`rt(A) ≤ ℓ + (m - 1) * (n + 2 * ℓ + 2 * m - 4)`. -/
theorem twoCluster_mixing_reset_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α) (D : TwoClusterData A) (hSync : A.IsSynchronizing)
    (b : α)
    (hbal : (D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card =
            (D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card)
    (hmix : ((D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card : ℚ) / (D.C₁.card : ℚ) +
            ((D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card : ℚ) / (D.C₂.card : ℚ) ≥ 1) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ D.ℓ + (D.C₁.card + D.C₂.card - 1) *
        (Fintype.card Q + 2 * D.ℓ + 2 * (D.C₁.card + D.C₂.card) - 4) := by
  have hm₁ : 0 < D.C₁.card := Finset.card_pos.mpr D.hC₁_ne
  have hm₂ : 0 < D.C₂.card := Finset.card_pos.mpr D.hC₂_ne
  let η : Fin D.C₁.card × Fin D.C₂.card → ℚ :=
    fun _ => (1 : ℚ) / ((D.C₁.card : ℚ) * (D.C₂.card : ℚ))
  let eword : Fin D.C₁.card × Fin D.C₂.card → List α :=
    fun idx => List.replicate (D.ℓ + idx.1.val + idx.2.val) D.a
  have hη_nn : ∀ idx, 0 ≤ η idx := fun _ =>
    div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hη_sum : ∑ idx : Fin D.C₁.card × Fin D.C₂.card, η idx = 1 := by
    simp only [η, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul]
    have hne : ((D.C₁.card : ℚ) * (D.C₂.card : ℚ)) ≠ 0 := by positivity
    exact mul_one_div_cancel hne
  have hL : ∀ idx : Fin D.C₁.card × Fin D.C₂.card,
      (eword idx).length ≤ D.ℓ + (D.C₁.card + D.C₂.card) - 2 := by
    intro idx
    simp only [eword, List.length_replicate]
    have h1 := idx.1.isLt; have h2 := idx.2.isLt; omega
  obtain ⟨w, hw, hlen⟩ := TwoClusterData.thetaLift_of_ergodic D hSync η eword
    (D.ℓ + (D.C₁.card + D.C₂.card) - 2) hη_nn hη_sum hL (TwoClusterData.ergodic_double_matrix D)
    b hbal hmix
  refine ⟨w, hw, le_trans hlen ?_⟩
  have hrew : Fintype.card Q + 2 * (D.ℓ + (D.C₁.card + D.C₂.card) - 2) =
      Fintype.card Q + 2 * D.ℓ + 2 * (D.C₁.card + D.C₂.card) - 4 := by omega
  rw [hrew]

/-- **Theorem D (Quadratic Bound `≤ 3 * (n - 1) ^ 2` — Breaching Obstruction O.3!)**:
Every synchronizing balanced-mixing 2-cluster DFA with arbitrary cycle lengths `m₁, m₂` and
**arbitrary tree height `ℓ ≥ 0`** admits a synchronizing word of length at most `3 * (n - 1) ^ 2`. -/
theorem twoCluster_mixing_quadratic_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α) (D : TwoClusterData A) (hSync : A.IsSynchronizing)
    (b : α)
    (hbal : (D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card =
            (D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card)
    (hmix : ((D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card : ℚ) / (D.C₁.card : ℚ) +
            ((D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card : ℚ) / (D.C₂.card : ℚ) ≥ 1) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ 3 * (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ := twoCluster_mixing_reset_bound A D hSync b hbal hmix
  refine ⟨w, hw, le_trans hlen ?_⟩
  have hm₁ : 1 ≤ D.C₁.card := Finset.card_pos.mpr D.hC₁_ne
  have hm₂ : 1 ≤ D.C₂.card := Finset.card_pos.mpr D.hC₂_ne
  have hℓ := D.hℓ_le
  set m := D.C₁.card + D.C₂.card
  set n := Fintype.card Q
  have hm2 : 2 ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  have h1 : n + 2 * D.ℓ + 2 * m - 4 ≤ 3 * n - 4 := by omega
  have h2 : D.ℓ + (m - 1) * (n + 2 * D.ℓ + 2 * m - 4) ≤ D.ℓ + (m - 1) * (3 * n - 4) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ h1) _
  refine le_trans h2 ?_
  set t := n - m
  have hℓt : D.ℓ ≤ t := by omega
  have hm_eq : m - 1 = n - 1 - t := by omega
  have h3 : D.ℓ + (m - 1) * (3 * n - 4) ≤ t + (n - 1 - t) * (3 * n - 4) := by
    rw [hm_eq]; omega
  refine le_trans h3 ?_
  have ht_le : t ≤ n - 1 := by omega
  have h3n4 : 4 ≤ 3 * n := by omega
  have hn1 : 1 ≤ n := by omega
  zify [ht_le, h3n4, hn1]
  nlinarith

/-- **Theorem D (Equal-Cycle Mixing 2-Cluster Bound `≤ 2 * (n - 1) ^ 2`, arbitrary `ℓ ≥ 0`)**:
When `m₁ = m₂`, the sharper single-cycle ergodic projector yields
`rt(A) ≤ ℓ + (m - 1) * (n + 2 * ℓ + m - 2) ≤ 2 * (n - 1) ^ 2`! -/
theorem twoCluster_equalCycle_mixing_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q] (A : DFA Q α) (D : TwoClusterData A) (hSync : A.IsSynchronizing)
    (heq : D.C₁.card = D.C₂.card) (b : α)
    (hbal : (D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card =
            (D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card)
    (hmix : ((D.C₁.filter (fun c => A.step c b ∈ D.B₂)).card : ℚ) / (D.C₁.card : ℚ) +
            ((D.C₂.filter (fun c => A.step c b ∈ D.B₁)).card : ℚ) / (D.C₂.card : ℚ) ≥ 1) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ D.ℓ + (D.C₁.card + D.C₂.card - 1) *
        (Fintype.card Q + 2 * D.ℓ + (D.C₁.card + D.C₂.card) - 2) ∧
      w.length ≤ 2 * (Fintype.card Q - 1) ^ 2 := by
  have hm₁ : 1 ≤ D.C₁.card := Finset.card_pos.mpr D.hC₁_ne
  let η : Fin D.C₁.card → ℚ := fun _ => (1 : ℚ) / (D.C₁.card : ℚ)
  let eword : Fin D.C₁.card → List α := fun j => List.replicate (D.ℓ + j.val) D.a
  have hη_nn : ∀ j, 0 ≤ η j := fun _ => div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hη_sum : ∑ j : Fin D.C₁.card, η j = 1 := by
    simp only [η, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hne : (D.C₁.card : ℚ) ≠ 0 := by positivity
    exact mul_one_div_cancel hne
  have hL : ∀ j : Fin D.C₁.card, (eword j).length ≤ D.ℓ + D.C₁.card - 1 := by
    intro j; simp only [eword, List.length_replicate]; have := j.isLt; omega
  obtain ⟨w, hw, hlen⟩ := TwoClusterData.thetaLift_of_ergodic D hSync η eword
    (D.ℓ + D.C₁.card - 1) hη_nn hη_sum hL (TwoClusterData.ergodic_equal_matrix D heq) b hbal hmix
  have hrew : Fintype.card Q + 2 * (D.ℓ + D.C₁.card - 1) =
      Fintype.card Q + 2 * D.ℓ + (D.C₁.card + D.C₂.card) - 2 := by omega
  rw [hrew] at hlen
  refine ⟨w, hw, hlen, le_trans hlen ?_⟩
  have hℓ := D.hℓ_le
  set m := D.C₁.card + D.C₂.card
  set n := Fintype.card Q
  set t := n - m
  have hm2 : 2 ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  have hℓt : D.ℓ ≤ t := by omega
  have h1 : n + 2 * D.ℓ + m - 2 ≤ 2 * n + t - 2 := by omega
  have h2 : D.ℓ + (m - 1) * (n + 2 * D.ℓ + m - 2) ≤ t + (n - 1 - t) * (2 * n + t - 2) := by
    have hm_eq : m - 1 = n - 1 - t := by omega
    rw [hm_eq]
    exact Nat.add_le_add hℓt (Nat.mul_le_mul_left _ h1)
  refine le_trans h2 ?_
  have ht_le : t ≤ n - 1 := by omega
  have hn1 : 1 ≤ n := by omega
  have h2nt : 2 ≤ 2 * n + t := by omega
  zify [ht_le, hn1, h2nt]
  nlinarith

end Cerny
