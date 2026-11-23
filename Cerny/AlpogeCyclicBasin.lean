import Cerny.AlpogeThetaLift
import Mathlib.Tactic.Zify

/-!
# Alpöge-Method One-Sided Cyclic-Basin Theta Lift & Exact `(n - 1)^2` for `ℓ > 0` `c`-Cluster DFAs

This file formalizes the Round 2 spectral breakthrough (`docs/alpoge_spectral_round2.md` §1)
directly on top of `Cerny.AlpogeThetaLift`, using 100% pure `ℚ`-linear algebra with **NO strong
connectivity**, **arbitrary tree height `ℓ ≥ 0`**, **arbitrary `c ≥ 2` equal cycles**,
**non-bijective cyclic basin shift `b`**, and **arbitrary extra letters in `α`**:

* `Cerny.multiCluster_singleton_start` (**Lemma D.2**): For any synchronizing DFA and any letter `a`
  acting bijectively on `C` (`|C| ≥ 2`) with `Q · a^ℓ ⊆ C`, there exist `q ∈ C` and `w₀` of length
  `≤ (n - |C|) + 1 + ℓ` with `|{q} w₀⁻¹ ∩ C| ≥ 2` (NO strong connectivity needed!).
* `Cerny.cyclicBasin_reset_bound` (**Theorem D_cyc**): Eliminating the left `E₁(a)` produces the
  exact rank-1 one-sided theta lift `Q_b^{1-side} = (1 / c) ∑_j P_b^j E₁(a) = 1 · (1 / m) [C]`
  of max word length `L₁ = ℓ + c + m₀ - 2 ≤ n - 1`, yielding:
  `rt(A) ≤ ℓ + (m - 2) * (n - 1 + (ℓ + c + m₀ - 2)) + ((n - m) + 1 + ℓ)`.
* `Cerny.cyclicBasin_quadratic_bound`: Strictly `< 2 * (n - 1) ^ 2` for ALL `m ≤ n`, `ℓ ≥ 0`.
* `Cerny.cyclicBasin_threeHalves_bound`: Strictly `< (3 / 2) * (n - 1) ^ 2` whenever `m₀ ≥ 2`.
* `Cerny.cyclicBasin_halfCycle_cerny`: **EXACT ČERNÝ CONJECTURE `rt(A) ≤ (n - 1) ^ 2`**
  whenever `2 * m ≤ n` (all `c ≥ 2, m₀ ≥ 1, ℓ ≥ 0`)!
* `Cerny.cyclicBasin_sevenTwelfths_cerny`: **EXACT ČERNÝ CONJECTURE `rt(A) ≤ (n - 1) ^ 2`**
  whenever `m₀ ≥ 2` and `12 * m ≤ 7 * n` (all `c ≥ 2, ℓ ≥ 0`)!
-/

namespace Cerny

universe u v

/-- **Lemma D.2 (Multi-Cluster Steinberg Singleton Start over `ℚ` — NO Strong Connectivity!)**:
In any synchronizing DFA, if a letter `a` maps `C` (`|C| ≥ 2`) injectively into `C` and maps all
of `Q` into `C` in `ℓ` steps (`Q · a^ℓ ⊆ C`), then there exist `q ∈ C` and `w₀` with
`w₀.length ≤ (|Q| - |C|) + 1 + ℓ` and `2 ≤ (A.preimage {q} w₀ ∩ C).card`. -/
theorem multiCluster_singleton_start {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (a : α) (C : Finset Q) (hC_ge2 : 2 ≤ C.card) (ℓ : ℕ)
    (hC_maps : ∀ q ∈ C, A.step q a ∈ C)
    (hC_inj : Set.InjOn (fun q => A.step q a) C)
    (hQ_in : ∀ q : Q, A.eval q (List.replicate ℓ a) ∈ C) :
    ∃ q ∈ C, ∃ w₀ : List α,
      w₀.length ≤ (Fintype.card Q - C.card) + 1 + ℓ ∧
      2 ≤ (A.preimage {q} w₀ ∩ C).card := by
  classical
  have hC_eval_maps : ∀ (k : ℕ) (q : Q), q ∈ C → A.eval q (List.replicate k a) ∈ C := by
    intro k
    induction k with
    | zero => intro q hq; simpa using hq
    | succ k ih =>
      intro q hq
      rw [List.replicate_succ, DFA.eval_cons]
      exact ih (A.step q a) (hC_maps q hq)
  have hC_eval_inj : ∀ k : ℕ, Set.InjOn (fun q => A.eval q (List.replicate k a)) C := by
    intro k
    induction k with
    | zero => intro p _ q _ h; simpa using h
    | succ k ih =>
      intro p hp q hq heq
      dsimp only at heq
      rw [List.replicate_succ, DFA.eval_cons, DFA.eval_cons] at heq
      exact hC_inj hp hq (ih (hC_maps p hp) (hC_maps q hq) heq)
  let fℓ : Q → Q := fun q => A.eval q (List.replicate ℓ a)
  have hfℓ_maps : ∀ q ∈ C, fℓ q ∈ C := fun q hq => hC_eval_maps ℓ q hq
  have hfℓ_inj : Set.InjOn fℓ C := hC_eval_inj ℓ
  have hfℓ_img : C.image fℓ = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨p, hp, rfl⟩
      exact hfℓ_maps p hp
    · rw [Finset.card_image_of_injOn hfℓ_inj]
  have hfℓ_surj : ∀ q ∈ C, ∃ p ∈ C, fℓ p = q := by
    intro q hq
    rw [← hfℓ_img, Finset.mem_image] at hq
    exact hq
  -- Uniform distribution `πC` on `C` and centered vectors `z q`
  let m : ℚ := (C.card : ℚ)
  have hm_pos : (0 : ℚ) < m := by dsimp only [m]; exact_mod_cast (by omega : 0 < C.card)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  let πC : Q → ℚ := fun x => if x ∈ C then (1 : ℚ) / m else 0
  have hπC_sum : ∑ x : Q, πC x = 1 := by
    simp only [πC, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
    exact mul_one_div_cancel hm_ne
  let z : Q → (Q → ℚ) := fun q x => (if fℓ x = q then (1 : ℚ) else 0) - 1 / m
  have hdot_z_eval : ∀ (u : List α) (q : Q),
      AlpogeThetaLift.dotLin πC (AlpogeThetaLift.pullback A u (z q)) =
        (1 / m) * (((A.preimage {q} (u ++ List.replicate ℓ a) ∩ C).card : ℚ) - 1) := by
    intro u q
    simp only [AlpogeThetaLift.dotLin, AlpogeThetaLift.pullback, LinearMap.coe_mk, AddHom.coe_mk,
      πC, z, fℓ]
    have hsplit :
        ∑ p : Q, (if p ∈ C then (1 : ℚ) / m else 0) *
          ((if A.eval (A.eval p u) (List.replicate ℓ a) = q then (1 : ℚ) else 0) - 1 / m) =
        ∑ p ∈ C, (1 / m) *
          ((if A.eval p (u ++ List.replicate ℓ a) = q then (1 : ℚ) else 0) - 1 / m) := by
      rw [← Finset.sum_subset (Finset.subset_univ C)]
      · refine Finset.sum_congr rfl fun p hp => ?_
        simp only [hp, ↓reduceIte, DFA.eval_append]
      · intro p _ hp; simp [hp]
    rw [hsplit, ← Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1
    have h1 : ∑ p ∈ C, (if A.eval p (u ++ List.replicate ℓ a) = q then (1 : ℚ) else 0) =
        ((A.preimage {q} (u ++ List.replicate ℓ a) ∩ C).card : ℚ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 2
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter, DFA.mem_preimage, Finset.mem_singleton]
      tauto
    have h2 : ∑ _p ∈ C, (1 : ℚ) / m = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_one_div_cancel hm_ne
    rw [h1, h2]
  have hz_in_H : ∀ q ∈ C, AlpogeThetaLift.dotLin πC (z q) = 0 := by
    intro q hq
    obtain ⟨p₀, hp₀C, hp₀_eq⟩ := hfℓ_surj q hq
    have hdot := hdot_z_eval [] q
    rw [AlpogeThetaLift.pullback_nil, List.nil_append] at hdot
    have hset : A.preimage {q} (List.replicate ℓ a) ∩ C = {p₀} := by
      ext p
      simp only [Finset.mem_inter, DFA.mem_preimage, Finset.mem_singleton]
      constructor
      · rintro ⟨hp_eq, hpC⟩
        exact hfℓ_inj hpC hp₀C (hp_eq.trans hp₀_eq.symm)
      · rintro rfl
        exact ⟨hp₀_eq, hp₀C⟩
    rw [hset, Finset.card_singleton] at hdot
    simpa using hdot
  have hz_sum_zero : ∀ x : Q, ∑ q ∈ C, z q x = 0 := by
    intro x
    simp only [z, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h1 : ∑ q ∈ C, (if fℓ x = q then (1 : ℚ) else 0) = 1 := by
      rw [Finset.sum_eq_single (fℓ x)]
      · simp
      · intro q _ hq; simp [Ne.symm hq]
      · intro hnot; exact absurd (hQ_in x) hnot
    rw [h1, mul_one_div_cancel hm_ne, sub_self]
  -- Ascending chain `W k` escaping `H = ker (dotLin πC)`
  let H : Submodule ℚ (Q → ℚ) := LinearMap.ker (AlpogeThetaLift.dotLin πC)
  let W : ℕ → Submodule ℚ (Q → ℚ) := fun k =>
    Submodule.span ℚ { v : Q → ℚ | ∃ (u : List α) (q : Q), q ∈ C ∧ u.length ≤ k ∧
      v = AlpogeThetaLift.pullback A u (z q) }
  have hW_mono : ∀ {j k}, j ≤ k → W j ≤ W k := by
    intro j k hjk
    apply Submodule.span_mono
    rintro v ⟨u, q, hq, hu, rfl⟩
    exact ⟨u, q, hq, hu.trans hjk, rfl⟩
  have hW0_leH : W 0 ≤ H := by
    rw [Submodule.span_le]
    rintro v ⟨u, q, hq, hu, rfl⟩
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu0
    rw [AlpogeThetaLift.pullback_nil]
    exact hz_in_H q hq
  -- Lower bound `C.card - 1 ≤ finrank (W 0)` via restriction to `C`
  have hW0_dim : C.card - 1 ≤ Module.finrank ℚ (W 0) := by
    let res : (Q → ℚ) →ₗ[ℚ] ({x : Q // x ∈ C} → ℚ) :=
      { toFun := fun v p => v p.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let sumC : ({x : Q // x ∈ C} → ℚ) →ₗ[ℚ] ℚ :=
      { toFun := fun w => ∑ p : {x : Q // x ∈ C}, w p
        map_add' := fun _ _ => by simp only [Pi.add_apply, Finset.sum_add_distrib]
        map_smul' := fun c w => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum] }
    have hsumC_surj : Function.Surjective sumC := by
      obtain ⟨c₀, hc₀⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
      intro r
      refine ⟨Pi.single ⟨c₀, hc₀⟩ r, ?_⟩
      simp only [sumC, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single ⟨c₀, hc₀⟩]
      · simp [Pi.single_eq_same]
      · intro p _ hp; simp [Pi.single_eq_of_ne hp]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hker_dim : Module.finrank ℚ (LinearMap.ker sumC) = C.card - 1 := by
      have hrn := LinearMap.finrank_range_add_finrank_ker sumC
      rw [LinearMap.range_eq_top.mpr hsumC_surj, finrank_top, Module.finrank_self,
        Module.finrank_pi, Fintype.card_coe] at hrn
      omega
    have hker_le_map : LinearMap.ker sumC ≤ (W 0).map res := by
      intro w hw
      have hw_sum : ∑ p : {x : Q // x ∈ C}, w p = 0 := hw
      let v : Q → ℚ := ∑ p : {x : Q // x ∈ C}, w p • z (fℓ p.1)
      have hv_mem : v ∈ W 0 := by
        refine Submodule.sum_mem (W 0) fun p _ => Submodule.smul_mem (W 0) (w p) ?_
        exact Submodule.subset_span ⟨[], fℓ p.1, hfℓ_maps p.1 p.2, le_rfl, rfl⟩
      refine ⟨v, hv_mem, ?_⟩
      ext r
      change (∑ p : {x : Q // x ∈ C}, w p • z (fℓ p.1)) r.1 = w r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, z, mul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hw_sum, zero_mul, sub_zero]
      rw [Finset.sum_eq_single r]
      · simp
      · intro p _ hpr
        have hne_f : fℓ r.1 ≠ fℓ p.1 := fun heq => hpr (Subtype.ext (hfℓ_inj p.2 r.2 heq.symm))
        simp [hne_f]
      · intro h; exact absurd (Finset.mem_univ r) h
    have h1 : Module.finrank ℚ (LinearMap.ker sumC) ≤ Module.finrank ℚ ((W 0).map res) :=
      Submodule.finrank_mono hker_le_map
    have h2 : Module.finrank ℚ ((W 0).map res) ≤ Module.finrank ℚ (W 0) :=
      Submodule.finrank_map_le res (W 0)
    omega
  -- Escape from `H` via synchronization (NO strong connectivity needed!)
  rcases hSync with ⟨w_sync, r₀, hr₀⟩
  let q₀ : Q := fℓ r₀
  have hq₀C : q₀ ∈ C := hQ_in r₀
  have hsync_notH : AlpogeThetaLift.pullback A w_sync (z q₀) ∉ H := by
    intro hmem
    change AlpogeThetaLift.dotLin πC (AlpogeThetaLift.pullback A w_sync (z q₀)) = 0 at hmem
    have hconst : ∀ p : Q,
        AlpogeThetaLift.pullback A w_sync (z q₀) p = 1 - 1 / m := by
      intro p
      simp only [AlpogeThetaLift.pullback, LinearMap.coe_mk, AddHom.coe_mk, z, hr₀ p, q₀,
        ↓reduceIte]
    simp only [AlpogeThetaLift.dotLin, LinearMap.coe_mk, AddHom.coe_mk] at hmem
    simp_rw [hconst, ← Finset.sum_mul, hπC_sum, one_mul] at hmem
    have hm_ge2 : (2 : ℚ) ≤ m := by dsimp only [m]; exact_mod_cast hC_ge2
    have h1m : 1 / m < 1 := by
      have hmul : (1 / m) * m = 1 := one_div_mul_cancel hm_ne
      nlinarith
    linarith
  have hex_esc : ∃ k : ℕ, ¬ (W k ≤ H) :=
    ⟨w_sync.length, fun hle => hsync_notH (hle (Submodule.subset_span ⟨w_sync, q₀, hq₀C, le_rfl, rfl⟩))⟩
  let j₀ := Nat.find hex_esc
  have hj₀_not : ¬ (W j₀ ≤ H) := Nat.find_spec hex_esc
  have hj₀_min : ∀ k < j₀, W k ≤ H := fun k hk => not_not.mp (Nat.find_min hex_esc hk)
  have hj₀_pos : 1 ≤ j₀ := by
    by_contra h0
    have hj0 : j₀ = 0 := by omega
    rw [hj0] at hj₀_not
    exact hj₀_not hW0_leH
  have hstrict : ∀ k, k + 1 < j₀ → W k < W (k + 1) := by
    intro k hk
    refine lt_of_le_of_ne (hW_mono (Nat.le_succ k)) fun heq => ?_
    have hclosed : ∀ (g : α) (v : Q → ℚ), v ∈ W k → AlpogeThetaLift.pullback A [g] v ∈ W k := by
      intro g v hv
      rw [heq]
      induction hv using Submodule.span_induction with
      | mem x hx =>
        rcases hx with ⟨u, q, hq, hu, rfl⟩
        rw [← AlpogeThetaLift.pullback_cons]
        exact Submodule.subset_span ⟨g :: u, q, hq, by simp; omega, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact (W (k + 1)).add_mem hx hy
      | smul c x _ hx => rw [map_smul]; exact (W (k + 1)).smul_mem c hx
    have hall : ∀ (u : List α) (q : Q), q ∈ C → AlpogeThetaLift.pullback A u (z q) ∈ W k := by
      intro u
      induction u with
      | nil => intro q hq; exact Submodule.subset_span ⟨[], q, hq, Nat.zero_le k, rfl⟩
      | cons g u ih =>
        intro q hq
        rw [AlpogeThetaLift.pullback_cons]
        exact hclosed g _ (ih q hq)
    exact hsync_notH (hj₀_min k (by omega) (hall w_sync q₀ hq₀C))
  have hdim : ∀ k ≤ j₀ - 1, (C.card - 1) + k ≤ Module.finrank ℚ (W k) := by
    intro k
    induction k with
    | zero => intro _; simpa using hW0_dim
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hlt := Submodule.finrank_lt_finrank_of_lt (hstrict k (by omega))
      omega
  have hj₀_le : j₀ ≤ Fintype.card Q - C.card + 1 := by
    have h1 := hdim (j₀ - 1) le_rfl
    have h2 : Module.finrank ℚ (W (j₀ - 1)) ≤ Module.finrank ℚ H :=
      Submodule.finrank_mono (hj₀_min (j₀ - 1) (by omega))
    rw [AlpogeThetaLift.finrank_ker_dotLin hπC_sum] at h2
    have hC_le_n : C.card ≤ Fintype.card Q := Finset.card_le_univ C
    omega
  -- Extract generator `(u, q')` outside `H`, then use `∑_{q ∈ C} z q = 0` to get `> 0`!
  have hex_gen : ∃ (u : List α) (q' : Q), q' ∈ C ∧ u.length ≤ j₀ ∧
      AlpogeThetaLift.dotLin πC (AlpogeThetaLift.pullback A u (z q')) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hj₀_not
    rw [Submodule.span_le]
    rintro v ⟨u, q, hq, hu, rfl⟩
    exact hall u q hq hu
  rcases hex_gen with ⟨u, q', hq'C, hulen, hq'_nz⟩
  have hsum_u_zero : ∑ q ∈ C, AlpogeThetaLift.dotLin πC (AlpogeThetaLift.pullback A u (z q)) = 0 := by
    rw [← map_sum, ← map_sum]
    have hz0 : (∑ q ∈ C, z q) = 0 := by
      ext x; simp only [Finset.sum_apply, Pi.zero_apply]; exact hz_sum_zero x
    rw [hz0, map_zero, map_zero]
  have hex_pos : ∃ q ∈ C, 0 < AlpogeThetaLift.dotLin πC (AlpogeThetaLift.pullback A u (z q)) := by
    by_contra hall
    push Not at hall
    have hlt_q' : AlpogeThetaLift.dotLin πC (AlpogeThetaLift.pullback A u (z q')) < 0 :=
      lt_of_le_of_ne (hall q' hq'C) hq'_nz
    have hsum_lt : ∑ q ∈ C, AlpogeThetaLift.dotLin πC (AlpogeThetaLift.pullback A u (z q)) <
        ∑ _q ∈ C, (0 : ℚ) :=
      Finset.sum_lt_sum (fun q hq => hall q hq) ⟨q', hq'C, hlt_q'⟩
    rw [hsum_u_zero, Finset.sum_const_zero] at hsum_lt
    exact lt_irrefl _ hsum_lt
  rcases hex_pos with ⟨q, hqC, hq_pos⟩
  rw [hdot_z_eval u q] at hq_pos
  have h1m_pos : (0 : ℚ) < 1 / m := div_pos zero_lt_one hm_pos
  have hcard_gt1 : (1 : ℚ) < ((A.preimage {q} (u ++ List.replicate ℓ a) ∩ C).card : ℚ) := by
    nlinarith
  have hcard_ge2 : 2 ≤ (A.preimage {q} (u ++ List.replicate ℓ a) ∩ C).card := by
    have hlt : 1 < (A.preimage {q} (u ++ List.replicate ℓ a) ∩ C).card := by exact_mod_cast hcard_gt1
    omega
  refine ⟨q, hqC, u ++ List.replicate ℓ a, ?_, hcard_ge2⟩
  simp only [List.length_append, List.length_replicate]
  omega

/-- Data witnessing a `c`-cluster equal-cycle letter `a` (`c ≥ 2` disjoint cycles of length
`m₀ ≥ 1`, disjoint basins `B i` covering `Q`, level `ℓ` with `ℓ + c * m₀ ≤ |Q|` and
`B i · a^ℓ ⊆ C i`) together with a (NOT necessarily bijective!) cyclic basin-shift letter `b`
satisfying `B i · b ⊆ B ((i + 1) mod c)`. -/
structure CyclicBasinData {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a b : α) where
  c : ℕ
  m₀ : ℕ
  hc : 2 ≤ c
  hm₀ : 1 ≤ m₀
  C : Fin c → Finset Q
  B : Fin c → Finset Q
  ℓ : ℕ
  hB_disj : ∀ i j : Fin c, i ≠ j → Disjoint (B i) (B j)
  hC_disj : ∀ i j : Fin c, i ≠ j → Disjoint (C i) (C j)
  hB_cover : ∀ q : Q, ∃ i : Fin c, q ∈ B i
  hC_card : ∀ i : Fin c, (C i).card = m₀
  hC_maps : ∀ i : Fin c, ∀ q ∈ C i, A.step q a ∈ C i
  hC_cycle : ∀ i : Fin c, ∀ p ∈ C i, ∀ q ∈ C i,
    ∃ s < m₀, A.eval p (List.replicate s a) = q
  hB_enter : ∀ i : Fin c, ∀ q ∈ B i, A.eval q (List.replicate ℓ a) ∈ C i
  hℓ_le : ℓ + c * m₀ ≤ Fintype.card Q
  hb_shift : ∀ i : Fin c, ∀ q ∈ B i,
    A.step q b ∈ B ⟨(i.1 + 1) % c, Nat.mod_lt _ (by omega)⟩

namespace AlpogeCyclicBasin

private lemma replicate_succ_append {α : Type v} (k : ℕ) (a : α) :
    List.replicate k a ++ [a] = List.replicate (k + 1) a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, ih, ← List.replicate_succ]

private lemma eval_replicate_in_cycle {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} {a b : α} (D : CyclicBasinData A a b) (i : Fin D.c) :
    ∀ (k : ℕ) (q : Q), q ∈ D.C i → A.eval q (List.replicate k a) ∈ D.C i := by
  intro k
  induction k with
  | zero => intro q hq; simpa using hq
  | succ k ih =>
    intro q hq
    rw [List.replicate_succ, DFA.eval_cons]
    exact ih (A.step q a) (D.hC_maps i q hq)

private lemma cycle_orbit_bijective {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} {a b : α} (D : CyclicBasinData A a b) (i : Fin D.c)
    {p : Q} (hp : p ∈ D.C i) :
    Function.Injective (fun s : Fin D.m₀ => A.eval p (List.replicate s.1 a)) ∧
    Finset.univ.image (fun s : Fin D.m₀ => A.eval p (List.replicate s.1 a)) = D.C i := by
  let g : Fin D.m₀ → Q := fun s => A.eval p (List.replicate s.1 a)
  have himg : Finset.univ.image g = D.C i := by
    ext q
    simp only [Finset.mem_image, Finset.mem_univ, true_and, g]
    constructor
    · rintro ⟨s, rfl⟩; exact eval_replicate_in_cycle D i s.1 p hp
    · intro hq
      obtain ⟨s, hs, hsq⟩ := D.hC_cycle i p hp q hq
      exact ⟨⟨s, hs⟩, hsq⟩
  have hcard : (Finset.univ.image g).card = (Finset.univ : Finset (Fin D.m₀)).card := by
    rw [himg, D.hC_card i, Finset.card_univ, Fintype.card_fin]
  have hinjOn : Set.InjOn g (Finset.univ : Finset (Fin D.m₀)) := Finset.card_image_iff.mp hcard
  exact ⟨fun s₁ s₂ h => hinjOn (Finset.mem_univ s₁) (Finset.mem_univ s₂) h, himg⟩

private lemma cycle_step_injOn {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} {a b : α} (D : CyclicBasinData A a b) (i : Fin D.c) :
    Set.InjOn (fun q => A.step q a) (D.C i) := by
  have hm₀_pos : 0 < D.m₀ := by have := D.hm₀; omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [D.hC_card i]; omega : 0 < (D.C i).card)
  obtain ⟨hg_inj, hg_img⟩ := cycle_orbit_bijective D i hp
  let g : Fin D.m₀ → Q := fun s => A.eval p (List.replicate s.1 a)
  have hper : A.eval p (List.replicate D.m₀ a) = p := by
    have hmem : A.eval p (List.replicate D.m₀ a) ∈ Finset.univ.image g := by
      rw [hg_img]; exact eval_replicate_in_cycle D i D.m₀ p hp
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨k, _, hk⟩
    by_cases hk0 : k.1 = 0
    · have : k = ⟨0, hm₀_pos⟩ := Fin.ext hk0
      rw [this] at hk
      simpa [g] using hk.symm
    · exfalso
      have htrap : ∀ t : ℕ, ∃ s : Fin D.m₀, k.1 ≤ s.1 ∧
          A.eval (g k) (List.replicate t a) = g s := by
        intro t
        induction t with
        | zero => exact ⟨k, le_rfl, by simp⟩
        | succ t ih =>
          rcases ih with ⟨s, hks, hts⟩
          have hstep : A.eval (g k) (List.replicate (t + 1) a) =
              A.eval p (List.replicate (s.1 + 1) a) := by
            rw [← replicate_succ_append t a, DFA.eval_append, hts, DFA.eval_singleton]
            dsimp only [g]
            rw [← DFA.eval_singleton, ← DFA.eval_append, replicate_succ_append s.1 a]
          rw [hstep]
          by_cases hs : s.1 + 1 < D.m₀
          · exact ⟨⟨s.1 + 1, hs⟩, by dsimp; omega, rfl⟩
          · have hseq : s.1 + 1 = D.m₀ := by omega
            rw [hseq, ← hk]
            exact ⟨k, le_rfl, rfl⟩
      have hgk_mem : g k ∈ D.C i := eval_replicate_in_cycle D i k.1 p hp
      obtain ⟨t, _, ht⟩ := D.hC_cycle i (g k) hgk_mem p hp
      obtain ⟨s, hks, hts⟩ := htrap t
      have heq0 : g s = g ⟨0, hm₀_pos⟩ := by
        calc g s = A.eval (g k) (List.replicate t a) := hts.symm
          _ = p := ht
          _ = g ⟨0, hm₀_pos⟩ := by simp [g]
      have hs0 : s.1 = 0 := congrArg Fin.val (hg_inj heq0)
      omega
  have himg_step : (D.C i).image (fun q => A.step q a) = D.C i := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨q, hq, rfl⟩
      exact D.hC_maps i q hq
    · have hsub : D.C i ⊆ (D.C i).image (fun q => A.step q a) := by
        intro q hq
        rw [← hg_img, Finset.mem_image] at hq
        rcases hq with ⟨s, _, rfl⟩
        rw [Finset.mem_image]
        by_cases hs0 : s.1 = 0
        · refine ⟨g ⟨D.m₀ - 1, by omega⟩, eval_replicate_in_cycle D i (D.m₀ - 1) p hp, ?_⟩
          have h1 : A.step (g ⟨D.m₀ - 1, by omega⟩) a = A.eval p (List.replicate D.m₀ a) := by
            dsimp only [g]
            rw [← DFA.eval_singleton, ← DFA.eval_append, replicate_succ_append,
              show D.m₀ - 1 + 1 = D.m₀ by omega]
          rw [h1, hper]
          have : s = ⟨0, hm₀_pos⟩ := Fin.ext hs0
          simp [this]
        · refine ⟨g ⟨s.1 - 1, by omega⟩, eval_replicate_in_cycle D i (s.1 - 1) p hp, ?_⟩
          dsimp only [g]
          rw [← DFA.eval_singleton, ← DFA.eval_append, replicate_succ_append,
            show s.1 - 1 + 1 = s.1 by omega]
      exact Finset.card_le_card hsub
  exact Finset.card_image_iff.mp (congrArg Finset.card himg_step)

private lemma eval_replicate_b_shift {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} {a b : α} (D : CyclicBasinData A a b) :
    ∀ (j : ℕ) (i : Fin D.c) (q : Q), q ∈ D.B i →
      A.eval q (List.replicate j b) ∈ D.B ⟨(i.1 + j) % D.c, Nat.mod_lt _ (by have := D.hc; omega)⟩ := by
  intro j
  induction j with
  | zero =>
    intro i q hq
    simp only [List.replicate_zero, DFA.eval_nil, add_zero]
    have : (⟨i.1 % D.c, Nat.mod_lt _ (by have := D.hc; omega)⟩ : Fin D.c) = i :=
      Fin.ext (Nat.mod_eq_of_lt i.2)
    rwa [this]
  | succ j ih =>
    intro i q hq
    rw [List.replicate_succ, DFA.eval_cons]
    have h1 := D.hb_shift i q hq
    have h2 := ih ⟨(i.1 + 1) % D.c, Nat.mod_lt _ (by have := D.hc; omega)⟩ (A.step q b) h1
    have hidx : (⟨((i.1 + 1) % D.c + j) % D.c, Nat.mod_lt _ (by have := D.hc; omega)⟩ : Fin D.c) =
        ⟨(i.1 + (j + 1)) % D.c, Nat.mod_lt _ (by have := D.hc; omega)⟩ := by
      apply Fin.ext
      dsimp only
      rw [Nat.mod_add_mod]
      congr 1; omega
    rwa [hidx] at h2

end AlpogeCyclicBasin

/-- **Theorem D_cyc (Sharp One-Sided Cyclic-Basin Reset Bound — Arbitrary `c ≥ 2, m₀ ≥ 1, ℓ ≥ 0`)**:
In ANY synchronizing DFA (NO strong connectivity!) admitting `CyclicBasinData A a b`,
the one-sided theta lift `Q_b^{1-side} = (1 / (c * m₀)) ∑_{j < c, s < m₀} P_{b^j a^{ℓ + s}}`
is exact rank-1 uniform on `C = ⋃_i C i` of max length `L₁ = ℓ + c + m₀ - 2`, yielding:
`w.length ≤ ℓ + (c * m₀ - 2) * (n - 1 + (ℓ + c + m₀ - 2)) + ((n - c * m₀) + 1 + ℓ)`. -/
theorem cyclicBasin_reset_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a b : α) (hSync : A.IsSynchronizing)
    (D : CyclicBasinData A a b) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ D.ℓ + (D.c * D.m₀ - 2) * (Fintype.card Q - 1 + (D.ℓ + D.c + D.m₀ - 2)) +
        ((Fintype.card Q - D.c * D.m₀) + 1 + D.ℓ) := by
  classical
  have hc_pos : 0 < D.c := by have := D.hc; omega
  have hm₀_pos : 0 < D.m₀ := by have := D.hm₀; omega
  let C_all : Finset Q := Finset.univ.biUnion D.C
  have hC_disj' : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin D.c)) : Set (Fin D.c)) D.C := by
    intro i _ j _ hij
    exact D.hC_disj i j hij
  have hCall_card : C_all.card = D.c * D.m₀ := by
    rw [Finset.card_biUnion hC_disj']
    simp only [D.hC_card, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id]
  have hm_ge2 : 2 ≤ C_all.card := by
    rw [hCall_card]
    have := D.hc; have := D.hm₀; nlinarith
  -- Step 1: Verify hypotheses of Lemma D.2 (`multiCluster_singleton_start`) on `C_all`
  have hCall_maps : ∀ q ∈ C_all, A.step q a ∈ C_all := by
    intro q hq
    simp only [C_all, Finset.mem_biUnion, Finset.mem_univ, true_and] at hq ⊢
    rcases hq with ⟨i, hqi⟩
    exact ⟨i, D.hC_maps i q hqi⟩
  have hCall_inj : Set.InjOn (fun q => A.step q a) C_all := by
    intro p hp q hq heq
    have hstep_eq : A.step p a = A.step q a := heq
    simp only [Finset.mem_coe, C_all, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp hq
    rcases hp with ⟨i, hpi⟩
    rcases hq with ⟨j, hqj⟩
    have hij : i = j := by
      by_contra hne
      have hdisj := D.hC_disj i j hne
      rw [Finset.disjoint_left] at hdisj
      have hqj' : A.step p a ∈ D.C j := hstep_eq ▸ D.hC_maps j q hqj
      exact hdisj (D.hC_maps i p hpi) hqj'
    subst hij
    exact AlpogeCyclicBasin.cycle_step_injOn D i hpi hqj heq
  have hQ_in : ∀ q : Q, A.eval q (List.replicate D.ℓ a) ∈ C_all := by
    intro q
    obtain ⟨i, hqi⟩ := D.hB_cover q
    simp only [C_all, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, D.hB_enter i q hqi⟩
  -- Step 2: Apply Lemma D.2 to get singleton start `q₀ ∈ C_all`, `|w₀| ≤ (n - m) + 1 + ℓ`, `|S₀| ≥ 2`
  obtain ⟨q₀, hq₀C, w₀, hw₀_len, hw₀_ge2⟩ :=
    multiCluster_singleton_start A hSync a C_all hm_ge2 D.ℓ hCall_maps hCall_inj hQ_in
  -- Step 3: Build the one-sided rank-1 uniform theta lift `Q_b^{1-side}` of length `L₁ = ℓ + c + m₀ - 2`
  let ι := Fin D.c × Fin D.m₀
  let L₁ : ℕ := D.ℓ + D.c + D.m₀ - 2
  let word : ι → List α := fun p => List.replicate p.1.1 b ++ List.replicate (D.ℓ + p.2.1) a
  let mQ : ℚ := (C_all.card : ℚ)
  have hmQ_pos : (0 : ℚ) < mQ := by dsimp only [mQ]; exact_mod_cast (by omega : 0 < C_all.card)
  have hmQ_ne : mQ ≠ 0 := ne_of_gt hmQ_pos
  let μ : ι → ℚ := fun _ => (1 : ℚ) / mQ
  let π : Q → ℚ := fun q => if q ∈ C_all then (1 : ℚ) / mQ else 0
  have hπ_nonneg : ∀ q : Q, 0 ≤ π q := fun q => by
    dsimp only [π]; split_ifs
    · exact div_nonneg zero_le_one hmQ_pos.le
    · exact le_rfl
  have hπ_supp : ∀ q : Q, 0 < π q ↔ q ∈ C_all := fun q => by
    dsimp only [π]; split_ifs with h
    · exact ⟨fun _ => h, fun _ => div_pos zero_lt_one hmQ_pos⟩
    · exact ⟨fun h0 => absurd h0 (lt_irrefl _), fun hq => absurd hq h⟩
  have hπ_sum : ∑ q : Q, π q = 1 := by
    simp only [π, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
    exact mul_one_div_cancel hmQ_ne
  have hμ_nonneg : ∀ i : ι, 0 ≤ μ i := fun _ => div_nonneg zero_le_one hmQ_pos.le
  have hμ_sum : ∑ i : ι, μ i = 1 := by
    dsimp only [ι, μ]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    rw [show ((D.c * D.m₀ : ℕ) : ℚ) = mQ by simp [mQ, hCall_card]]
    exact mul_one_div_cancel hmQ_ne
  have hL₁ : ∀ i : ι, 0 < μ i → (word i).length ≤ L₁ := by
    intro ⟨j, s⟩ _
    simp only [word, L₁, List.length_append, List.length_replicate]
    have hj := j.2; have hs := s.2; have := D.hc; have := D.hm₀; omega
  have hRankOne : ∀ p q : Q, (∑ i : ι, if A.eval p (word i) = q then μ i else 0) = π q := by
    intro p q
    obtain ⟨i₀, hpBi₀⟩ := D.hB_cover p
    rw [Fintype.sum_prod_type]
    have hinner : ∀ j : Fin D.c,
        (∑ s : Fin D.m₀, if A.eval p (word (j, s)) = q then μ (j, s) else 0) =
          if q ∈ D.C ⟨(i₀.1 + j.1) % D.c, Nat.mod_lt _ hc_pos⟩ then (1 : ℚ) / mQ else 0 := by
      intro j
      let r : Fin D.c := ⟨(i₀.1 + j.1) % D.c, Nat.mod_lt _ hc_pos⟩
      let pj : Q := A.eval (A.eval p (List.replicate j.1 b)) (List.replicate D.ℓ a)
      have hpj_mem : pj ∈ D.C r :=
        D.hB_enter r _ (AlpogeCyclicBasin.eval_replicate_b_shift D j.1 i₀ p hpBi₀)
      obtain ⟨hg_inj, hg_img⟩ := AlpogeCyclicBasin.cycle_orbit_bijective D r hpj_mem
      have heval_eq : ∀ s : Fin D.m₀, A.eval p (word (j, s)) = A.eval pj (List.replicate s.1 a) := by
        intro s
        simp only [word, pj, DFA.eval_append, List.replicate_add]
      simp_rw [heval_eq]
      change (∑ s : Fin D.m₀, if A.eval pj (List.replicate s.1 a) = q then μ (j, s) else 0) =
        if q ∈ D.C r then (1 : ℚ) / mQ else 0
      by_cases hqCr : q ∈ D.C r
      · simp only [hqCr, ↓reduceIte, μ]
        rw [← hg_img, Finset.mem_image] at hqCr
        rcases hqCr with ⟨s₀, _, hs₀⟩
        rw [Finset.sum_eq_single s₀]
        · simp [hs₀]
        · intro s _ hsne
          have hne : A.eval pj (List.replicate s.1 a) ≠ q := fun heq =>
            hsne (hg_inj (heq.trans hs₀.symm))
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ s₀) h
      · simp only [hqCr, ↓reduceIte]
        refine Finset.sum_eq_zero fun s _ => ?_
        have hne : A.eval pj (List.replicate s.1 a) ≠ q := fun heq =>
          hqCr (heq ▸ AlpogeCyclicBasin.eval_replicate_in_cycle D r s.1 pj hpj_mem)
        simp only [hne, ↓reduceIte]
    simp_rw [hinner]
    -- Re-index `j : Fin D.c` via the cyclic shift bijection `r(j) = (i₀ + j) % c`
    let shift : Fin D.c → Fin D.c := fun j => ⟨(i₀.1 + j.1) % D.c, Nat.mod_lt _ hc_pos⟩
    have hshift_bij : Function.Bijective shift := by
      refine (Fintype.bijective_iff_surjective_and_card shift).mpr ⟨?_, rfl⟩
      intro r
      refine ⟨⟨(r.1 + D.c - i₀.1) % D.c, Nat.mod_lt _ hc_pos⟩, ?_⟩
      apply Fin.ext
      dsimp only [shift]
      rw [Nat.add_mod_mod]
      have hsum : i₀.1 + (r.1 + D.c - i₀.1) = r.1 + D.c := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt r.2]
    let eShift : Fin D.c ≃ Fin D.c := Equiv.ofBijective shift hshift_bij
    have hsum_reindex :
        (∑ j : Fin D.c, if q ∈ D.C (shift j) then (1 : ℚ) / mQ else 0) =
        ∑ r : Fin D.c, if q ∈ D.C r then (1 : ℚ) / mQ else 0 :=
      Equiv.sum_comp eShift (fun r : Fin D.c => if q ∈ D.C r then (1 : ℚ) / mQ else 0)
    rw [hsum_reindex]
    by_cases hqC : q ∈ C_all
    · simp only [π, hqC, ↓reduceIte]
      simp only [C_all, Finset.mem_biUnion, Finset.mem_univ, true_and] at hqC
      rcases hqC with ⟨r₀, hqr₀⟩
      rw [Finset.sum_eq_single r₀]
      · simp [hqr₀]
      · intro r _ hrne
        have hnot : q ∉ D.C r := fun hqr =>
          (Finset.disjoint_left.mp (D.hC_disj r₀ r hrne.symm)) hqr₀ hqr
        simp [hnot]
      · intro h; exact absurd (Finset.mem_univ r₀) h
    · simp only [π, hqC, ↓reduceIte]
      refine Finset.sum_eq_zero fun r _ => ?_
      have hnot : q ∉ D.C r := fun hqr =>
        hqC (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ r, hqr⟩)
      simp [hnot]
  -- Step 4: Iteratively extend `S₀ = {q₀} w₀⁻¹ ∩ C_all` (`|S₀| ≥ 2`) to `C_all` in ≤ `m - 2` steps!
  have hext_step : ∀ S : Finset Q, S.Nonempty → S ⊂ C_all →
      ∃ u : List α, u.length ≤ Fintype.card Q - 1 + L₁ ∧ S.card < (A.preimage S u ∩ C_all).card := by
    intro S hSne hSsub
    obtain ⟨u, hulen, hgt⟩ := rankOne_exists_extending_word A hSync C_all π μ word L₁
      hπ_nonneg hπ_supp hπ_sum hμ_nonneg hμ_sum hL₁ hRankOne hSne hSsub
    refine ⟨u, hulen, ?_⟩
    have hsum_S : ∑ x ∈ S, π x = (S.card : ℚ) * (1 / mQ) := by
      have hsub : S ⊆ C_all := hSsub.1
      calc ∑ x ∈ S, π x = ∑ _x ∈ S, (1 / mQ) :=
            Finset.sum_congr rfl fun x hx => by simp [π, hsub hx]
        _ = (S.card : ℚ) * (1 / mQ) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hsum_pre : ∑ q ∈ A.preimage S u, π q = ((A.preimage S u ∩ C_all).card : ℚ) * (1 / mQ) := by
      calc ∑ q ∈ A.preimage S u, π q
          = ∑ q ∈ (A.preimage S u).filter (· ∈ C_all), (1 / mQ) := by
            simp only [π]; rw [Finset.sum_filter]
        _ = ((A.preimage S u ∩ C_all).card : ℚ) * (1 / mQ) := by
            rw [Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul]
    rw [hsum_S, hsum_pre] at hgt
    have h1m_pos : (0 : ℚ) < 1 / mQ := div_pos zero_lt_one hmQ_pos
    have hlt_q : (S.card : ℚ) < ((A.preimage S u ∩ C_all).card : ℚ) := by nlinarith
    exact_mod_cast hlt_q
  have hbuild : ∀ d : ℕ, ∀ S : Finset Q, S.Nonempty → S ⊆ C_all → C_all.card - S.card ≤ d →
      ∃ v : List α, v.length ≤ d * (Fintype.card Q - 1 + L₁) ∧ C_all ⊆ A.preimage S v := by
    intro d
    induction d with
    | zero =>
      intro S _ hSC hle
      have hcard_eq : S.card = C_all.card := le_antisymm (Finset.card_le_card hSC) (by omega)
      have hSeq : S = C_all := Finset.eq_of_subset_of_card_le hSC (by omega)
      exact ⟨[], by simp, by rw [DFA.preimage_nil, hSeq]⟩
    | succ d ih =>
      intro S hSne hSC hle
      by_cases hfull : S = C_all
      · exact ⟨[], Nat.zero_le _, by rw [DFA.preimage_nil, hfull]⟩
      · have hSsub : S ⊂ C_all := Finset.ssubset_iff_subset_ne.mpr ⟨hSC, hfull⟩
        obtain ⟨u, hulen, hugt⟩ := hext_step S hSne hSsub
        let S' : Finset Q := A.preimage S u ∩ C_all
        have hS'ne : S'.Nonempty := Finset.card_pos.mp (lt_trans (Finset.card_pos.mpr hSne) hugt)
        have hS'sub : S' ⊆ C_all := Finset.inter_subset_right
        have hS'card : S'.card = (A.preimage S u ∩ C_all).card := rfl
        obtain ⟨v, hvlen, hvsub⟩ := ih S' hS'ne hS'sub (by omega)
        refine ⟨v ++ u, ?_, ?_⟩
        · rw [List.length_append]
          calc v.length + u.length
              ≤ d * (Fintype.card Q - 1 + L₁) + (Fintype.card Q - 1 + L₁) := Nat.add_le_add hvlen hulen
            _ = (d + 1) * (Fintype.card Q - 1 + L₁) := by ring
        · intro q hq
          have hq' := hvsub hq
          rw [DFA.mem_preimage] at hq'
          rw [DFA.mem_preimage, DFA.eval_append]
          have hmem : A.eval q v ∈ A.preimage S u := (Finset.mem_inter.mp hq').1
          rwa [DFA.mem_preimage] at hmem
  let S₀ : Finset Q := A.preimage {q₀} w₀ ∩ C_all
  have hS₀_card : 2 ≤ S₀.card := hw₀_ge2
  have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp (by omega)
  have hS₀_sub : S₀ ⊆ C_all := Finset.inter_subset_right
  obtain ⟨v, hvlen, hvsub⟩ := hbuild (C_all.card - 2) S₀ hS₀_ne hS₀_sub (by omega)
  -- Step 5: Prepend `a^ℓ` to map all of `Q` into `C_all`, then `v ++ w₀` resets to `q₀`!
  refine ⟨List.replicate D.ℓ a ++ v ++ w₀, ?_, ?_⟩
  · refine ⟨q₀, fun q => ?_⟩
    rw [List.append_assoc, DFA.eval_append, DFA.eval_append]
    have h1 : A.eval q (List.replicate D.ℓ a) ∈ C_all := hQ_in q
    have h2 : A.eval (A.eval q (List.replicate D.ℓ a)) v ∈ S₀ := by
      have := hvsub h1; rwa [DFA.mem_preimage] at this
    have h3 : A.eval (A.eval q (List.replicate D.ℓ a)) v ∈ A.preimage {q₀} w₀ :=
      (Finset.mem_inter.mp h2).1
    rw [DFA.mem_preimage, Finset.mem_singleton] at h3
    exact h3
  · simp only [List.length_append, List.length_replicate]
    rw [hCall_card] at hvlen hw₀_len
    dsimp only [L₁] at hvlen
    omega

/-- **Theorem D_cyc (Unconditional `< 2(n - 1)^2` Bound for ALL `m ≤ n`, Arbitrary `ℓ ≥ 0`)**: -/
theorem cyclicBasin_quadratic_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a b : α) (hSync : A.IsSynchronizing)
    (D : CyclicBasinData A a b) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length < 2 * (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ := cyclicBasin_reset_bound A a b hSync D
  refine ⟨w, hw, lt_of_le_of_lt hlen ?_⟩
  set n := Fintype.card Q
  set m := D.c * D.m₀
  have hc := D.hc
  have hm₀ := D.hm₀
  have hℓ := D.hℓ_le
  have hm_ge2 : 2 ≤ m := by dsimp only [m]; nlinarith
  have hm_le_n : m ≤ n := by omega
  have hcm_le : D.c + D.m₀ - 2 ≤ m - 1 := by
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ D.c + D.m₀ := by omega
    zify [h1, h2]
    dsimp only [m]
    push_cast
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (D.c : ℤ) - 1 by omega)
      (show (0 : ℤ) ≤ (D.m₀ : ℤ) - 1 by omega)]
  have hL_le : Fintype.card Q - 1 + (D.ℓ + D.c + D.m₀ - 2) ≤ 2 * n - 2 := by omega
  have hstep1 : D.ℓ + (m - 2) * (Fintype.card Q - 1 + (D.ℓ + D.c + D.m₀ - 2)) +
      ((n - m) + 1 + D.ℓ) ≤ 3 * (n - m) + 1 + (m - 2) * (2 * n - 2) := by
    have hmul : (m - 2) * (Fintype.card Q - 1 + (D.ℓ + D.c + D.m₀ - 2)) ≤ (m - 2) * (2 * n - 2) :=
      Nat.mul_le_mul_left (m - 2) hL_le
    omega
  refine lt_of_le_of_lt hstep1 ?_
  by_cases hn2 : n = 2
  · have hm2 : m = 2 := by omega
    rw [hn2, hm2]; decide
  · have hn3 : 3 ≤ n := by omega
    zify [hm_le_n, hm_ge2, (show 2 ≤ 2 * n by omega), (show 1 ≤ n by omega)]
    nlinarith

/-- **Theorem D_cyc (`m₀ ≥ 2` Tight `< 3/2 * (n - 1)^2` Bound for Arbitrary `c ≥ 2, ℓ ≥ 0`)**: -/
theorem cyclicBasin_threeHalves_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a b : α) (hSync : A.IsSynchronizing)
    (D : CyclicBasinData A a b) (hm₀2 : 2 ≤ D.m₀) :
    ∃ w : List α, A.IsSyncWord w ∧ 2 * w.length < 3 * (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ := cyclicBasin_reset_bound A a b hSync D
  refine ⟨w, hw, lt_of_le_of_lt (Nat.mul_le_mul_left 2 hlen) ?_⟩
  set n := Fintype.card Q
  set m := D.c * D.m₀
  have hc := D.hc
  have hℓ := D.hℓ_le
  have hm_ge4 : 4 ≤ m := by dsimp only [m]; nlinarith
  have hm_le_n : m ≤ n := by omega
  have hcm_le : 2 * (D.c + D.m₀ - 2) ≤ m := by
    have h2 : 2 ≤ D.c + D.m₀ := by omega
    zify [h2]
    dsimp only [m]
    push_cast
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (D.c : ℤ) - 2 by omega)
      (show (0 : ℤ) ≤ (D.m₀ : ℤ) - 2 by omega)]
  have h2L : 2 * (n - 1 + (D.ℓ + D.c + D.m₀ - 2)) ≤ 4 * n - 2 - m := by omega
  have hmul : (m - 2) * (2 * (n - 1 + (D.ℓ + D.c + D.m₀ - 2))) ≤ (m - 2) * (4 * n - 2 - m) :=
    Nat.mul_le_mul_left (m - 2) h2L
  have hstep1 : 2 * (D.ℓ + (m - 2) * (n - 1 + (D.ℓ + D.c + D.m₀ - 2)) + ((n - m) + 1 + D.ℓ)) ≤
      6 * (n - m) + 2 + (m - 2) * (4 * n - 2 - m) := by
    have hring : 2 * ((m - 2) * (n - 1 + (D.ℓ + D.c + D.m₀ - 2))) =
        (m - 2) * (2 * (n - 1 + (D.ℓ + D.c + D.m₀ - 2))) := by ring
    omega
  refine lt_of_le_of_lt hstep1 ?_
  zify [hm_le_n, (show 2 ≤ m by omega), (show 2 ≤ 4 * n by omega),
    (show m ≤ 4 * n - 2 by omega), (show 1 ≤ n by omega)]
  nlinarith

/-- **Theorem D_cyc (EXACT ČERNÝ CONJECTURE `(n - 1)^2` for `2 * m ≤ n`, Arbitrary `c ≥ 2, m₀ ≥ 1, ℓ ≥ 0`)**:
For ANY synchronizing DFA (NO strong connectivity!) with a `c`-cluster equal-cycle letter `a`
(`m = c * m₀`, arbitrary tree height `ℓ ≤ n - m`) and a (possibly non-bijective!) cyclic basin-shift
letter `b`, whenever `2 * (c * m₀) ≤ n`, Černý's Conjecture `w.length ≤ (n - 1) ^ 2` holds! -/
theorem cyclicBasin_halfCycle_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a b : α) (hSync : A.IsSynchronizing)
    (D : CyclicBasinData A a b) (hhalf : 2 * (D.c * D.m₀) ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ := cyclicBasin_reset_bound A a b hSync D
  refine ⟨w, hw, le_trans hlen ?_⟩
  set n := Fintype.card Q
  set m := D.c * D.m₀
  have hc := D.hc
  have hm₀ := D.hm₀
  have hℓ := D.hℓ_le
  have hm_ge2 : 2 ≤ m := by dsimp only [m]; nlinarith
  have hm_le_n : m ≤ n := by omega
  have hn_ge4 : 4 ≤ n := by omega
  have hcm_le : D.c + D.m₀ - 2 ≤ m - 1 := by
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ D.c + D.m₀ := by omega
    zify [h1, h2]
    dsimp only [m]
    push_cast
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (D.c : ℤ) - 1 by omega)
      (show (0 : ℤ) ≤ (D.m₀ : ℤ) - 1 by omega)]
  have hL_le : n - 1 + (D.ℓ + D.c + D.m₀ - 2) ≤ 2 * n - 2 := by omega
  have hmul : (m - 2) * (n - 1 + (D.ℓ + D.c + D.m₀ - 2)) ≤ (m - 2) * (2 * n - 2) :=
    Nat.mul_le_mul_left (m - 2) hL_le
  have hstep1 : D.ℓ + (m - 2) * (n - 1 + (D.ℓ + D.c + D.m₀ - 2)) + ((n - m) + 1 + D.ℓ) ≤
      3 * (n - m) + 1 + (m - 2) * (2 * n - 2) := by omega
  refine le_trans hstep1 ?_
  zify [hm_le_n, hm_ge2, (show 2 ≤ 2 * n by omega), (show 1 ≤ n by omega)] at hhalf ⊢
  nlinarith

/-- **Theorem D_cyc (EXACT ČERNÝ CONJECTURE `(n - 1)^2` for `m₀ ≥ 2` and `12 * m ≤ 7 * n`)**:
For ANY synchronizing DFA (NO strong connectivity!) with `CyclicBasinData A a b`, cycle length
`m₀ ≥ 2`, arbitrary `c ≥ 2`, arbitrary tree height `ℓ ≤ n - c * m₀`, and `12 * (c * m₀) ≤ 7 * n`,
Černý's Conjecture `w.length ≤ (n - 1) ^ 2` holds! -/
theorem cyclicBasin_sevenTwelfths_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a b : α) (hSync : A.IsSynchronizing)
    (D : CyclicBasinData A a b) (hm₀2 : 2 ≤ D.m₀)
    (h712 : 12 * (D.c * D.m₀) ≤ 7 * Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ := cyclicBasin_reset_bound A a b hSync D
  refine ⟨w, hw, ?_⟩
  set n := Fintype.card Q
  set m := D.c * D.m₀
  have hc := D.hc
  have hℓ := D.hℓ_le
  have hm_ge4 : 4 ≤ m := by dsimp only [m]; nlinarith
  have hm_le_n : m ≤ n := by omega
  have hn_ge7 : 7 ≤ n := by omega
  have hcm_le : 2 * (D.c + D.m₀ - 2) ≤ m := by
    have h2 : 2 ≤ D.c + D.m₀ := by omega
    zify [h2]
    dsimp only [m]
    push_cast
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (D.c : ℤ) - 2 by omega)
      (show (0 : ℤ) ≤ (D.m₀ : ℤ) - 2 by omega)]
  have h2L : 2 * (n - 1 + (D.ℓ + D.c + D.m₀ - 2)) ≤ 4 * n - 2 - m := by omega
  have hmul : (m - 2) * (2 * (n - 1 + (D.ℓ + D.c + D.m₀ - 2))) ≤ (m - 2) * (4 * n - 2 - m) :=
    Nat.mul_le_mul_left (m - 2) h2L
  have hstep1 : 2 * w.length ≤ 6 * (n - m) + 2 + (m - 2) * (4 * n - 2 - m) := by
    have h2w := Nat.mul_le_mul_left 2 hlen
    have hring : 2 * ((m - 2) * (n - 1 + (D.ℓ + D.c + D.m₀ - 2))) =
        (m - 2) * (2 * (n - 1 + (D.ℓ + D.c + D.m₀ - 2))) := by ring
    omega
  -- Prove `288 * w.length ≤ 288 * (n - 1)^2` directly over `ℤ`!
  suffices h288 : 288 * w.length ≤ 288 * (n - 1) ^ 2 by omega
  have h144 : 288 * w.length ≤ 144 * (6 * (n - m) + 2 + (m - 2) * (4 * n - 2 - m)) := by omega
  refine le_trans h144 ?_
  zify [hm_le_n, (show 2 ≤ m by omega), (show 2 ≤ 4 * n by omega),
    (show m ≤ 4 * n - 2 by omega), (show 1 ≤ n by omega)] at h712 ⊢
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ 7 * (n : ℤ) - 12 * (m : ℤ) by linarith)
    (show (0 : ℤ) ≤ 41 * (n : ℤ) - 12 * (m : ℤ) - 72 by linarith)]

end Cerny
