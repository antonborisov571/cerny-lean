import Cerny.Defs
import Cerny.AlpogeThetaLift
import Cerny.AlpogeCyclicBasin
import Mathlib.Tactic.Zify

/-!
# Opposite-Drift / Two-Sided Flux-Witness 2-Cluster Exact Černý Bound (Theorems G₀ & G)

This file formalizes **Theorems G₀ & G** (`docs/round3_two_cluster_and_s2.md` §1 & §5.1)
using 100% pure `ℚ`-linear algebra with **NO strong connectivity**, **NO mixing condition**,
**NO cluster-balance condition**, **arbitrary cycle lengths `m₁, m₂ ≥ 1`**, **arbitrary tree
height `ℓ ≤ n - (m₁ + m₂)`**, and **arbitrary extra letters in `α`**:

## Main Results
* `Cerny.optimal_twoCluster_avg` (**Lemma G.1**): Optimal degree `d_a = m₁ + m₂ - gcd(m₁, m₂) - 1`
  uniform averaging distribution `E₁(a)` over `Fin m₁ × Fin (m₂ / gcd m₁ m₂)` words
  `a^{ℓ + i + r * g}` mapping `p ∈ B₁ ↦ (1 / m₁) [C₁]` and `p ∈ B₂ ↦ (1 / m₂) [C₂]`.
* `Cerny.twoCluster_oppositeDrift_extend` (**Theorem G₀(1)**): 3-case uniform-on-`C` extension
  for any synchronizing 2-cluster DFA with opposite-drift words `u_pos, u_neg` of length `≤ L₀`:
  - `s₁ * m₂ ≠ s₂ * m₁` gives `|w| ≤ L₀ + ℓ + d_a` via a direct positive expectation;
  - `s₁ * m₂ = s₂ * m₁` gives `|w| ≤ n - 1 + ℓ + d_a` via an ascending `ℚ`-subspace chain.
* `Cerny.twoCluster_fluxWitness_reset_bound_general` & `Cerny.twoCluster_fluxWitness_reset_bound`
  (**Theorem G₀(2)**): Reset bounds for arbitrary `L₀` and sharpened Case-3 separation
  (`c₃ = min (g - 1) (m - 2)`) for `L₀ ≤ n - 1`.
* `Cerny.twoCluster_oppositeDrift_cerny` (**Theorem G — Exact Černý Conjecture `(n - 1)^2`!**):
  When `L₀ = 1` (two opposite-drift letters `b_pos, b_neg ∈ α`), EVERY synchronizing 2-cluster DFA
  satisfies `∃ w, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2` for ALL `m₁, m₂ ≥ 1`
  and ALL `ℓ ≤ n - (m₁ + m₂)`!
* `Cerny.twoCluster_oppositeDrift_ge_six_bound`: Sharper `≤ n^2 - 3 * n + 3` for `n ≥ 6`.
* `Cerny.twoCluster_fluxWitness_quadratic_bound`, `Cerny.twoCluster_fluxWitness_halfCycle_cerny`,
  `Cerny.twoCluster_equalCycle_fluxWitness_bound`,
  `Cerny.twoCluster_equalCycle_fluxWitness_sevenTwelfths_cerny`:
  Corollaries for `L₀ ≤ n - 1` (`≤ 2n^2 + 7 - 7n < 2(n - 1)^2`, exact `(n - 1)^2` for
  `2m ≤ n`, `≤ (3/2)(n - 1)^2` for `m₁ = m₂`, and exact `(n - 1)^2` for `m₁ = m₂ ∧ 12m ≤ 7n`).
-/

namespace Cerny

universe u v

/-! ### Section 1: Flux Counts & Cycle Helpers -/

/-- Cross-cluster flux `k₁₂(u) = |{q ∈ C₁ : q · u ∈ B₂}|`. -/
def TwoClusterData.flux12 {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} (D : TwoClusterData A) (u : List α) : ℕ :=
  (D.C₁.filter (fun q => A.eval q u ∈ D.B₂)).card

/-- Cross-cluster flux `k₂₁(u) = |{q ∈ C₂ : q · u ∈ B₁}|`. -/
def TwoClusterData.flux21 {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} (D : TwoClusterData A) (u : List α) : ℕ :=
  (D.C₂.filter (fun q => A.eval q u ∈ D.B₁)).card

namespace AlpogeOppositeDrift

/-- Product-index equivalence `Fin q × Fin g ≃ Fin m` whenever `q * g = m` and `0 < g`. -/
private def mulFinEquiv {q g m : ℕ} (hg : 0 < g) (hm : q * g = m) :
    Fin q × Fin g ≃ Fin m where
  toFun p := ⟨p.1.val * g + p.2.val, by
    have h1 : (p.1.val + 1) * g ≤ q * g := Nat.mul_le_mul_right g p.1.isLt
    have h2 : p.1.val * g + g = (p.1.val + 1) * g := by ring
    omega⟩
  invFun i :=
    ⟨⟨i.val / g, by
        have hlt : i.val < g * q := by rw [Nat.mul_comm, hm]; exact i.isLt
        exact Nat.div_lt_of_lt_mul hlt⟩,
     ⟨i.val % g, Nat.mod_lt i.val hg⟩⟩
  left_inv p := by
    ext
    · dsimp only
      rw [Nat.mul_comm p.1.val g, Nat.mul_add_div hg, Nat.div_eq_of_lt p.2.isLt, Nat.add_zero]
    · dsimp only
      rw [Nat.mul_comm p.1.val g, Nat.mul_add_mod, Nat.mod_eq_of_lt p.2.isLt]
  right_inv i := by
    ext
    dsimp only
    rw [Nat.mul_comm (i.val / g) g, Nat.div_add_mod]

/-- On a finite invariant transitive cycle `C`, `step · a` is injective on `C`. -/
private lemma cycle_step_injOn {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a : α) (C : Finset Q) (hC_inv : ∀ q ∈ C, A.step q a ∈ C)
    (hC_trans : ∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) :
    Set.InjOn (fun x => A.step x a) C := by
  let f : Q → Q := fun x => A.step x a
  let fC : C → C := fun x => ⟨f x.1, hC_inv x.1 x.2⟩
  have hfC_surj : Function.Surjective fC := by
    intro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hC_trans (f y) (hC_inv y hy) y hy
    refine ⟨⟨f^[k] y, ?_⟩, Subtype.ext ?_⟩
    · clear hk
      induction k with
      | zero => exact hy
      | succ k ih => rw [Function.iterate_succ_apply']; exact hC_inv _ ih
    · change f (f^[k] y) = y
      rw [← Function.iterate_succ_apply' f k y, Function.iterate_succ_apply]
      exact hk
  have hfC_inj : Function.Injective fC :=
    (Fintype.bijective_iff_surjective_and_card fC).mpr ⟨hfC_surj, rfl⟩ |>.1
  intro p hp q hq heq
  have : fC ⟨p, hp⟩ = fC ⟨q, hq⟩ := Subtype.ext heq
  exact congrArg Subtype.val (hfC_inj this)

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
  let fC : C → C := fun x => ⟨f x.1, hC_inv x.1 x.2⟩
  have hfC_iter : ∀ (k : ℕ) (x : C), (fC^[k] x).1 = f^[k] x.1 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply, ih]; rfl
  have hfC_inj : Function.Injective fC := by
    intro x y hxy
    exact Subtype.ext (cycle_step_injOn A a C hC_inv hC_trans x.2 y.2 (congrArg Subtype.val hxy))
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
  let g : Fin C.card → C := fun j => ⟨f^[j.val] c₀, hiter_mem j.val⟩
  have hg_inj : Function.Injective g := by
    intro i j hij
    have hval : f^[i.val] c₀ = f^[j.val] c₀ := congrArg Subtype.val hij
    by_contra hne
    have hstep : ∀ x y : ℕ, x < y → y < C.card → f^[x] c₀ = f^[y] c₀ → False := by
      intro x y hxy hyc heq
      have hsub : fC^[x] ⟨c₀, hc₀⟩ = fC^[y] ⟨c₀, hc₀⟩ :=
        Subtype.ext (by rw [hfC_iter, hfC_iter]; exact heq)
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

/-- Number of states in `C₁ ∪ C₂` mapped into `B₁` by `u` satisfies
`|(C₁ ∪ C₂) ∩ B₁ u⁻¹| + flux12(u) = |C₁| + flux21(u)`. -/
private lemma card_filter_B₁_add_flux12 {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} (D : TwoClusterData A) (u : List α) :
    ((D.C₁ ∪ D.C₂).filter (fun p => A.eval p u ∈ D.B₁)).card + D.flux12 u =
      D.C₁.card + D.flux21 u := by
  have hdisj : Disjoint (D.C₁.filter (fun p => A.eval p u ∈ D.B₁))
      (D.C₂.filter (fun p => A.eval p u ∈ D.B₁)) :=
    Finset.disjoint_filter_filter D.hC_disj
  have hunion : (D.C₁ ∪ D.C₂).filter (fun p => A.eval p u ∈ D.B₁) =
      D.C₁.filter (fun p => A.eval p u ∈ D.B₁) ∪ D.C₂.filter (fun p => A.eval p u ∈ D.B₁) :=
    Finset.filter_union _ _ _
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hcompl : D.C₁.filter (fun p => A.eval p u ∈ D.B₂) =
      D.C₁.filter (fun p => A.eval p u ∉ D.B₁) := by
    ext p
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    constructor
    · intro h2 h1
      exact Finset.disjoint_left.mp D.hB_disj h1 h2
    · intro hnot1
      have huniv : A.eval p u ∈ D.B₁ ∪ D.B₂ := by rw [D.hB_union]; exact Finset.mem_univ _
      exact (Finset.mem_union.mp huniv).resolve_left hnot1
  have hsplit : (D.C₁.filter (fun p => A.eval p u ∈ D.B₁)).card +
      (D.C₁.filter (fun p => A.eval p u ∉ D.B₁)).card = D.C₁.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
    congr 1
    ext p; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  rw [TwoClusterData.flux12, TwoClusterData.flux21, hcompl]
  omega

/-- Number of sizes `r ∈ [s, m)` divisible by `m / g` (upper bound on remaining Case-3 steps). -/
private def case3Count (m g s : ℕ) : ℕ :=
  ((Finset.range m).filter (fun r => s ≤ r ∧ (m / g) ∣ r)).card

private lemma case3Count_anti {m g s s' : ℕ} (h : s ≤ s') :
    case3Count m g s' ≤ case3Count m g s := by
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
  exact ⟨hr.1, h.trans hr.2.1, hr.2.2⟩

private lemma case3Count_strict_drop {m g s s' : ℕ} (hss' : s < s') (hsm : s < m)
    (hdvd : (m / g) ∣ s) :
    case3Count m g s' + 1 ≤ case3Count m g s := by
  have hsub : (Finset.range m).filter (fun r => s' ≤ r ∧ (m / g) ∣ r) ⊂
      (Finset.range m).filter (fun r => s ≤ r ∧ (m / g) ∣ r) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨s, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨hsm, le_rfl, hdvd⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        omega
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
      exact ⟨hr.1, (Nat.le_of_lt hss').trans hr.2.1, hr.2.2⟩
  exact Finset.card_lt_card hsub

private lemma case3Count_le_sub (m g s : ℕ) : case3Count m g s ≤ m - s := by
  dsimp only [case3Count]
  have hsub : (Finset.range m).filter (fun r => s ≤ r ∧ (m / g) ∣ r) ⊆
      Finset.range m \ Finset.range s := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff] at hr ⊢
    exact ⟨hr.1, by omega⟩
  have hle := Finset.card_le_card hsub
  by_cases hsm : s ≤ m
  · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.range_mono hsm),
      Finset.card_range, Finset.card_range] at hle
    exact hle
  · have hms : m ≤ s := Nat.le_of_not_le hsm
    have hemp : Finset.range m \ Finset.range s = ∅ := by
      rw [Finset.sdiff_eq_empty_iff_subset]
      exact Finset.range_mono hms
    rw [hemp, Finset.card_empty] at hle
    omega

private lemma case3Count_le_pred_gcd {m g s : ℕ} (hg : 0 < g) (hdvd : g ∣ m) (hs : 1 ≤ s) :
    case3Count m g s ≤ g - 1 := by
  set q := m / g
  have hqm : q * g = m := Nat.div_mul_cancel hdvd
  by_cases hq0 : q = 0
  · have hm0 : m = 0 := by rw [← hqm, hq0, zero_mul]
    dsimp only [case3Count]
    rw [hm0, Finset.range_zero, Finset.filter_empty, Finset.card_empty]
    exact Nat.zero_le _
  · have hq_pos : 0 < q := Nat.pos_of_ne_zero hq0
    have hcard_le : case3Count m g s ≤ ((Finset.range g).erase 0).card := by
      refine Finset.card_le_card_of_injOn (fun r => r / q) ?_ ?_
      · intro r hr
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
        have hmul : q * (r / q) = r := Nat.mul_div_cancel' hr.2.2
        have hne0 : r / q ≠ 0 := by
          intro h0; rw [h0, mul_zero] at hmul; omega
        have hlt_g : r / q < g := by
          by_contra hge
          have hge' : g ≤ r / q := Nat.le_of_not_lt hge
          have : q * g ≤ q * (r / q) := Nat.mul_le_mul_left q hge'
          omega
        exact Finset.mem_erase.mpr ⟨hne0, Finset.mem_range.mpr hlt_g⟩
      · intro r₁ hr₁ r₂ hr₂ heq
        dsimp only at heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
        have h1 : q * (r₁ / q) = r₁ := Nat.mul_div_cancel' hr₁.2.2
        have h2 : q * (r₂ / q) = r₂ := Nat.mul_div_cancel' hr₂.2.2
        rw [← h1, ← h2, heq]
    have herase : ((Finset.range g).erase 0).card = g - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hg), Finset.card_range]
    omega

/-- In Case 3 (`s₁ * m₂ = s₂ * m₁`), the quotient `(m₁ + m₂) / gcd(m₁, m₂)` divides `s₁ + s₂`. -/
private lemma case3_size_dvd {m₁ m₂ s₁ s₂ : ℕ} (hm₁ : 0 < m₁)
    (heq : s₁ * m₂ = s₂ * m₁) :
    ((m₁ + m₂) / Nat.gcd m₁ m₂) ∣ (s₁ + s₂) := by
  set g := Nat.gcd m₁ m₂
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left m₂ hm₁
  set q₁ := m₁ / g
  set q₂ := m₂ / g
  have hq₁ : q₁ * g = m₁ := Nat.div_mul_cancel (Nat.gcd_dvd_left m₁ m₂)
  have hq₂ : q₂ * g = m₂ := Nat.div_mul_cancel (Nat.gcd_dvd_right m₁ m₂)
  have hq₁_pos : 0 < q₁ := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hq₁; omega
  have hsum_div : (m₁ + m₂) / g = q₁ + q₂ := by
    have hadd : m₁ + m₂ = (q₁ + q₂) * g := by rw [Nat.add_mul, hq₁, hq₂]
    rw [hadd, Nat.mul_div_cancel _ hg_pos]
  have hcross : s₁ * q₂ = s₂ * q₁ := by
    have h1 : (s₁ * q₂) * g = (s₂ * q₁) * g := by
      calc (s₁ * q₂) * g = s₁ * (q₂ * g) := by ring
      _ = s₁ * m₂ := by rw [hq₂]
      _ = s₂ * m₁ := heq
      _ = s₂ * (q₁ * g) := by rw [hq₁]
      _ = (s₂ * q₁) * g := by ring
    exact Nat.eq_of_mul_eq_mul_right hg_pos h1
  have hcop : Nat.Coprime q₁ q₂ := Nat.coprime_div_gcd_div_gcd hg_pos
  have hdvd₁ : q₁ ∣ s₁ := by
    have hdvd_prod : q₁ ∣ s₁ * q₂ := ⟨s₂, by linarith⟩
    exact hcop.dvd_of_dvd_mul_right hdvd_prod
  rcases hdvd₁ with ⟨τ, hτ⟩
  have hτ₂ : s₂ = q₂ * τ := by
    have h1 : q₁ * (q₂ * τ) = q₁ * s₂ := by
      calc q₁ * (q₂ * τ) = (q₁ * τ) * q₂ := by ring
      _ = s₁ * q₂ := by rw [← hτ]
      _ = s₂ * q₁ := hcross
      _ = q₁ * s₂ := by ring
    exact (Nat.eq_of_mul_eq_mul_left hq₁_pos h1).symm
  rw [hsum_div]
  exact ⟨τ, by rw [hτ, hτ₂]; ring⟩

end AlpogeOppositeDrift

/-! ### Section 2: Lemma G.1 — Optimal Degree-`(m - g - 1)` Averaging Distribution -/

/-- **Lemma G.1 (Optimal Nonnegative 2-Cycle Averaging Distribution)**:
For any 2-cluster letter `a` with disjoint cycles `C₁, C₂` of lengths `m₁, m₂ ≥ 1`,
`g = gcd(m₁, m₂)`, `q₂ = m₂ / g`, disjoint basins `B₁ ⊔ B₂ = univ`, and `Bᵢ · a^ℓ ⊆ Cᵢ`:
the uniform distribution over the `m₁ * q₂` words `{a^{ℓ + i + r * g} : 0 ≤ i < m₁, 0 ≤ r < q₂}`
has max word length `≤ ℓ + (m₁ + m₂ - g - 1)` and exact matrix rows `(1 / m₁) [C₁]` on `B₁`
and `(1 / m₂) [C₂]` on `B₂`. -/
theorem optimal_twoCluster_avg {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    {A : DFA Q α} (D : TwoClusterData A) :
    let m₁ := D.C₁.card
    let m₂ := D.C₂.card
    let g := Nat.gcd m₁ m₂
    let q₂ := m₂ / g
    (∀ idx : Fin m₁ × Fin q₂,
      (List.replicate (D.ℓ + idx.1.val + idx.2.val * g) D.a).length ≤
        D.ℓ + (m₁ + m₂ - g - 1)) ∧
    (∀ p q : Q,
      (∑ idx : Fin m₁ × Fin q₂,
        if A.eval p (List.replicate (D.ℓ + idx.1.val + idx.2.val * g) D.a) = q
        then (1 : ℚ) / ((m₁ : ℚ) * (q₂ : ℚ)) else 0) =
      if p ∈ D.B₁ then (if q ∈ D.C₁ then (1 : ℚ) / (m₁ : ℚ) else 0)
      else (if q ∈ D.C₂ then (1 : ℚ) / (m₂ : ℚ) else 0)) := by
  dsimp only
  set m₁ := D.C₁.card
  set m₂ := D.C₂.card
  set g := Nat.gcd m₁ m₂
  set q₁ := m₁ / g
  set q₂ := m₂ / g
  have hm₁_pos : 0 < m₁ := Finset.card_pos.mpr D.hC₁_ne
  have hm₂_pos : 0 < m₂ := Finset.card_pos.mpr D.hC₂_ne
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left m₂ hm₁_pos
  have hq₁_mul : q₁ * g = m₁ := Nat.div_mul_cancel (Nat.gcd_dvd_left m₁ m₂)
  have hq₂_mul : q₂ * g = m₂ := Nat.div_mul_cancel (Nat.gcd_dvd_right m₁ m₂)
  have hq₁_pos : 0 < q₁ := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hq₁_mul; omega
  have hq₂_pos : 0 < q₂ := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hq₂_mul; omega
  have hg_le_m₂ : g ≤ m₂ := Nat.le_of_dvd hm₂_pos (Nat.gcd_dvd_right m₁ m₂)
  constructor
  · -- Part 1: Max length bound `ℓ + i + r * g ≤ ℓ + (m₁ + m₂ - g - 1)`
    intro ⟨i, r⟩
    rw [List.length_replicate]
    dsimp only
    have hr : (r.val + 1) * g ≤ q₂ * g := Nat.mul_le_mul_right g r.isLt
    have hr' : r.val * g + g ≤ m₂ := by nlinarith
    have hi : i.val + 1 ≤ m₁ := i.isLt
    omega
  · -- Part 2: Exact row action `(1/m₁)[C₁]` on `B₁` and `(1/m₂)[C₂]` on `B₂`
    intro p q
    have hm₁_q : (m₁ : ℚ) ≠ 0 := by exact_mod_cast hm₁_pos.ne'
    have hm₂_q : (m₂ : ℚ) ≠ 0 := by exact_mod_cast hm₂_pos.ne'
    have hq₁_q : (q₁ : ℚ) ≠ 0 := by exact_mod_cast hq₁_pos.ne'
    have hq₂_q : (q₂ : ℚ) ≠ 0 := by exact_mod_cast hq₂_pos.ne'
    have hg_q : (g : ℚ) ≠ 0 := by exact_mod_cast hg_pos.ne'
    have hfactor : ∀ (P : Fin m₁ × Fin q₂ → Prop) [DecidablePred P] (c : ℚ),
        (∑ x, if P x then c else 0) = c * ∑ x, if P x then (1 : ℚ) else 0 := by
      intro P _ c
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
    rw [hfactor]
    by_cases hp1 : p ∈ D.B₁
    · simp only [hp1, ↓reduceIte]
      rw [Fintype.sum_prod_type_right]
      have hinner : ∀ r : Fin q₂,
          (∑ i : Fin m₁,
            if A.eval p (List.replicate (D.ℓ + i.val + r.val * g) D.a) = q
            then (1 : ℚ) else 0) = if q ∈ D.C₁ then 1 else 0 := by
        intro r
        let c₀ := (fun x => A.step x D.a)^[D.ℓ + r.val * g] p
        have hc₀ : c₀ ∈ D.C₁ := by
          dsimp [c₀]
          rw [add_comm, Function.iterate_add_apply]
          have hstart := D.hB₁_enter p hp1
          clear hp1
          induction (r.val * g) with
          | zero => exact hstart
          | succ k ih => rw [Function.iterate_succ_apply']; exact D.hC₁_inv _ ih
        have hrew : ∀ i : Fin m₁,
            A.eval p (List.replicate (D.ℓ + i.val + r.val * g) D.a) =
              (fun x => A.step x D.a)^[i.val] c₀ := by
          intro i
          rw [DFA.eval_replicate]
          dsimp [c₀]
          rw [← Function.iterate_add_apply]
          congr 1; omega
        simp_rw [hrew]
        exact AlpogeOppositeDrift.cycle_sum_indicator A D.a D.C₁ D.hC₁_inv D.hC₁_trans hc₀ q
      simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      split_ifs
      · field_simp
      · simp
    · simp only [hp1, ↓reduceIte]
      have hp2 : p ∈ D.B₂ := by
        have : p ∈ D.B₁ ∪ D.B₂ := by rw [D.hB_union]; exact Finset.mem_univ p
        exact (Finset.mem_union.mp this).resolve_left hp1
      rw [Fintype.sum_prod_type]
      let e₁ : Fin q₁ × Fin g ≃ Fin m₁ := AlpogeOppositeDrift.mulFinEquiv hg_pos hq₁_mul
      let e₂ : Fin q₂ × Fin g ≃ Fin m₂ := AlpogeOppositeDrift.mulFinEquiv hg_pos hq₂_mul
      have hreidx₁ :
          (∑ i : Fin m₁, ∑ r : Fin q₂,
            if A.eval p (List.replicate (D.ℓ + i.val + r.val * g) D.a) = q
            then (1 : ℚ) else 0) =
          ∑ k : Fin q₁, ∑ i₀ : Fin g, ∑ r : Fin q₂,
            if A.eval p (List.replicate (D.ℓ + (k.val * g + i₀.val) + r.val * g) D.a) = q
            then (1 : ℚ) else 0 := by
        rw [← Fintype.sum_equiv e₁
          (fun x : Fin q₁ × Fin g => ∑ r : Fin q₂,
            if A.eval p (List.replicate (D.ℓ + (x.1.val * g + x.2.val) + r.val * g) D.a) = q
            then (1 : ℚ) else 0)
          (fun i : Fin m₁ => ∑ r : Fin q₂,
            if A.eval p (List.replicate (D.ℓ + i.val + r.val * g) D.a) = q
            then (1 : ℚ) else 0)
          (fun _ => rfl)]
        rw [Fintype.sum_prod_type]
      rw [hreidx₁]
      have hinner : ∀ k : Fin q₁,
          (∑ i₀ : Fin g, ∑ r : Fin q₂,
            if A.eval p (List.replicate (D.ℓ + (k.val * g + i₀.val) + r.val * g) D.a) = q
            then (1 : ℚ) else 0) = if q ∈ D.C₂ then 1 else 0 := by
        intro k
        rw [Finset.sum_comm]
        have hprod :
            (∑ y : Fin q₂ × Fin g,
              if A.eval p (List.replicate (D.ℓ + (k.val * g + y.2.val) + y.1.val * g) D.a) = q
              then (1 : ℚ) else 0) =
            ∑ r : Fin q₂, ∑ i₀ : Fin g,
              if A.eval p (List.replicate (D.ℓ + (k.val * g + i₀.val) + r.val * g) D.a) = q
              then (1 : ℚ) else 0 :=
          Fintype.sum_prod_type _
        rw [← hprod]
        let c₀ := (fun x => A.step x D.a)^[D.ℓ + k.val * g] p
        have hc₀ : c₀ ∈ D.C₂ := by
          dsimp [c₀]
          rw [add_comm, Function.iterate_add_apply]
          have hstart := D.hB₂_enter p hp2
          clear hp2 hp1
          induction (k.val * g) with
          | zero => exact hstart
          | succ t ih => rw [Function.iterate_succ_apply']; exact D.hC₂_inv _ ih
        rw [Fintype.sum_equiv e₂
          (fun y : Fin q₂ × Fin g =>
            if A.eval p (List.replicate (D.ℓ + (k.val * g + y.2.val) + y.1.val * g) D.a) = q
            then (1 : ℚ) else 0)
          (fun j : Fin m₂ =>
            if (fun x => A.step x D.a)^[j.val] c₀ = q then (1 : ℚ) else 0)
          (fun y => by
            have hst : A.eval p (List.replicate (D.ℓ + (k.val * g + y.2.val) + y.1.val * g) D.a) =
                (fun x => A.step x D.a)^[(e₂ y).val] c₀ := by
              dsimp only [e₂, AlpogeOppositeDrift.mulFinEquiv, Equiv.coe_fn_mk, c₀]
              rw [DFA.eval_replicate, ← Function.iterate_add_apply]
              congr 1; omega
            simp only [hst])]
        exact AlpogeOppositeDrift.cycle_sum_indicator A D.a D.C₂ D.hC₂_inv D.hC₂_trans hc₀ q
      simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hq₁_cast : (q₁ : ℚ) * (g : ℚ) = (m₁ : ℚ) := by exact_mod_cast hq₁_mul
      have hq₂_cast : (q₂ : ℚ) * (g : ℚ) = (m₂ : ℚ) := by exact_mod_cast hq₂_mul
      split_ifs
      · field_simp
        nlinarith [hq₁_cast, hq₂_cast]
      · simp

/-! ### Section 3: Theorem G₀(1) — 3-Case Uniform-on-`C` Extension -/

/-- **Theorem G₀(1) (3-Case Uniform-on-`C` Opposite-Drift Extension — NO Strong Connectivity!)**:
In any synchronizing 2-cluster DFA with opposite-drift words `u_pos, u_neg` of length `≤ L₀`
(`k₁₂(u_pos) < k₂₁(u_pos)` and `k₂₁(u_neg) < k₁₂(u_neg)`), every nonempty proper subset `S ⊂ C₁ ∪ C₂`
admits a strictly `C`-extending word `w` with `|S w⁻¹ ∩ (C₁ ∪ C₂)| > |S|` and length:
- `≤ L₀ + ℓ + (m₁ + m₂ - g - 1)` when `s₁ * m₂ ≠ s₂ * m₁` (Cases 1 & 2, direct positive drift);
- `≤ (n - 1) + ℓ + (m₁ + m₂ - g - 1)` when `s₁ * m₂ = s₂ * m₁` (Case 3, `ℚ`-subspace chain). -/
theorem twoCluster_oppositeDrift_extend {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (D : TwoClusterData A)
    (u_pos u_neg : List α) (L₀ : ℕ)
    (hu_pos_len : u_pos.length ≤ L₀) (hu_neg_len : u_neg.length ≤ L₀)
    (hu_pos : D.flux12 u_pos < D.flux21 u_pos) (hu_neg : D.flux21 u_neg < D.flux12 u_neg)
    (S : Finset Q) (hSC : S ⊆ D.C₁ ∪ D.C₂) (hS_ne : S.Nonempty)
    (hS_lt : S.card < (D.C₁ ∪ D.C₂).card) :
    ∃ w : List α,
      w.length ≤
        (if (S ∩ D.C₁).card * D.C₂.card = (S ∩ D.C₂).card * D.C₁.card
          then Fintype.card Q - 1 else L₀) +
        D.ℓ + (D.C₁.card + D.C₂.card - Nat.gcd D.C₁.card D.C₂.card - 1) ∧
      S.card < (A.preimage S w ∩ (D.C₁ ∪ D.C₂)).card := by
  classical
  set C := D.C₁ ∪ D.C₂
  set m₁ := D.C₁.card
  set m₂ := D.C₂.card
  set m := m₁ + m₂
  set g := Nat.gcd m₁ m₂
  set q₂ := m₂ / g
  set d_a := m₁ + m₂ - g - 1
  set s₁ := (S ∩ D.C₁).card
  set s₂ := (S ∩ D.C₂).card
  have hC_card : C.card = m := Finset.card_union_of_disjoint D.hC_disj
  have hm₁_pos : 0 < m₁ := Finset.card_pos.mpr D.hC₁_ne
  have hm₂_pos : 0 < m₂ := Finset.card_pos.mpr D.hC₂_ne
  have hm_pos : 0 < m := by omega
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left m₂ hm₁_pos
  have hq₂_mul : q₂ * g = m₂ := Nat.div_mul_cancel (Nat.gcd_dvd_right m₁ m₂)
  have hq₂_pos : 0 < q₂ := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hq₂_mul; omega
  have hs_split : s₁ + s₂ = S.card := by
    have hunion : S ∩ D.C₁ ∪ S ∩ D.C₂ = S := by
      rw [← Finset.inter_union_distrib_left]
      exact Finset.inter_eq_left.mpr hSC
    have hdisj : Disjoint (S ∩ D.C₁) (S ∩ D.C₂) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right D.hC_disj)
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hm₁_q : (0 : ℚ) < (m₁ : ℚ) := by exact_mod_cast hm₁_pos
  have hm₂_q : (0 : ℚ) < (m₂ : ℚ) := by exact_mod_cast hm₂_pos
  have hm_q : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm_pos
  have hq₂_q : (0 : ℚ) < (q₂ : ℚ) := by exact_mod_cast hq₂_pos
  -- Uniform distribution `π` on `C` and optimal averaging family `(μ, word)` from Lemma G.1
  let π : Q → ℚ := fun q => if q ∈ C then (1 : ℚ) / (m : ℚ) else 0
  have hπ_sum : ∑ q : Q, π q = 1 := by
    simp only [π, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, hC_card]
    exact mul_one_div_cancel hm_q.ne'
  have hπ_S : ∑ x ∈ S, π x = (S.card : ℚ) / (m : ℚ) := by
    have h1 : ∑ x ∈ S, π x = ∑ _x ∈ S, (1 : ℚ) / (m : ℚ) :=
      Finset.sum_congr rfl fun x hx => by simp [π, hSC hx]
    rw [h1, Finset.sum_const, nsmul_eq_mul]
    ring
  have hdot_card : ∀ w : List α,
      AlpogeThetaLift.dotLin π (AlpogeThetaLift.pullback A w (AlpogeThetaLift.centered π S)) =
        (((A.preimage S w ∩ C).card : ℚ) - (S.card : ℚ)) / (m : ℚ) := by
    intro w
    rw [AlpogeThetaLift.dotLin_pullback_centered A π hπ_sum S w, hπ_S]
    have hpre : ∑ q ∈ A.preimage S w, π q = ((A.preimage S w ∩ C).card : ℚ) / (m : ℚ) := by
      simp only [π, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hpre]
    ring
  have hpos_iff : ∀ w : List α,
      0 < AlpogeThetaLift.dotLin π (AlpogeThetaLift.pullback A w (AlpogeThetaLift.centered π S)) →
      S.card < (A.preimage S w ∩ C).card := by
    intro w hgt
    rw [hdot_card w] at hgt
    have hsub : (0 : ℚ) < ((A.preimage S w ∩ C).card : ℚ) - (S.card : ℚ) := by
      by_contra hle
      have hle' : ((A.preimage S w ∩ C).card : ℚ) - (S.card : ℚ) ≤ 0 := not_lt.mp hle
      have : (((A.preimage S w ∩ C).card : ℚ) - (S.card : ℚ)) / (m : ℚ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hle' hm_q.le
      linarith
    exact_mod_cast (show (S.card : ℚ) < ((A.preimage S w ∩ C).card : ℚ) by linarith)
  let ι := Fin m₁ × Fin q₂
  let word : ι → List α := fun idx => List.replicate (D.ℓ + idx.1.val + idx.2.val * g) D.a
  let μ : ι → ℚ := fun _ => (1 : ℚ) / ((m₁ : ℚ) * (q₂ : ℚ))
  have hμ_pos : ∀ idx : ι, 0 < μ idx := fun _ => div_pos zero_lt_one (mul_pos hm₁_q hq₂_q)
  obtain ⟨hword_len, hE₁⟩ := optimal_twoCluster_avg D
  -- Master identity for `E₁(a) γ_S` evaluated at every state `p`
  let Δ : ℚ := (s₁ : ℚ) * (m₂ : ℚ) - (s₂ : ℚ) * (m₁ : ℚ)
  have hE₁_centered : ∀ p : Q,
      (∑ idx : ι, μ idx *
          AlpogeThetaLift.pullback A (word idx) (AlpogeThetaLift.centered π S) p) =
        if p ∈ D.B₁ then Δ / ((m₁ : ℚ) * (m : ℚ)) else -Δ / ((m₂ : ℚ) * (m : ℚ)) := by
    intro p
    have hswap :
        (∑ idx : ι, μ idx *
            AlpogeThetaLift.pullback A (word idx) (AlpogeThetaLift.centered π S) p) =
          ∑ q : Q, (∑ idx : ι, if A.eval p (word idx) = q then μ idx else 0) *
            AlpogeThetaLift.centered π S q := by
      simp only [AlpogeThetaLift.pullback, LinearMap.coe_mk, AddHom.coe_mk]
      have hterm : ∀ idx : ι,
          μ idx * AlpogeThetaLift.centered π S (A.eval p (word idx)) =
            ∑ q : Q, (if A.eval p (word idx) = q then μ idx else 0) *
              AlpogeThetaLift.centered π S q := by
        intro idx
        rw [Finset.sum_eq_single (A.eval p (word idx))]
        · simp
        · intro q _ hq; simp [Ne.symm hq]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [hterm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => by rw [Finset.sum_mul]
    rw [hswap]
    have hE₁_p : ∀ q : Q,
        (∑ idx : ι, if A.eval p (word idx) = q then μ idx else 0) =
          if p ∈ D.B₁ then (if q ∈ D.C₁ then (1 : ℚ) / (m₁ : ℚ) else 0)
          else (if q ∈ D.C₂ then (1 : ℚ) / (m₂ : ℚ) else 0) :=
      fun q => hE₁ p q
    simp_rw [hE₁_p]
    have hs_cast : (S.card : ℚ) = (s₁ : ℚ) + (s₂ : ℚ) := by exact_mod_cast hs_split.symm
    have hm_cast : (m : ℚ) = (m₁ : ℚ) + (m₂ : ℚ) := by exact_mod_cast rfl
    by_cases hp1 : p ∈ D.B₁
    · simp only [hp1, ↓reduceIte]
      have hsum :
          (∑ q : Q, (if q ∈ D.C₁ then (1 : ℚ) / (m₁ : ℚ) else 0) *
              AlpogeThetaLift.centered π S q) =
            (1 / (m₁ : ℚ)) * ∑ q ∈ D.C₁, ((if q ∈ S then (1 : ℚ) else 0) - (S.card : ℚ) / (m : ℚ)) := by
        rw [← Finset.sum_subset (Finset.subset_univ D.C₁)]
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q hq => by
            simp only [hq, ↓reduceIte, AlpogeThetaLift.centered, hπ_S]
        · intro q _ hq; simp [hq]
      rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      have hind : ∑ q ∈ D.C₁, (if q ∈ S then (1 : ℚ) else 0) = (s₁ : ℚ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 2
        ext q; simp only [Finset.mem_filter, Finset.mem_inter]; tauto
      rw [hind]
      dsimp only [Δ]
      field_simp [hm₁_q.ne', hm_q.ne']
      rw [hs_cast, hm_cast]
      ring
    · simp only [hp1, ↓reduceIte]
      have hsum :
          (∑ q : Q, (if q ∈ D.C₂ then (1 : ℚ) / (m₂ : ℚ) else 0) *
              AlpogeThetaLift.centered π S q) =
            (1 / (m₂ : ℚ)) * ∑ q ∈ D.C₂, ((if q ∈ S then (1 : ℚ) else 0) - (S.card : ℚ) / (m : ℚ)) := by
        rw [← Finset.sum_subset (Finset.subset_univ D.C₂)]
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q hq => by
            simp only [hq, ↓reduceIte, AlpogeThetaLift.centered, hπ_S]
        · intro q _ hq; simp [hq]
      rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      have hind : ∑ q ∈ D.C₂, (if q ∈ S then (1 : ℚ) else 0) = (s₂ : ℚ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 2
        ext q; simp only [Finset.mem_filter, Finset.mem_inter]; tauto
      rw [hind]
      dsimp only [Δ]
      field_simp [hm₂_q.ne', hm_q.ne']
      rw [hs_cast, hm_cast]
      ring
  -- Master identity for `∑ idx, μ idx * dotLin π (pullback A (u ++ word idx) γ_S)`
  have havg_formula : ∀ u : List α,
      (∑ idx : ι, μ idx *
          AlpogeThetaLift.dotLin π
            (AlpogeThetaLift.pullback A (u ++ word idx) (AlpogeThetaLift.centered π S))) =
        (Δ * ((D.flux21 u : ℚ) - (D.flux12 u : ℚ))) / ((m : ℚ) * (m₁ : ℚ) * (m₂ : ℚ)) := by
    intro u
    have h1 :
        (∑ idx : ι, μ idx *
            AlpogeThetaLift.dotLin π
              (AlpogeThetaLift.pullback A (u ++ word idx) (AlpogeThetaLift.centered π S))) =
          ∑ p : Q, π p *
            (∑ idx : ι, μ idx *
              AlpogeThetaLift.pullback A (word idx) (AlpogeThetaLift.centered π S) (A.eval p u)) := by
      simp only [AlpogeThetaLift.dotLin, AlpogeThetaLift.pullback, LinearMap.coe_mk, AddHom.coe_mk,
        DFA.eval_append, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun idx _ => by ring
    rw [h1]
    simp_rw [hE₁_centered]
    have h2 :
        (∑ p : Q, π p *
            (if A.eval p u ∈ D.B₁ then Δ / ((m₁ : ℚ) * (m : ℚ)) else -Δ / ((m₂ : ℚ) * (m : ℚ)))) =
          (1 / (m : ℚ)) * ∑ p ∈ C,
            (if A.eval p u ∈ D.B₁ then Δ / ((m₁ : ℚ) * (m : ℚ)) else -Δ / ((m₂ : ℚ) * (m : ℚ))) := by
      rw [← Finset.sum_subset (Finset.subset_univ C)]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => by simp [π, hp]
      · intro p _ hp; simp [π, hp]
    rw [h2]
    set X := (C.filter (fun p => A.eval p u ∈ D.B₁)).card
    set Y := (C.filter (fun p => A.eval p u ∉ D.B₁)).card
    have hXY : X + Y = m := by
      rw [← hC_card]
      dsimp only [X, Y]
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
      congr 1
      ext p; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    have hsplit_sum :
        (∑ p ∈ C,
            if A.eval p u ∈ D.B₁ then Δ / ((m₁ : ℚ) * (m : ℚ)) else -Δ / ((m₂ : ℚ) * (m : ℚ))) =
          (X : ℚ) * (Δ / ((m₁ : ℚ) * (m : ℚ))) + (Y : ℚ) * (-Δ / ((m₂ : ℚ) * (m : ℚ))) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    rw [hsplit_sum]
    have hX_flux : (X : ℚ) + (D.flux12 u : ℚ) = (m₁ : ℚ) + (D.flux21 u : ℚ) := by
      exact_mod_cast AlpogeOppositeDrift.card_filter_B₁_add_flux12 D u
    have hXY_q : (X : ℚ) + (Y : ℚ) = (m₁ : ℚ) + (m₂ : ℚ) := by
      have hm_cast : (m : ℚ) = (m₁ : ℚ) + (m₂ : ℚ) := by exact_mod_cast rfl
      have h1 : (X : ℚ) + (Y : ℚ) = (m : ℚ) := by exact_mod_cast hXY
      linarith
    have hm_cast : (m : ℚ) = (m₁ : ℚ) + (m₂ : ℚ) := by exact_mod_cast rfl
    have hY_eq : (Y : ℚ) = (m₁ : ℚ) + (m₂ : ℚ) - (X : ℚ) := by linarith
    have hX_sub : (X : ℚ) - (m₁ : ℚ) = (D.flux21 u : ℚ) - (D.flux12 u : ℚ) := by linarith
    rw [hY_eq]
    field_simp [hm_q.ne', hm₁_q.ne', hm₂_q.ne']
    rw [hm_cast, ← hX_sub]
    ring
  -- Split into Case 3 (`s₁ * m₂ = s₂ * m₁`) vs Cases 1 & 2 (`s₁ * m₂ ≠ s₂ * m₁`)
  by_cases hbal : s₁ * m₂ = s₂ * m₁
  · -- **Case 3 (`s₁ * m₂ = s₂ * m₁`)**: `Δ = 0`, so average is `0` for all `u`!
    simp only [hbal, ↓reduceIte]
    have hΔ0 : Δ = 0 := by
      dsimp only [Δ]
      have hcast : (s₁ : ℚ) * (m₂ : ℚ) = (s₂ : ℚ) * (m₁ : ℚ) := by exact_mod_cast hbal
      linarith
    have hzero_exp : ∀ u : List α,
        (∑ idx : ι, μ idx *
            AlpogeThetaLift.dotLin π
              (AlpogeThetaLift.pullback A (u ++ word idx) (AlpogeThetaLift.centered π S))) = 0 := by
      intro u
      rw [havg_formula u, hΔ0, zero_mul, zero_div]
    -- Bounds `0 < π(S) < 1`
    have hπS_pos : (0 : ℚ) < ∑ x ∈ S, π x := by
      rw [hπ_S]
      exact div_pos (by exact_mod_cast Finset.card_pos.mpr hS_ne) hm_q
    have hπS_lt1 : ∑ x ∈ S, π x < 1 := by
      rw [hπ_S]
      have hlt : (S.card : ℚ) < (m : ℚ) := by rw [hC_card] at hS_lt; exact_mod_cast hS_lt
      have hmul : ((S.card : ℚ) / (m : ℚ)) * (m : ℚ) = (S.card : ℚ) := div_mul_cancel₀ _ hm_q.ne'
      nlinarith
    -- Ascending subspace chain in `Q → ℚ` escaping `H = ker (dotLin π)`
    let i₀ : ι := ⟨⟨0, hm₁_pos⟩, ⟨0, hq₂_pos⟩⟩
    let H : Submodule ℚ (Q → ℚ) := LinearMap.ker (AlpogeThetaLift.dotLin π)
    let W : ℕ → Submodule ℚ (Q → ℚ) := fun k =>
      Submodule.span ℚ { v : Q → ℚ | ∃ (u : List α) (idx : ι), u.length ≤ k ∧
        v = AlpogeThetaLift.pullback A (u ++ word idx) (AlpogeThetaLift.centered π S) }
    have hW_mono : ∀ {j k}, j ≤ k → W j ≤ W k := by
      intro j k hjk
      apply Submodule.span_mono
      rintro v ⟨u, idx, hu, rfl⟩
      exact ⟨u, idx, hu.trans hjk, rfl⟩
    have hW0_dim : 1 ≤ Module.finrank ℚ (W 0) := by
      let v₀ := AlpogeThetaLift.pullback A ([] ++ word i₀) (AlpogeThetaLift.centered π S)
      have hv₀_mem : v₀ ∈ W 0 := Submodule.subset_span ⟨[], i₀, le_rfl, rfl⟩
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
      ⟨w_sync.length, fun hle => hsync_notH (hle (Submodule.subset_span ⟨w_sync, i₀, le_rfl, rfl⟩))⟩
    let k₀ := Nat.find hex_esc
    have hk₀_not : ¬ (W k₀ ≤ H) := Nat.find_spec hex_esc
    have hk₀_min : ∀ j < k₀, W j ≤ H := fun j hj => not_not.mp (Nat.find_min hex_esc hj)
    have hk₀_le : k₀ ≤ Fintype.card Q - 1 := by
      by_cases hk0 : k₀ = 0
      · omega
      · have hstrict : ∀ j, j + 1 < k₀ → W j < W (j + 1) := by
          intro j hj
          refine lt_of_le_of_ne (hW_mono (Nat.le_succ j)) fun heq => ?_
          have hclosed : ∀ (b : α) (v : Q → ℚ),
              v ∈ W j → AlpogeThetaLift.pullback A [b] v ∈ W j := by
            intro b v hv
            rw [heq]
            induction hv using Submodule.span_induction with
            | mem x hx =>
              rcases hx with ⟨u, idx, hu, rfl⟩
              rw [← AlpogeThetaLift.pullback_cons]
              exact Submodule.subset_span ⟨b :: u, idx, by simp; omega, rfl⟩
            | zero => simp
            | add x y _ _ hx hy => rw [map_add]; exact (W (j + 1)).add_mem hx hy
            | smul c x _ hx => rw [map_smul]; exact (W (j + 1)).smul_mem c hx
          have hall : ∀ (u : List α) (idx : ι),
              AlpogeThetaLift.pullback A (u ++ word idx) (AlpogeThetaLift.centered π S) ∈ W j := by
            intro u
            induction u with
            | nil => intro idx; exact Submodule.subset_span ⟨[], idx, Nat.zero_le j, rfl⟩
            | cons b u ih =>
              intro idx
              rw [List.cons_append, AlpogeThetaLift.pullback_cons]
              exact hclosed b _ (ih idx)
          exact hsync_notH (hk₀_min j (by omega) (hall w_sync i₀))
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
    have hex_gen : ∃ (u : List α) (i₁ : ι), u.length ≤ k₀ ∧
        AlpogeThetaLift.dotLin π
          (AlpogeThetaLift.pullback A (u ++ word i₁) (AlpogeThetaLift.centered π S)) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hk₀_not
      rw [Submodule.span_le]
      rintro v ⟨u, idx, hu, rfl⟩
      exact hall u idx hu
    rcases hex_gen with ⟨u, i₁, hulen, hi₁_nz⟩
    have hex_pos : ∃ idx : ι,
        0 < AlpogeThetaLift.dotLin π
          (AlpogeThetaLift.pullback A (u ++ word idx) (AlpogeThetaLift.centered π S)) := by
      by_contra hall
      push Not at hall
      have hnonpos : ∀ idx : ι,
          μ idx * AlpogeThetaLift.dotLin π
            (AlpogeThetaLift.pullback A (u ++ word idx) (AlpogeThetaLift.centered π S)) ≤ 0 :=
        fun idx => mul_nonpos_of_nonneg_of_nonpos (hμ_pos idx).le (hall idx)
      have hlt_i₁ :
          μ i₁ * AlpogeThetaLift.dotLin π
            (AlpogeThetaLift.pullback A (u ++ word i₁) (AlpogeThetaLift.centered π S)) < 0 :=
        mul_neg_of_pos_of_neg (hμ_pos i₁) (lt_of_le_of_ne (hall i₁) hi₁_nz)
      have hsum_lt :
          ∑ idx : ι, μ idx * AlpogeThetaLift.dotLin π
            (AlpogeThetaLift.pullback A (u ++ word idx) (AlpogeThetaLift.centered π S)) <
          ∑ _idx : ι, (0 : ℚ) :=
        Finset.sum_lt_sum (fun idx _ => hnonpos idx) ⟨i₁, Finset.mem_univ i₁, hlt_i₁⟩
      rw [hzero_exp u, Finset.sum_const_zero] at hsum_lt
      exact lt_irrefl _ hsum_lt
    rcases hex_pos with ⟨idx, hidx_pos⟩
    refine ⟨u ++ word idx, ?_, hpos_iff (u ++ word idx) hidx_pos⟩
    rw [List.length_append]
    have hwl : (word idx).length ≤ D.ℓ + d_a := hword_len idx
    omega
  · -- **Cases 1 & 2 (`s₁ * m₂ ≠ s₂ * m₁`)**: Direct positive drift using `u_pos` or `u_neg`!
    simp only [hbal, ↓reduceIte]
    have hchoose : ∃ u : List α, u.length ≤ L₀ ∧
        0 < ∑ idx : ι, μ idx *
          AlpogeThetaLift.dotLin π
            (AlpogeThetaLift.pullback A (u ++ word idx) (AlpogeThetaLift.centered π S)) := by
      have hden_pos : (0 : ℚ) < (m : ℚ) * (m₁ : ℚ) * (m₂ : ℚ) :=
        mul_pos (mul_pos hm_q hm₁_q) hm₂_q
      rcases lt_or_gt_of_ne hbal with hlt | hgt
      · refine ⟨u_neg, hu_neg_len, ?_⟩
        rw [havg_formula u_neg]
        have hΔ_neg : Δ < 0 := by
          dsimp only [Δ]
          have : (s₁ : ℚ) * (m₂ : ℚ) < (s₂ : ℚ) * (m₁ : ℚ) := by exact_mod_cast hlt
          linarith
        have hfl_neg : (D.flux21 u_neg : ℚ) - (D.flux12 u_neg : ℚ) < 0 := by
          have : (D.flux21 u_neg : ℚ) < (D.flux12 u_neg : ℚ) := by exact_mod_cast hu_neg
          linarith
        exact div_pos (mul_pos_of_neg_of_neg hΔ_neg hfl_neg) hden_pos
      · refine ⟨u_pos, hu_pos_len, ?_⟩
        rw [havg_formula u_pos]
        have hΔ_pos : 0 < Δ := by
          dsimp only [Δ]
          have : (s₂ : ℚ) * (m₁ : ℚ) < (s₁ : ℚ) * (m₂ : ℚ) := by exact_mod_cast hgt
          linarith
        have hfl_pos : 0 < (D.flux21 u_pos : ℚ) - (D.flux12 u_pos : ℚ) := by
          have : (D.flux12 u_pos : ℚ) < (D.flux21 u_pos : ℚ) := by exact_mod_cast hu_pos
          linarith
        exact div_pos (mul_pos hΔ_pos hfl_pos) hden_pos
    rcases hchoose with ⟨u, hu_len, hsum_pos⟩
    have hex_pos : ∃ idx : ι,
        0 < AlpogeThetaLift.dotLin π
          (AlpogeThetaLift.pullback A (u ++ word idx) (AlpogeThetaLift.centered π S)) := by
      by_contra hall
      push Not at hall
      have hsum_le :
          (∑ idx : ι, μ idx *
            AlpogeThetaLift.dotLin π
              (AlpogeThetaLift.pullback A (u ++ word idx) (AlpogeThetaLift.centered π S))) ≤ 0 :=
        Finset.sum_nonpos fun idx _ => mul_nonpos_of_nonneg_of_nonpos (hμ_pos idx).le (hall idx)
      linarith
    rcases hex_pos with ⟨idx, hidx_pos⟩
    refine ⟨u ++ word idx, ?_, hpos_iff (u ++ word idx) hidx_pos⟩
    rw [List.length_append]
    have hwl : (word idx).length ≤ D.ℓ + d_a := hword_len idx
    omega

/-! ### Section 4: Theorem G₀(2) — Case-3 Counting & Reset Bounds -/

/-- Helper: verify the `multiCluster_singleton_start` hypotheses for `D : TwoClusterData A`. -/
private lemma twoCluster_singleton_start {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (D : TwoClusterData A) :
    ∃ q₀ ∈ D.C₁ ∪ D.C₂, ∃ w_init : List α,
      w_init.length ≤ (Fintype.card Q - (D.C₁.card + D.C₂.card)) + 1 + D.ℓ ∧
      2 ≤ (A.preimage {q₀} w_init ∩ (D.C₁ ∪ D.C₂)).card := by
  have hC_card : (D.C₁ ∪ D.C₂).card = D.C₁.card + D.C₂.card :=
    Finset.card_union_of_disjoint D.hC_disj
  have hC_ge2 : 2 ≤ (D.C₁ ∪ D.C₂).card := by
    have h1 := Finset.card_pos.mpr D.hC₁_ne
    have h2 := Finset.card_pos.mpr D.hC₂_ne
    omega
  have hC_maps : ∀ q ∈ D.C₁ ∪ D.C₂, A.step q D.a ∈ D.C₁ ∪ D.C₂ := by
    intro q hq
    rcases Finset.mem_union.mp hq with h1 | h2
    · exact Finset.mem_union_left _ (D.hC₁_inv q h1)
    · exact Finset.mem_union_right _ (D.hC₂_inv q h2)
  have hC_inj : Set.InjOn (fun q => A.step q D.a) (↑(D.C₁ ∪ D.C₂) : Set Q) := by
    have hinj₁ := AlpogeOppositeDrift.cycle_step_injOn A D.a D.C₁ D.hC₁_inv D.hC₁_trans
    have hinj₂ := AlpogeOppositeDrift.cycle_step_injOn A D.a D.C₂ D.hC₂_inv D.hC₂_trans
    intro p hp q hq heq
    dsimp only at heq
    rw [Finset.mem_coe, Finset.mem_union] at hp hq
    rcases hp with hp1 | hp2 <;> rcases hq with hq1 | hq2
    · exact hinj₁ hp1 hq1 heq
    · exfalso
      have h1 : A.step p D.a ∈ D.C₁ := D.hC₁_inv p hp1
      have h2 : A.step p D.a ∈ D.C₂ := heq ▸ D.hC₂_inv q hq2
      exact Finset.disjoint_left.mp D.hC_disj h1 h2
    · exfalso
      have h1 : A.step p D.a ∈ D.C₂ := D.hC₂_inv p hp2
      have h2 : A.step p D.a ∈ D.C₁ := heq ▸ D.hC₁_inv q hq1
      exact Finset.disjoint_left.mp D.hC_disj h2 h1
    · exact hinj₂ hp2 hq2 heq
  have hQ_in : ∀ q : Q, A.eval q (List.replicate D.ℓ D.a) ∈ D.C₁ ∪ D.C₂ := by
    intro q
    rw [DFA.eval_replicate]
    have hq : q ∈ D.B₁ ∪ D.B₂ := by rw [D.hB_union]; exact Finset.mem_univ q
    rcases Finset.mem_union.mp hq with h1 | h2
    · exact Finset.mem_union_left _ (D.hB₁_enter q h1)
    · exact Finset.mem_union_right _ (D.hB₂_enter q h2)
  simpa only [hC_card] using
    multiCluster_singleton_start A hSync D.a (D.C₁ ∪ D.C₂) hC_ge2 D.ℓ hC_maps hC_inj hQ_in

/-- **Theorem G₀(2a) (Arbitrary `L₀` Reset Bound)**:
For ANY `L₀` (not necessarily `≤ n - 1`), opposite-drift words `u_pos, u_neg` of length `≤ L₀`
give a synchronizing word of length
`≤ ℓ + (m - 2) * (max L₀ (n - 1) + ℓ + (m - g - 1)) + ((n - m) + 1 + ℓ)`. -/
theorem twoCluster_fluxWitness_reset_bound_general {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (D : TwoClusterData A)
    (u_pos u_neg : List α) (L₀ : ℕ)
    (hu_pos_len : u_pos.length ≤ L₀) (hu_neg_len : u_neg.length ≤ L₀)
    (hu_pos : D.flux12 u_pos < D.flux21 u_pos) (hu_neg : D.flux21 u_neg < D.flux12 u_neg) :
    let m := D.C₁.card + D.C₂.card
    let d_a := m - Nat.gcd D.C₁.card D.C₂.card - 1
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ D.ℓ + (m - 2) * (max L₀ (Fintype.card Q - 1) + D.ℓ + d_a) +
        ((Fintype.card Q - m) + 1 + D.ℓ) := by
  dsimp only
  set C := D.C₁ ∪ D.C₂
  set m := D.C₁.card + D.C₂.card
  set d_a := m - Nat.gcd D.C₁.card D.C₂.card - 1
  set M := max L₀ (Fintype.card Q - 1) + D.ℓ + d_a
  have hC_card : C.card = m := Finset.card_union_of_disjoint D.hC_disj
  have hind : ∀ k : ℕ, ∀ S : Finset Q, S ⊆ C → S.Nonempty → m - S.card = k →
      ∃ v : List α, C ⊆ A.preimage S v ∧ v.length ≤ k * M := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro S hSC hS_ne hk
      by_cases hfull : S.card = m
      · have hSC_eq : S = C := Finset.eq_of_subset_of_card_le hSC (by rw [hC_card]; omega)
        refine ⟨[], ?_, by simp⟩
        intro q hq
        rw [DFA.mem_preimage, DFA.eval_nil, hSC_eq]
        exact hq
      · have hS_le : S.card ≤ m := by rw [← hC_card]; exact Finset.card_le_card hSC
        have hS_lt : S.card < C.card := by rw [hC_card]; omega
        obtain ⟨w, hw_len, hw_gt⟩ :=
          twoCluster_oppositeDrift_extend A hSync D u_pos u_neg L₀ hu_pos_len hu_neg_len hu_pos hu_neg S hSC hS_ne hS_lt
        have hw_le_M : w.length ≤ M := by
          dsimp only [M, d_a]
          split_ifs at hw_len <;> omega
        set S' := A.preimage S w ∩ C
        have hS'C : S' ⊆ C := Finset.inter_subset_right
        have hS'_ne : S'.Nonempty := Finset.card_pos.mp (by omega)
        have hS'_le : S'.card ≤ m := by rw [← hC_card]; exact Finset.card_le_card hS'C
        have hk'_lt : m - S'.card < k := by omega
        obtain ⟨v', hv'_pre, hv'_len⟩ := ih (m - S'.card) hk'_lt S' hS'C hS'_ne rfl
        refine ⟨v' ++ w, ?_, ?_⟩
        · intro q hq
          have hmem : A.eval q v' ∈ S' := by simpa [DFA.mem_preimage] using hv'_pre hq
          rw [DFA.mem_preimage, DFA.eval_append]
          exact (DFA.mem_preimage A S w _).mp (Finset.mem_inter.mp hmem).1
        · rw [List.length_append]
          have hstep : (m - S'.card) * M + M ≤ k * M := by
            have h1 : (m - S'.card + 1) * M ≤ k * M := Nat.mul_le_mul_right M (by omega)
            nlinarith
          omega
  obtain ⟨q₀, hq₀C, w_init, hw_init_len, hw_init_card⟩ := twoCluster_singleton_start A hSync D
  set S₀ := A.preimage {q₀} w_init ∩ C
  have hS₀C : S₀ ⊆ C := Finset.inter_subset_right
  have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv_pre, hv_len⟩ := hind (m - S₀.card) S₀ hS₀C hS₀_ne rfl
  refine ⟨List.replicate D.ℓ D.a ++ v ++ w_init, ?_, ?_⟩
  · refine ⟨q₀, fun p => ?_⟩
    rw [List.append_assoc, DFA.eval_append, DFA.eval_append]
    have hpC : A.eval p (List.replicate D.ℓ D.a) ∈ C := by
      rw [DFA.eval_replicate]
      have hp : p ∈ D.B₁ ∪ D.B₂ := by rw [D.hB_union]; exact Finset.mem_univ p
      rcases Finset.mem_union.mp hp with h1 | h2
      · exact Finset.mem_union_left _ (D.hB₁_enter p h1)
      · exact Finset.mem_union_right _ (D.hB₂_enter p h2)
    have hpS₀ : A.eval (A.eval p (List.replicate D.ℓ D.a)) v ∈ S₀ := by
      simpa [DFA.mem_preimage] using hv_pre hpC
    have hp_pre : A.eval (A.eval p (List.replicate D.ℓ D.a)) v ∈ A.preimage {q₀} w_init :=
      (Finset.mem_inter.mp hpS₀).1
    simpa [DFA.mem_preimage] using hp_pre
  · rw [List.length_append, List.length_append, List.length_replicate]
    have hm_sub : (m - S₀.card) * M ≤ (m - 2) * M := Nat.mul_le_mul_right M (by omega)
    omega

/-- **Theorem G₀(2b) (Sharp Case-3 Separation Reset Bound for `L₀ ≤ n - 1`)**:
Whenever `L₀ ≤ n - 1`, Case 3 (`s₁ * m₂ = s₂ * m₁`) occurs at most `c₃ := min (g - 1) (m - 2)`
times along the strictly increasing chain `2 ≤ |S₀| < … < |S_k| = m`, yielding:
`w.length ≤ ℓ + c₃ * (n - 1 + ℓ + d_a) + (m - 2 - c₃) * (L₀ + ℓ + d_a) + ((n - m) + 1 + ℓ)`. -/
theorem twoCluster_fluxWitness_reset_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (D : TwoClusterData A)
    (u_pos u_neg : List α) (L₀ : ℕ)
    (hL₀_le : L₀ ≤ Fintype.card Q - 1)
    (hu_pos_len : u_pos.length ≤ L₀) (hu_neg_len : u_neg.length ≤ L₀)
    (hu_pos : D.flux12 u_pos < D.flux21 u_pos) (hu_neg : D.flux21 u_neg < D.flux12 u_neg) :
    let m := D.C₁.card + D.C₂.card
    let g := Nat.gcd D.C₁.card D.C₂.card
    let d_a := m - g - 1
    let c₃ := min (g - 1) (m - 2)
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ D.ℓ + c₃ * (Fintype.card Q - 1 + D.ℓ + d_a) +
        (m - 2 - c₃) * (L₀ + D.ℓ + d_a) + ((Fintype.card Q - m) + 1 + D.ℓ) := by
  dsimp only
  set C := D.C₁ ∪ D.C₂
  set m₁ := D.C₁.card
  set m₂ := D.C₂.card
  set m := m₁ + m₂
  set g := Nat.gcd m₁ m₂
  set d_a := m - g - 1
  set c₃ := min (g - 1) (m - 2)
  set A_cost := Fintype.card Q - 1 + D.ℓ + d_a
  set B_cost := L₀ + D.ℓ + d_a
  have hBA : B_cost ≤ A_cost := by dsimp only [A_cost, B_cost]; omega
  have hC_card : C.card = m := Finset.card_union_of_disjoint D.hC_disj
  have hm₁_pos : 0 < m₁ := Finset.card_pos.mpr D.hC₁_ne
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left m₂ hm₁_pos
  have hg_dvd_m : g ∣ m := Nat.dvd_add (Nat.gcd_dvd_left m₁ m₂) (Nat.gcd_dvd_right m₁ m₂)
  -- Strong induction tracking `r * B_cost + case3Count m g S.card * (A_cost - B_cost)`
  have hind : ∀ k : ℕ, ∀ S : Finset Q, S ⊆ C → S.Nonempty → m - S.card = k →
      ∃ v : List α, C ⊆ A.preimage S v ∧
        v.length ≤ k * B_cost + AlpogeOppositeDrift.case3Count m g S.card * (A_cost - B_cost) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro S hSC hS_ne hk
      by_cases hfull : S.card = m
      · have hSC_eq : S = C := Finset.eq_of_subset_of_card_le hSC (by rw [hC_card]; omega)
        refine ⟨[], ?_, by simp⟩
        intro q hq
        rw [DFA.mem_preimage, DFA.eval_nil, hSC_eq]
        exact hq
      · have hS_le : S.card ≤ m := by rw [← hC_card]; exact Finset.card_le_card hSC
        have hS_lt : S.card < C.card := by rw [hC_card]; omega
        obtain ⟨w, hw_len, hw_gt⟩ :=
          twoCluster_oppositeDrift_extend A hSync D u_pos u_neg L₀ hu_pos_len hu_neg_len hu_pos hu_neg S hSC hS_ne hS_lt
        set S' := A.preimage S w ∩ C
        have hS'C : S' ⊆ C := Finset.inter_subset_right
        have hS'_ne : S'.Nonempty := Finset.card_pos.mp (by omega)
        have hS'_le : S'.card ≤ m := by rw [← hC_card]; exact Finset.card_le_card hS'C
        have hk'_lt : m - S'.card < k := by omega
        obtain ⟨v', hv'_pre, hv'_len⟩ := ih (m - S'.card) hk'_lt S' hS'C hS'_ne rfl
        refine ⟨v' ++ w, ?_, ?_⟩
        · intro q hq
          have hmem : A.eval q v' ∈ S' := by simpa [DFA.mem_preimage] using hv'_pre hq
          rw [DFA.mem_preimage, DFA.eval_append]
          exact (DFA.mem_preimage A S w _).mp (Finset.mem_inter.mp hmem).1
        · rw [List.length_append]
          by_cases hbal : (S ∩ D.C₁).card * D.C₂.card = (S ∩ D.C₂).card * D.C₁.card
          · simp only [hbal, ↓reduceIte] at hw_len
            have hs_split : (S ∩ D.C₁).card + (S ∩ D.C₂).card = S.card := by
              have hunion : S ∩ D.C₁ ∪ S ∩ D.C₂ = S := by
                rw [← Finset.inter_union_distrib_left]
                exact Finset.inter_eq_left.mpr hSC
              have hdisj : Disjoint (S ∩ D.C₁) (S ∩ D.C₂) :=
                Finset.disjoint_of_subset_left Finset.inter_subset_right
                  (Finset.disjoint_of_subset_right Finset.inter_subset_right D.hC_disj)
              rw [← Finset.card_union_of_disjoint hdisj, hunion]
            have hdvd : (m / g) ∣ S.card := by
              rw [← hs_split]
              exact AlpogeOppositeDrift.case3_size_dvd hm₁_pos hbal
            have hdrop := AlpogeOppositeDrift.case3Count_strict_drop hw_gt (by omega) hdvd
            have hstep1 : (m - S'.card + 1) * B_cost ≤ k * B_cost :=
              Nat.mul_le_mul_right B_cost (by omega)
            have hstep2 : (AlpogeOppositeDrift.case3Count m g S'.card + 1) * (A_cost - B_cost) ≤
                AlpogeOppositeDrift.case3Count m g S.card * (A_cost - B_cost) :=
              Nat.mul_le_mul_right (A_cost - B_cost) hdrop
            have hwA : w.length ≤ B_cost + (A_cost - B_cost) := by
              have : w.length ≤ A_cost := hw_len
              omega
            nlinarith
          · simp only [hbal, ↓reduceIte] at hw_len
            have hanti := AlpogeOppositeDrift.case3Count_anti (m := m) (g := g) (Nat.le_of_lt hw_gt)
            have hstep1 : (m - S'.card + 1) * B_cost ≤ k * B_cost :=
              Nat.mul_le_mul_right B_cost (by omega)
            have hstep2 : AlpogeOppositeDrift.case3Count m g S'.card * (A_cost - B_cost) ≤
                AlpogeOppositeDrift.case3Count m g S.card * (A_cost - B_cost) :=
              Nat.mul_le_mul_right (A_cost - B_cost) hanti
            have hwB : w.length ≤ B_cost := hw_len
            nlinarith
  obtain ⟨q₀, hq₀C, w_init, hw_init_len, hw_init_card⟩ := twoCluster_singleton_start A hSync D
  set S₀ := A.preimage {q₀} w_init ∩ C
  have hS₀C : S₀ ⊆ C := Finset.inter_subset_right
  have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv_pre, hv_len⟩ := hind (m - S₀.card) S₀ hS₀C hS₀_ne rfl
  refine ⟨List.replicate D.ℓ D.a ++ v ++ w_init, ?_, ?_⟩
  · refine ⟨q₀, fun p => ?_⟩
    rw [List.append_assoc, DFA.eval_append, DFA.eval_append]
    have hpC : A.eval p (List.replicate D.ℓ D.a) ∈ C := by
      rw [DFA.eval_replicate]
      have hp : p ∈ D.B₁ ∪ D.B₂ := by rw [D.hB_union]; exact Finset.mem_univ p
      rcases Finset.mem_union.mp hp with h1 | h2
      · exact Finset.mem_union_left _ (D.hB₁_enter p h1)
      · exact Finset.mem_union_right _ (D.hB₂_enter p h2)
    have hpS₀ : A.eval (A.eval p (List.replicate D.ℓ D.a)) v ∈ S₀ := by
      simpa [DFA.mem_preimage] using hv_pre hpC
    have hp_pre : A.eval (A.eval p (List.replicate D.ℓ D.a)) v ∈ A.preimage {q₀} w_init :=
      (Finset.mem_inter.mp hpS₀).1
    simpa [DFA.mem_preimage] using hp_pre
  · rw [List.length_append, List.length_append, List.length_replicate]
    have hc3_le_g : AlpogeOppositeDrift.case3Count m g S₀.card ≤ g - 1 :=
      AlpogeOppositeDrift.case3Count_le_pred_gcd hg_pos hg_dvd_m (by omega)
    have hc3_le_sub : AlpogeOppositeDrift.case3Count m g S₀.card ≤ m - 2 :=
      (AlpogeOppositeDrift.case3Count_le_sub m g S₀.card).trans (by omega)
    have hc3_le : AlpogeOppositeDrift.case3Count m g S₀.card ≤ c₃ := le_min hc3_le_g hc3_le_sub
    have h1 : (m - S₀.card) * B_cost ≤ (m - 2) * B_cost :=
      Nat.mul_le_mul_right B_cost (by omega)
    have h2 : AlpogeOppositeDrift.case3Count m g S₀.card * (A_cost - B_cost) ≤
        c₃ * (A_cost - B_cost) :=
      Nat.mul_le_mul_right (A_cost - B_cost) hc3_le
    have hc3_le_m2 : c₃ ≤ m - 2 := min_le_right _ _
    have hrew : (m - 2) * B_cost + c₃ * (A_cost - B_cost) =
        c₃ * A_cost + (m - 2 - c₃) * B_cost := by
      zify [hBA, hc3_le_m2]
      ring
    omega

/-! ### Section 5: Theorem G (Exact Černý `(n - 1)^2`!) & Corollaries -/

namespace AlpogeOppositeDrift

/-- Pure `ℕ` arithmetic core for Theorem G (`L₀ = 1 → R ≤ (n - 1)^2`). -/
private lemma arith_cerny_L1 (n m g ℓ R : ℕ) (hm_ge2 : 2 ≤ m) (hg_pos : 0 < g)
    (h2g : 2 * g ≤ m) (hℓ : ℓ + m ≤ n)
    (hR : R ≤ ℓ + min (g - 1) (m - 2) * (n - 1 + ℓ + (m - g - 1)) +
        (m - 2 - min (g - 1) (m - 2)) * (1 + ℓ + (m - g - 1)) +
        (n - m + 1 + ℓ)) :
    R ≤ (n - 1) ^ 2 := by
  have hn_ge2 : 2 ≤ n := by omega
  by_cases hm2 : m = 2
  · subst hm2
    have hc3 : min (g - 1) (2 - 2) = 0 := by omega
    rw [hc3] at hR
    have hwl : R ≤ ℓ + (n - 2 + 1 + ℓ) := by simpa using hR
    by_cases hn2 : n = 2
    · subst hn2; omega
    · have h3n : R ≤ 3 * n - 5 := by omega
      have h5 : 5 ≤ 3 * n := by omega
      have h1 : 1 ≤ n := by omega
      have hn3 : (3 : ℤ) ≤ (n : ℤ) := by omega
      zify [h1, h5] at h3n ⊢
      nlinarith only [h3n, hn3]
  · have hm_ge3 : 3 ≤ m := by omega
    have hn_ge3 : 3 ≤ n := by omega
    set c₃ := min (g - 1) (m - 2)
    have hc3_le_g : c₃ ≤ g - 1 := min_le_left _ _
    have hc3_le_m2 : c₃ ≤ m - 2 := min_le_right _ _
    have h1 : 1 ≤ n := by omega
    have h2 : m ≤ n := by omega
    have h3 : g ≤ m := by omega
    have h4 : 1 ≤ m - g := by omega
    zify [h1, h2, h3, h4, hm_ge2, hc3_le_m2] at hR ⊢
    zify [hg_pos] at hc3_le_g
    have hℓ_z : (ℓ : ℤ) ≤ (n : ℤ) - (m : ℤ) := by omega
    have h2g_z : 2 * (g : ℤ) ≤ (m : ℤ) := by exact_mod_cast h2g
    have hnm_z : (0 : ℤ) ≤ (n : ℤ) - (m : ℤ) := by omega
    have hstep_c3 : (c₃ : ℤ) * ((n : ℤ) - 2) ≤ ((g : ℤ) - 1) * ((n : ℤ) - 2) :=
      mul_le_mul_of_nonneg_right hc3_le_g (by omega)
    have hstep_l : ((m : ℤ) - 2) * (ℓ : ℤ) ≤ ((m : ℤ) - 2) * ((n : ℤ) - (m : ℤ)) :=
      mul_le_mul_of_nonneg_left hℓ_z (by omega)
    have hlin : (R : ℤ) ≤ (m : ℤ) * n - 3 * m + 3 + (g : ℤ) * (n - m) := by
      nlinarith only [hR, hℓ_z, hstep_c3, hstep_l]
    have h2g_prod : 2 * (g : ℤ) * ((n : ℤ) - m) ≤ (m : ℤ) * ((n : ℤ) - m) := by
      nlinarith only [h2g_z, hnm_z]
    have h2R : 2 * (R : ℤ) ≤ -(m : ℤ) ^ 2 + (3 * (n : ℤ) - 6) * m + 6 := by
      nlinarith only [hlin, h2g_prod]
    set t : ℤ := (n : ℤ) - (m : ℤ) with ht_def
    by_cases hn6 : 6 ≤ n
    · have hnt : 0 ≤ ((n : ℤ) - 6) * t := mul_nonneg (by omega) hnm_z
      have hn6_z : (6 : ℤ) ≤ (n : ℤ) := by omega
      nlinarith only [h2R, ht_def, hnt, hn6_z, sq_nonneg t]
    · have hcases : n = 3 ∨ n = 4 ∨ n = 5 := by omega
      rcases hcases with hn_eq | hn_eq | hn_eq
      · have hn_z : (n : ℤ) = 3 := by omega
        have hm_z : (m : ℤ) = 3 := by omega
        nlinarith only [h2R, hn_z, hm_z]
      · have hn_z : (n : ℤ) = 4 := by omega
        nlinarith only [h2R, ht_def, hn_z, sq_nonneg (t - 1)]
      · have hn_z : (n : ℤ) = 5 := by omega
        nlinarith only [h2R, ht_def, hn_z, sq_nonneg (2 * t - 1)]

/-- Pure `ℕ` arithmetic core for `n ≥ 6` sharpening of Theorem G (`R ≤ n^2 - 3 * n + 3`). -/
private lemma arith_ge6_L1 (n m g ℓ R : ℕ) (hn6 : 6 ≤ n) (hm_ge2 : 2 ≤ m) (hg_pos : 0 < g)
    (h2g : 2 * g ≤ m) (hℓ : ℓ + m ≤ n)
    (hR : R ≤ ℓ + min (g - 1) (m - 2) * (n - 1 + ℓ + (m - g - 1)) +
        (m - 2 - min (g - 1) (m - 2)) * (1 + ℓ + (m - g - 1)) +
        (n - m + 1 + ℓ)) :
    R ≤ n ^ 2 - 3 * n + 3 := by
  have h3n_le : 3 * n ≤ n ^ 2 := by nlinarith
  by_cases hm2 : m = 2
  · subst hm2
    have hc3 : min (g - 1) (2 - 2) = 0 := by omega
    rw [hc3] at hR
    have hwl : R ≤ ℓ + (n - 2 + 1 + ℓ) := by simpa using hR
    have h3n : R ≤ 3 * n - 5 := by omega
    have h5 : 5 ≤ 3 * n := by omega
    zify [h3n_le, h5] at h3n ⊢
    nlinarith
  · have hm_ge3 : 3 ≤ m := by omega
    set c₃ := min (g - 1) (m - 2)
    have hc3_le_g : c₃ ≤ g - 1 := min_le_left _ _
    have hc3_le_m2 : c₃ ≤ m - 2 := min_le_right _ _
    have h1 : 1 ≤ n := by omega
    have h2 : m ≤ n := by omega
    have h3 : g ≤ m := by omega
    have h4 : 1 ≤ m - g := by omega
    zify [h1, h2, h3, h4, hm_ge2, hc3_le_m2, h3n_le] at hR ⊢
    zify [hg_pos] at hc3_le_g
    have hℓ_z : (ℓ : ℤ) ≤ (n : ℤ) - (m : ℤ) := by omega
    have h2g_z : 2 * (g : ℤ) ≤ (m : ℤ) := by exact_mod_cast h2g
    have hnm_z : (0 : ℤ) ≤ (n : ℤ) - (m : ℤ) := by omega
    have hstep_c3 : (c₃ : ℤ) * ((n : ℤ) - 2) ≤ ((g : ℤ) - 1) * ((n : ℤ) - 2) :=
      mul_le_mul_of_nonneg_right hc3_le_g (by omega)
    have hstep_l : ((m : ℤ) - 2) * (ℓ : ℤ) ≤ ((m : ℤ) - 2) * ((n : ℤ) - (m : ℤ)) :=
      mul_le_mul_of_nonneg_left hℓ_z (by omega)
    have hlin : (R : ℤ) ≤ (m : ℤ) * n - 3 * m + 3 + (g : ℤ) * (n - m) := by nlinarith
    have h2g_prod : 2 * (g : ℤ) * ((n : ℤ) - m) ≤ (m : ℤ) * ((n : ℤ) - m) := by nlinarith
    have h2R : 2 * (R : ℤ) ≤ -(m : ℤ) ^ 2 + (3 * (n : ℤ) - 6) * m + 6 := by nlinarith
    set t : ℤ := (n : ℤ) - (m : ℤ)
    have hnt : 0 ≤ ((n : ℤ) - 6) * t := mul_nonneg (by omega) hnm_z
    nlinarith [sq_nonneg t]

/-- Pure `ℕ` arithmetic core for `L₀ ≤ n - 1` universal `< 2(n - 1)^2` bound. -/
private lemma arith_quad (n m g ℓ L₀ R : ℕ) (hm_ge2 : 2 ≤ m) (hg_pos : 0 < g)
    (hℓ : ℓ + m ≤ n) (hL₀ : L₀ ≤ n - 1)
    (hR : R ≤ ℓ + (m - 2) * (max L₀ (n - 1) + ℓ + (m - g - 1)) + (n - m + 1 + ℓ)) :
    R ≤ 2 * n ^ 2 + 7 - 7 * n ∧ R < 2 * (n - 1) ^ 2 := by
  have hn_ge2 : 2 ≤ n := by omega
  rw [max_eq_right hL₀] at hR
  have hstep : n - 1 + ℓ + (m - g - 1) ≤ 2 * n - 3 := by omega
  have hmul : (m - 2) * (n - 1 + ℓ + (m - g - 1)) ≤ (m - 2) * (2 * n - 3) :=
    Nat.mul_le_mul_left (m - 2) hstep
  have hlin : R ≤ 3 * (n - m) + 1 + (m - 2) * (2 * n - 3) := by omega
  have h7n_le : 7 * n ≤ 2 * n ^ 2 + 7 := by nlinarith
  have hm_le_n : m ≤ n := by omega
  have h2n3 : 3 ≤ 2 * n := by omega
  have h1 : 1 ≤ n := by omega
  zify [hm_ge2, hm_le_n, h2n3, h7n_le, h1] at hlin ⊢
  by_cases hn4 : 4 ≤ n
  · have hmn : ((2 : ℤ) * n - 6) * (m : ℤ) ≤ ((2 : ℤ) * n - 6) * (n : ℤ) :=
      mul_le_mul_of_nonneg_left (by omega) (by omega)
    constructor <;> nlinarith
  · interval_cases n
    · have : m = 2 := by omega
      subst this; constructor <;> omega
    · constructor <;> omega

/-- Pure `ℕ` arithmetic core for `L₀ ≤ n - 1 ∧ 2 * m ≤ n → R ≤ (n - 1)^2`. -/
private lemma arith_half (n m g ℓ L₀ R : ℕ) (hm_ge2 : 2 ≤ m) (hg_pos : 0 < g)
    (hℓ : ℓ + m ≤ n) (hL₀ : L₀ ≤ n - 1) (hhalf : 2 * m ≤ n)
    (hR : R ≤ ℓ + (m - 2) * (max L₀ (n - 1) + ℓ + (m - g - 1)) + (n - m + 1 + ℓ)) :
    R ≤ (n - 1) ^ 2 := by
  have hn_ge4 : 4 ≤ n := by omega
  rw [max_eq_right hL₀] at hR
  have hstep : n - 1 + ℓ + (m - g - 1) ≤ 2 * n - 3 := by omega
  have hmul : (m - 2) * (n - 1 + ℓ + (m - g - 1)) ≤ (m - 2) * (2 * n - 3) :=
    Nat.mul_le_mul_left (m - 2) hstep
  have hlin : R ≤ 3 * (n - m) + 1 + (m - 2) * (2 * n - 3) := by omega
  have hm_le_n : m ≤ n := by omega
  have h2n3 : 3 ≤ 2 * n := by omega
  have h1 : 1 ≤ n := by omega
  zify [hm_ge2, hm_le_n, h2n3, h1] at hlin ⊢
  have h2m_z : 2 * (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hhalf
  have hprod : ((2 : ℤ) * n - 6) * (2 * (m : ℤ)) ≤ ((2 : ℤ) * n - 6) * (n : ℤ) :=
    mul_le_mul_of_nonneg_left h2m_z (by omega)
  nlinarith

/-- Pure `ℕ` arithmetic core for equal-cycle `L₀ ≤ n - 1 → 2 * R ≤ 3 * (n - 1)^2`. -/
private lemma arith_equal_threeHalves (n m₁ ℓ L₀ R : ℕ) (hm₁ : 0 < m₁)
    (hℓ : ℓ + (m₁ + m₁) ≤ n) (hL₀ : L₀ ≤ n - 1)
    (hR : R ≤ ℓ + (m₁ + m₁ - 2) * (max L₀ (n - 1) + ℓ + (m₁ + m₁ - m₁ - 1)) +
        (n - (m₁ + m₁) + 1 + ℓ)) :
    2 * R ≤ 3 * (n - 1) ^ 2 := by
  rw [max_eq_right hL₀] at hR
  set m := m₁ + m₁
  have hm_ge2 : 2 ≤ m := by omega
  have hm_le_n : m ≤ n := by omega
  have hn_ge2 : 2 ≤ n := by omega
  have h1 : 1 ≤ n := by omega
  have hda : m - m₁ - 1 = m₁ - 1 := by omega
  have hstep : 2 * (n - 1 + ℓ + (m - m₁ - 1)) ≤ 4 * n - 4 - m := by omega
  have hmul : (m - 2) * (2 * (n - 1 + ℓ + (m - m₁ - 1))) ≤ (m - 2) * (4 * n - 4 - m) :=
    Nat.mul_le_mul_left (m - 2) hstep
  have h2R : 2 * R ≤ 6 * (n - m) + 2 + (m - 2) * (4 * n - 4 - m) := by
    have h1' : 2 * R ≤ 2 * ℓ + (m - 2) * (2 * (n - 1 + ℓ + (m - m₁ - 1))) +
        2 * (n - m + 1 + ℓ) := by nlinarith
    omega
  have h4n4 : 4 ≤ 4 * n := by omega
  have hm4n : m ≤ 4 * n - 4 := by omega
  zify [hm_ge2, hm_le_n, h4n4, hm4n, h1] at h2R ⊢
  by_cases hn4 : 4 ≤ n
  · have hnm : (0 : ℤ) ≤ (n : ℤ) - (m : ℤ) := by omega
    have hprod : 0 ≤ (2 * (n : ℤ) - 8) * ((n : ℤ) - (m : ℤ)) := mul_nonneg (by omega) hnm
    have hn4_z : (4 : ℤ) ≤ (n : ℤ) := by omega
    nlinarith only [h2R, hprod, hn4_z, sq_nonneg ((n : ℤ) - (m : ℤ))]
  · have hcases : n = 2 ∨ n = 3 := by omega
    rcases hcases with hn_eq | hn_eq
    · have hn_z : (n : ℤ) = 2 := by omega
      have hm_z : (m : ℤ) = 2 := by omega
      nlinarith only [h2R, hn_z, hm_z]
    · have hn_z : (n : ℤ) = 3 := by omega
      have hm_z : (m : ℤ) = 2 := by omega
      nlinarith only [h2R, hn_z, hm_z]

/-- Pure `ℕ` arithmetic core for equal-cycle `12 * m ≤ 7 * n → R ≤ (n - 1)^2`. -/
private lemma arith_equal_sevenTwelfths (n m₁ ℓ L₀ R : ℕ) (hm₁ : 0 < m₁)
    (hℓ : ℓ + (m₁ + m₁) ≤ n) (hL₀ : L₀ ≤ n - 1) (h712 : 12 * (m₁ + m₁) ≤ 7 * n)
    (hR : R ≤ ℓ + (m₁ + m₁ - 2) * (max L₀ (n - 1) + ℓ + (m₁ + m₁ - m₁ - 1)) +
        (n - (m₁ + m₁) + 1 + ℓ)) :
    R ≤ (n - 1) ^ 2 := by
  rw [max_eq_right hL₀] at hR
  have hn_ge4 : 4 ≤ n := by omega
  have h1 : 1 ≤ n := by omega
  by_cases hm₁1 : m₁ = 1
  · subst hm₁1
    have hwl : R ≤ ℓ + (n - 2 + 1 + ℓ) := by simpa using hR
    have h3n : R ≤ 3 * n - 5 := by omega
    have h5 : 5 ≤ 3 * n := by omega
    have hn4_z : (4 : ℤ) ≤ (n : ℤ) := by omega
    zify [h1, h5] at h3n ⊢
    nlinarith only [h3n, hn4_z]
  · set m := m₁ + m₁
    have hm_ge2 : 2 ≤ m := by omega
    have hm_le_n : m ≤ n := by omega
    have hm_ge4 : 4 ≤ m := by omega
    have hn_ge7 : 7 ≤ n := by omega
    have hstep : 2 * (n - 1 + ℓ + (m - m₁ - 1)) ≤ 4 * n - 4 - m := by omega
    have hmul : (m - 2) * (2 * (n - 1 + ℓ + (m - m₁ - 1))) ≤ (m - 2) * (4 * n - 4 - m) :=
      Nat.mul_le_mul_left (m - 2) hstep
    have h2R : 2 * R ≤ 6 * (n - m) + 2 + (m - 2) * (4 * n - 4 - m) := by
      have h1' : 2 * R ≤ 2 * ℓ + (m - 2) * (2 * (n - 1 + ℓ + (m - m₁ - 1))) +
          2 * (n - m + 1 + ℓ) := by nlinarith
      omega
    have h4n4 : 4 ≤ 4 * n := by omega
    have hm4n : m ≤ 4 * n - 4 := by omega
    zify [hm_ge2, hm_le_n, h4n4, hm4n, h1] at h2R ⊢
    set u : ℤ := 7 * (n : ℤ) - 12 * (m : ℤ)
    have hu_nonneg : 0 ≤ u := by
      have : 12 * (m : ℤ) ≤ 7 * (n : ℤ) := by exact_mod_cast h712
      linarith
    have hprod : 0 ≤ (34 * (n : ℤ) - 96) * u := mul_nonneg (by omega) hu_nonneg
    nlinarith [sq_nonneg u]

end AlpogeOppositeDrift

/-- **Theorem G (EXACT Černý Conjecture `(n - 1)^2` for Opposite-Drift 2-Cluster `ℓ ≥ 0` DFAs!)**:
In ANY synchronizing `n`-state DFA (`NO` strong connectivity, `NO` cluster-balance, `NO` mixing,
arbitrary extra letters in `α`) with a 2-cluster letter `a` of arbitrary cycle lengths `m₁, m₂ ≥ 1`
and arbitrary tree height `ℓ ≤ n - (m₁ + m₂)`, if `α` contains two opposite-drift letters
`b_pos, b_neg` satisfying `k₁₂(b_pos) < k₂₁(b_pos)` and `k₂₁(b_neg) < k₁₂(b_neg)`, then:
`∃ w, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2`! -/
theorem twoCluster_oppositeDrift_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (D : TwoClusterData A)
    (b_pos b_neg : α)
    (hb_pos : (D.C₁.filter (fun q => A.step q b_pos ∈ D.B₂)).card <
           (D.C₂.filter (fun q => A.step q b_pos ∈ D.B₁)).card)
    (hb_neg : (D.C₂.filter (fun q => A.step q b_neg ∈ D.B₁)).card <
           (D.C₁.filter (fun q => A.step q b_neg ∈ D.B₂)).card) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have hm₁_pos : 0 < D.C₁.card := Finset.card_pos.mpr D.hC₁_ne
  have hm₂_pos : 0 < D.C₂.card := Finset.card_pos.mpr D.hC₂_ne
  have hg_pos : 0 < Nat.gcd D.C₁.card D.C₂.card := Nat.gcd_pos_of_pos_left D.C₂.card hm₁_pos
  have hg_le₁ : Nat.gcd D.C₁.card D.C₂.card ≤ D.C₁.card :=
    Nat.le_of_dvd hm₁_pos (Nat.gcd_dvd_left _ _)
  have hg_le₂ : Nat.gcd D.C₁.card D.C₂.card ≤ D.C₂.card :=
    Nat.le_of_dvd hm₂_pos (Nat.gcd_dvd_right _ _)
  have hℓ : D.ℓ + (D.C₁.card + D.C₂.card) ≤ Fintype.card Q := by have := D.hℓ_le; omega
  obtain ⟨w, hw_sync, hw_len⟩ :=
    twoCluster_fluxWitness_reset_bound A hSync D [b_pos] [b_neg] 1 (by omega) le_rfl le_rfl
      hb_pos hb_neg
  exact ⟨w, hw_sync,
    AlpogeOppositeDrift.arith_cerny_L1 (Fintype.card Q) (D.C₁.card + D.C₂.card)
      (Nat.gcd D.C₁.card D.C₂.card) D.ℓ w.length (by omega) hg_pos (by omega) hℓ hw_len⟩

/-- **Sharpening of Theorem G for `n ≥ 6`**: under the exact hypotheses of
`twoCluster_oppositeDrift_cerny`, `w.length ≤ n ^ 2 - 3 * n + 3` for all `n ≥ 6`! -/
theorem twoCluster_oppositeDrift_ge_six_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (D : TwoClusterData A)
    (hn6 : 6 ≤ Fintype.card Q)
    (b_pos b_neg : α)
    (hb_pos : (D.C₁.filter (fun q => A.step q b_pos ∈ D.B₂)).card <
           (D.C₂.filter (fun q => A.step q b_pos ∈ D.B₁)).card)
    (hb_neg : (D.C₂.filter (fun q => A.step q b_neg ∈ D.B₁)).card <
           (D.C₁.filter (fun q => A.step q b_neg ∈ D.B₂)).card) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ Fintype.card Q ^ 2 - 3 * Fintype.card Q + 3 := by
  have hm₁_pos : 0 < D.C₁.card := Finset.card_pos.mpr D.hC₁_ne
  have hm₂_pos : 0 < D.C₂.card := Finset.card_pos.mpr D.hC₂_ne
  have hg_pos : 0 < Nat.gcd D.C₁.card D.C₂.card := Nat.gcd_pos_of_pos_left D.C₂.card hm₁_pos
  have hg_le₁ : Nat.gcd D.C₁.card D.C₂.card ≤ D.C₁.card :=
    Nat.le_of_dvd hm₁_pos (Nat.gcd_dvd_left _ _)
  have hg_le₂ : Nat.gcd D.C₁.card D.C₂.card ≤ D.C₂.card :=
    Nat.le_of_dvd hm₂_pos (Nat.gcd_dvd_right _ _)
  have hℓ : D.ℓ + (D.C₁.card + D.C₂.card) ≤ Fintype.card Q := by have := D.hℓ_le; omega
  obtain ⟨w, hw_sync, hw_len⟩ :=
    twoCluster_fluxWitness_reset_bound A hSync D [b_pos] [b_neg] 1 (by omega) le_rfl le_rfl
      hb_pos hb_neg
  exact ⟨w, hw_sync,
    AlpogeOppositeDrift.arith_ge6_L1 (Fintype.card Q) (D.C₁.card + D.C₂.card)
      (Nat.gcd D.C₁.card D.C₂.card) D.ℓ w.length hn6 (by omega) hg_pos (by omega) hℓ hw_len⟩

/-- **Theorem G₀(3a) (Universal `< 2(n - 1)^2` Bound for `L₀ ≤ n - 1`)**:
Whenever opposite-drift words `u_pos, u_neg` exist of length `≤ L₀ ≤ n - 1`, for ALL `(m₁, m₂)` and
ALL `ℓ ≤ n - m`: `w.length ≤ 2 * n^2 + 7 - 7 * n` (which equals `2 * n^2 - 7 * n + 7` for `n ≥ 4`
and is strictly `< 2 * (n - 1)^2` for ALL `n ≥ 2`). -/
theorem twoCluster_fluxWitness_quadratic_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (D : TwoClusterData A)
    (u_pos u_neg : List α) (L₀ : ℕ)
    (hL₀_le : L₀ ≤ Fintype.card Q - 1)
    (hu_pos_len : u_pos.length ≤ L₀) (hu_neg_len : u_neg.length ≤ L₀)
    (hu_pos : D.flux12 u_pos < D.flux21 u_pos) (hu_neg : D.flux21 u_neg < D.flux12 u_neg) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 2 * Fintype.card Q ^ 2 + 7 - 7 * Fintype.card Q ∧
      w.length < 2 * (Fintype.card Q - 1) ^ 2 := by
  have hm₁_pos : 0 < D.C₁.card := Finset.card_pos.mpr D.hC₁_ne
  have hm₂_pos : 0 < D.C₂.card := Finset.card_pos.mpr D.hC₂_ne
  have hg_pos : 0 < Nat.gcd D.C₁.card D.C₂.card := Nat.gcd_pos_of_pos_left D.C₂.card hm₁_pos
  have hℓ : D.ℓ + (D.C₁.card + D.C₂.card) ≤ Fintype.card Q := by have := D.hℓ_le; omega
  obtain ⟨w, hw_sync, hw_len⟩ :=
    twoCluster_fluxWitness_reset_bound_general A hSync D u_pos u_neg L₀ hu_pos_len hu_neg_len
      hu_pos hu_neg
  have hq := AlpogeOppositeDrift.arith_quad (Fintype.card Q) (D.C₁.card + D.C₂.card)
    (Nat.gcd D.C₁.card D.C₂.card) D.ℓ L₀ w.length (by omega) hg_pos hℓ hL₀_le hw_len
  exact ⟨w, hw_sync, hq.1, hq.2⟩

/-- **Theorem G₀(3b) (EXACT Černý `(n - 1)^2` for `L₀ ≤ n - 1` and `2 * m ≤ n`)**:
Whenever opposite-drift words `u_pos, u_neg` exist of length `≤ L₀ ≤ n - 1` and the total cycle size
satisfies `2 * (m₁ + m₂) ≤ n`, the Černý Conjecture holds EXACTLY: `w.length ≤ (n - 1)^2`! -/
theorem twoCluster_fluxWitness_halfCycle_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (D : TwoClusterData A)
    (u_pos u_neg : List α) (L₀ : ℕ)
    (hL₀_le : L₀ ≤ Fintype.card Q - 1)
    (hu_pos_len : u_pos.length ≤ L₀) (hu_neg_len : u_neg.length ≤ L₀)
    (hu_pos : D.flux12 u_pos < D.flux21 u_pos) (hu_neg : D.flux21 u_neg < D.flux12 u_neg)
    (hhalf : 2 * (D.C₁.card + D.C₂.card) ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have hm₁_pos : 0 < D.C₁.card := Finset.card_pos.mpr D.hC₁_ne
  have hm₂_pos : 0 < D.C₂.card := Finset.card_pos.mpr D.hC₂_ne
  have hg_pos : 0 < Nat.gcd D.C₁.card D.C₂.card := Nat.gcd_pos_of_pos_left D.C₂.card hm₁_pos
  have hℓ : D.ℓ + (D.C₁.card + D.C₂.card) ≤ Fintype.card Q := by have := D.hℓ_le; omega
  obtain ⟨w, hw_sync, hw_len⟩ :=
    twoCluster_fluxWitness_reset_bound_general A hSync D u_pos u_neg L₀ hu_pos_len hu_neg_len
      hu_pos hu_neg
  exact ⟨w, hw_sync,
    AlpogeOppositeDrift.arith_half (Fintype.card Q) (D.C₁.card + D.C₂.card)
      (Nat.gcd D.C₁.card D.C₂.card) D.ℓ L₀ w.length (by omega) hg_pos hℓ hL₀_le hhalf hw_len⟩

/-- **Theorem G₀(3c) (Equal-Cycle `(3/2)(n - 1)^2` Bound for `L₀ ≤ n - 1`)**:
When `m₁ = m₂` and opposite-drift words `u_pos, u_neg` exist of length `≤ L₀ ≤ n - 1`,
`2 * w.length ≤ 3 * (n - 1)^2` for ALL `n ≥ 2` and ALL `ℓ ≤ n - m`! -/
theorem twoCluster_equalCycle_fluxWitness_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (D : TwoClusterData A)
    (heq : D.C₁.card = D.C₂.card)
    (u_pos u_neg : List α) (L₀ : ℕ)
    (hL₀_le : L₀ ≤ Fintype.card Q - 1)
    (hu_pos_len : u_pos.length ≤ L₀) (hu_neg_len : u_neg.length ≤ L₀)
    (hu_pos : D.flux12 u_pos < D.flux21 u_pos) (hu_neg : D.flux21 u_neg < D.flux12 u_neg) :
    ∃ w : List α, A.IsSyncWord w ∧ 2 * w.length ≤ 3 * (Fintype.card Q - 1) ^ 2 := by
  have hm₁_pos : 0 < D.C₁.card := Finset.card_pos.mpr D.hC₁_ne
  have hℓ : D.ℓ + (D.C₁.card + D.C₁.card) ≤ Fintype.card Q := by have := D.hℓ_le; omega
  obtain ⟨w, hw_sync, hw_len⟩ :=
    twoCluster_fluxWitness_reset_bound_general A hSync D u_pos u_neg L₀ hu_pos_len hu_neg_len
      hu_pos hu_neg
  rw [← heq, Nat.gcd_self] at hw_len
  exact ⟨w, hw_sync,
    AlpogeOppositeDrift.arith_equal_threeHalves (Fintype.card Q) D.C₁.card D.ℓ L₀ w.length
      hm₁_pos hℓ hL₀_le hw_len⟩

/-- **Theorem G₀(3d) (Equal-Cycle Exact Černý `(n - 1)^2` for `12 * m ≤ 7 * n`)**:
When `m₁ = m₂`, opposite-drift words `u_pos, u_neg` exist of length `≤ L₀ ≤ n - 1`, and
`12 * (m₁ + m₂) ≤ 7 * n`, the Černý Conjecture holds EXACTLY: `w.length ≤ (n - 1)^2`! -/
theorem twoCluster_equalCycle_fluxWitness_sevenTwelfths_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (D : TwoClusterData A)
    (heq : D.C₁.card = D.C₂.card)
    (u_pos u_neg : List α) (L₀ : ℕ)
    (hL₀_le : L₀ ≤ Fintype.card Q - 1)
    (hu_pos_len : u_pos.length ≤ L₀) (hu_neg_len : u_neg.length ≤ L₀)
    (hu_pos : D.flux12 u_pos < D.flux21 u_pos) (hu_neg : D.flux21 u_neg < D.flux12 u_neg)
    (h712 : 12 * (D.C₁.card + D.C₂.card) ≤ 7 * Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have hm₁_pos : 0 < D.C₁.card := Finset.card_pos.mpr D.hC₁_ne
  have hℓ : D.ℓ + (D.C₁.card + D.C₁.card) ≤ Fintype.card Q := by have := D.hℓ_le; omega
  have h712' : 12 * (D.C₁.card + D.C₁.card) ≤ 7 * Fintype.card Q := by omega
  obtain ⟨w, hw_sync, hw_len⟩ :=
    twoCluster_fluxWitness_reset_bound_general A hSync D u_pos u_neg L₀ hu_pos_len hu_neg_len
      hu_pos hu_neg
  rw [← heq, Nat.gcd_self] at hw_len
  exact ⟨w, hw_sync,
    AlpogeOppositeDrift.arith_equal_sevenTwelfths (Fintype.card Q) D.C₁.card D.ℓ L₀ w.length
      hm₁_pos hℓ hL₀_le h712' hw_len⟩

end Cerny
