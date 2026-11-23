import Cerny.Defs
import Cerny.AdditionalClasses
import Cerny.AlpogeThetaLift
import Cerny.AlpogeOppositeDrift
import Cerny.AlpogeCycleDrain
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push

/-!
# Partial Cycle-Drain Unbalanced 2-Cycle Reset Bounds (Theorem F_part)

This file formalizes **Theorem F_part** (`docs/round4_two_cluster_dichotomy.md` §2.2 & §3.3),
extending Theorem F (`Cerny/AlpogeCycleDrain.lean`) strictly beyond complete cycle drain
(`r = m₂ - k₂₁(b) = 0`) to **arbitrary partial stay counts `r ≥ 1`** whenever `2 * r * m₁ < m₂`
— with **NO strong connectivity** and **arbitrary extra letters in `α`**:

## Main Results
* `Cerny.partialDrain_reduce_to_one` (Step 1): Iterative `C₂`-reduction over `Fin m₂` produces
  `w₁` with `w₁.length ≤ 1 + r * m₂` and `|(Q · w₁) ∩ C₂| ≤ 1`.
* `Cerny.partialDrain_exists_collapseWord` (Step 2): Combining `Cerny.szykula_avoiding_lemma`
  and `Cerny.optimal_twoCluster_avg` (Lemma G.1) produces a collapse word `w₀` with
  `Q · w₀ ⊆ C₁` and `w₀.length ≤ (r + 1) * m₂ + n`.
* `Cerny.partialDrain_threeHalves_bound` (**Theorem F_part(1)**): For ALL `r ≥ 1` with
  `2 * r * m₁ < m₂`, `2 * w.length ≤ 3 * (n - 1) ^ 2`.
* `Cerny.partialDrain_ge_two_cerny`, `Cerny.partialDrain_one_cerny`, and
  `Cerny.partialDrain_exact_cerny` (**Theorem F_part(2) — EXACT Černý `(n - 1)^2`!**):
  For ALL `r ≥ 2` with `2 * r * m₁ < m₂`, AND for `r = 1` with `4 * m₁ < m₂`,
  `∃ w, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2`!
-/

namespace Cerny

universe u v

namespace AlpogePartialDrain

/-- On a finite invariant transitive cycle `C`, iterating `step · a` for `0 ≤ j < |C|`
visits every state of `C` once, so `∑ j : Fin C.card, 1_{f^[j] c₀ ∈ D} = (D ∩ C).card`. -/
private lemma cycle_count_in_finset {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a : α) (C : Finset Q) (hC_inv : ∀ q ∈ C, A.step q a ∈ C)
    (hC_trans : ∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    {c₀ : Q} (hc₀ : c₀ ∈ C) (D : Finset Q) :
    (∑ j : Fin C.card, if (fun x => A.step x a)^[j.val] c₀ ∈ D then 1 else 0) = (D ∩ C).card := by
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
  have hg_bij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_inj, by simp⟩
  let e : Fin C.card ≃ C := Equiv.ofBijective g hg_bij
  have hsum : (∑ j : Fin C.card, if (e j).1 ∈ D then (1 : ℕ) else 0) =
      ∑ x : C, if x.1 ∈ D then (1 : ℕ) else 0 :=
    Fintype.sum_equiv e (fun j => if (e j).1 ∈ D then 1 else 0)
      (fun x => if x.1 ∈ D then 1 else 0) (fun _ => rfl)
  change (∑ j : Fin C.card, if (e j).1 ∈ D then 1 else 0) = (D ∩ C).card
  rw [hsum, Finset.sum_coe_sort C (fun x => if x ∈ D then (1 : ℕ) else 0),
    ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter]
  tauto

/-- Pure `ℕ` quadratic upper bound on `2 * R` from Theorem F₀ with `L₀ = (r + 1) * m₂ + n`. -/
private lemma arith_twoR_bound (n m₁ m₂ r R : ℕ)
    (hm₁ : 2 ≤ m₁) (hn : n = m₁ + m₂) (hcond : 2 * r * m₁ < m₂)
    (hR : R ≤ ((r + 1) * m₂ + n) +
        (m₁ - 2) * (n - 1 + ((r + 1) * m₂ + n) + m₁ - 1) +
        (n - m₁ + 1 + ((r + 1) * m₂ + n))) :
    2 * (R : ℤ) ≤ (n : ℤ) ^ 2 + 4 * (n : ℤ) * (m₁ : ℤ) + (m₁ : ℤ) ^ 2 - 3 * (n : ℤ) - 8 := by
  have h1 : 1 ≤ n := by omega
  have hm₁_le : m₁ ≤ n := by omega
  have hsub2 : 1 ≤ n - 1 + ((r + 1) * m₂ + n) + m₁ := by omega
  zify [hm₁, h1, hm₁_le, hsub2] at hR
  have hn_z : (n : ℤ) = (m₁ : ℤ) + (m₂ : ℤ) := by exact_mod_cast hn
  have hm₂_z : (m₂ : ℤ) = (n : ℤ) - (m₁ : ℤ) := by linarith
  have hcond_z : 2 * (r : ℤ) * (m₁ : ℤ) ≤ (m₂ : ℤ) - 1 := by
    have : 2 * (r : ℤ) * (m₁ : ℤ) < (m₂ : ℤ) := by exact_mod_cast hcond
    linarith
  have hm₂_nn : (0 : ℤ) ≤ (m₂ : ℤ) := by omega
  have hmul_r : 2 * (r : ℤ) * (m₁ : ℤ) * (m₂ : ℤ) ≤ ((m₂ : ℤ) - 1) * (m₂ : ℤ) :=
    mul_le_mul_of_nonneg_right hcond_z hm₂_nn
  have hm₁_z : (2 : ℤ) ≤ (m₁ : ℤ) := by omega
  nlinarith only [hR, hm₂_z, hmul_r, hm₁_z]

/-- Pure `ℕ` arithmetic core for `2 * R ≤ 3 * (n - 1)^2` (all `r ≥ 1`, `2 * r * m₁ < m₂`). -/
private lemma arith_threeHalves (n m₁ m₂ r R : ℕ)
    (hm₁ : 2 ≤ m₁) (hr : 1 ≤ r) (hn : n = m₁ + m₂) (hcond : 2 * r * m₁ < m₂)
    (hR : R ≤ ((r + 1) * m₂ + n) +
        (m₁ - 2) * (n - 1 + ((r + 1) * m₂ + n) + m₁ - 1) +
        (n - m₁ + 1 + ((r + 1) * m₂ + n))) :
    2 * R ≤ 3 * (n - 1) ^ 2 := by
  have h2R := arith_twoR_bound n m₁ m₂ r R hm₁ hn hcond hR
  have h2m₁ : 2 * m₁ ≤ 2 * r * m₁ := by
    have : 2 * m₁ * 1 ≤ 2 * m₁ * r := Nat.mul_le_mul_left (2 * m₁) hr
    linarith
  have h3m₁ : 3 * (m₁ : ℤ) ≤ (n : ℤ) - 1 := by omega
  have hn_ge1 : 1 ≤ n := by omega
  have hm₁_nn : (0 : ℤ) ≤ (m₁ : ℤ) := by omega
  have hn_nn : (0 : ℤ) ≤ (n : ℤ) := by omega
  have hsq : 9 * (m₁ : ℤ) ^ 2 ≤ ((n : ℤ) - 1) ^ 2 := by nlinarith only [h3m₁, hm₁_nn]
  have hnm₁ : (n : ℤ) * (3 * (m₁ : ℤ)) ≤ (n : ℤ) * ((n : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left h3m₁ hn_nn
  zify [hn_ge1]
  nlinarith only [h2R, hsq, hnm₁, hn_nn]

/-- Pure `ℕ` arithmetic core for exact `(n - 1)^2` whenever `5 * m₁ ≤ n - 1`. -/
private lemma arith_exact_cerny (n m₁ m₂ r R : ℕ)
    (hm₁ : 2 ≤ m₁) (hn : n = m₁ + m₂) (hcond : 2 * r * m₁ < m₂) (h5m₁ : 5 * m₁ < n)
    (hR : R ≤ ((r + 1) * m₂ + n) +
        (m₁ - 2) * (n - 1 + ((r + 1) * m₂ + n) + m₁ - 1) +
        (n - m₁ + 1 + ((r + 1) * m₂ + n))) :
    R ≤ (n - 1) ^ 2 := by
  have h2R := arith_twoR_bound n m₁ m₂ r R hm₁ hn hcond hR
  have h5m₁_z : 5 * (m₁ : ℤ) ≤ (n : ℤ) - 1 := by omega
  have hn_ge1 : 1 ≤ n := by omega
  have hm₁_nn : (0 : ℤ) ≤ (m₁ : ℤ) := by omega
  have hn_nn : (0 : ℤ) ≤ (n : ℤ) := by omega
  have hsq : 25 * (m₁ : ℤ) ^ 2 ≤ ((n : ℤ) - 1) ^ 2 := by nlinarith only [h5m₁_z, hm₁_nn]
  have hnm₁ : (n : ℤ) * (5 * (m₁ : ℤ)) ≤ (n : ℤ) * ((n : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left h5m₁_z hn_nn
  zify [hn_ge1]
  nlinarith only [h2R, hsq, hnm₁, hn_nn, sq_nonneg (2 * (n : ℤ) - 1)]

end AlpogePartialDrain

/-! ### Step 1: Iterative `C₂`-Reduction to `|(Q · w₁) ∩ C₂| ≤ 1` -/

/-- **Step 1 (`partialDrain_reduce_to_one`)**:
In a 2-cycle permutation DFA (`Q = C₁ ⊔ C₂`, `m₁ ≥ 2`, `m₂ ≥ 2`) with `k₁₂(b) ≤ 1` and
`r = |{x ∈ C₂ : x · b ∈ C₂}| ≥ 1` satisfying `2 * r * m₁ < m₂`, there exists `w₁` of length
`≤ 1 + r * m₂` with `|(Q · w₁) ∩ C₂| ≤ 1`. -/
theorem partialDrain_reduce_to_one {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a b : α) (C₁ C₂ : Finset Q)
    (hm₁ : 2 ≤ C₁.card)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hcond : 2 * (C₂.filter (fun x => A.step x b ∈ C₂)).card * C₁.card < C₂.card) :
    ∃ w₁ : List α,
      w₁.length ≤ 1 + (C₂.filter (fun x => A.step x b ∈ C₂)).card * C₂.card ∧
      (A.image Finset.univ w₁ ∩ C₂).card ≤ 1 := by
  set U₁₂ := C₁.filter (fun x => A.step x b ∈ C₂)
  set D₂ := C₂.filter (fun x => A.step x b ∈ C₂)
  set r := D₂.card
  set m₂ := C₂.card
  have hC₁_iter : ∀ (k : ℕ) (q : Q), q ∈ C₁ → (fun x => A.step x a)^[k] q ∈ C₁ := by
    intro k
    induction k with
    | zero => intro q hq; exact hq
    | succ k ih => intro q hq; rw [Function.iterate_succ_apply']; exact hC₁_inv _ (ih q hq)
  -- Initial word `[b]` satisfies `|(Q · b) ∩ C₂| ≤ 1 + r`
  have hinit_card : (A.image Finset.univ [b] ∩ C₂).card ≤ 1 + r := by
    have hsub : A.image Finset.univ [b] ∩ C₂ ⊆
        U₁₂.image (fun x => A.step x b) ∪ D₂.image (fun x => A.step x b) := by
      intro y hy
      rcases Finset.mem_inter.mp hy with ⟨hy_img, hyC₂⟩
      rcases (DFA.mem_image A Finset.univ [b] y).mp hy_img with ⟨x, _, hxb⟩
      rw [DFA.eval_singleton] at hxb
      have hx_mem : x ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ x
      rcases Finset.mem_union.mp hx_mem with hx1 | hx2
      · exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx1, hxb ▸ hyC₂⟩, hxb⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx2, hxb ▸ hyC₂⟩, hxb⟩)
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 : (U₁₂.image (fun x => A.step x b)).card ≤ U₁₂.card := Finset.card_image_le
    have h3 : (D₂.image (fun x => A.step x b)).card ≤ D₂.card := Finset.card_image_le
    omega
  -- Single reduction step: if `|(Q · w) ∩ C₂| = s ≥ 2`, some `a^j b` (`j < m₂`) drops it to `≤ s - 1`
  have hreduce : ∀ w : List α, 2 ≤ (A.image Finset.univ w ∩ C₂).card →
      ∃ j : Fin m₂,
        (A.image Finset.univ (w ++ List.replicate j.val a ++ [b]) ∩ C₂).card ≤
          (A.image Finset.univ w ∩ C₂).card - 1 := by
    intro w hs_ge2
    set T := A.image Finset.univ w ∩ C₂
    set s := T.card
    -- For every `j : Fin m₂`, `|(Q · w a^j b) ∩ C₂| ≤ 1 + |{x ∈ T : x · a^j ∈ D₂}|`
    have hbound_j : ∀ j : Fin m₂,
        (A.image Finset.univ (w ++ List.replicate j.val a ++ [b]) ∩ C₂).card ≤
          1 + (T.filter (fun x => (fun y => A.step y a)^[j.val] x ∈ D₂)).card := by
      intro j
      let Fj := T.filter (fun x => (fun y => A.step y a)^[j.val] x ∈ D₂)
      have hsub : A.image Finset.univ (w ++ List.replicate j.val a ++ [b]) ∩ C₂ ⊆
          U₁₂.image (fun x => A.step x b) ∪
            Fj.image (fun x => A.step ((fun y => A.step y a)^[j.val] x) b) := by
        intro y hy
        rcases Finset.mem_inter.mp hy with ⟨hy_img, hyC₂⟩
        rcases (DFA.mem_image A Finset.univ _ y).mp hy_img with ⟨p, _, hp_eval⟩
        rw [DFA.eval_append, DFA.eval_append, DFA.eval_replicate, DFA.eval_singleton] at hp_eval
        set x := A.eval p w
        set z := (fun y => A.step y a)^[j.val] x
        have hz_mem : z ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ z
        rcases Finset.mem_union.mp hz_mem with hz1 | hz2
        · exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz1, hp_eval ▸ hyC₂⟩, hp_eval⟩)
        · have hxC₂ : x ∈ C₂ := by
            have hx_mem : x ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ x
            rcases Finset.mem_union.mp hx_mem with hx1 | hx2
            · exfalso
              exact Finset.disjoint_left.mp hC_disj (hC₁_iter j.val x hx1) hz2
            · exact hx2
          have hxT : x ∈ T :=
            Finset.mem_inter.mpr ⟨(DFA.mem_image A Finset.univ w x).mpr ⟨p, Finset.mem_univ p, rfl⟩, hxC₂⟩
          have hzD₂ : z ∈ D₂ := Finset.mem_filter.mpr ⟨hz2, hp_eval ▸ hyC₂⟩
          exact Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxT, hzD₂⟩, hp_eval⟩)
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h2 : (U₁₂.image (fun x => A.step x b)).card ≤ U₁₂.card := Finset.card_image_le
      have h3 : (Fj.image (fun x => A.step ((fun y => A.step y a)^[j.val] x) b)).card ≤ Fj.card :=
        Finset.card_image_le
      change (A.image Finset.univ (w ++ List.replicate j.val a ++ [b]) ∩ C₂).card ≤ 1 + Fj.card
      omega
    -- Exact sum over `j : Fin m₂` equals `s * r`
    have hsum_sr :
        (∑ j : Fin m₂, (T.filter (fun x => (fun y => A.step y a)^[j.val] x ∈ D₂)).card) = s * r := by
      have hcard_j : ∀ j : Fin m₂,
          (T.filter (fun x => (fun y => A.step y a)^[j.val] x ∈ D₂)).card =
            ∑ x ∈ T, if (fun y => A.step y a)^[j.val] x ∈ D₂ then 1 else 0 := by
        intro j
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      simp_rw [hcard_j]
      rw [Finset.sum_comm]
      have hinner : ∀ x ∈ T,
          (∑ j : Fin m₂, if (fun y => A.step y a)^[j.val] x ∈ D₂ then 1 else 0) = r := by
        intro x hx
        have hxC₂ : x ∈ C₂ := (Finset.mem_inter.mp hx).2
        have hcount := AlpogePartialDrain.cycle_count_in_finset A a C₂ hC₂_inv hC₂_trans hxC₂ D₂
        have hD₂C₂ : D₂ ∩ C₂ = D₂ := Finset.inter_eq_left.mpr (Finset.filter_subset _ C₂)
        rw [hD₂C₂] at hcount
        exact hcount
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
    -- Pigeonhole: `s * r < m₂ * (s - 1)` gives some `j` with `Fj.card ≤ s - 2`
    have hsr_lt : s * r < m₂ * (s - 1) := by
      have h2r_lt : 2 * r < m₂ := by nlinarith
      zify [show 1 ≤ s by omega]
      nlinarith
    have hex_j : ∃ j : Fin m₂,
        (T.filter (fun x => (fun y => A.step y a)^[j.val] x ∈ D₂)).card < s - 1 := by
      by_contra hall
      push Not at hall
      have hge : ∑ _j : Fin m₂, (s - 1) ≤
          ∑ j : Fin m₂, (T.filter (fun x => (fun y => A.step y a)^[j.val] x ∈ D₂)).card :=
        Finset.sum_le_sum fun j _ => hall j
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hge
      omega
    obtain ⟨j, hj⟩ := hex_j
    have hbj := hbound_j j
    exact ⟨j, by omega⟩
  -- Strong induction on `k := (A.image Finset.univ w ∩ C₂).card - 1`
  have hind : ∀ k : ℕ, ∀ w : List α, (A.image Finset.univ w ∩ C₂).card - 1 = k →
      ∃ w' : List α, w'.length ≤ w.length + k * m₂ ∧ (A.image Finset.univ w' ∩ C₂).card ≤ 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro w hk
      by_cases hk0 : k = 0
      · exact ⟨w, by simp, by omega⟩
      · have hge2 : 2 ≤ (A.image Finset.univ w ∩ C₂).card := by omega
        obtain ⟨j, hj⟩ := hreduce w hge2
        set w_next := w ++ List.replicate j.val a ++ [b]
        have hk'_lt : (A.image Finset.univ w_next ∩ C₂).card - 1 < k := by omega
        obtain ⟨w', hw'_len, hw'_card⟩ :=
          ih ((A.image Finset.univ w_next ∩ C₂).card - 1) hk'_lt w_next rfl
        refine ⟨w', ?_, hw'_card⟩
        have hstep_len : w_next.length ≤ w.length + m₂ := by
          dsimp only [w_next]
          rw [List.length_append, List.length_append, List.length_replicate, List.length_singleton]
          have := j.isLt; omega
        have hmul : ((A.image Finset.univ w_next ∩ C₂).card - 1 + 1) * m₂ ≤ k * m₂ :=
          Nat.mul_le_mul_right m₂ (by omega)
        nlinarith
  obtain ⟨w₁, hw₁_len, hw₁_card⟩ := hind ((A.image Finset.univ [b] ∩ C₂).card - 1) [b] rfl
  refine ⟨w₁, ?_, hw₁_card⟩
  rw [List.length_singleton] at hw₁_len
  have hmul : ((A.image Finset.univ [b] ∩ C₂).card - 1) * m₂ ≤ r * m₂ :=
    Nat.mul_le_mul_right m₂ (by omega)
  omega

/-! ### Step 2: Collapse Word `Q · w₀ ⊆ C₁` of Length `≤ (r + 1) * m₂ + n` -/

/-- **Step 2 (`partialDrain_exists_collapseWord`)**:
Combining Step 1 (`partialDrain_reduce_to_one`), Szykuła's Avoiding-Subset Lemma
(`Cerny.szykula_avoiding_lemma`), and Lemma G.1 (`Cerny.optimal_twoCluster_avg`) produces
a collapse word `w₀` with `w₀.length ≤ (r + 1) * m₂ + n` and `∀ q, A.eval q w₀ ∈ C₁`. -/
theorem partialDrain_exists_collapseWord {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (a b : α) (C₁ C₂ : Finset Q)
    (hm₁ : 2 ≤ C₁.card) (hm₂ : 2 ≤ C₂.card)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hcond : 2 * (C₂.filter (fun x => A.step x b ∈ C₂)).card * C₁.card < C₂.card) :
    ∃ w₀ : List α,
      w₀.length ≤ ((C₂.filter (fun x => A.step x b ∈ C₂)).card + 1) * C₂.card + Fintype.card Q ∧
      ∀ q : Q, A.eval q w₀ ∈ C₁ := by
  set U₁₂ := C₁.filter (fun x => A.step x b ∈ C₂)
  set D₂ := C₂.filter (fun x => A.step x b ∈ C₂)
  set r := D₂.card
  set m₁ := C₁.card
  set m₂ := C₂.card
  set n := Fintype.card Q
  have hn_eq : n = m₁ + m₂ := by
    dsimp only [n, m₁, m₂]
    rw [← Finset.card_univ, ← hC_union, Finset.card_union_of_disjoint hC_disj]
  have hsplit_card : ∀ T : Finset Q, T.card = (T ∩ C₁).card + (T ∩ C₂).card := by
    intro T
    have hunion : T ∩ C₁ ∪ T ∩ C₂ = T := by
      rw [← Finset.inter_union_distrib_left, hC_union, Finset.inter_univ]
    have hdisj : Disjoint (T ∩ C₁) (T ∩ C₂) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hC_disj)
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  -- Step 1 gives `w₁` of length `≤ 1 + r * m₂` with `|(Q · w₁) ∩ C₂| ≤ 1`
  obtain ⟨w₁, hw₁_len_raw, hw₁_card⟩ :=
    partialDrain_reduce_to_one A a b C₁ C₂ hm₁ hC_disj hC_union hC₁_inv hC₂_inv hC₂_trans hk₁₂ hcond
  have hw₁_len : w₁.length ≤ 1 + r * m₂ := hw₁_len_raw
  set S := A.image Finset.univ w₁
  have hS_le : S.card ≤ m₁ + 1 := by
    have h1 := hsplit_card S
    have h2 : (S ∩ C₁).card ≤ m₁ := Finset.card_le_card Finset.inter_subset_right
    omega
  -- Helper: given `v` with `|v| ≤ 1 + (r + 1) * m₂`, `|Q · v| ≤ m₁ + 1`, and `¬ C₁ ⊆ Q · v`,
  -- Lemma G.1 (`optimal_twoCluster_avg`) finds `e = i + s * g` with `(Q · v a^e b) ⊆ C₁`!
  have hfinish : ∀ v : List α, v.length ≤ 1 + (r + 1) * m₂ →
      (A.image Finset.univ v).card ≤ m₁ + 1 → ¬ (C₁ ⊆ A.image Finset.univ v) →
      ∃ w₀ : List α, w₀.length ≤ (r + 1) * m₂ + n ∧ ∀ q : Q, A.eval q w₀ ∈ C₁ := by
    intro v hv_len hS'_le hnot_sub
    set S' := A.image Finset.univ v
    set a₁ := (S' ∩ C₁).card
    set a₂ := (S' ∩ C₂).card
    have ha_sum : a₁ + a₂ ≤ m₁ + 1 := by have := hsplit_card S'; omega
    have ha₁_lt : a₁ ≤ m₁ - 1 := by
      have hss : S' ∩ C₁ ⊂ C₁ := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, fun heq => ?_⟩
        apply hnot_sub
        intro x hx; rw [← heq] at hx; exact (Finset.mem_inter.mp hx).1
      have := Finset.card_lt_card hss
      omega
    -- Construct `D : TwoClusterData A` with `ℓ = 0`, `B₁ = C₁`, `B₂ = C₂` to invoke Lemma G.1!
    let D : TwoClusterData A :=
      { a := a
        C₁ := C₁
        C₂ := C₂
        B₁ := C₁
        B₂ := C₂
        ℓ := 0
        hC₁_ne := Finset.card_pos.mp (by omega)
        hC₂_ne := Finset.card_pos.mp (by omega)
        hC_disj := hC_disj
        hB_disj := hC_disj
        hB_union := hC_union
        hC₁_inv := hC₁_inv
        hC₁_trans := hC₁_trans
        hC₂_inv := hC₂_inv
        hC₂_trans := hC₂_trans
        hB₁_enter := fun _ h => h
        hB₂_enter := fun _ h => h
        hℓ_le := by omega }
    obtain ⟨hword_len, hE₁⟩ := optimal_twoCluster_avg D
    set g := Nat.gcd m₁ m₂
    set q₂ := m₂ / g
    have hm₁_pos : 0 < m₁ := by omega
    have hm₂_pos : 0 < m₂ := by omega
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left m₂ hm₁_pos
    have hq₂_mul : q₂ * g = m₂ := Nat.div_mul_cancel (Nat.gcd_dvd_right m₁ m₂)
    have hq₂_pos : 0 < q₂ := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at hq₂_mul; omega
    let ι := Fin m₁ × Fin q₂
    let word : ι → List α := fun idx => List.replicate (0 + idx.1.val + idx.2.val * g) a
    let μ : ℚ := (1 : ℚ) / ((m₁ : ℚ) * (q₂ : ℚ))
    have hm₁_q : (0 : ℚ) < (m₁ : ℚ) := by exact_mod_cast hm₁_pos
    have hm₂_q : (0 : ℚ) < (m₂ : ℚ) := by exact_mod_cast hm₂_pos
    have hq₂_q : (0 : ℚ) < (q₂ : ℚ) := by exact_mod_cast hq₂_pos
    have hμ_pos : 0 < μ := div_pos zero_lt_one (mul_pos hm₁_q hq₂_q)
    let Bad : Finset Q := Finset.univ.filter (fun z => A.step z b ∈ C₂)
    have hBad_C₁ : Bad ∩ C₁ = U₁₂ := by
      ext z; simp only [Bad, U₁₂, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have hBad_C₂ : Bad ∩ C₂ = D₂ := by
      ext z; simp only [Bad, D₂, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    -- Exact weighted average of `|(S' · word idx) ∩ Bad|` (counted with multiplicity)
    have havg_eq :
        (∑ idx : ι, μ * ((S'.filter (fun p => A.eval p (word idx) ∈ Bad)).card : ℚ)) =
          (a₁ : ℚ) * ((U₁₂.card : ℚ) / (m₁ : ℚ)) + (a₂ : ℚ) * ((r : ℚ) / (m₂ : ℚ)) := by
      have hcard_idx : ∀ idx : ι,
          ((S'.filter (fun p => A.eval p (word idx) ∈ Bad)).card : ℚ) =
            ∑ p ∈ S', ∑ z ∈ Bad, if A.eval p (word idx) = z then (1 : ℚ) else 0 := by
        intro idx
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hmem : A.eval p (word idx) ∈ Bad
        · simp only [hmem, ↓reduceIte, Nat.cast_one]
          rw [Finset.sum_eq_single (A.eval p (word idx))]
          · simp
          · intro z _ hz; simp [Ne.symm hz]
          · intro h; exact absurd hmem h
        · simp only [hmem, ↓reduceIte, Nat.cast_zero]
          exact (Finset.sum_eq_zero fun z hz => by
            have hne : A.eval p (word idx) ≠ z := fun h => hmem (h ▸ hz)
            simp [hne]).symm
      simp_rw [hcard_idx]
      trans ∑ p ∈ S', ∑ z ∈ Bad,
          (∑ idx : ι, if A.eval p (word idx) = z then μ else 0)
      · calc (∑ idx : ι, μ * ∑ p ∈ S', ∑ z ∈ Bad,
              (if A.eval p (word idx) = z then (1 : ℚ) else 0))
            = ∑ idx : ι, ∑ p ∈ S', ∑ z ∈ Bad,
                (if A.eval p (word idx) = z then μ else 0) := by
                refine Finset.sum_congr rfl fun idx _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun p _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun z _ => by split_ifs <;> ring
          _ = ∑ p ∈ S', ∑ idx : ι, ∑ z ∈ Bad,
                (if A.eval p (word idx) = z then μ else 0) := Finset.sum_comm
          _ = ∑ p ∈ S', ∑ z ∈ Bad, ∑ idx : ι,
                (if A.eval p (word idx) = z then μ else 0) :=
                Finset.sum_congr rfl fun p _ => Finset.sum_comm
      · have hE₁' : ∀ p z : Q,
            (∑ idx : ι, if A.eval p (word idx) = z then μ else 0) =
              if p ∈ C₁ then (if z ∈ C₁ then (1 : ℚ) / (m₁ : ℚ) else 0)
              else (if z ∈ C₂ then (1 : ℚ) / (m₂ : ℚ) else 0) :=
          fun p z => hE₁ p z
        simp_rw [hE₁']
        have hinner : ∀ p ∈ S',
            (∑ z ∈ Bad, if p ∈ C₁ then (if z ∈ C₁ then (1 : ℚ) / (m₁ : ℚ) else 0)
              else (if z ∈ C₂ then (1 : ℚ) / (m₂ : ℚ) else 0)) =
              if p ∈ C₁ then (U₁₂.card : ℚ) / (m₁ : ℚ) else (r : ℚ) / (m₂ : ℚ) := by
          intro p _
          by_cases hp1 : p ∈ C₁
          · simp only [hp1, ↓reduceIte, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
              hBad_C₁, Finset.sum_const, nsmul_eq_mul]
            ring
          · simp only [hp1, ↓reduceIte, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
              hBad_C₂, Finset.sum_const, nsmul_eq_mul]
            ring
        rw [Finset.sum_congr rfl hinner, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
          nsmul_eq_mul, nsmul_eq_mul]
        have hf1 : S'.filter (fun p => p ∈ C₁) = S' ∩ C₁ := Finset.filter_mem_eq_inter
        have hf2 : S'.filter (fun p => p ∉ C₁) = S' ∩ C₂ := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_inter, and_congr_right_iff]
          intro _
          constructor
          · intro hnot1
            have huniv : p ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ p
            exact (Finset.mem_union.mp huniv).resolve_left hnot1
          · intro hp2 hp1
            exact Finset.disjoint_left.mp hC_disj hp1 hp2
        rw [hf1, hf2]
    -- Show weighted average `< 1` using `a₁ ≤ m₁ - 1`, `a₁ + a₂ ≤ m₁ + 1`, `2 * r * m₁ < m₂`
    have havg_lt1 :
        (∑ idx : ι, μ * ((S'.filter (fun p => A.eval p (word idx) ∈ Bad)).card : ℚ)) < 1 := by
      rw [havg_eq]
      have hU_le : (U₁₂.card : ℚ) ≤ 1 := by exact_mod_cast hk₁₂
      have ha₁_nn : (0 : ℚ) ≤ (a₁ : ℚ) := Nat.cast_nonneg a₁
      have hU_term : (a₁ : ℚ) * ((U₁₂.card : ℚ) / (m₁ : ℚ)) ≤ (a₁ : ℚ) / (m₁ : ℚ) := by
        have h1 : (U₁₂.card : ℚ) / (m₁ : ℚ) ≤ 1 / (m₁ : ℚ) :=
          div_le_div_of_nonneg_right hU_le hm₁_q.le
        have h2 := mul_le_mul_of_nonneg_left h1 ha₁_nn
        linarith [show (a₁ : ℚ) * (1 / (m₁ : ℚ)) = (a₁ : ℚ) / (m₁ : ℚ) by ring]
      have hcross : (a₁ : ℚ) * (m₂ : ℚ) + (a₂ : ℚ) * (r : ℚ) * (m₁ : ℚ) < (m₁ : ℚ) * (m₂ : ℚ) := by
        have ha₁_z : (a₁ : ℚ) ≤ (m₁ : ℚ) - 1 := by
          have : a₁ + 1 ≤ m₁ := by omega
          have : (a₁ : ℚ) + 1 ≤ (m₁ : ℚ) := by exact_mod_cast this
          linarith
        have ha_sum_z : (a₁ : ℚ) + (a₂ : ℚ) ≤ (m₁ : ℚ) + 1 := by exact_mod_cast ha_sum
        have hcond_z : 2 * (r : ℚ) * (m₁ : ℚ) < (m₂ : ℚ) := by exact_mod_cast hcond
        have hrm₁_nn : (0 : ℚ) ≤ (r : ℚ) * (m₁ : ℚ) := mul_nonneg (Nat.cast_nonneg r) hm₁_q.le
        have hdiff_pos : (0 : ℚ) < (m₂ : ℚ) - (r : ℚ) * (m₁ : ℚ) := by linarith
        nlinarith only [ha₁_z, ha_sum_z, hcond_z, hrm₁_nn, hdiff_pos]
      have hdiv_lt : (a₁ : ℚ) / (m₁ : ℚ) + (a₂ : ℚ) * ((r : ℚ) / (m₂ : ℚ)) < 1 := by
        have hden : (0 : ℚ) < (m₁ : ℚ) * (m₂ : ℚ) := mul_pos hm₁_q hm₂_q
        have hrew : (a₁ : ℚ) / (m₁ : ℚ) + (a₂ : ℚ) * ((r : ℚ) / (m₂ : ℚ)) =
            ((a₁ : ℚ) * (m₂ : ℚ) + (a₂ : ℚ) * (r : ℚ) * (m₁ : ℚ)) / ((m₁ : ℚ) * (m₂ : ℚ)) := by
          field_simp [hm₁_q.ne', hm₂_q.ne']
        rw [hrew]
        have hmul : (((a₁ : ℚ) * (m₂ : ℚ) + (a₂ : ℚ) * (r : ℚ) * (m₁ : ℚ)) /
            ((m₁ : ℚ) * (m₂ : ℚ))) * ((m₁ : ℚ) * (m₂ : ℚ)) =
            (a₁ : ℚ) * (m₂ : ℚ) + (a₂ : ℚ) * (r : ℚ) * (m₁ : ℚ) :=
          div_mul_cancel₀ _ hden.ne'
        nlinarith only [hcross, hmul, hden]
      linarith
    -- Since `∑ idx, μ = 1` and average `< 1`, some `idx` has card `= 0`!
    have hμ_sum : ∑ _idx : ι, μ = 1 := by
      dsimp only [ι, μ]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul]
      have hcast : ((m₁ * q₂ : ℕ) : ℚ) = (m₁ : ℚ) * (q₂ : ℚ) := Nat.cast_mul m₁ q₂
      rw [hcast]
      exact mul_one_div_cancel (mul_pos hm₁_q hq₂_q).ne'
    have hex_zero : ∃ idx : ι, (S'.filter (fun p => A.eval p (word idx) ∈ Bad)).card = 0 := by
      by_contra hall
      push Not at hall
      have hge1 : ∀ idx : ι,
          μ ≤ μ * ((S'.filter (fun p => A.eval p (word idx) ∈ Bad)).card : ℚ) := by
        intro idx
        have h1 : (1 : ℚ) ≤ ((S'.filter (fun p => A.eval p (word idx) ∈ Bad)).card : ℚ) := by
          have : 1 ≤ (S'.filter (fun p => A.eval p (word idx) ∈ Bad)).card :=
            Nat.pos_of_ne_zero (hall idx)
          exact_mod_cast this
        nlinarith only [hμ_pos, h1]
      have hsum_ge : ∑ _idx : ι, μ ≤
          ∑ idx : ι, μ * ((S'.filter (fun p => A.eval p (word idx) ∈ Bad)).card : ℚ) :=
        Finset.sum_le_sum fun idx _ => hge1 idx
      rw [hμ_sum] at hsum_ge
      linarith
    obtain ⟨idx, hidx0⟩ := hex_zero
    refine ⟨v ++ word idx ++ [b], ?_, ?_⟩
    · rw [List.length_append, List.length_append, List.length_singleton]
      have hwl : (word idx).length ≤ 0 + (m₁ + m₂ - g - 1) := hword_len idx
      omega
    · intro q
      rw [DFA.eval_append, DFA.eval_append, DFA.eval_singleton]
      have hqS' : A.eval q v ∈ S' := (DFA.mem_image A Finset.univ v _).mpr ⟨q, Finset.mem_univ q, rfl⟩
      have hnot_bad : A.eval (A.eval q v) (word idx) ∉ Bad := by
        intro hbad
        have hmem : A.eval q v ∈ S'.filter (fun p => A.eval p (word idx) ∈ Bad) :=
          Finset.mem_filter.mpr ⟨hqS', hbad⟩
        have hpos := Finset.card_pos.mpr ⟨A.eval q v, hmem⟩
        omega
      have hnotC₂ : A.step (A.eval (A.eval q v) (word idx)) b ∉ C₂ := fun h2 =>
        hnot_bad (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
      have huniv : A.step (A.eval (A.eval q v) (word idx)) b ∈ C₁ ∪ C₂ := by
        rw [hC_union]; exact Finset.mem_univ _
      exact (Finset.mem_union.mp huniv).resolve_right hnotC₂
  -- Now split on whether `C₁ ⊆ S` (`S = Q · w₁`)
  by_cases hC₁S : C₁ ⊆ S
  · by_cases hSC₁ : S ⊆ C₁
    · refine ⟨w₁, ?_, fun q => hSC₁ ((DFA.mem_image A Finset.univ w₁ _).mpr ⟨q, Finset.mem_univ q, rfl⟩)⟩
      have : (r + 1) * m₂ = r * m₂ + m₂ := by ring
      omega
    · -- `C₁ ⊂ S` (`|S| = m₁ + 1`): apply Szykuła's Avoiding-Subset Lemma (`|u| ≤ m₂`)!
      have hC₁_ne : C₁.Nonempty := Finset.card_pos.mp (by omega)
      have hC₁_ne_univ : C₁ ≠ Finset.univ := by
        intro huniv
        have := congrArg Finset.card huniv
        rw [Finset.card_univ] at this
        omega
      have hAvoid : ∃ u : List α, ¬ (C₁ ⊆ A.image S u) := by
        rcases hSync with ⟨w_sync, q₀, hq₀⟩
        refine ⟨w_sync, fun hsub => ?_⟩
        have himg_sub : A.image S w_sync ⊆ {q₀} := by
          intro y hy
          rcases (DFA.mem_image A S w_sync y).mp hy with ⟨p, _, rfl⟩
          exact Finset.mem_singleton.mpr (hq₀ p)
        have hcard : C₁.card ≤ 1 := by
          calc C₁.card ≤ (A.image S w_sync).card := Finset.card_le_card hsub
            _ ≤ ({q₀} : Finset Q).card := Finset.card_le_card himg_sub
            _ = 1 := Finset.card_singleton q₀
        omega
      obtain ⟨u, hu_len, hu_prop⟩ := szykula_avoiding_lemma A S C₁ hC₁_ne hC₁S hC₁_ne_univ hAvoid
      have hv_len : (w₁ ++ u).length ≤ 1 + (r + 1) * m₂ := by
        rw [List.length_append]
        have : (r + 1) * m₂ = r * m₂ + m₂ := by ring
        omega
      have himg_eq : A.image Finset.univ (w₁ ++ u) = A.image S u := DFA.image_append A Finset.univ w₁ u
      rcases hu_prop with hnot_sub | hlt_card
      · exact hfinish (w₁ ++ u) hv_len
          (by rw [himg_eq]; exact (DFA.card_image_le A S u).trans hS_le)
          (by rw [himg_eq]; exact hnot_sub)
      · by_cases hC₁Su : C₁ ⊆ A.image S u
        · -- `C₁ ⊆ A.image S u` and `|A.image S u| < |S| ≤ m₁ + 1`, so `A.image S u = C₁`!
          have heq : A.image S u = C₁ :=
            (Finset.eq_of_subset_of_card_le hC₁Su (by omega)).symm
          refine ⟨w₁ ++ u, ?_, fun q => ?_⟩
          · omega
          · have hmem : A.eval q (w₁ ++ u) ∈ A.image Finset.univ (w₁ ++ u) :=
              (DFA.mem_image A Finset.univ (w₁ ++ u) _).mpr ⟨q, Finset.mem_univ q, rfl⟩
            rwa [himg_eq, heq] at hmem
        · exact hfinish (w₁ ++ u) hv_len
            (by rw [himg_eq]; exact (DFA.card_image_le A S u).trans hS_le)
            (by rw [himg_eq]; exact hC₁Su)
  · have hv_len : w₁.length ≤ 1 + (r + 1) * m₂ := by
      have : (r + 1) * m₂ = r * m₂ + m₂ := by ring
      omega
    exact hfinish w₁ hv_len hS_le hC₁S

/-! ### Step 3: Main Exports — Sub-`(3/2)` & Exact Černý `(n - 1)^2` Bounds (Theorem F_part) -/

/-- **Theorem F_part(1) (`< (3/2)(n - 1)^2` for ALL `r ≥ 1` with `2 * r * m₁ < m₂`)**:
Every synchronizing 2-cycle permutation DFA (`m₁, m₂ ≥ 2`, NO strong connectivity!) with
`k₁₂(b) ≤ 1` and `r = m₂ - k₂₁(b) ≥ 1` satisfying `2 * r * m₁ < m₂` obeys
`2 * w.length ≤ 3 * (Fintype.card Q - 1) ^ 2`! -/
theorem partialDrain_threeHalves_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (a b : α) (C₁ C₂ : Finset Q)
    (hm₁ : 2 ≤ C₁.card) (hm₂ : 2 ≤ C₂.card)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hr_pos : 1 ≤ (C₂.filter (fun x => A.step x b ∈ C₂)).card)
    (hcond : 2 * (C₂.filter (fun x => A.step x b ∈ C₂)).card * C₁.card < C₂.card) :
    ∃ w : List α, A.IsSyncWord w ∧ 2 * w.length ≤ 3 * (Fintype.card Q - 1) ^ 2 := by
  have hn_eq : Fintype.card Q = C₁.card + C₂.card := by
    rw [← Finset.card_univ, ← hC_union, Finset.card_union_of_disjoint hC_disj]
  obtain ⟨w₀, hw₀_len, hw₀_in⟩ :=
    partialDrain_exists_collapseWord A hSync a b C₁ C₂ hm₁ hm₂ hC_disj hC_union
      hC₁_inv hC₁_trans hC₂_inv hC₂_trans hk₁₂ hcond
  obtain ⟨w, hw_sync, hw_len⟩ :=
    shortCollapse_cycle_reset_bound A hSync a C₁ hm₁ hC₁_inv hC₁_trans w₀
      (((C₂.filter (fun x => A.step x b ∈ C₂)).card + 1) * C₂.card + Fintype.card Q)
      hw₀_len hw₀_in
  exact ⟨w, hw_sync,
    AlpogePartialDrain.arith_threeHalves (Fintype.card Q) C₁.card C₂.card
      (C₂.filter (fun x => A.step x b ∈ C₂)).card w.length hm₁ hr_pos hn_eq hcond hw_len⟩

/-- **Theorem F_part(2) (EXACT Černý Conjecture `(n - 1)^2` for `r ≥ 2` OR `r = 1 ∧ 4 * m₁ < m₂`)**:
Whenever `k₁₂(b) ≤ 1`, `2 * r * m₁ < m₂`, AND either `2 ≤ r` or `4 * m₁ < m₂`, the Černý
Conjecture holds **EXACTLY**: `∃ w, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2`! -/
theorem partialDrain_exact_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (a b : α) (C₁ C₂ : Finset Q)
    (hm₁ : 2 ≤ C₁.card) (hm₂ : 2 ≤ C₂.card)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hcond : 2 * (C₂.filter (fun x => A.step x b ∈ C₂)).card * C₁.card < C₂.card)
    (hregime : 2 ≤ (C₂.filter (fun x => A.step x b ∈ C₂)).card ∨ 4 * C₁.card < C₂.card) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have hn_eq : Fintype.card Q = C₁.card + C₂.card := by
    rw [← Finset.card_univ, ← hC_union, Finset.card_union_of_disjoint hC_disj]
  have h5m₁ : 5 * C₁.card < Fintype.card Q := by
    rcases hregime with hr2 | h4m₁
    · have h4 : 4 * C₁.card ≤ 2 * (C₂.filter (fun x => A.step x b ∈ C₂)).card * C₁.card := by
        have := Nat.mul_le_mul_right C₁.card (show 4 ≤ 2 * (C₂.filter (fun x => A.step x b ∈ C₂)).card by omega)
        simpa [Nat.mul_assoc] using this
      omega
    · omega
  obtain ⟨w₀, hw₀_len, hw₀_in⟩ :=
    partialDrain_exists_collapseWord A hSync a b C₁ C₂ hm₁ hm₂ hC_disj hC_union
      hC₁_inv hC₁_trans hC₂_inv hC₂_trans hk₁₂ hcond
  obtain ⟨w, hw_sync, hw_len⟩ :=
    shortCollapse_cycle_reset_bound A hSync a C₁ hm₁ hC₁_inv hC₁_trans w₀
      (((C₂.filter (fun x => A.step x b ∈ C₂)).card + 1) * C₂.card + Fintype.card Q)
      hw₀_len hw₀_in
  exact ⟨w, hw_sync,
    AlpogePartialDrain.arith_exact_cerny (Fintype.card Q) C₁.card C₂.card
      (C₂.filter (fun x => A.step x b ∈ C₂)).card w.length hm₁ hn_eq hcond h5m₁ hw_len⟩

/-- **Corollary (`r ≥ 2` exact Černý `(n - 1)^2`)**: For ALL `r ≥ 2` with `2 * r * m₁ < m₂`,
`w.length ≤ (Fintype.card Q - 1) ^ 2`. -/
theorem partialDrain_ge_two_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (a b : α) (C₁ C₂ : Finset Q)
    (hm₁ : 2 ≤ C₁.card) (hm₂ : 2 ≤ C₂.card)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hr2 : 2 ≤ (C₂.filter (fun x => A.step x b ∈ C₂)).card)
    (hcond : 2 * (C₂.filter (fun x => A.step x b ∈ C₂)).card * C₁.card < C₂.card) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  partialDrain_exact_cerny A hSync a b C₁ C₂ hm₁ hm₂ hC_disj hC_union
    hC₁_inv hC₁_trans hC₂_inv hC₂_trans hk₁₂ hcond (Or.inl hr2)

/-- **Corollary (`r = 1, 4 * m₁ < m₂` exact Černý `(n - 1)^2`)**: When `r = 1` and `4 * m₁ < m₂`,
`w.length ≤ (Fintype.card Q - 1) ^ 2`. -/
theorem partialDrain_one_cerny {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (a b : α) (C₁ C₂ : Finset Q)
    (hm₁ : 2 ≤ C₁.card) (hm₂ : 2 ≤ C₂.card)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hr1 : (C₂.filter (fun x => A.step x b ∈ C₂)).card = 1)
    (h4m₁ : 4 * C₁.card < C₂.card) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 :=
  partialDrain_exact_cerny A hSync a b C₁ C₂ hm₁ hm₂ hC_disj hC_union
    hC₁_inv hC₁_trans hC₂_inv hC₂_trans hk₁₂ (by rw [hr1]; omega) (Or.inr h4m₁)

end Cerny
