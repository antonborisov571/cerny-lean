import Cerny.Defs
import Cerny.AdditionalClasses
import Cerny.AlpogeThetaLift
import Cerny.AlpogeOppositeDrift
import Cerny.AlpogeCycleDrain
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push

/-!
# Complete Exact Černý Closure of `2 r m₁ < m₂` (`Theorem F_part_exact`) & Small-`gcd` Partial Drain (`Theorem F_gcd`)

This file formalizes Round 5's 2-cycle closure theorems (`docs/round5_two_cycle_closure.md` §1 & §5.1)
with **NO strong connectivity** and **arbitrary finite alphabet `α`**:

## Main Results
* `Cerny.shortShift_exp_halving` (**Lemma F_exp**): Pure Markov short-shift halving (`2 * r < m₂`)
  reduces `|(Q · w₁) ∩ C₂| ≤ 1` in length `≤ 1 + (Nat.log 2 r + 1) * (2 * r + 1) ≤ 1 + r * (2 * r + 1)`
  — completely independent of `m₂`!
* `Cerny.partialDrain_exp_collapseWord` & `Cerny.partialDrain_all_exact_cerny`
  (**Theorem F_part_exact — 100% Exact Černý `(n - 1)^2`!**):
  For ALL synchronizing 2-cycle permutation DFAs (`m₁, m₂ ≥ 2`) with `k₁₂(b) ≤ 1`, `r ≥ 1`, and
  `2 * r * m₁ < m₂`, proves `∃ w, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2` — closing
  100% of Round 4's `r = 1, 2 m₁ < m₂ ≤ 4 m₁` gap with ZERO exceptions!
* `Cerny.smallGcd_collapseWord` & `Cerny.smallGcd_reset_bound` (**Theorem F_gcd**):
  Replacing `2 * r * m₁ < m₂` by `2 * r * gcd(m₁, m₂) < m₂` (completely removing any upper bound
  on `m₁` for coprime `(m₁, m₂)`!) produces a zero-linear-algebra collapse word `Q · w₀ ⊆ C₁`
  of length `≤ 1 + (Nat.log 2 r + 1) * (2 * r + 1) + m₂ + (2 * r + 1) * m₁`.
* `Cerny.smallGcd_r1_reset_bound`, `Cerny.smallGcd_r1_five_bound`, `Cerny.smallGcd_r1_le_half_bound`
  (**Corollary F_gcd.1**): For ALL `r = 1, 2 * gcd(m₁, m₂) < m₂`,
  `w.length ≤ 3 * m₁^2 + (2 * n - 1) * m₁ - n + 5 < 5 * (n - 1)^2` always, and
  `4 * w.length ≤ 7 * n^2 - 16 * n + 25` (`w.length < 2 * (n - 1)^2`) whenever `m₁ ≤ m₂`.
-/

namespace Cerny

universe u v

namespace PartialDrainExact

/-! ### Cycle Orbit & Period Helpers -/

/-- On a finite invariant transitive cycle `C`, iterating `step · a` for `0 ≤ j < |C|`
gives a bijection `Fin C.card ≃ C`, `f^[C.card] c₀ = c₀`, and `f^[k] c₀ = c₀ ↔ C.card ∣ k`. -/
private lemma cycle_period_props {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a : α) (C : Finset Q) (hC_inv : ∀ q ∈ C, A.step q a ∈ C)
    (hC_trans : ∀ p ∈ C, ∀ q ∈ C, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) :
    (∀ k : ℕ, ∀ q ∈ C, (fun x => A.step x a)^[k] q ∈ C) ∧
    Set.InjOn (fun x => A.step x a) (C : Set Q) ∧
    (∀ c₀ ∈ C, (fun x => A.step x a)^[C.card] c₀ = c₀) ∧
    (∀ c₀ ∈ C, ∀ k : ℕ, (fun x => A.step x a)^[k] c₀ = c₀ ↔ C.card ∣ k) ∧
    (∀ c₀ ∈ C, ∀ D : Finset Q,
      (∑ j : Fin C.card, if (fun x => A.step x a)^[j.val] c₀ ∈ D then 1 else 0) = (D ∩ C).card) := by
  let f : Q → Q := fun x => A.step x a
  have hiter_mem : ∀ k : ℕ, ∀ q ∈ C, f^[k] q ∈ C := by
    intro k
    induction k with
    | zero => intro q hq; exact hq
    | succ k ih => intro q hq; rw [Function.iterate_succ_apply']; exact hC_inv _ (ih q hq)
  let fC : C → C := fun x => ⟨f x.1, hC_inv x.1 x.2⟩
  have hfC_iter : ∀ (k : ℕ) (x : C), (fC^[k] x).1 = f^[k] x.1 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply, ih]; rfl
  have hfC_surj : Function.Surjective fC := by
    intro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hC_trans (f y) (hC_inv y hy) y hy
    refine ⟨⟨f^[k] y, hiter_mem k y hy⟩, Subtype.ext ?_⟩
    change f (f^[k] y) = y
    rw [← Function.iterate_succ_apply' f k y, Function.iterate_succ_apply]
    exact hk
  have hfC_inj : Function.Injective fC :=
    (Fintype.bijective_iff_surjective_and_card fC).mpr ⟨hfC_surj, rfl⟩ |>.1
  have hinj : Set.InjOn f (C : Set Q) := by
    intro p hp q hq heq
    have hsub : fC ⟨p, hp⟩ = fC ⟨q, hq⟩ := Subtype.ext heq
    exact congrArg Subtype.val (hfC_inj hsub)
  have hmin : ∀ c₀ ∈ C, ∀ k : ℕ, 0 < k → k < C.card → f^[k] c₀ ≠ c₀ := by
    intro c₀ hc₀ k hk0 hkc hfix
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
  have hbij_orbit : ∀ (c₀ : Q) (hc₀ : c₀ ∈ C),
      Function.Bijective (fun j : Fin C.card => (⟨f^[j.val] c₀, hiter_mem j.val c₀ hc₀⟩ : C)) := by
    intro c₀ hc₀
    have hg_inj : Function.Injective
        (fun j : Fin C.card => (⟨f^[j.val] c₀, hiter_mem j.val c₀ hc₀⟩ : C)) := by
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
        exact hmin c₀ hc₀ (y - x) (by omega) (by omega) hfix
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · exact hstep i.val j.val hlt j.isLt hval
      · exact hstep j.val i.val hgt i.isLt hval.symm
    exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hg_inj, by simp⟩
  have hperiod : ∀ c₀ ∈ C, f^[C.card] c₀ = c₀ := by
    intro c₀ hc₀
    obtain ⟨i, hi⟩ := (hbij_orbit c₀ hc₀).2 ⟨f^[C.card] c₀, hiter_mem C.card c₀ hc₀⟩
    have hval : f^[i.val] c₀ = f^[C.card] c₀ := congrArg Subtype.val hi
    by_cases hi0 : i.val = 0
    · rw [hi0, Function.iterate_zero_apply] at hval; exact hval.symm
    · exfalso
      have hsub : fC^[i.val] ⟨c₀, hc₀⟩ = fC^[C.card] ⟨c₀, hc₀⟩ :=
        Subtype.ext (by rw [hfC_iter, hfC_iter]; exact hval)
      have hsplit : C.card = i.val + (C.card - i.val) := by omega
      have hiter : fC^[C.card] ⟨c₀, hc₀⟩ = fC^[i.val] (fC^[C.card - i.val] ⟨c₀, hc₀⟩) := by
        rw [← Function.iterate_add_apply, ← hsplit]
      rw [hiter] at hsub
      have hfixC : fC^[C.card - i.val] ⟨c₀, hc₀⟩ = ⟨c₀, hc₀⟩ := (hfC_inj.iterate i.val) hsub.symm
      have hfix : f^[C.card - i.val] c₀ = c₀ := by
        have := congrArg Subtype.val hfixC; rwa [hfC_iter] at this
      exact hmin c₀ hc₀ (C.card - i.val) (by omega) (by omega) hfix
  have hdvd_iff : ∀ c₀ ∈ C, ∀ k : ℕ, f^[k] c₀ = c₀ ↔ C.card ∣ k := by
    intro c₀ hc₀ k
    have hmul : ∀ t : ℕ, f^[C.card * t] c₀ = c₀ := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hperiod c₀ hc₀]
    have hmod : f^[k] c₀ = f^[k % C.card] c₀ := by
      have hdiv : k = k % C.card + C.card * (k / C.card) := by have := Nat.div_add_mod k C.card; omega
      conv_lhs => rw [hdiv, Function.iterate_add_apply, hmul]
    constructor
    · intro hfix
      rw [hmod] at hfix
      have hpos : 0 < C.card := Finset.card_pos.mpr ⟨c₀, hc₀⟩
      have hrem : k % C.card = 0 := by
        by_contra hne
        exact hmin c₀ hc₀ (k % C.card) (Nat.pos_of_ne_zero hne) (Nat.mod_lt k hpos) hfix
      exact Nat.dvd_of_mod_eq_zero hrem
    · rintro ⟨t, rfl⟩
      exact hmul t
  have hcount : ∀ c₀ ∈ C, ∀ D : Finset Q,
      (∑ j : Fin C.card, if f^[j.val] c₀ ∈ D then 1 else 0) = (D ∩ C).card := by
    intro c₀ hc₀ D
    let e : Fin C.card ≃ C := Equiv.ofBijective _ (hbij_orbit c₀ hc₀)
    have hsum : (∑ j : Fin C.card, if (e j).1 ∈ D then (1 : ℕ) else 0) =
        ∑ x : C, if x.1 ∈ D then (1 : ℕ) else 0 :=
      Fintype.sum_equiv e (fun j => if (e j).1 ∈ D then 1 else 0)
        (fun x => if x.1 ∈ D then 1 else 0) (fun _ => rfl)
    change (∑ j : Fin C.card, if (e j).1 ∈ D then 1 else 0) = (D ∩ C).card
    rw [hsum, Finset.sum_coe_sort C (fun x => if x ∈ D then (1 : ℕ) else 0),
      ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_inter]; tauto
  exact ⟨hiter_mem, hinj, hperiod, hdvd_iff, hcount⟩

/-- `Nat.log 2 r + 1 ≤ r` for every `r ≥ 1`. -/
private lemma log2_succ_le (r : ℕ) (hr : 1 ≤ r) : Nat.log 2 r + 1 ≤ r := by
  have hlt : Nat.log 2 r < r :=
    Nat.log_lt_of_lt_pow (by omega) Nat.lt_two_pow_self
  omega

/-- Pure `ℕ` arithmetic core for Theorem `F_part_exact` (`r ≥ 1, m₁ ≥ 2, 2 r m₁ < m₂ → R ≤ (n - 1)^2`). -/
private lemma arith_exact_all_r (n m₁ m₂ r R : ℕ)
    (hm₁ : 2 ≤ m₁) (hr : 1 ≤ r) (hn : n = m₁ + m₂) (hcond : 2 * r * m₁ < m₂)
    (hR : R ≤ (r * (2 * r + 1) + m₂ + n) +
        (m₁ - 2) * (n - 1 + (r * (2 * r + 1) + m₂ + n) + m₁ - 1) +
        (n - m₁ + 1 + (r * (2 * r + 1) + m₂ + n))) :
    R ≤ (n - 1) ^ 2 := by
  have h1 : 1 ≤ n := by omega
  have hm₁_le : m₁ ≤ n := by omega
  have hsub2 : 1 ≤ n - 1 + (r * (2 * r + 1) + m₂ + n) + m₁ := by omega
  zify [hm₁, h1, hm₁_le, hsub2] at hR ⊢
  have hn_z : (n : ℤ) = (m₁ : ℤ) + (m₂ : ℤ) := by exact_mod_cast hn
  have hm₂_z : (m₂ : ℤ) = (n : ℤ) - (m₁ : ℤ) := by linarith
  -- Notice `m₁^2` cancels identically!
  have hR' : (R : ℤ) ≤ (m₁ : ℤ) * (r : ℤ) * (2 * (r : ℤ) + 1) +
      (3 * (n : ℤ) - 5) * (m₁ : ℤ) - (n : ℤ) + 5 := by
    nlinarith only [hR, hm₂_z]
  have hcond_z : 2 * (r : ℤ) * (m₁ : ℤ) + 1 ≤ (m₂ : ℤ) := by
    have : 2 * (r : ℤ) * (m₁ : ℤ) < (m₂ : ℤ) := by exact_mod_cast hcond
    linarith
  have hprod_bound : (2 * (r : ℤ) + 1) * (m₁ : ℤ) ≤ (n : ℤ) - 1 := by linarith
  by_cases hr1 : r = 1
  · subst hr1
    push_cast at hR' hprod_bound
    have h3m₁ : 3 * (m₁ : ℤ) ≤ (n : ℤ) - 1 := by linarith
    have hn7 : (7 : ℤ) ≤ (n : ℤ) := by omega
    have h3n2 : (0 : ℤ) ≤ 3 * (n : ℤ) - 2 := by omega
    have hmul : (3 * (n : ℤ) - 2) * (3 * (m₁ : ℤ)) ≤ (3 * (n : ℤ) - 2) * ((n : ℤ) - 1) :=
      mul_le_mul_of_nonneg_left h3m₁ h3n2
    nlinarith only [hR', hmul, hn7]
  · have hr2 : (2 : ℤ) ≤ (r : ℤ) := by omega
    have hm₁_z : (2 : ℤ) ≤ (m₁ : ℤ) := by exact_mod_cast hm₁
    have hr_nn : (0 : ℤ) ≤ (r : ℤ) := by omega
    have h5m₁ : 5 * (m₁ : ℤ) ≤ (n : ℤ) - 1 := by
      have : 5 * (m₁ : ℤ) ≤ (2 * (r : ℤ) + 1) * (m₁ : ℤ) := by nlinarith only [hr2, hm₁_z]
      linarith
    have h4r : 4 * (r : ℤ) ≤ (n : ℤ) - 3 := by
      have : 4 * (r : ℤ) + 2 ≤ (2 * (r : ℤ) + 1) * (m₁ : ℤ) := by nlinarith only [hr_nn, hm₁_z]
      linarith
    have hn11 : (11 : ℤ) ≤ (n : ℤ) := by linarith
    have hterm1 : (m₁ : ℤ) * (r : ℤ) * (2 * (r : ℤ) + 1) ≤ (r : ℤ) * ((n : ℤ) - 1) := by
      have := mul_le_mul_of_nonneg_left hprod_bound hr_nn
      linarith
    have hterm1' : 4 * ((r : ℤ) * ((n : ℤ) - 1)) ≤ ((n : ℤ) - 3) * ((n : ℤ) - 1) := by
      have := mul_le_mul_of_nonneg_right h4r (show (0 : ℤ) ≤ (n : ℤ) - 1 by omega)
      linarith
    have hterm2 : (3 * (n : ℤ) - 5) * (5 * (m₁ : ℤ)) ≤ (3 * (n : ℤ) - 5) * ((n : ℤ) - 1) :=
      mul_le_mul_of_nonneg_left h5m₁ (by omega)
    nlinarith only [hR', hterm1, hterm1', hterm2, hn11]

/-- Pure `ℕ` arithmetic core for Corollary `F_gcd.1` (`r = 1, 2 g < m₂`). -/
private lemma arith_smallGcd_r1 (n m₁ m₂ R : ℕ)
    (hm₁ : 2 ≤ m₁) (hm₂ : 3 ≤ m₂) (hn : n = m₁ + m₂)
    (hR : R ≤ (1 + (Nat.log 2 1 + 1) * (2 * 1 + 1) + m₂ + (2 * 1 + 1) * m₁) +
        (m₁ - 2) * (n - 1 + (1 + (Nat.log 2 1 + 1) * (2 * 1 + 1) + m₂ + (2 * 1 + 1) * m₁) + m₁ - 1) +
        (n - m₁ + 1 + (1 + (Nat.log 2 1 + 1) * (2 * 1 + 1) + m₂ + (2 * 1 + 1) * m₁))) :
    R ≤ 3 * m₁ ^ 2 + (2 * n - 1) * m₁ - n + 5 := by
  have hlog : Nat.log 2 1 = 0 := by decide
  rw [hlog] at hR
  have h1 : 1 ≤ n := by omega
  have hm₁_le : m₁ ≤ n := by omega
  have hsub2 : 1 ≤ n - 1 + (1 + (0 + 1) * (2 * 1 + 1) + m₂ + (2 * 1 + 1) * m₁) + m₁ := by omega
  have h2n1 : 1 ≤ 2 * n := by omega
  have hn_le : n ≤ 3 * m₁ ^ 2 + (2 * n - 1) * m₁ := by
    have : n ≤ (2 * n - 1) * 1 := by omega
    have : (2 * n - 1) * 1 ≤ (2 * n - 1) * m₁ := Nat.mul_le_mul_left _ (by omega)
    omega
  zify [hm₁, h1, hm₁_le, hsub2, h2n1, hn_le] at hR ⊢
  have hn_z : (n : ℤ) = (m₁ : ℤ) + (m₂ : ℤ) := by exact_mod_cast hn
  nlinarith only [hR, hn_z]

end PartialDrainExact

/-! ### Section 1: Lemma F_exp — Markov Short-Shift Exponential `C₂`-Halving -/

/-- **Lemma F_exp (Short-Shift Exponential `C₂`-Halving — Independent of `m₂`!)**:
For any 2-cycle permutation letter `a` (`Q = C₁ ⊔ C₂`) and letter `b` with `k₁₂(b) ≤ 1` and
`1 ≤ r := |{x ∈ C₂ : x · b ∈ C₂}|` satisfying `2 * r < m₂`, Markov's inequality on `{0, ..., 2r}`
halves `|(Q · w) ∩ C₂| - 1` at each round of length `≤ 2r + 1`, yielding `w₁` with:
- `w₁.length ≤ 1 + (Nat.log 2 r + 1) * (2 * r + 1)`,
- `w₁.length ≤ 1 + r * (2 * r + 1)`,
- `|(Q · w₁) ∩ C₂| ≤ 1`. -/
theorem shortShift_exp_halving {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a b : α) (C₁ C₂ : Finset Q)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hr_pos : 1 ≤ (C₂.filter (fun x => A.step x b ∈ C₂)).card)
    (h2r : 2 * (C₂.filter (fun x => A.step x b ∈ C₂)).card < C₂.card) :
    let r := (C₂.filter (fun x => A.step x b ∈ C₂)).card
    ∃ w₁ : List α,
      w₁.length ≤ 1 + (Nat.log 2 r + 1) * (2 * r + 1) ∧
      w₁.length ≤ 1 + r * (2 * r + 1) ∧
      (A.image Finset.univ w₁ ∩ C₂).card ≤ 1 := by
  dsimp only
  set U₁₂ := C₁.filter (fun x => A.step x b ∈ C₂)
  set D₂ := C₂.filter (fun x => A.step x b ∈ C₂)
  set r := D₂.card
  set m₂ := C₂.card
  have hC₁_iter : ∀ (k : ℕ) (q : Q), q ∈ C₁ → (fun x => A.step x a)^[k] q ∈ C₁ := by
    intro k
    induction k with
    | zero => intro q hq; exact hq
    | succ k ih => intro q hq; rw [Function.iterate_succ_apply']; exact hC₁_inv _ (ih q hq)
  have hcount_C₂ := (PartialDrainExact.cycle_period_props A a C₂ hC₂_inv hC₂_trans).2.2.2.2
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
  -- Single Markov short-shift halving step: `∃ j ≤ 2r` dropping `s - 1` to `≤ (s - 1) / 2`
  have hhalve : ∀ w : List α, 2 ≤ (A.image Finset.univ w ∩ C₂).card →
      ∃ j : Fin m₂, j.val ≤ 2 * r ∧
        (A.image Finset.univ (w ++ List.replicate j.val a ++ [b]) ∩ C₂).card - 1 ≤
          ((A.image Finset.univ w ∩ C₂).card - 1) / 2 := by
    intro w hs_ge2
    set T := A.image Finset.univ w ∩ C₂
    set s := T.card
    set k := (s - 1) / 2
    let h : Fin m₂ → ℕ := fun j => (T.filter (fun x => (fun y => A.step y a)^[j.val] x ∈ D₂)).card
    -- Upper bound `|(Q · w a^j b) ∩ C₂| ≤ 1 + h j`
    have hbound_j : ∀ j : Fin m₂,
        (A.image Finset.univ (w ++ List.replicate j.val a ++ [b]) ∩ C₂).card ≤ 1 + h j := by
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
            · exfalso; exact Finset.disjoint_left.mp hC_disj (hC₁_iter j.val x hx1) hz2
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
    -- Exact sum `∑ j, h j = s * r`
    have hsum_sr : ∑ j : Fin m₂, h j = s * r := by
      have hcard_j : ∀ j : Fin m₂,
          h j = ∑ x ∈ T, if (fun y => A.step y a)^[j.val] x ∈ D₂ then 1 else 0 := by
        intro j
        dsimp only [h]
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      simp_rw [hcard_j]
      rw [Finset.sum_comm]
      have hinner : ∀ x ∈ T,
          (∑ j : Fin m₂, if (fun y => A.step y a)^[j.val] x ∈ D₂ then 1 else 0) = r := by
        intro x hx
        have hc := hcount_C₂ x (Finset.mem_inter.mp hx).2 D₂
        have hD₂C₂ : D₂ ∩ C₂ = D₂ := Finset.inter_eq_left.mpr (Finset.filter_subset _ C₂)
        rwa [hD₂C₂] at hc
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
    -- Markov bound on bad shifts `B = {j : k + 1 ≤ h j}`: `B.card ≤ 2 * r`
    let B : Finset (Fin m₂) := Finset.univ.filter (fun j => k + 1 ≤ h j)
    have hB_le : B.card ≤ 2 * r := by
      have hmarkov : B.card * (k + 1) ≤ (2 * r) * (k + 1) := by
        calc B.card * (k + 1)
            = ∑ _j ∈ B, (k + 1) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ j ∈ B, h j := Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2
          _ ≤ ∑ j : Fin m₂, h j :=
              Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
          _ = s * r := hsum_sr
          _ ≤ (2 * (k + 1)) * r := Nat.mul_le_mul_right r (by omega)
          _ = (2 * r) * (k + 1) := by ring
      exact Nat.le_of_mul_le_mul_right hmarkov (Nat.succ_pos k)
    -- Pigeonhole on `Small = {j : Fin m₂ | j.val ≤ 2 * r}` of card `2 * r + 1 > B.card`
    let Small : Finset (Fin m₂) := Finset.univ.filter (fun j => j.val ≤ 2 * r)
    have hSmall_ge : 2 * r + 1 ≤ Small.card := by
      have hinj : Function.Injective (fun i : Fin (2 * r + 1) =>
          (⟨i.val, by omega⟩ : Fin m₂)) := fun i₁ i₂ heq => by
        dsimp only at heq
        exact Fin.ext (congrArg (Fin.val : Fin m₂ → ℕ) heq)
      have hsub : (Finset.univ : Finset (Fin (2 * r + 1))).image
          (fun i => (⟨i.val, by omega⟩ : Fin m₂)) ⊆ Small := by
        intro j hj
        rcases Finset.mem_image.mp hj with ⟨i, _, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
      exact hcard
    have hex_good : ∃ j ∈ Small, j ∉ B := by
      by_contra hall
      push Not at hall
      have hle := Finset.card_le_card hall
      omega
    rcases hex_good with ⟨j, hjSmall, hjnotB⟩
    have hj_le : j.val ≤ 2 * r := (Finset.mem_filter.mp hjSmall).2
    have hhj_le : h j ≤ k := by
      have : ¬ (k + 1 ≤ h j) := fun hge => hjnotB (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hge⟩)
      omega
    have hbj := hbound_j j
    exact ⟨j, hj_le, by omega⟩
  -- Induction on `t`: if `|T| - 1 < 2^t`, reaches `|T| ≤ 1` in `≤ t * (2 * r + 1)` extra letters
  have hind : ∀ t : ℕ, ∀ w : List α, (A.image Finset.univ w ∩ C₂).card - 1 < 2 ^ t →
      ∃ w' : List α, w'.length ≤ w.length + t * (2 * r + 1) ∧
        (A.image Finset.univ w' ∩ C₂).card ≤ 1 := by
    intro t
    induction t with
    | zero =>
      intro w hlt
      exact ⟨w, by simp, by omega⟩
    | succ t ih =>
      intro w hlt
      by_cases hle1 : (A.image Finset.univ w ∩ C₂).card ≤ 1
      · exact ⟨w, by omega, hle1⟩
      · obtain ⟨j, hj_le, hdrop⟩ := hhalve w (by omega)
        set w_next := w ++ List.replicate j.val a ++ [b]
        have hlt_next : (A.image Finset.univ w_next ∩ C₂).card - 1 < 2 ^ t := by
          have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
          omega
        obtain ⟨w', hw'_len, hw'_card⟩ := ih w_next hlt_next
        refine ⟨w', ?_, hw'_card⟩
        have hstep_len : w_next.length ≤ w.length + (2 * r + 1) := by
          dsimp only [w_next]
          rw [List.length_append, List.length_append, List.length_replicate, List.length_singleton]
          omega
        have hmul : (t + 1) * (2 * r + 1) = (2 * r + 1) + t * (2 * r + 1) := by ring
        omega
  have hlt_pow : (A.image Finset.univ [b] ∩ C₂).card - 1 < 2 ^ (Nat.log 2 r + 1) := by
    have h1 : r < 2 ^ (Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self (by omega) r
    omega
  obtain ⟨w₁, hw₁_len, hw₁_card⟩ := hind (Nat.log 2 r + 1) [b] hlt_pow
  rw [List.length_singleton] at hw₁_len
  have hlog_le := PartialDrainExact.log2_succ_le r hr_pos
  have hmul_le : (Nat.log 2 r + 1) * (2 * r + 1) ≤ r * (2 * r + 1) :=
    Nat.mul_le_mul_right (2 * r + 1) hlog_le
  exact ⟨w₁, hw₁_len, by omega, hw₁_card⟩

/-! ### Section 2: Theorem F_part_exact — 100% Exact Černý `(n - 1)^2` for ALL `2 r m₁ < m₂`! -/

/-- **Short Collapse Word via `Lemma F_exp` + `szykula_avoiding_lemma` + `optimal_twoCluster_avg`**:
Produces `w₀` with `Q · w₀ ⊆ C₁` and
`w₀.length ≤ (Nat.log 2 r + 1) * (2 * r + 1) + m₂ + n ≤ r * (2 * r + 1) + m₂ + n`. -/
theorem partialDrain_exp_collapseWord {Q : Type u} {α : Type v}
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
    let r := (C₂.filter (fun x => A.step x b ∈ C₂)).card
    ∃ w₀ : List α,
      w₀.length ≤ (Nat.log 2 r + 1) * (2 * r + 1) + C₂.card + Fintype.card Q ∧
      w₀.length ≤ r * (2 * r + 1) + C₂.card + Fintype.card Q ∧
      ∀ q : Q, A.eval q w₀ ∈ C₁ := by
  dsimp only
  set U₁₂ := C₁.filter (fun x => A.step x b ∈ C₂)
  set D₂ := C₂.filter (fun x => A.step x b ∈ C₂)
  set r := D₂.card
  set m₁ := C₁.card
  set m₂ := C₂.card
  set n := Fintype.card Q
  set L_exp := (Nat.log 2 r + 1) * (2 * r + 1)
  have hL_le : L_exp ≤ r * (2 * r + 1) :=
    Nat.mul_le_mul_right (2 * r + 1) (PartialDrainExact.log2_succ_le r hr_pos)
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
  have h2r : 2 * r < m₂ := by nlinarith
  obtain ⟨w₁, hw₁_len_raw, _, hw₁_card⟩ :=
    shortShift_exp_halving A a b C₁ C₂ hC_disj hC_union hC₁_inv hC₂_inv hC₂_trans hk₁₂ hr_pos h2r
  have hw₁_len : w₁.length ≤ 1 + L_exp := hw₁_len_raw
  set S := A.image Finset.univ w₁
  have hS_le : S.card ≤ m₁ + 1 := by
    have h1 := hsplit_card S
    have h2 : (S ∩ C₁).card ≤ m₁ := Finset.card_le_card Finset.inter_subset_right
    omega
  -- Helper: given `v` with `|v| ≤ 1 + L_exp + m₂`, `|Q · v| ≤ m₁ + 1`, `¬ C₁ ⊆ Q · v`,
  -- Lemma G.1 (`optimal_twoCluster_avg`) yields `w₀` of length `≤ L_exp + m₂ + n`!
  have hfinish : ∀ v : List α, v.length ≤ 1 + L_exp + m₂ →
      (A.image Finset.univ v).card ≤ m₁ + 1 → ¬ (C₁ ⊆ A.image Finset.univ v) →
      ∃ w₀ : List α, w₀.length ≤ L_exp + m₂ + n ∧ w₀.length ≤ r * (2 * r + 1) + m₂ + n ∧
        ∀ q : Q, A.eval q w₀ ∈ C₁ := by
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
    let D : TwoClusterData A :=
      { a := a, C₁ := C₁, C₂ := C₂, B₁ := C₁, B₂ := C₂, ℓ := 0
        hC₁_ne := Finset.card_pos.mp (by omega), hC₂_ne := Finset.card_pos.mp (by omega)
        hC_disj := hC_disj, hB_disj := hC_disj, hB_union := hC_union
        hC₁_inv := hC₁_inv, hC₁_trans := hC₁_trans, hC₂_inv := hC₂_inv, hC₂_trans := hC₂_trans
        hB₁_enter := fun _ h => h, hB₂_enter := fun _ h => h, hℓ_le := by omega }
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
      ext z; simp only [Bad, U₁₂, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    have hBad_C₂ : Bad ∩ C₂ = D₂ := by
      ext z; simp only [Bad, D₂, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
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
      trans ∑ p ∈ S', ∑ z ∈ Bad, (∑ idx : ι, if A.eval p (word idx) = z then μ else 0)
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
              hBad_C₁, Finset.sum_const, nsmul_eq_mul]; ring
          · simp only [hp1, ↓reduceIte, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
              hBad_C₂, Finset.sum_const, nsmul_eq_mul]; ring
        rw [Finset.sum_congr rfl hinner, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
          nsmul_eq_mul, nsmul_eq_mul]
        have hf1 : S'.filter (fun p => p ∈ C₁) = S' ∩ C₁ := Finset.filter_mem_eq_inter
        have hf2 : S'.filter (fun p => p ∉ C₁) = S' ∩ C₂ := by
          ext p; simp only [Finset.mem_filter, Finset.mem_inter, and_congr_right_iff]; intro _
          constructor
          · intro hnot1
            have huniv : p ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ p
            exact (Finset.mem_union.mp huniv).resolve_left hnot1
          · intro hp2 hp1; exact Finset.disjoint_left.mp hC_disj hp1 hp2
        rw [hf1, hf2]
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
    have hμ_sum : ∑ _idx : ι, μ = 1 := by
      dsimp only [ι, μ]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul]
      rw [Nat.cast_mul m₁ q₂]
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
    refine ⟨v ++ word idx ++ [b], ?_, ?_, ?_⟩
    · rw [List.length_append, List.length_append, List.length_singleton]
      have hwl : (word idx).length ≤ 0 + (m₁ + m₂ - g - 1) := hword_len idx
      omega
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
  by_cases hC₁S : C₁ ⊆ S
  · by_cases hSC₁ : S ⊆ C₁
    · exact ⟨w₁, by omega, by omega,
        fun q => hSC₁ ((DFA.mem_image A Finset.univ w₁ _).mpr ⟨q, Finset.mem_univ q, rfl⟩)⟩
    · have hC₁_ne : C₁.Nonempty := Finset.card_pos.mp (by omega)
      have hC₁_ne_univ : C₁ ≠ Finset.univ := by
        intro huniv; have := congrArg Finset.card huniv; rw [Finset.card_univ] at this; omega
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
      have hv_len : (w₁ ++ u).length ≤ 1 + L_exp + m₂ := by rw [List.length_append]; omega
      have himg_eq : A.image Finset.univ (w₁ ++ u) = A.image S u := DFA.image_append A Finset.univ w₁ u
      rcases hu_prop with hnot_sub | hlt_card
      · exact hfinish (w₁ ++ u) hv_len
          (by rw [himg_eq]; exact (DFA.card_image_le A S u).trans hS_le)
          (by rw [himg_eq]; exact hnot_sub)
      · by_cases hC₁Su : C₁ ⊆ A.image S u
        · have heq : A.image S u = C₁ := (Finset.eq_of_subset_of_card_le hC₁Su (by omega)).symm
          refine ⟨w₁ ++ u, by omega, by omega, fun q => ?_⟩
          have hmem : A.eval q (w₁ ++ u) ∈ A.image Finset.univ (w₁ ++ u) :=
            (DFA.mem_image A Finset.univ (w₁ ++ u) _).mpr ⟨q, Finset.mem_univ q, rfl⟩
          rwa [himg_eq, heq] at hmem
        · exact hfinish (w₁ ++ u) hv_len
            (by rw [himg_eq]; exact (DFA.card_image_le A S u).trans hS_le)
            (by rw [himg_eq]; exact hC₁Su)
  · exact hfinish w₁ (by omega) hS_le hC₁S

/-- **Theorem F_part_exact (100% Exact Černý Conjecture `(n - 1)^2` for ALL `r ≥ 1, 2 r m₁ < m₂`)**:
Closes Round 4's sole gap (`r = 1, 2 m₁ < m₂ ≤ 4 m₁`) with ZERO exceptions! Every synchronizing
2-cycle permutation DFA (`m₁, m₂ ≥ 2`, NO strong connectivity!) with `k₁₂(b) ≤ 1`, `r ≥ 1`, and
`2 * r * m₁ < m₂` satisfies `∃ w, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2`! -/
theorem partialDrain_all_exact_cerny {Q : Type u} {α : Type v}
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
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have hn_eq : Fintype.card Q = C₁.card + C₂.card := by
    rw [← Finset.card_univ, ← hC_union, Finset.card_union_of_disjoint hC_disj]
  set r := (C₂.filter (fun x => A.step x b ∈ C₂)).card
  obtain ⟨w₀, _, hw₀_len, hw₀_in⟩ :=
    partialDrain_exp_collapseWord A hSync a b C₁ C₂ hm₁ hm₂ hC_disj hC_union
      hC₁_inv hC₁_trans hC₂_inv hC₂_trans hk₁₂ hr_pos hcond
  obtain ⟨w, hw_sync, hw_len⟩ :=
    shortCollapse_cycle_reset_bound A hSync a C₁ hm₁ hC₁_inv hC₁_trans w₀
      (r * (2 * r + 1) + C₂.card + Fintype.card Q) hw₀_len hw₀_in
  exact ⟨w, hw_sync,
    PartialDrainExact.arith_exact_all_r (Fintype.card Q) C₁.card C₂.card r w.length
      hm₁ hr_pos hn_eq hcond hw_len⟩

/-! ### Section 3: Theorem F_gcd — Small-`gcd` Partial Cycle-Drain (Removing `m₁`!) -/

/-- **Theorem F_gcd(1) (Zero-Linear-Algebra Small-`gcd` Collapse Word)**:
Whenever `2 * r * gcd(m₁, m₂) < m₂` (NO upper bound on `m₁`!), `k₁₂(b) ≤ 1`, and `r ≥ 1`,
there exists a collapse word `w₀` with `∀ q, A.eval q w₀ ∈ C₁` and
`w₀.length ≤ 1 + (Nat.log 2 r + 1) * (2 * r + 1) + m₂ + (2 * r + 1) * m₁`. -/
theorem smallGcd_collapseWord {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (a b : α) (C₁ C₂ : Finset Q)
    (hm₁ : 2 ≤ C₁.card)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hr_pos : 1 ≤ (C₂.filter (fun x => A.step x b ∈ C₂)).card)
    (hgcd_cond : 2 * (C₂.filter (fun x => A.step x b ∈ C₂)).card * Nat.gcd C₁.card C₂.card < C₂.card) :
    let r := (C₂.filter (fun x => A.step x b ∈ C₂)).card
    ∃ w₀ : List α,
      w₀.length ≤ 1 + (Nat.log 2 r + 1) * (2 * r + 1) + C₂.card + (2 * r + 1) * C₁.card ∧
      ∀ q : Q, A.eval q w₀ ∈ C₁ := by
  dsimp only
  set U₁₂ := C₁.filter (fun x => A.step x b ∈ C₂)
  set D₂ := C₂.filter (fun x => A.step x b ∈ C₂)
  set r := D₂.card
  set m₁ := C₁.card
  set m₂ := C₂.card
  set g := Nat.gcd m₁ m₂
  set q₁ := m₁ / g
  set q₂ := m₂ / g
  set L_exp := (Nat.log 2 r + 1) * (2 * r + 1)
  have hm₁_pos : 0 < m₁ := by omega
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left m₂ hm₁_pos
  have hq₁_mul : q₁ * g = m₁ := Nat.div_mul_cancel (Nat.gcd_dvd_left m₁ m₂)
  have hq₂_mul : q₂ * g = m₂ := Nat.div_mul_cancel (Nat.gcd_dvd_right m₁ m₂)
  have h2r_lt_q₂ : 2 * r < q₂ := by
    have : (2 * r) * g < q₂ * g := by simpa [hq₂_mul] using hgcd_cond
    exact Nat.lt_of_mul_lt_mul_right this
  have h2r_lt_m₂ : 2 * r < m₂ := by nlinarith
  have hC₁_props := PartialDrainExact.cycle_period_props A a C₁ hC₁_inv hC₁_trans
  have hC₂_props := PartialDrainExact.cycle_period_props A a C₂ hC₂_inv hC₂_trans
  have hC₁_iter := hC₁_props.1
  have hC₁_inj := hC₁_props.2.1
  have hC₁_period := hC₁_props.2.2.1
  have hC₂_iter := hC₂_props.1
  have hC₂_inj := hC₂_props.2.1
  have hC₂_dvd := hC₂_props.2.2.2.1
  -- Key AP distinctness on `C₂`: for any `y ∈ C₂` and `e₁`, `t ↦ y · a^(e₁ + t * m₁)` is injective on `Fin (2*r + 1)`
  have hap_inj : ∀ y ∈ C₂, ∀ e₁ : ℕ,
      Function.Injective (fun t : Fin (2 * r + 1) =>
        (fun x => A.step x a)^[e₁ + t.val * m₁] y) := by
    intro y hy e₁ t₁ t₂ heq
    dsimp only at heq
    by_contra hne
    have hstep_absurd : ∀ a₁ a₂ : ℕ, a₁ < a₂ → a₂ < 2 * r + 1 →
        (fun x => A.step x a)^[e₁ + a₁ * m₁] y = (fun x => A.step x a)^[e₁ + a₂ * m₁] y → False := by
      intro a₁ a₂ hlt ha₂ heq'
      have hsplit : e₁ + a₂ * m₁ = (e₁ + a₁ * m₁) + (a₂ - a₁) * m₁ := by
        have : a₂ = a₁ + (a₂ - a₁) := by omega
        calc e₁ + a₂ * m₁ = e₁ + (a₁ + (a₂ - a₁)) * m₁ := by rw [← this]
          _ = (e₁ + a₁ * m₁) + (a₂ - a₁) * m₁ := by ring
      conv_rhs at heq' => rw [hsplit, Function.iterate_add_apply]
      -- Iterated `step · a` is injective on `C₂`
      have hinj_iter : ∀ k : ℕ, Set.InjOn ((fun x => A.step x a)^[k]) (C₂ : Set Q) := by
        intro k
        induction k with
        | zero => intro p _ q _ h; exact h
        | succ k ih =>
          intro p hp q hq h
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
          exact ih hp hq (hC₂_inj (hC₂_iter k p hp) (hC₂_iter k q hq) h)
      have hfix : (fun x => A.step x a)^[(a₂ - a₁) * m₁] y = y :=
        (hinj_iter (e₁ + a₁ * m₁) (hC₂_iter _ y hy) hy heq'.symm)
      have hdvd_m₂ : m₂ ∣ (a₂ - a₁) * m₁ := (hC₂_dvd y hy ((a₂ - a₁) * m₁)).mp hfix
      have hdvd_q₂ : q₂ ∣ (a₂ - a₁) * q₁ := by
        rcases hdvd_m₂ with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        have h1 : ((a₂ - a₁) * q₁) * g = (q₂ * c) * g := by
          calc ((a₂ - a₁) * q₁) * g = (a₂ - a₁) * (q₁ * g) := by ring
            _ = (a₂ - a₁) * m₁ := by rw [hq₁_mul]
            _ = m₂ * c := hc
            _ = (q₂ * g) * c := by rw [hq₂_mul]
            _ = (q₂ * c) * g := by ring
        exact Nat.eq_of_mul_eq_mul_right hg_pos h1
      have hcop : Nat.Coprime q₂ q₁ := (Nat.coprime_div_gcd_div_gcd hg_pos).symm
      have hdvd_diff : q₂ ∣ (a₂ - a₁) := hcop.dvd_of_dvd_mul_right hdvd_q₂
      have hle := Nat.le_of_dvd (by omega) hdvd_diff
      omega
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hstep_absurd t₁.val t₂.val hlt t₂.isLt heq
    · exact hstep_absurd t₂.val t₁.val hgt t₁.isLt heq.symm
  -- Unified clearance lemma for any `S'` missing a state `v₀ ∈ C₁` with `|S' ∩ C₂| ≤ 2` and `U₁₂ = {u₀}`
  have hclear : ∀ (S' : Finset Q) (u₀ : Q), U₁₂ = {u₀} → u₀ ∈ C₁ →
      (∃ v₀ ∈ C₁, v₀ ∉ S') → (S' ∩ C₂).card ≤ 2 →
      ∃ e : ℕ, e + 1 ≤ (2 * r + 1) * m₁ ∧
        ∀ q ∈ S', A.eval q (List.replicate e a ++ [b]) ∈ C₁ := by
    intro S' u₀ hU_eq hu₀ ⟨v₀, hv₀C₁, hv₀notS'⟩ hS'C₂_le
    obtain ⟨k₀, hk₀⟩ := hC₁_trans v₀ hv₀C₁ u₀ hu₀
    set e₁ := k₀ % m₁
    have he₁_lt : e₁ < m₁ := Nat.mod_lt k₀ hm₁_pos
    have hv₀_e₁ : (fun x => A.step x a)^[e₁] v₀ = u₀ := by
      have hmul : ∀ t : ℕ, (fun x => A.step x a)^[m₁ * t] v₀ = v₀ := by
        intro t
        induction t with
        | zero => simp
        | succ t ih => rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hC₁_period v₀ hv₀C₁]
      have hdiv : k₀ = e₁ + m₁ * (k₀ / m₁) := by have := Nat.div_add_mod k₀ m₁; omega
      rw [hdiv, Function.iterate_add_apply, hmul] at hk₀
      exact hk₀
    have hv₀_t : ∀ t : ℕ, (fun x => A.step x a)^[e₁ + t * m₁] v₀ = u₀ := by
      intro t
      have hmul : (fun x => A.step x a)^[t * m₁] v₀ = v₀ := by
        induction t with
        | zero => simp
        | succ t ih =>
          rw [Nat.succ_mul, Function.iterate_add_apply, hC₁_period v₀ hv₀C₁, ih]
      rw [Function.iterate_add_apply, hmul, hv₀_e₁]
    have hinj_C₁_iter : ∀ k : ℕ, Set.InjOn ((fun x => A.step x a)^[k]) (C₁ : Set Q) := by
      intro k
      induction k with
      | zero => intro p _ q _ h; exact h
      | succ k ih =>
        intro p hp q hq h
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
        exact ih hp hq (hC₁_inj (hC₁_iter k p hp) (hC₁_iter k q hq) h)
    -- Union bound over `y ∈ S' ∩ C₂` (`≤ 2` states, each hits `D₂` at `≤ r` values of `t : Fin (2*r + 1)`)
    let BadOf : Q → Finset (Fin (2 * r + 1)) := fun y =>
      Finset.univ.filter (fun t => (fun x => A.step x a)^[e₁ + t.val * m₁] y ∈ D₂)
    have hBad_card : ∀ y ∈ S' ∩ C₂, (BadOf y).card ≤ r := by
      intro y hy
      have hyC₂ : y ∈ C₂ := (Finset.mem_inter.mp hy).2
      refine Finset.card_le_card_of_injOn
        (fun t : Fin (2 * r + 1) => (fun x => A.step x a)^[e₁ + t.val * m₁] y) ?_ ?_
      · intro t ht; exact (Finset.mem_filter.mp ht).2
      · intro t₁ _ t₂ _ heq; exact hap_inj y hyC₂ e₁ heq
    let BadAll : Finset (Fin (2 * r + 1)) := (S' ∩ C₂).biUnion BadOf
    have hBadAll_le : BadAll.card ≤ 2 * r := by
      calc BadAll.card
          ≤ ∑ y ∈ S' ∩ C₂, (BadOf y).card := Finset.card_biUnion_le
        _ ≤ ∑ _y ∈ S' ∩ C₂, r := Finset.sum_le_sum hBad_card
        _ = (S' ∩ C₂).card * r := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 2 * r := Nat.mul_le_mul_right r hS'C₂_le
    have hex_t : ∃ t : Fin (2 * r + 1), t ∉ BadAll := by
      by_contra hall; push Not at hall
      have hsub : (Finset.univ : Finset (Fin (2 * r + 1))) ⊆ BadAll := fun t _ => hall t
      have hle := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at hle
      omega
    obtain ⟨t, ht_good⟩ := hex_t
    refine ⟨e₁ + t.val * m₁, ?_, ?_⟩
    · have ht_le : t.val ≤ 2 * r := by omega
      have hmul : t.val * m₁ ≤ (2 * r) * m₁ := Nat.mul_le_mul_right m₁ ht_le
      have hexp : (2 * r + 1) * m₁ = m₁ + (2 * r) * m₁ := by ring
      omega
    · intro q hqS'
      rw [DFA.eval_append, DFA.eval_replicate, DFA.eval_singleton]
      have hq_mem : q ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ q
      rcases Finset.mem_union.mp hq_mem with hq1 | hq2
      · have hne_u₀ : (fun x => A.step x a)^[e₁ + t.val * m₁] q ≠ u₀ := by
          intro heq
          have hqv₀ : q = v₀ := hinj_C₁_iter _ hq1 hv₀C₁ (heq.trans (hv₀_t t.val).symm)
          exact hv₀notS' (hqv₀ ▸ hqS')
        have hnotC₂ : A.step ((fun x => A.step x a)^[e₁ + t.val * m₁] q) b ∉ C₂ := by
          intro h2
          have hmemU : (fun x => A.step x a)^[e₁ + t.val * m₁] q ∈ U₁₂ :=
            Finset.mem_filter.mpr ⟨hC₁_iter _ q hq1, h2⟩
          rw [hU_eq, Finset.mem_singleton] at hmemU
          exact hne_u₀ hmemU
        have huniv : A.step ((fun x => A.step x a)^[e₁ + t.val * m₁] q) b ∈ C₁ ∪ C₂ := by
          rw [hC_union]; exact Finset.mem_univ _
        exact (Finset.mem_union.mp huniv).resolve_right hnotC₂
      · have hqS'C₂ : q ∈ S' ∩ C₂ := Finset.mem_inter.mpr ⟨hqS', hq2⟩
        have hnotD₂ : (fun x => A.step x a)^[e₁ + t.val * m₁] q ∉ D₂ := by
          intro hD
          apply ht_good
          exact Finset.mem_biUnion.mpr ⟨q, hqS'C₂, Finset.mem_filter.mpr ⟨Finset.mem_univ t, hD⟩⟩
        have hnotC₂ : A.step ((fun x => A.step x a)^[e₁ + t.val * m₁] q) b ∉ C₂ := fun h2 =>
          hnotD₂ (Finset.mem_filter.mpr ⟨hC₂_iter _ q hq2, h2⟩)
        have huniv : A.step ((fun x => A.step x a)^[e₁ + t.val * m₁] q) b ∈ C₁ ∪ C₂ := by
          rw [hC_union]; exact Finset.mem_univ _
        exact (Finset.mem_union.mp huniv).resolve_right hnotC₂
  -- Step 1: `shortShift_exp_halving` gives `w₁` of length `≤ 1 + L_exp` with `|S ∩ C₂| ≤ 1`
  obtain ⟨w₁, hw₁_len_raw, _, hw₁_card⟩ :=
    shortShift_exp_halving A a b C₁ C₂ hC_disj hC_union hC₁_inv hC₂_inv hC₂_trans hk₁₂ hr_pos h2r_lt_m₂
  have hw₁_len : w₁.length ≤ 1 + L_exp := hw₁_len_raw
  set S := A.image Finset.univ w₁
  by_cases hSC₂_empty : (S ∩ C₂).card = 0
  · refine ⟨w₁, by omega, fun q => ?_⟩
    have hqS : A.eval q w₁ ∈ S := (DFA.mem_image A Finset.univ w₁ _).mpr ⟨q, Finset.mem_univ q, rfl⟩
    have hnot2 : A.eval q w₁ ∉ C₂ := by
      intro h2
      have hpos := Finset.card_pos.mpr ⟨A.eval q w₁, Finset.mem_inter.mpr ⟨hqS, h2⟩⟩
      omega
    have huniv : A.eval q w₁ ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ _
    exact (Finset.mem_union.mp huniv).resolve_right hnot2
  · have hSC₂_eq1 : (S ∩ C₂).card = 1 := by omega
    obtain ⟨z, hz_eq⟩ := Finset.card_eq_one.mp hSC₂_eq1
    have hzS : z ∈ S := (Finset.mem_inter.mp (hz_eq ▸ Finset.mem_singleton_self z)).1
    have hzC₂ : z ∈ C₂ := (Finset.mem_inter.mp (hz_eq ▸ Finset.mem_singleton_self z)).2
    by_cases hU0 : U₁₂.card = 0
    · -- `k₁₂ = 0`: rotate `z` to any `x ∈ C₂ \ D₂` in `≤ m₂ - 1` steps and apply `b`!
      have hex_k21 : ∃ x ∈ C₂, x ∉ D₂ := by
        by_contra hall; push Not at hall
        have hle := Finset.card_le_card hall
        omega
      obtain ⟨x, hxC₂, hxnotD₂⟩ := hex_k21
      obtain ⟨k₀, hk₀⟩ := hC₂_trans z hzC₂ x hxC₂
      set j := k₀ % m₂
      have hj_lt : j < m₂ := Nat.mod_lt k₀ (by omega)
      have hzj : (fun y => A.step y a)^[j] z = x := by
        have hper := hC₂_props.2.2.1 z hzC₂
        have hmul : ∀ t : ℕ, (fun y => A.step y a)^[m₂ * t] z = z := by
          intro t; induction t with
          | zero => simp
          | succ t ih => rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hper]
        have hdiv : k₀ = j + m₂ * (k₀ / m₂) := by have := Nat.div_add_mod k₀ m₂; omega
        rw [hdiv, Function.iterate_add_apply, hmul] at hk₀
        exact hk₀
      refine ⟨w₁ ++ List.replicate j a ++ [b], ?_, ?_⟩
      · rw [List.length_append, List.length_append, List.length_replicate, List.length_singleton]
        omega
      · intro q
        rw [DFA.eval_append, DFA.eval_append, DFA.eval_replicate, DFA.eval_singleton]
        set p := A.eval q w₁
        have hpS : p ∈ S := (DFA.mem_image A Finset.univ w₁ p).mpr ⟨q, Finset.mem_univ q, rfl⟩
        have hp_mem : p ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ p
        rcases Finset.mem_union.mp hp_mem with hp1 | hp2
        · have hnotC₂ : A.step ((fun y => A.step y a)^[j] p) b ∉ C₂ := by
            intro h2
            have hmemU : (fun y => A.step y a)^[j] p ∈ U₁₂ :=
              Finset.mem_filter.mpr ⟨hC₁_iter j p hp1, h2⟩
            have hpos := Finset.card_pos.mpr ⟨(fun y => A.step y a)^[j] p, hmemU⟩
            omega
          have huniv : A.step ((fun y => A.step y a)^[j] p) b ∈ C₁ ∪ C₂ := by
            rw [hC_union]; exact Finset.mem_univ _
          exact (Finset.mem_union.mp huniv).resolve_right hnotC₂
        · have hpz : p = z := by
            have : p ∈ S ∩ C₂ := Finset.mem_inter.mpr ⟨hpS, hp2⟩
            rwa [hz_eq, Finset.mem_singleton] at this
          rw [hpz, hzj]
          have hnotC₂ : A.step x b ∉ C₂ := fun h2 =>
            hxnotD₂ (Finset.mem_filter.mpr ⟨hxC₂, h2⟩)
          have huniv : A.step x b ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ _
          exact (Finset.mem_union.mp huniv).resolve_right hnotC₂
    · -- `k₁₂ = 1`: `U₁₂ = {u₀}`
      have hU1 : U₁₂.card = 1 := by omega
      obtain ⟨u₀, hu₀_eq⟩ := Finset.card_eq_one.mp hU1
      have hu₀C₁ : u₀ ∈ C₁ := (Finset.mem_filter.mp (hu₀_eq ▸ Finset.mem_singleton_self u₀)).1
      by_cases hC₁S : C₁ ⊆ S
      · -- **Subcase B (`C₁ ⊆ S`, unified via `@verifier` `#154` shortcut!)**:
        -- Rotate `z` to any `x₀ ∈ D₂` (`j < m₂`) and apply `b`; then `S' ∩ C₁` misses a state and `|S' ∩ C₂| ≤ 2`!
        obtain ⟨x₀, hx₀D₂⟩ := Finset.card_pos.mp hr_pos
        have hx₀C₂ : x₀ ∈ C₂ := (Finset.mem_filter.mp hx₀D₂).1
        have hx₀bC₂ : A.step x₀ b ∈ C₂ := (Finset.mem_filter.mp hx₀D₂).2
        obtain ⟨k₀, hk₀⟩ := hC₂_trans z hzC₂ x₀ hx₀C₂
        set j := k₀ % m₂
        have hj_lt : j < m₂ := Nat.mod_lt k₀ (by omega)
        have hzj : (fun y => A.step y a)^[j] z = x₀ := by
          have hper := hC₂_props.2.2.1 z hzC₂
          have hmul : ∀ t : ℕ, (fun y => A.step y a)^[m₂ * t] z = z := by
            intro t; induction t with
            | zero => simp
            | succ t ih => rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hper]
          have hdiv : k₀ = j + m₂ * (k₀ / m₂) := by have := Nat.div_add_mod k₀ m₂; omega
          rw [hdiv, Function.iterate_add_apply, hmul] at hk₀
          exact hk₀
        set v := w₁ ++ List.replicate j a ++ [b]
        set S' := A.image Finset.univ v
        -- Show `S' ∩ C₁ ⊆ (C₁.erase u₀).image (step · b)`, so `∃ v₀ ∈ C₁, v₀ ∉ S'`
        have hS'C₁_sub : S' ∩ C₁ ⊆ (C₁.erase u₀).image (fun q => A.step q b) := by
          intro y hy
          rcases Finset.mem_inter.mp hy with ⟨hyS', hyC₁⟩
          rcases (DFA.mem_image A Finset.univ v y).mp hyS' with ⟨p₀, _, hp₀⟩
          dsimp only [v] at hp₀
          rw [DFA.eval_append, DFA.eval_append, DFA.eval_replicate, DFA.eval_singleton] at hp₀
          set p := A.eval p₀ w₁
          have hpS : p ∈ S := (DFA.mem_image A Finset.univ w₁ p).mpr ⟨p₀, Finset.mem_univ p₀, rfl⟩
          have hp_mem : p ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ p
          rcases Finset.mem_union.mp hp_mem with hp1 | hp2
          · set q := (fun y => A.step y a)^[j] p
            have hqC₁ : q ∈ C₁ := hC₁_iter j p hp1
            have hq_ne : q ≠ u₀ := by
              intro hqu
              have hu₀U : u₀ ∈ U₁₂ := hu₀_eq ▸ Finset.mem_singleton_self u₀
              have hu₀b : A.step u₀ b ∈ C₂ := (Finset.mem_filter.mp hu₀U).2
              exact Finset.disjoint_left.mp hC_disj hyC₁ (hp₀ ▸ hqu ▸ hu₀b)
            exact Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨hq_ne, hqC₁⟩, hp₀⟩
          · exfalso
            have hpz : p = z := by
              have : p ∈ S ∩ C₂ := Finset.mem_inter.mpr ⟨hpS, hp2⟩
              rwa [hz_eq, Finset.mem_singleton] at this
            rw [hpz, hzj] at hp₀
            exact Finset.disjoint_left.mp hC_disj hyC₁ (hp₀ ▸ hx₀bC₂)
        have hmiss : ∃ v₀ ∈ C₁, v₀ ∉ S' := by
          by_contra hall; push Not at hall
          have hsub : C₁ ⊆ S' ∩ C₁ := fun x hx => Finset.mem_inter.mpr ⟨hall x hx, hx⟩
          have h1 := (Finset.card_le_card hsub).trans
            ((Finset.card_le_card hS'C₁_sub).trans Finset.card_image_le)
          rw [Finset.card_erase_of_mem hu₀C₁] at h1
          omega
        -- Show `S' ∩ C₂ ⊆ {A.step u₀ b, A.step x₀ b}`, so `(S' ∩ C₂).card ≤ 2`
        have hS'C₂_sub : S' ∩ C₂ ⊆ {A.step u₀ b, A.step x₀ b} := by
          intro y hy
          rcases Finset.mem_inter.mp hy with ⟨hyS', hyC₂⟩
          rcases (DFA.mem_image A Finset.univ v y).mp hyS' with ⟨p₀, _, hp₀⟩
          dsimp only [v] at hp₀
          rw [DFA.eval_append, DFA.eval_append, DFA.eval_replicate, DFA.eval_singleton] at hp₀
          set p := A.eval p₀ w₁
          have hpS : p ∈ S := (DFA.mem_image A Finset.univ w₁ p).mpr ⟨p₀, Finset.mem_univ p₀, rfl⟩
          have hp_mem : p ∈ C₁ ∪ C₂ := by rw [hC_union]; exact Finset.mem_univ p
          rcases Finset.mem_union.mp hp_mem with hp1 | hp2
          · have hmemU : (fun y => A.step y a)^[j] p ∈ U₁₂ :=
              Finset.mem_filter.mpr ⟨hC₁_iter j p hp1, hp₀ ▸ hyC₂⟩
            rw [hu₀_eq, Finset.mem_singleton] at hmemU
            rw [← hp₀, hmemU]
            exact Finset.mem_insert_self _ _
          · have hpz : p = z := by
              have : p ∈ S ∩ C₂ := Finset.mem_inter.mpr ⟨hpS, hp2⟩
              rwa [hz_eq, Finset.mem_singleton] at this
            rw [← hp₀, hpz, hzj]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have hS'C₂_le : (S' ∩ C₂).card ≤ 2 :=
          (Finset.card_le_card hS'C₂_sub).trans (Finset.card_le_two)
        obtain ⟨e, he_len, he_in⟩ := hclear S' u₀ hu₀_eq hu₀C₁ hmiss hS'C₂_le
        refine ⟨v ++ (List.replicate e a ++ [b]), ?_, ?_⟩
        · dsimp only [v]
          simp only [List.length_append, List.length_replicate, List.length_singleton]
          omega
        · intro q
          rw [DFA.eval_append]
          exact he_in (A.eval q v) ((DFA.mem_image A Finset.univ v _).mpr ⟨q, Finset.mem_univ q, rfl⟩)
      · -- **Subcase A (`¬ C₁ ⊆ S`)**: apply `hclear` directly to `S`!
        have hmiss : ∃ v₀ ∈ C₁, v₀ ∉ S := by
          by_contra hall; push Not at hall; exact hC₁S hall
        obtain ⟨e, he_len, he_in⟩ := hclear S u₀ hu₀_eq hu₀C₁ hmiss (by omega)
        refine ⟨w₁ ++ (List.replicate e a ++ [b]), ?_, ?_⟩
        · rw [List.length_append, List.length_append, List.length_replicate, List.length_singleton]
          omega
        · intro q
          rw [DFA.eval_append]
          exact he_in (A.eval q w₁) ((DFA.mem_image A Finset.univ w₁ _).mpr ⟨q, Finset.mem_univ q, rfl⟩)

/-- **Theorem F_gcd(3) (General Small-`gcd` Reset Bound via Theorem F₀)**:
For ANY `r ≥ 1` with `2 * r * gcd(m₁, m₂) < m₂` (NO `m₁` upper bound!), plugging
`smallGcd_collapseWord` into `Cerny.shortCollapse_cycle_reset_bound` gives an explicit `O(r n^2)`
reset bound (sub-cubic `O(n^{5/2})` for all `r ≤ √n`!). -/
theorem smallGcd_reset_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (a b : α) (C₁ C₂ : Finset Q)
    (hm₁ : 2 ≤ C₁.card)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hr_pos : 1 ≤ (C₂.filter (fun x => A.step x b ∈ C₂)).card)
    (hgcd_cond : 2 * (C₂.filter (fun x => A.step x b ∈ C₂)).card * Nat.gcd C₁.card C₂.card < C₂.card) :
    let r := (C₂.filter (fun x => A.step x b ∈ C₂)).card
    let L₀ := 1 + (Nat.log 2 r + 1) * (2 * r + 1) + C₂.card + (2 * r + 1) * C₁.card
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ L₀ + (C₁.card - 2) * (Fintype.card Q - 1 + L₀ + C₁.card - 1) +
        (Fintype.card Q - C₁.card + 1 + L₀) := by
  dsimp only
  obtain ⟨w₀, hw₀_len, hw₀_in⟩ :=
    smallGcd_collapseWord A a b C₁ C₂ hm₁ hC_disj hC_union hC₁_inv hC₁_trans hC₂_inv hC₂_trans
      hk₁₂ hr_pos hgcd_cond
  exact shortCollapse_cycle_reset_bound A hSync a C₁ hm₁ hC₁_inv hC₁_trans w₀ _ hw₀_len hw₀_in

/-- **Corollary F_gcd.1a (`r = 1, 2 * gcd(m₁, m₂) < m₂` — Sharp Bound)**:
`w.length ≤ 3 * m₁ ^ 2 + (2 * n - 1) * m₁ - n + 5`. -/
theorem smallGcd_r1_reset_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (a b : α) (C₁ C₂ : Finset Q)
    (hm₁ : 2 ≤ C₁.card)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hr1 : (C₂.filter (fun x => A.step x b ∈ C₂)).card = 1)
    (hgcd_cond : 2 * Nat.gcd C₁.card C₂.card < C₂.card) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 3 * C₁.card ^ 2 + (2 * Fintype.card Q - 1) * C₁.card - Fintype.card Q + 5 := by
  have hn_eq : Fintype.card Q = C₁.card + C₂.card := by
    rw [← Finset.card_univ, ← hC_union, Finset.card_union_of_disjoint hC_disj]
  have hg_pos : 0 < Nat.gcd C₁.card C₂.card := Nat.gcd_pos_of_pos_left C₂.card (by omega)
  have hm₂ : 3 ≤ C₂.card := by omega
  obtain ⟨w, hw_sync, hw_len⟩ :=
    smallGcd_reset_bound A hSync a b C₁ C₂ hm₁ hC_disj hC_union hC₁_inv hC₁_trans hC₂_inv hC₂_trans
      hk₁₂ (by omega) (by rw [hr1]; omega)
  rw [hr1] at hw_len
  exact ⟨w, hw_sync, PartialDrainExact.arith_smallGcd_r1 (Fintype.card Q) C₁.card C₂.card w.length
    hm₁ hm₂ hn_eq hw_len⟩

/-- **Corollary F_gcd.1b (`r = 1, 2 * gcd(m₁, m₂) < m₂` — Universal `< 5 (n - 1)^2`!)**:
Covers 100% of coprime `r = 1` DFAs with ARBITRARY `m₁ ≫ m₂`:
`w.length ≤ 5 * n ^ 2 + 35 - 26 * n` (which equals `5 * n ^ 2 - 26 * n + 35` for `n ≥ 6`
and the exact `30` at `n = 5`) and `w.length < 5 * (n - 1) ^ 2`! -/
theorem smallGcd_r1_five_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (a b : α) (C₁ C₂ : Finset Q)
    (hm₁ : 2 ≤ C₁.card)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hr1 : (C₂.filter (fun x => A.step x b ∈ C₂)).card = 1)
    (hgcd_cond : 2 * Nat.gcd C₁.card C₂.card < C₂.card) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 5 * Fintype.card Q ^ 2 + 35 - 26 * Fintype.card Q ∧
      w.length < 5 * (Fintype.card Q - 1) ^ 2 := by
  have hn_eq : Fintype.card Q = C₁.card + C₂.card := by
    rw [← Finset.card_univ, ← hC_union, Finset.card_union_of_disjoint hC_disj]
  have hg_pos : 0 < Nat.gcd C₁.card C₂.card := Nat.gcd_pos_of_pos_left C₂.card (by omega)
  have hm₂ : 3 ≤ C₂.card := by omega
  obtain ⟨w, hw_sync, hw_len⟩ :=
    smallGcd_r1_reset_bound A hSync a b C₁ C₂ hm₁ hC_disj hC_union hC₁_inv hC₁_trans hC₂_inv hC₂_trans
      hk₁₂ hr1 hgcd_cond
  have harith : ∀ n m₁ R : ℕ, 2 ≤ m₁ → m₁ + 3 ≤ n →
      R ≤ 3 * m₁ ^ 2 + (2 * n - 1) * m₁ - n + 5 →
      R ≤ 5 * n ^ 2 + 35 - 26 * n ∧ R < 5 * (n - 1) ^ 2 := by
    intro n m₁ R h2 h3 hR
    have h2n1 : 1 ≤ 2 * n := by omega
    have h1n : 1 ≤ n := by omega
    have hn_le : n ≤ 3 * m₁ ^ 2 + (2 * n - 1) * m₁ := by
      have : n ≤ (2 * n - 1) * 1 := by omega
      have : (2 * n - 1) * 1 ≤ (2 * n - 1) * m₁ := Nat.mul_le_mul_left _ (by omega)
      omega
    have h26 : 26 * n ≤ 5 * n ^ 2 + 35 := by
      zify; nlinarith [sq_nonneg (10 * (n : ℤ) - 26)]
    zify [h2n1, h1n, hn_le, h26] at hR ⊢
    have hm₁_ub : (m₁ : ℤ) ≤ (n : ℤ) - 3 := by omega
    have hm₁_nn : (0 : ℤ) ≤ (m₁ : ℤ) := by omega
    have hn5 : (5 : ℤ) ≤ (n : ℤ) := by omega
    have hsq : (m₁ : ℤ) ^ 2 ≤ ((n : ℤ) - 3) ^ 2 := by nlinarith only [hm₁_ub, hm₁_nn]
    have hlin : (2 * (n : ℤ) - 1) * (m₁ : ℤ) ≤ (2 * (n : ℤ) - 1) * ((n : ℤ) - 3) :=
      mul_le_mul_of_nonneg_left hm₁_ub (by omega)
    constructor <;> nlinarith only [hR, hsq, hlin, hn5]
  have ha := harith (Fintype.card Q) C₁.card w.length hm₁ (by omega) hw_len
  exact ⟨w, hw_sync, ha.1, ha.2⟩

/-- **Corollary F_gcd.1c (`r = 1, 2 * gcd(m₁, m₂) < m₂, m₁ ≤ m₂` — Strictly `< 2 (n - 1)^2`!)**:
`4 * w.length ≤ 7 * n ^ 2 - 16 * n + 25` and `w.length < 2 * (n - 1) ^ 2`! -/
theorem smallGcd_r1_le_half_bound {Q : Type u} {α : Type v}
    [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (a b : α) (C₁ C₂ : Finset Q)
    (hm₁ : 2 ≤ C₁.card) (hle : C₁.card ≤ C₂.card)
    (hC_disj : Disjoint C₁ C₂) (hC_union : C₁ ∪ C₂ = Finset.univ)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hC₂_inv : ∀ q ∈ C₂, A.step q a ∈ C₂)
    (hC₂_trans : ∀ p ∈ C₂, ∀ q ∈ C₂, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hk₁₂ : (C₁.filter (fun x => A.step x b ∈ C₂)).card ≤ 1)
    (hr1 : (C₂.filter (fun x => A.step x b ∈ C₂)).card = 1)
    (hgcd_cond : 2 * Nat.gcd C₁.card C₂.card < C₂.card) :
    ∃ w : List α, A.IsSyncWord w ∧
      4 * w.length ≤ 7 * Fintype.card Q ^ 2 - 16 * Fintype.card Q + 25 ∧
      w.length < 2 * (Fintype.card Q - 1) ^ 2 := by
  have hn_eq : Fintype.card Q = C₁.card + C₂.card := by
    rw [← Finset.card_univ, ← hC_union, Finset.card_union_of_disjoint hC_disj]
  have hg_pos : 0 < Nat.gcd C₁.card C₂.card := Nat.gcd_pos_of_pos_left C₂.card (by omega)
  have hne : C₁.card ≠ C₂.card := by
    intro heq
    rw [heq, Nat.gcd_self] at hgcd_cond
    omega
  have h2m₁ : 2 * C₁.card + 1 ≤ Fintype.card Q := by omega
  obtain ⟨w, hw_sync, hw_len⟩ :=
    smallGcd_r1_reset_bound A hSync a b C₁ C₂ hm₁ hC_disj hC_union hC₁_inv hC₁_trans hC₂_inv hC₂_trans
      hk₁₂ hr1 hgcd_cond
  have harith : ∀ n m₁ R : ℕ, 2 ≤ m₁ → 2 * m₁ + 1 ≤ n →
      R ≤ 3 * m₁ ^ 2 + (2 * n - 1) * m₁ - n + 5 →
      4 * R ≤ 7 * n ^ 2 - 16 * n + 25 ∧ R < 2 * (n - 1) ^ 2 := by
    intro n m₁ R h2 hhalf hR
    have h2n1 : 1 ≤ 2 * n := by omega
    have h1n : 1 ≤ n := by omega
    have hn_le : n ≤ 3 * m₁ ^ 2 + (2 * n - 1) * m₁ := by
      have : n ≤ (2 * n - 1) * 1 := by omega
      have : (2 * n - 1) * 1 ≤ (2 * n - 1) * m₁ := Nat.mul_le_mul_left _ (by omega)
      omega
    have h16 : 16 * n ≤ 7 * n ^ 2 := by nlinarith
    zify [h2n1, h1n, hn_le, h16] at hR ⊢
    have h2m₁_z : 2 * (m₁ : ℤ) ≤ (n : ℤ) - 1 := by omega
    have hm₁_nn : (0 : ℤ) ≤ (m₁ : ℤ) := by omega
    have hn5 : (5 : ℤ) ≤ (n : ℤ) := by omega
    have hsq : 4 * (m₁ : ℤ) ^ 2 ≤ ((n : ℤ) - 1) ^ 2 := by nlinarith only [h2m₁_z, hm₁_nn]
    have hlin : (2 * (n : ℤ) - 1) * (2 * (m₁ : ℤ)) ≤ (2 * (n : ℤ) - 1) * ((n : ℤ) - 1) :=
      mul_le_mul_of_nonneg_left h2m₁_z (by omega)
    constructor <;> nlinarith only [hR, hsq, hlin, hn5]
  have ha := harith (Fintype.card Q) C₁.card w.length hm₁ h2m₁ hw_len
  exact ⟨w, hw_sync, ha.1, ha.2⟩

end Cerny
