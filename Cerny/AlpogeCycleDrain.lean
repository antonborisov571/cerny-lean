import Cerny.Defs
import Cerny.AdditionalClasses
import Cerny.AlpogeThetaLift
import Cerny.Circular
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push

/-!
# Cycle-Drain Unbalanced Multi-Cluster DFAs (Theorems F₀ & F — Solving `KS_A_{2m-1}` to `O(n²)`)

This file formalizes Theorems F₀ and F from `docs/round3_two_cluster_and_s2.md` (§2 & §5.2),
combining Szykuła's Avoiding-Subset Lemma (`Cerny.szykula_avoiding_lemma`) with a rank-1
uniform-on-`C₁` theta lift (`Cerny.rankOne_exists_extending_word`) and a generalized
collapse-word singleton start over `ℚ` — with **ZERO strong-connectivity assumption**,
arbitrary alphabet `α`, and arbitrary cycle/tree structure on `Q \ C₁`!

## Main Results

* `Cerny.collapseWord_singleton_start` (**Lemma F.2**): Any synchronizing DFA with a word `w₀`
  (`|w₀| ≤ L₀`) collapsing `Q` into `C₁` (`|C₁| ≥ 2`) admits `q₀ ∈ C₁` and `w_init` of length
  `≤ n - |C₁| + 1 + L₀` with `|{q₀} w_init⁻¹ ∩ C₁| ≥ 2`.
* `Cerny.shortCollapse_cycle_reset_bound` (**Theorem F₀**): If `a` acts as a single `m₁`-cycle on
  `C₁` (`m₁ ≥ 2`) and `w₀` (`|w₀| ≤ L₀`) maps `Q` into `C₁`, then
  `rt(A) ≤ L₀ + (m₁ - 2) * (n - 1 + L₀ + m₁ - 1) + (n - m₁ + 1 + L₀)`.
* `Cerny.cycleDrain_exists_collapseWord` (**Lemma F.1 / Theorem F(1)**): For a tree-free `m₁`-cycle
  `C₁` (`2 ≤ m₁ < n`, `(Q \ C₁) · a ⊆ Q \ C₁`) and a draining letter `b` (`(Q \ {u₀}) · b ⊆ C₁`,
  `u₀ ∈ C₁`), there exists `w₀` of length `≤ n + 1` mapping all of `Q` into `C₁`.
* `Cerny.cycleDrain_reset_bound` (**Theorem F(2)**): `rt(A) ≤ m₁^2 + (2n - 4) * m₁ - n + 5`.
* `Cerny.cycleDrain_quadratic_bound`: `rt(A) ≤ 3n^2 - 9n + 10 < 3(n - 1)^2` for all `2 ≤ m₁ < n`.
* `Cerny.cycleDrain_ks_regime_bound`: For `2 * m₁ ≤ n + 1` (covering the entire Kisielewicz–Szykuła
  `A_{2m-1}` family), `4 * w.length ≤ 5n^2 - 6n + 13` (i.e. `w.length ≤ (5n^2 - 6n + 13) / 4`).
* `Cerny.cycleDrain_twoFifths_cerny`: **Exact Černý Conjecture `≤ (n - 1)^2`** whenever
  `5 * m₁ ≤ 2 * n`.
* `Cerny.cycleDrain_card_one_cerny` & `Cerny.cycleDrain_full_cerny`: Boundary cases `m₁ = 1`
  and `m₁ = n` also satisfy exact `(n - 1)^2`.
-/

namespace Cerny

universe u v

namespace AlpogeCycleDrain

section CycleHelpers

variable {Q : Type u} {α : Type v} [DecidableEq Q]

omit [DecidableEq Q] in
/-- Restriction of `step · a` to an `a`-invariant transitive cycle `C₁` is bijective, and iterating
`0 ≤ j < |C₁|` from any basepoint `c₀ ∈ C₁` gives a bijection `Fin C₁.card ≃ C₁`. -/
lemma cycle_step_bijective (A : DFA Q α) (a : α) (C₁ : Finset Q)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) :
    Function.Bijective (fun x : C₁ => (⟨A.step x.1 a, hC₁_inv x.1 x.2⟩ : C₁)) := by
  let f : Q → Q := fun x => A.step x a
  let fC : C₁ → C₁ := fun x => ⟨f x.1, hC₁_inv x.1 x.2⟩
  have hfC_surj : Function.Surjective fC := by
    intro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hC₁_trans (f y) (hC₁_inv y hy) y hy
    have hmem : f^[k] y ∈ C₁ := by
      clear hk
      induction k with
      | zero => exact hy
      | succ k ih => rw [Function.iterate_succ_apply']; exact hC₁_inv _ ih
    refine ⟨⟨f^[k] y, hmem⟩, Subtype.ext ?_⟩
    change f (f^[k] y) = y
    rw [← Function.iterate_succ_apply' f k y, Function.iterate_succ_apply]
    exact hk
  exact (Fintype.bijective_iff_surjective_and_card fC).mpr ⟨hfC_surj, rfl⟩

lemma cycle_iterate_bijective (A : DFA Q α) (a : α) (C₁ : Finset Q)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    {c₀ : Q} (hc₀ : c₀ ∈ C₁) :
    Function.Bijective (fun j : Fin C₁.card =>
      (⟨(fun x => A.step x a)^[j.val] c₀, by
        clear hC₁_trans
        induction j.val with
        | zero => exact hc₀
        | succ k ih => rw [Function.iterate_succ_apply']; exact hC₁_inv _ ih⟩ : C₁)) := by
  let f : Q → Q := fun x => A.step x a
  let fC : C₁ → C₁ := fun x => ⟨f x.1, hC₁_inv x.1 x.2⟩
  have hfC_inj : Function.Injective fC := (cycle_step_bijective A a C₁ hC₁_inv hC₁_trans).1
  have hfC_iter : ∀ (k : ℕ) (x : C₁), (fC^[k] x).1 = f^[k] x.1 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply, ih]; rfl
  have hmin : ∀ k : ℕ, 0 < k → k < C₁.card → f^[k] c₀ ≠ c₀ := by
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
    have hsub : C₁ ⊆ (Finset.range k).image (fun j => f^[j] c₀) := by
      intro y hy
      obtain ⟨t, rfl⟩ := hC₁_trans c₀ hc₀ y hy
      rw [Finset.mem_image]
      exact ⟨t % k, Finset.mem_range.mpr (Nat.mod_lt t hk0), (hmod t).symm⟩
    have hle := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_range] at hle
    omega
  have hg_inj : Function.Injective (fun j : Fin C₁.card =>
      (⟨f^[j.val] c₀, by
        induction j.val with
        | zero => exact hc₀
        | succ k ih => rw [Function.iterate_succ_apply']; exact hC₁_inv _ ih⟩ : C₁)) := by
    intro i j hij
    have hval : f^[i.val] c₀ = f^[j.val] c₀ := congrArg Subtype.val hij
    by_contra hne
    have hstep : ∀ x y : ℕ, x < y → y < C₁.card → f^[x] c₀ = f^[y] c₀ → False := by
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
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hg_inj, by simp⟩

lemma cycle_sum_indicator (A : DFA Q α) (a : α) (C₁ : Finset Q)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    {c₀ : Q} (hc₀ : c₀ ∈ C₁) (q : Q) :
    (∑ j : Fin C₁.card, if (fun x => A.step x a)^[j.val] c₀ = q then (1 : ℚ) else 0) =
      if q ∈ C₁ then 1 else 0 := by
  have hbij := cycle_iterate_bijective A a C₁ hC₁_inv hC₁_trans hc₀
  by_cases hqC : q ∈ C₁
  · simp only [hqC, ↓reduceIte]
    obtain ⟨j₀, hj₀⟩ := hbij.2 ⟨q, hqC⟩
    have hj₀_val : (fun x => A.step x a)^[j₀.val] c₀ = q := congrArg Subtype.val hj₀
    rw [Finset.sum_eq_single j₀]
    · simp [hj₀_val]
    · intro j _ hne
      have hval_ne : (fun x => A.step x a)^[j.val] c₀ ≠ q := by
        intro heq
        apply hne
        exact hbij.1 (Subtype.ext (heq.trans hj₀_val.symm))
      simp [hval_ne]
    · intro h; exact absurd (Finset.mem_univ j₀) h
  · simp only [hqC, ↓reduceIte]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hmem : (fun x => A.step x a)^[j.val] c₀ ∈ C₁ := by
      induction j.val with
      | zero => exact hc₀
      | succ k ih => rw [Function.iterate_succ_apply']; exact hC₁_inv _ ih
    have hne : (fun x => A.step x a)^[j.val] c₀ ≠ q := fun heq => hqC (heq ▸ hmem)
    simp [hne]

end CycleHelpers

end AlpogeCycleDrain

/-! ### Lemma F.2: Generalized Collapse-Word Singleton Start over `ℚ` -/

/-- **Lemma F.2 (Generalized Collapse-Word Singleton Start — NO Strong Connectivity!)**:
Let `A` be a synchronizing `n`-state DFA, `C₁ ⊆ Q` with `|C₁| ≥ 2`, and `w₀` a word of length
`≤ L₀` satisfying `Q · w₀ ⊆ C₁`. Then there exist `q₀ ∈ C₁` and `w_init` of length
`≤ n - |C₁| + 1 + L₀` such that `|{q₀} w_init⁻¹ ∩ C₁| ≥ 2`. -/
theorem collapseWord_singleton_start {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (C₁ : Finset Q) (hm₁ : 2 ≤ C₁.card)
    (w₀ : List α) (L₀ : ℕ) (hw₀_len : w₀.length ≤ L₀)
    (hw₀_in : ∀ q : Q, A.eval q w₀ ∈ C₁) :
    ∃ q₀ ∈ C₁, ∃ w_init : List α,
      w_init.length ≤ Fintype.card Q - C₁.card + 1 + L₀ ∧
      2 ≤ ((A.preimage {q₀} w_init) ∩ C₁).card := by
  classical
  let f : C₁ → C₁ := fun x => ⟨A.eval x.1 w₀, hw₀_in x.1⟩
  by_cases hinj : Function.Injective f
  · -- Case 2: `f : C₁ → C₁` is injective, hence bijective on finite `C₁`
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩
    have hm₁_pos : 0 < C₁.card := by omega
    have hm₁Q : (C₁.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm₁_pos)
    obtain ⟨c₀, hc₀⟩ := Finset.card_pos.mp hm₁_pos
    let zCol : Q → (Q → ℚ) := fun q p =>
      (if A.eval p w₀ = q then (1 : ℚ) else 0) - (C₁.card : ℚ)⁻¹
    let sumC : (Q → ℚ) →ₗ[ℚ] ℚ :=
      { toFun := fun v => ∑ p ∈ C₁, v p
        map_add' := fun _ _ => Finset.sum_add_distrib
        map_smul' := fun _ _ => by simp [Finset.mul_sum] }
    let HC : Submodule ℚ (Q → ℚ) := LinearMap.ker sumC
    have hsumC_pull : ∀ (u : List α) (q : Q),
        sumC (AlpogeThetaLift.pullback A u (zCol q)) =
          (((A.preimage {q} (u ++ w₀)) ∩ C₁).card : ℚ) - 1 := by
      intro u q
      simp only [sumC, AlpogeThetaLift.pullback, zCol, LinearMap.coe_mk, AddHom.coe_mk,
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hm₁Q]
      congr 1
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 2
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter, DFA.mem_preimage, Finset.mem_singleton,
        DFA.eval_append, and_comm]
    have hsum_zCol : ∑ q ∈ C₁, zCol q = 0 := by
      ext p
      simp only [Finset.sum_apply, zCol, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        mul_inv_cancel₀ hm₁Q, Pi.zero_apply]
      have h1 : (∑ q ∈ C₁, if A.eval p w₀ = q then (1 : ℚ) else 0) = 1 := by
        rw [Finset.sum_eq_single (A.eval p w₀)]
        · simp
        · intro q _ hq; simp [Ne.symm hq]
        · intro h; exact absurd (hw₀_in p) h
      rw [h1, sub_self]
    have hfinrank_HC : Module.finrank ℚ HC = Fintype.card Q - 1 := by
      have hsurj : LinearMap.range sumC = ⊤ := by
        rw [eq_top_iff]
        intro c _
        refine ⟨c • Pi.single c₀ (1 : ℚ), ?_⟩
        simp only [map_smul, sumC, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_eq_single c₀]
        · simp
        · intro p _ hp; simp [Pi.single_eq_of_ne hp]
        · intro h; exact absurd hc₀ h
      have hadd := LinearMap.finrank_range_add_finrank_ker sumC
      rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at hadd
      change Module.finrank ℚ (LinearMap.ker sumC) = Fintype.card Q - 1
      omega
    -- Ascending subspaces `Wj j = span { pullback A u (zCol q) : |u| ≤ j, q ∈ C₁ }`
    let Wj : ℕ → Submodule ℚ (Q → ℚ) := fun j =>
      Submodule.span ℚ {v | ∃ u : List α, u.length ≤ j ∧ ∃ q ∈ C₁,
        v = AlpogeThetaLift.pullback A u (zCol q)}
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
      change sumC (AlpogeThetaLift.pullback A [] (zCol q)) = 0
      rw [hsumC_pull, List.nil_append]
      obtain ⟨⟨p₀, hp₀⟩, hp₀_eq⟩ := hbij.2 ⟨q, hq⟩
      have hp₀_val : A.eval p₀ w₀ = q := congrArg Subtype.val hp₀_eq
      have hsing : (A.preimage {q} w₀) ∩ C₁ = {p₀} := by
        ext p
        simp only [Finset.mem_inter, DFA.mem_preimage, Finset.mem_singleton]
        constructor
        · rintro ⟨hpw, hpC⟩
          have hf_eq : f ⟨p, hpC⟩ = f ⟨p₀, hp₀⟩ := Subtype.ext (hpw.trans hp₀_val.symm)
          exact congrArg Subtype.val (hinj hf_eq)
        · rintro rfl
          exact ⟨hp₀_val, hp₀⟩
      rw [hsing, Finset.card_singleton]
      norm_num
    have hW0_dim : C₁.card - 1 ≤ Module.finrank ℚ (Wj 0) := by
      let C' := C₁.erase c₀
      have hC'_card : C'.card = C₁.card - 1 := Finset.card_erase_of_mem hc₀
      let bvec : C' → Wj 0 := fun q =>
        ⟨zCol q.1, Submodule.subset_span ⟨[], le_rfl, q.1, (Finset.mem_erase.mp q.2).2, rfl⟩⟩
      have hli : LinearIndependent ℚ bvec := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hfun : ∑ q : C', c q • zCol q.1 = 0 := by
          have := congrArg Subtype.val hc
          simpa [bvec] using this
        have hpre : ∀ q ∈ C₁, ∃ p ∈ C₁, A.eval p w₀ = q := by
          intro q hq
          obtain ⟨⟨p, hp⟩, hpq⟩ := hbij.2 ⟨q, hq⟩
          exact ⟨p, hp, congrArg Subtype.val hpq⟩
        obtain ⟨p₀, _, hp₀⟩ := hpre c₀ hc₀
        have hsum_c : ∑ q : C', c q = 0 := by
          have hv0 := congrFun hfun p₀
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zCol, hp₀, Pi.zero_apply] at hv0
          have hterm : ∀ q : C',
              c q * ((if c₀ = q.1 then (1 : ℚ) else 0) - (C₁.card : ℚ)⁻¹) =
                c q * -(C₁.card : ℚ)⁻¹ := by
            intro q
            have hne : c₀ ≠ q.1 := (Finset.mem_erase.mp q.2).1.symm
            simp [hne]
          simp_rw [hterm, ← Finset.sum_mul] at hv0
          exact (mul_eq_zero.mp hv0).resolve_right (neg_ne_zero.mpr (inv_ne_zero hm₁Q))
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
    -- Synchronization escapes `HC`
    have hex_not : ∃ j : ℕ, ¬ Wj j ≤ HC := by
      rcases hSync with ⟨w_sync, r₀, hr₀⟩
      refine ⟨w_sync.length, fun hle => ?_⟩
      let q₀ := A.eval r₀ w₀
      have hq₀C : q₀ ∈ C₁ := hw₀_in r₀
      have hmem : AlpogeThetaLift.pullback A w_sync (zCol q₀) ∈ HC :=
        hle (Submodule.subset_span ⟨w_sync, le_rfl, q₀, hq₀C, rfl⟩)
      change sumC (AlpogeThetaLift.pullback A w_sync (zCol q₀)) = 0 at hmem
      rw [hsumC_pull] at hmem
      have hpre_univ : A.preimage {q₀} (w_sync ++ w₀) = Finset.univ := by
        ext p
        simp only [DFA.mem_preimage, Finset.mem_univ, Finset.mem_singleton,
          DFA.eval_append, hr₀ p, q₀]
      rw [hpre_univ, Finset.univ_inter] at hmem
      have hm2Q : (2 : ℚ) ≤ (C₁.card : ℚ) := by exact_mod_cast hm₁
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
    have hstrict : ∀ j, j + 1 < j₀ → Wj j < Wj (j + 1) := by
      intro j hj
      refine lt_of_le_of_ne (hWj_mono (Nat.le_succ j)) fun heq => ?_
      have hclosed : ∀ (g : α) (v : Q → ℚ), v ∈ Wj j →
          AlpogeThetaLift.pullback A [g] v ∈ Wj j := by
        intro g v hv
        rw [heq]
        induction hv using Submodule.span_induction with
        | mem x hx =>
          rcases hx with ⟨u, hu, q, hq, rfl⟩
          rw [← AlpogeThetaLift.pullback_cons]
          exact Submodule.subset_span ⟨g :: u, by simp; omega, q, hq, rfl⟩
        | zero => simp
        | add x y _ _ hx hy => rw [map_add]; exact (Wj (j + 1)).add_mem hx hy
        | smul c x _ hx => rw [map_smul]; exact (Wj (j + 1)).smul_mem c hx
      have hall_in : ∀ (u : List α) (q : Q), q ∈ C₁ →
          AlpogeThetaLift.pullback A u (zCol q) ∈ Wj j := by
        intro u
        induction u with
        | nil => intro q hq; exact Submodule.subset_span ⟨[], Nat.zero_le j, q, hq, rfl⟩
        | cons g u ih =>
          intro q hq
          rw [AlpogeThetaLift.pullback_cons]
          exact hclosed g _ (ih q hq)
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
    have hj₀_le : j₀ ≤ Fintype.card Q - C₁.card + 1 := by
      have h1 := hchain (j₀ - 1) le_rfl
      have h2 : Module.finrank ℚ (Wj (j₀ - 1)) ≤ Module.finrank ℚ HC :=
        Submodule.finrank_mono (hj_lt_HC (j₀ - 1) (by omega))
      rw [hfinrank_HC] at h2
      have hle_univ : C₁.card ≤ Fintype.card Q := Finset.card_le_univ C₁
      omega
    have hex_nz : ∃ u : List α, u.length ≤ j₀ ∧ ∃ q' ∈ C₁,
        sumC (AlpogeThetaLift.pullback A u (zCol q')) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hj₀_spec
      rw [Submodule.span_le]
      rintro v ⟨u, hu, q, hq, rfl⟩
      exact hall u hu q hq
    rcases hex_nz with ⟨u, hu, q', hq', hnz⟩
    have hsum0 : ∑ q ∈ C₁, sumC (AlpogeThetaLift.pullback A u (zCol q)) = 0 := by
      rw [← map_sum, ← map_sum, hsum_zCol, map_zero, map_zero]
    have hex_pos : ∃ q₀ ∈ C₁, 0 < sumC (AlpogeThetaLift.pullback A u (zCol q₀)) := by
      by_contra hle
      push Not at hle
      have hall0 : ∀ q ∈ C₁, sumC (AlpogeThetaLift.pullback A u (zCol q)) = 0 := by
        have hge : ∀ q ∈ C₁, 0 ≤ -sumC (AlpogeThetaLift.pullback A u (zCol q)) :=
          fun q hq => neg_nonneg.mpr (hle q hq)
        have hneg0 : ∑ q ∈ C₁, -sumC (AlpogeThetaLift.pullback A u (zCol q)) = 0 := by
          rw [Finset.sum_neg_distrib, hsum0, neg_zero]
        intro q hq
        have := (Finset.sum_eq_zero_iff_of_nonneg hge).mp hneg0 q hq
        linarith
      exact hnz (hall0 q' hq')
    rcases hex_pos with ⟨q₀, hq₀C, hpos⟩
    rw [hsumC_pull] at hpos
    refine ⟨q₀, hq₀C, u ++ w₀, ?_, ?_⟩
    · rw [List.length_append]
      omega
    · have h1 : (1 : ℚ) < (((A.preimage {q₀} (u ++ w₀)) ∩ C₁).card : ℚ) := by linarith
      have h1' : 1 < ((A.preimage {q₀} (u ++ w₀)) ∩ C₁).card := by exact_mod_cast h1
      omega
  · -- Case 1: `f : C₁ → C₁` is not injective — `w₀` itself merges two states of `C₁`!
    unfold Function.Injective at hinj
    push Not at hinj
    rcases hinj with ⟨⟨x, hx⟩, ⟨y, hy⟩, hfeq, hne⟩
    have hev : A.eval x w₀ = A.eval y w₀ := congrArg Subtype.val hfeq
    have hxy : x ≠ y := fun h => hne (Subtype.ext h)
    let q₀ := A.eval x w₀
    refine ⟨q₀, hw₀_in x, w₀, by omega, ?_⟩
    have hsub : ({x, y} : Finset Q) ⊆ (A.preimage {q₀} w₀) ∩ C₁ := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨by simp [q₀], hx⟩
      · exact Finset.mem_inter.mpr ⟨by simp [q₀, hev], hy⟩
    have hcard := Finset.card_le_card hsub
    rwa [Finset.card_pair hxy] at hcard

/-! ### Theorem F₀: Short-Collapse Cycle Theta Lift Engine -/

/-- **Theorem F₀ (Short-Collapse Cycle Theta Lift Engine — NO Strong Connectivity!)**:
Let `A` be a synchronizing `n`-state DFA, `a` a letter acting as a single `m₁`-cycle on `C₁`
(`m₁ ≥ 2`), and `w₀` a word of length `≤ L₀` satisfying `Q · w₀ ⊆ C₁`. Then `A` admits a
synchronizing word of length at most
`L₀ + (m₁ - 2) * (n - 1 + L₀ + m₁ - 1) + (n - m₁ + 1 + L₀)`. -/
theorem shortCollapse_cycle_reset_bound {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (a : α) (C₁ : Finset Q) (hm₁ : 2 ≤ C₁.card)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (w₀ : List α) (L₀ : ℕ) (hw₀_len : w₀.length ≤ L₀)
    (hw₀_in : ∀ q : Q, A.eval q w₀ ∈ C₁) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤
        L₀ + (C₁.card - 2) * (Fintype.card Q - 1 + L₀ + C₁.card - 1) +
          (Fintype.card Q - C₁.card + 1 + L₀) := by
  have hm₁_pos : (0 : ℚ) < (C₁.card : ℚ) := by exact_mod_cast (show 0 < C₁.card by omega)
  let π : Q → ℚ := fun q => if q ∈ C₁ then (1 : ℚ) / (C₁.card : ℚ) else 0
  let μ : Fin C₁.card → ℚ := fun _ => (1 : ℚ) / (C₁.card : ℚ)
  let word : Fin C₁.card → List α := fun s => w₀ ++ List.replicate s.val a
  let L₁ : ℕ := L₀ + (C₁.card - 1)
  have hπ_nonneg : ∀ q : Q, 0 ≤ π q := fun q => by
    dsimp [π]; split_ifs
    · exact div_nonneg zero_le_one hm₁_pos.le
    · exact le_rfl
  have hπ_supp : ∀ q : Q, 0 < π q ↔ q ∈ C₁ := fun q => by
    dsimp [π]; split_ifs with hq
    · exact ⟨fun _ => hq, fun _ => div_pos zero_lt_one hm₁_pos⟩
    · exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h hq⟩
  have hπ_sum : ∑ q : Q, π q = 1 := by
    dsimp [π]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_mem_eq_inter,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one_div_cancel (ne_of_gt hm₁_pos)]
  have hμ_nonneg : ∀ i : Fin C₁.card, 0 ≤ μ i := fun _ => div_nonneg zero_le_one hm₁_pos.le
  have hμ_sum : ∑ i : Fin C₁.card, μ i = 1 := by
    simp only [μ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div_cancel (ne_of_gt hm₁_pos)]
  have hL₁ : ∀ i : Fin C₁.card, 0 < μ i → (word i).length ≤ L₁ := by
    intro i _
    simp only [word, L₁, List.length_append, List.length_replicate]
    have := i.isLt
    omega
  have hRankOne : ∀ p q : Q,
      (∑ i : Fin C₁.card, if A.eval p (word i) = q then μ i else 0) = π q := by
    intro p q
    have hfactor :
        (∑ i : Fin C₁.card, if A.eval p (word i) = q then μ i else 0) =
          ((1 : ℚ) / (C₁.card : ℚ)) *
            ∑ i : Fin C₁.card, if (fun x => A.step x a)^[i.val] (A.eval p w₀) = q then (1 : ℚ) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [word, μ, DFA.eval_append, DFA.eval_replicate]
      split_ifs <;> ring
    rw [hfactor, AlpogeCycleDrain.cycle_sum_indicator A a C₁ hC₁_inv hC₁_trans (hw₀_in p) q]
    dsimp [π]
    split_ifs <;> ring
  -- Iterative extension on `C₁` via `rankOne_exists_extending_word`
  have hex_chain : ∀ k : ℕ, ∀ S : Finset Q, S ⊆ C₁ → S.Nonempty → C₁.card - S.card ≤ k →
      ∃ X : List α, C₁ ⊆ A.preimage S X ∧ X.length ≤ k * (Fintype.card Q - 1 + L₁) := by
    intro k
    induction k with
    | zero =>
      intro S hSC _ hk
      have hcard := Finset.card_le_card hSC
      have heq := Finset.eq_of_subset_of_card_le hSC (by omega)
      exact ⟨[], by rw [DFA.preimage_nil, heq], by simp⟩
    | succ k ih =>
      intro S hSC hSne hk
      by_cases heq : S = C₁
      · exact ⟨[], by rw [DFA.preimage_nil, heq], by simp⟩
      · have hssub : S ⊂ C₁ := Finset.ssubset_iff_subset_ne.mpr ⟨hSC, heq⟩
        obtain ⟨u, hulen, hugt⟩ :=
          rankOne_exists_extending_word A hSync C₁ π μ word L₁ hπ_nonneg hπ_supp hπ_sum
            hμ_nonneg hμ_sum hL₁ hRankOne hSne hssub
        have hπS : ∑ x ∈ S, π x = (S.card : ℚ) / (C₁.card : ℚ) := by
          have : ∀ x ∈ S, π x = 1 / (C₁.card : ℚ) := fun x hx => by simp [π, hSC hx]
          rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one_div]
        have hπ_pre : ∑ q ∈ A.preimage S u, π q =
            (((A.preimage S u) ∩ C₁).card : ℚ) / (C₁.card : ℚ) := by
          dsimp [π]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_one_div, Finset.filter_mem_eq_inter]
        rw [hπS, hπ_pre, div_lt_div_iff_of_pos_right hm₁_pos] at hugt
        have hcard_gt : S.card < ((A.preimage S u) ∩ C₁).card := by exact_mod_cast hugt
        let S' := (A.preimage S u) ∩ C₁
        have hS'ne : S'.Nonempty :=
          Finset.card_pos.mp (lt_trans (Finset.card_pos.mpr hSne) hcard_gt)
        have hS'k : C₁.card - S'.card ≤ k := by dsimp only [S']; omega
        obtain ⟨X', hX'sub, hX'len⟩ := ih S' Finset.inter_subset_right hS'ne hS'k
        refine ⟨X' ++ u, ?_, ?_⟩
        · rw [DFA.preimage_append]
          exact hX'sub.trans (A.preimage_mono Finset.inter_subset_left X')
        · rw [List.length_append]
          calc X'.length + u.length
              ≤ k * (Fintype.card Q - 1 + L₁) + (Fintype.card Q - 1 + L₁) :=
                Nat.add_le_add hX'len hulen
            _ = (k + 1) * (Fintype.card Q - 1 + L₁) := by ring
  obtain ⟨q₀, hq₀C, w_init, hw_init_len, hw_init_card⟩ :=
    collapseWord_singleton_start A hSync C₁ hm₁ w₀ L₀ hw₀_len hw₀_in
  let S₀ := (A.preimage {q₀} w_init) ∩ C₁
  have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp (by dsimp only [S₀]; omega)
  have hS₀_k : C₁.card - S₀.card ≤ C₁.card - 2 := by dsimp only [S₀]; omega
  obtain ⟨X, hXsub, hXlen⟩ := hex_chain (C₁.card - 2) S₀ Finset.inter_subset_right hS₀_ne hS₀_k
  refine ⟨w₀ ++ X ++ w_init, ⟨q₀, fun q => ?_⟩, ?_⟩
  · rw [DFA.eval_append, DFA.eval_append]
    have h1 : A.eval q w₀ ∈ C₁ := hw₀_in q
    have h2 : A.eval q w₀ ∈ A.preimage S₀ X := hXsub h1
    rw [DFA.mem_preimage] at h2
    have h3 : A.eval (A.eval q w₀) X ∈ A.preimage {q₀} w_init := Finset.inter_subset_left h2
    simpa [DFA.mem_preimage] using h3
  · simp only [List.length_append]
    have hL₁_eq : Fintype.card Q - 1 + L₁ = Fintype.card Q - 1 + L₀ + C₁.card - 1 := by
      dsimp only [L₁]
      omega
    rw [hL₁_eq] at hXlen
    omega

/-! ### Lemma F.1 & Theorem F: Cycle-Drain Unbalanced Multi-Cluster DFAs -/

/-- **Lemma F.1 (Theorem F(1) — Short Collapse Word via Szykuła's Avoiding-Subset Lemma)**:
Let `A` be a synchronizing DFA with a tree-free `m₁`-cycle `C₁` of `a` (`2 ≤ m₁ < n`,
`(Q \ C₁) · a ⊆ Q \ C₁`) and a draining letter `b` sending `Q \ {u₀}` into `C₁` (`u₀ ∈ C₁`).
Then there exists a word `w₀` of length at most `n + 1` mapping every state into `C₁`. -/
theorem cycleDrain_exists_collapseWord {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (a b : α) (C₁ : Finset Q)
    (hm₁_ge : 2 ≤ C₁.card) (hm₁_lt : C₁.card < Fintype.card Q)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hTreeFree : ∀ q : Q, q ∉ C₁ → A.step q a ∉ C₁)
    (u₀ : Q) (hu₀ : u₀ ∈ C₁)
    (hDrain : ∀ q : Q, q ≠ u₀ → A.step q b ∈ C₁) :
    ∃ w₀ : List α, w₀.length ≤ Fintype.card Q + 1 ∧ ∀ q : Q, A.eval q w₀ ∈ C₁ := by
  let f : Q → Q := fun x => A.step x a
  have hTreeFree_iter : ∀ (k : ℕ) (x : Q), x ∉ C₁ → f^[k] x ∉ C₁ := by
    intro k
    induction k with
    | zero => intro x hx; exact hx
    | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hTreeFree _ (ih x hx)
  let fC : C₁ → C₁ := fun x => ⟨f x.1, hC₁_inv x.1 x.2⟩
  have hfC_inj : Function.Injective fC :=
    (AlpogeCycleDrain.cycle_step_bijective A a C₁ hC₁_inv hC₁_trans).1
  have hfC_iter : ∀ (k : ℕ) (x : C₁), (fC^[k] x).1 = f^[k] x.1 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply, ih]; rfl
  -- Key rotation observation: any `T` not containing `C₁` is drained into `C₁` in `≤ |C₁|` steps!
  have hrot : ∀ T : Finset Q, ¬ (C₁ ⊆ T) →
      ∃ r : ℕ, r < C₁.card ∧ ∀ x ∈ T, A.eval x (List.replicate r a ++ [b]) ∈ C₁ := by
    intro T hnot
    obtain ⟨z, hzC, hzNotT⟩ := Finset.not_subset.mp hnot
    have hbij := AlpogeCycleDrain.cycle_iterate_bijective A a C₁ hC₁_inv hC₁_trans hzC
    obtain ⟨r, hr⟩ := hbij.2 ⟨u₀, hu₀⟩
    have hr_val : f^[r.val] z = u₀ := congrArg Subtype.val hr
    refine ⟨r.val, r.isLt, fun x hxT => ?_⟩
    rw [DFA.eval_append, DFA.eval_replicate, DFA.eval_singleton]
    apply hDrain
    intro heq
    have hxC : x ∈ C₁ := by
      by_contra hxNot
      exact hTreeFree_iter r.val x hxNot (heq.symm ▸ hu₀)
    have hf_eq : fC^[r.val] ⟨x, hxC⟩ = fC^[r.val] ⟨z, hzC⟩ :=
      Subtype.ext (by rw [hfC_iter, hfC_iter]; exact heq.trans hr_val.symm)
    have hxz : x = z := congrArg Subtype.val ((hfC_inj.iterate r.val) hf_eq)
    exact hzNotT (hxz ▸ hxT)
  -- Set `S := Q · b` (`S ⊆ insert (u₀ · b) C₁`, so `|S| ≤ m₁ + 1`)
  let S : Finset Q := A.image Finset.univ [b]
  have hS_sub : S ⊆ insert (A.step u₀ b) C₁ := by
    intro y hy
    rw [DFA.mem_image] at hy
    rcases hy with ⟨q, _, rfl⟩
    rw [DFA.eval_singleton, Finset.mem_insert]
    by_cases hqu : q = u₀
    · left; rw [hqu]
    · right; exact hDrain q hqu
  have hS_card_le : S.card ≤ C₁.card + 1 :=
    (Finset.card_le_card hS_sub).trans (Finset.card_insert_le _ _)
  by_cases hCS : C₁ ⊆ S
  · -- Case 1b: `C₁ ⊆ S`
    by_cases hSeq : S = C₁
    · refine ⟨[b], by simp, fun q => ?_⟩
      have hmem : A.eval q [b] ∈ S := by
        rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩
      rwa [hSeq] at hmem
    · have hS_gt : C₁.card < S.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hCS, fun h => hSeq h.symm⟩)
      have hS_card : S.card = C₁.card + 1 := by omega
      have hC₁_ne : C₁.Nonempty := Finset.card_pos.mp (by omega)
      have hC₁_ne_univ : C₁ ≠ Finset.univ := by
        intro heq
        have := congrArg Finset.card heq
        rw [Finset.card_univ] at this
        omega
      have hAvoid : ∃ u : List α, ¬ (C₁ ⊆ A.image S u) := by
        rcases hSync with ⟨w_sync, qs, hqs⟩
        refine ⟨w_sync, fun hsub => ?_⟩
        have himg_sub : A.image S w_sync ⊆ {qs} := by
          intro y hy
          rw [DFA.mem_image] at hy
          rcases hy with ⟨p, _, rfl⟩
          simp [hqs p]
        have hle := (Finset.card_le_card hsub).trans (Finset.card_le_card himg_sub)
        rw [Finset.card_singleton] at hle
        omega
      obtain ⟨u, hulen, hures⟩ := szykula_avoiding_lemma A S C₁ hC₁_ne hCS hC₁_ne_univ hAvoid
      by_cases hsub : C₁ ⊆ A.image S u
      · -- `C₁ ⊆ S · u` and `|S · u| < m₁ + 1` force `S · u = C₁`!
        have hlt : (A.image S u).card < S.card := hures.resolve_left (not_not.mpr hsub)
        have heq_C₁ : A.image S u = C₁ := (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
        refine ⟨b :: u, by simp; omega, fun q => ?_⟩
        rw [← heq_C₁, DFA.eval_cons, DFA.mem_image]
        exact ⟨A.step q b, by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩, rfl⟩
      · -- `¬ (C₁ ⊆ S · u)`: apply the rotation observation to `T = S · u`!
        obtain ⟨r, hr_lt, hr_drain⟩ := hrot (A.image S u) hsub
        refine ⟨b :: u ++ (List.replicate r a ++ [b]), ?_, fun q => ?_⟩
        · simp only [List.cons_append, List.length_cons, List.length_append, List.length_replicate,
            List.length_nil]
          omega
        · rw [List.cons_append, DFA.eval_cons, DFA.eval_append]
          apply hr_drain
          rw [DFA.mem_image]
          exact ⟨A.step q b, by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩, rfl⟩
  · -- Case 1a: `¬ (C₁ ⊆ S)`
    obtain ⟨r, hr_lt, hr_drain⟩ := hrot S hCS
    refine ⟨b :: (List.replicate r a ++ [b]), ?_, fun q => ?_⟩
    · simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil]
      omega
    · rw [DFA.eval_cons]
      apply hr_drain
      rw [DFA.mem_image]
      exact ⟨q, Finset.mem_univ q, rfl⟩

/-- **Theorem F (Cycle-Drain Unbalanced Multi-Cluster Sharp Reset Bound)**:
`∃ w, A.IsSyncWord w ∧ w.length ≤ m₁^2 + (2n - 4) * m₁ - n + 5`. -/
theorem cycleDrain_reset_bound {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (a b : α) (C₁ : Finset Q)
    (hm₁_ge : 2 ≤ C₁.card) (hm₁_lt : C₁.card < Fintype.card Q)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hTreeFree : ∀ q : Q, q ∉ C₁ → A.step q a ∉ C₁)
    (u₀ : Q) (hu₀ : u₀ ∈ C₁)
    (hDrain : ∀ q : Q, q ≠ u₀ → A.step q b ∈ C₁) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤
        C₁.card ^ 2 + (2 * Fintype.card Q - 4) * C₁.card - Fintype.card Q + 5 := by
  obtain ⟨w₀, hw₀_len, hw₀_in⟩ :=
    cycleDrain_exists_collapseWord A hSync a b C₁ hm₁_ge hm₁_lt hC₁_inv hC₁_trans hTreeFree
      u₀ hu₀ hDrain
  obtain ⟨w, hw, hlen⟩ :=
    shortCollapse_cycle_reset_bound A hSync a C₁ hm₁_ge hC₁_inv hC₁_trans w₀
      (Fintype.card Q + 1) hw₀_len hw₀_in
  refine ⟨w, hw, le_trans hlen ?_⟩
  set n := Fintype.card Q
  set m₁ := C₁.card
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have h2n4 : 4 ≤ 2 * n := by omega
  have hsub_ok : n ≤ m₁ ^ 2 + (2 * n - 4) * m₁ := by zify [h2n4]; nlinarith
  have hm₁_le : m₁ ≤ n := le_of_lt hm₁_lt
  have h1 : 1 ≤ n - 1 + (n + 1) + m₁ := by omega
  zify [hm₁_ge, hn1, h2n4, hsub_ok, hm₁_le, h1]
  linarith [sq m₁]

/-- **Theorem F Corollary 1 (Universal Quadratic Bound `< 3(n - 1)^2`)**:
for all `2 ≤ m₁ < n`, `∃ w, A.IsSyncWord w ∧ w.length ≤ 3n^2 - 9n + 10` (and `< 3(n - 1)^2`). -/
theorem cycleDrain_quadratic_bound {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (a b : α) (C₁ : Finset Q)
    (hm₁_ge : 2 ≤ C₁.card) (hm₁_lt : C₁.card < Fintype.card Q)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hTreeFree : ∀ q : Q, q ∉ C₁ → A.step q a ∉ C₁)
    (u₀ : Q) (hu₀ : u₀ ∈ C₁)
    (hDrain : ∀ q : Q, q ≠ u₀ → A.step q b ∈ C₁) :
    ∃ w : List α, A.IsSyncWord w ∧
      w.length ≤ 3 * Fintype.card Q ^ 2 - 9 * Fintype.card Q + 10 ∧
      w.length < 3 * (Fintype.card Q - 1) ^ 2 := by
  obtain ⟨w, hw, hlen⟩ :=
    cycleDrain_reset_bound A hSync a b C₁ hm₁_ge hm₁_lt hC₁_inv hC₁_trans hTreeFree u₀ hu₀ hDrain
  refine ⟨w, hw, ?_, ?_⟩
  · refine le_trans hlen ?_
    set n := Fintype.card Q
    set m₁ := C₁.card
    have hn3 : 3 ≤ n := by omega
    have h2n4 : 4 ≤ 2 * n := by omega
    have hsub1 : n ≤ m₁ ^ 2 + (2 * n - 4) * m₁ := by zify [h2n4]; nlinarith
    have hsub2 : 9 * n ≤ 3 * n ^ 2 := by nlinarith
    have hm₁_le : m₁ ≤ n - 1 := by omega
    zify [h2n4, hsub1, hsub2]
    nlinarith
  · refine lt_of_le_of_lt hlen ?_
    set n := Fintype.card Q
    set m₁ := C₁.card
    have hn3 : 3 ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    have h2n4 : 4 ≤ 2 * n := by omega
    have hsub1 : n ≤ m₁ ^ 2 + (2 * n - 4) * m₁ := by zify [h2n4]; nlinarith
    have hm₁_le : m₁ ≤ n - 1 := by omega
    zify [hn1, h2n4, hsub1]
    nlinarith

/-- **Theorem F Corollary 2 (Kisielewicz–Szykuła `A_{2m-1}` Regime `2m₁ ≤ n + 1`)**:
whenever `2 * m₁ ≤ n + 1`, `4 * w.length ≤ 5n^2 - 6n + 13` (hence `w.length ≤ (5n^2 - 6n + 13) / 4`),
exponentially improving Berlinkov (2013)'s `Θ(2^(n/2) n^2)` bound on `A_{2m-1}`! -/
theorem cycleDrain_ks_regime_bound {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (a b : α) (C₁ : Finset Q)
    (hm₁_ge : 2 ≤ C₁.card) (hm₁_lt : C₁.card < Fintype.card Q)
    (hks : 2 * C₁.card ≤ Fintype.card Q + 1)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hTreeFree : ∀ q : Q, q ∉ C₁ → A.step q a ∉ C₁)
    (u₀ : Q) (hu₀ : u₀ ∈ C₁)
    (hDrain : ∀ q : Q, q ≠ u₀ → A.step q b ∈ C₁) :
    ∃ w : List α, A.IsSyncWord w ∧
      4 * w.length ≤ 5 * Fintype.card Q ^ 2 - 6 * Fintype.card Q + 13 ∧
      w.length ≤ (5 * Fintype.card Q ^ 2 - 6 * Fintype.card Q + 13) / 4 := by
  obtain ⟨w, hw, hlen⟩ :=
    cycleDrain_reset_bound A hSync a b C₁ hm₁_ge hm₁_lt hC₁_inv hC₁_trans hTreeFree u₀ hu₀ hDrain
  have h4 : 4 * w.length ≤ 5 * Fintype.card Q ^ 2 - 6 * Fintype.card Q + 13 := by
    have h4len : 4 * w.length ≤
        4 * (C₁.card ^ 2 + (2 * Fintype.card Q - 4) * C₁.card - Fintype.card Q + 5) :=
      Nat.mul_le_mul_left 4 hlen
    refine le_trans h4len ?_
    set n := Fintype.card Q
    set m₁ := C₁.card
    have hn3 : 3 ≤ n := by omega
    have h2n4 : 4 ≤ 2 * n := by omega
    have hsub1 : n ≤ m₁ ^ 2 + (2 * n - 4) * m₁ := by zify [h2n4]; nlinarith
    have hsub2 : 6 * n ≤ 5 * n ^ 2 := by nlinarith
    zify [h2n4, hsub1, hsub2]
    nlinarith
  exact ⟨w, hw, h4, by omega⟩

/-- **Theorem F Corollary 3 (Exact Černý Conjecture `(n - 1)^2` for `5m₁ ≤ 2n`)**:
every synchronizing cycle-drain multi-cluster DFA with `2 ≤ m₁` and `5 * m₁ ≤ 2 * n` satisfies
the exact Černý Conjecture `w.length ≤ (n - 1)^2`! -/
theorem cycleDrain_twoFifths_cerny {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (a b : α) (C₁ : Finset Q)
    (hm₁_ge : 2 ≤ C₁.card) (h52 : 5 * C₁.card ≤ 2 * Fintype.card Q)
    (hC₁_inv : ∀ q ∈ C₁, A.step q a ∈ C₁)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q)
    (hTreeFree : ∀ q : Q, q ∉ C₁ → A.step q a ∉ C₁)
    (u₀ : Q) (hu₀ : u₀ ∈ C₁)
    (hDrain : ∀ q : Q, q ≠ u₀ → A.step q b ∈ C₁) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have hm₁_lt : C₁.card < Fintype.card Q := by omega
  obtain ⟨w, hw, hlen⟩ :=
    cycleDrain_reset_bound A hSync a b C₁ hm₁_ge hm₁_lt hC₁_inv hC₁_trans hTreeFree u₀ hu₀ hDrain
  refine ⟨w, hw, ?_⟩
  set n := Fintype.card Q
  set m₁ := C₁.card
  have hn5 : 5 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have h2n4 : 4 ≤ 2 * n := by omega
  have hsub1 : n ≤ m₁ ^ 2 + (2 * n - 4) * m₁ := by zify [h2n4]; nlinarith
  have h25 : 25 * (m₁ ^ 2 + (2 * n - 4) * m₁ - n + 5) ≤ 25 * (n - 1) ^ 2 := by
    zify [hn1, h2n4, hsub1]
    have hfactor : (25 : ℤ) * ((n : ℤ) - 1) ^ 2 - (24 * (n : ℤ) ^ 2 - 65 * (n : ℤ) + 125) =
        ((n : ℤ) - 5) * ((n : ℤ) + 20) := by ring
    nlinarith
  omega

/-- **Theorem F Boundary Case `m₁ = 1`**: if `|C₁| = 1` and `(Q \ {u₀}) · b ⊆ C₁`, then `b` has
rank `≤ 2`, so exact Černý Conjecture `w.length ≤ (n - 1)^2` holds unconditionally! -/
theorem cycleDrain_card_one_cerny {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (b : α) (C₁ : Finset Q) (hm₁ : C₁.card = 1)
    (u₀ : Q)
    (hDrain : ∀ q : Q, q ≠ u₀ → A.step q b ∈ C₁) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have : Nonempty Q := hSync.nonempty
  have hsub : A.image Finset.univ [b] ⊆ insert (A.step u₀ b) C₁ := by
    intro y hy
    rw [DFA.mem_image] at hy
    rcases hy with ⟨q, _, rfl⟩
    rw [DFA.eval_singleton, Finset.mem_insert]
    by_cases hqu : q = u₀
    · left; rw [hqu]
    · right; exact hDrain q hqu
  have hrank : (A.image Finset.univ [b]).card ≤ 2 := by
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    omega
  exact rank_le_two_cerny A hSync ⟨b, hrank⟩

/-- **Theorem F Boundary Case `m₁ = n`**: if `a` acts as a single `n`-cycle on `C₁ = Q`, then `A`
is circular, so exact Černý Conjecture `w.length ≤ (n - 1)^2` holds! -/
theorem cycleDrain_full_cerny {Q : Type u} {α : Type v} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing)
    (a : α) (C₁ : Finset Q) (hm₁ : C₁.card = Fintype.card Q)
    (hC₁_trans : ∀ p ∈ C₁, ∀ q ∈ C₁, ∃ k : ℕ, (fun x => A.step x a)^[k] p = q) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length ≤ (Fintype.card Q - 1) ^ 2 := by
  have : Nonempty Q := hSync.nonempty
  have hC₁_univ : C₁ = Finset.univ := Finset.eq_univ_of_card C₁ hm₁
  let f : Q → Q := fun x => A.step x a
  have htrans : ∀ p q : Q, ∃ k : ℕ, f^[k] p = q := fun p q =>
    hC₁_trans p (by rw [hC₁_univ]; exact Finset.mem_univ p)
      q (by rw [hC₁_univ]; exact Finset.mem_univ q)
  have hbij : Function.Bijective f := by
    have hsurj : Function.Surjective f := by
      intro q
      obtain ⟨k, hk⟩ := htrans (f q) q
      refine ⟨f^[k] q, ?_⟩
      rw [← Function.iterate_succ_apply' f k q, Function.iterate_succ_apply]
      exact hk
    exact (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, rfl⟩
  exact circular_cerny A ⟨a, hbij, htrans⟩ hSync

end Cerny
