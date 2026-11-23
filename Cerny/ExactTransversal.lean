import Cerny.Defs
import Cerny.SubPinFrankl
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact-Transversal Corank-Gap Lemma (Theorem T22: `δ(r) ≤ λ(r) + r + 1`)

This file formalizes **Theorem T22** (`docs/round5_general_bridge.md` §3):
for EVERY synchronizing DFA `A` on `n ≥ 2` states and EVERY `1 ≤ r ≤ n - 2`:
$$\delta(r) \le \lambda(r) + r + 1 \qquad (\text{equivalently, } \lambda(r + 1) \le 2\lambda(r) + r + 1).$$

This simultaneously sharpens Shitov's `δ(r) ≤ λ(r) + 2r` (`Cerny.shitov_corank_gap`) to `λ(r) + r + 1`
AND removes Shitov's `r < n / 2` hypothesis completely, via a self-contained linear algebra proof
over `ℚ` on the `r`-dimensional fiber-annihilator subspace `W_u^⊥`.
-/

namespace Cerny

universe u v

section ExactTransversal

variable {Q : Type u} {α : Type v}

/-- Indicator vector `1_T : Q → ℚ` of a finite set `T ⊆ Q`. -/
private def indVec [DecidableEq Q] (T : Finset Q) : Q → ℚ :=
  fun q => if q ∈ T then 1 else 0

/-- Linear pushforward map `v ↦ v M_w` on `Q → ℚ` induced by a word `w`. -/
private def pushMap [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) :
    (Q → ℚ) →ₗ[ℚ] (Q → ℚ) where
  toFun v q := ∑ p : Q, if A.eval p w = q then v p else 0
  map_add' v₁ v₂ := by
    ext q
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  map_smul' c v := by
    ext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> ring

private theorem pushMap_nil [Fintype Q] [DecidableEq Q] (A : DFA Q α) (v : Q → ℚ) :
    pushMap A [] v = v := by
  ext q
  simp only [pushMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single q]
  · simp
  · intro p _ hne; simp [hne]
  · intro hnot; exact absurd (Finset.mem_univ q) hnot

private theorem pushMap_append [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (w₁ w₂ : List α) (v : Q → ℚ) :
    pushMap A (w₁ ++ w₂) v = pushMap A w₂ (pushMap A w₁ v) := by
  ext q
  simp only [pushMap, LinearMap.coe_mk, AddHom.coe_mk]
  have hrew : (∑ y : Q, if A.eval y w₂ = q then
      (∑ x : Q, if A.eval x w₁ = y then v x else 0) else 0) =
      ∑ y : Q, ∑ x : Q, if A.eval y w₂ = q then (if A.eval x w₁ = y then v x else 0) else 0 := by
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  rw [hrew, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [DFA.eval_append]
  have h1 : (∑ y : Q, if A.eval y w₂ = q then (if A.eval x w₁ = y then v x else 0) else 0) =
      ∑ y : Q, if A.eval x w₁ = y then (if A.eval y w₂ = q then v x else 0) else 0 := by
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> rfl
  rw [h1, Finset.sum_ite_eq]
  simp

private theorem pushMap_indVec_of_card_eq [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (T : Finset Q) (w : List α) (hcard : (A.image T w).card = T.card) :
    pushMap A w (indVec T) = indVec (A.image T w) := by
  have hinj : Set.InjOn (fun x => A.eval x w) (T : Set Q) :=
    Finset.injOn_of_card_image_eq hcard
  ext q
  simp only [pushMap, LinearMap.coe_mk, AddHom.coe_mk, indVec]
  by_cases hq : q ∈ A.image T w
  · simp only [hq, ↓reduceIte]
    rw [DFA.mem_image] at hq
    obtain ⟨p₀, hp₀T, hp₀eq⟩ := hq
    rw [Finset.sum_eq_single p₀]
    · simp [hp₀eq, hp₀T]
    · intro p _ hne
      by_cases hpT : p ∈ T
      · have hne' : A.eval p w ≠ q := fun heq => hne (hinj hpT hp₀T (heq.trans hp₀eq.symm))
        simp [hne']
      · simp [hpT]
    · intro hnot; exact absurd (Finset.mem_univ p₀) hnot
  · simp only [hq, ↓reduceIte]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hpT : p ∈ T
    · have hne' : A.eval p w ≠ q := fun heq => hq ((DFA.mem_image A T w q).mpr ⟨p, hpT, heq⟩)
      simp [hne']
    · simp [hpT]

private theorem pushMap_sync_indVec [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (S : Finset Q) (w : List α) (q₀ : Q) (hw : ∀ p : Q, A.eval p w = q₀) (q : Q) :
    pushMap A w (indVec S) q = if q = q₀ then (S.card : ℚ) else 0 := by
  simp only [pushMap, LinearMap.coe_mk, AddHom.coe_mk, indVec]
  by_cases hq : q = q₀
  · subst hq
    have hrew : (∑ p : Q, if A.eval p w = q then (if p ∈ S then (1 : ℚ) else 0) else 0) =
        ∑ p : Q, if p ∈ S then (1 : ℚ) else 0 := by
      refine Finset.sum_congr rfl fun p _ => by simp [hw p]
    simp only [↓reduceIte, hrew, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  · simp only [hq, ↓reduceIte]
    refine Finset.sum_eq_zero fun p _ => ?_
    have hne : A.eval p w ≠ q := by rw [hw p]; exact Ne.symm hq
    simp [hne]

/-- Fiber-sum linear map `z ↦ (∑_{p ∈ y u⁻¹} z_p)_{y ∈ Q·u}` for a word `u`. -/
private def fiberMap [Fintype Q] [DecidableEq Q] (A : DFA Q α) (u : List α) :
    (Q → ℚ) →ₗ[ℚ] ({y // y ∈ A.image Finset.univ u} → ℚ) where
  toFun z y := ∑ p ∈ A.preimage {y.1} u, z p
  map_add' z₁ z₂ := by
    ext y; simp [Finset.sum_add_distrib]
  map_smul' c z := by
    ext y; simp [Finset.mul_sum]

private theorem fiberMap_surjective [Fintype Q] [DecidableEq Q] (A : DFA Q α) (u : List α) :
    Function.Surjective (fiberMap A u) := by
  intro g
  refine ⟨fun p =>
    g ⟨A.eval p u, (DFA.mem_image A Finset.univ u (A.eval p u)).mpr ⟨p, Finset.mem_univ p, rfl⟩⟩ /
      ((A.preimage {A.eval p u} u).card : ℚ), ?_⟩
  ext ⟨y, hy⟩
  simp only [fiberMap, LinearMap.coe_mk, AddHom.coe_mk]
  have hne : (A.preimage {y} u).Nonempty := by
    rw [DFA.mem_image] at hy
    obtain ⟨p, _, hp⟩ := hy
    exact ⟨p, by simp [DFA.mem_preimage, hp]⟩
  have hpos : (0 : ℚ) < ((A.preimage {y} u).card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hcongr : (∑ p ∈ A.preimage {y} u,
      g ⟨A.eval p u, (DFA.mem_image A Finset.univ u (A.eval p u)).mpr ⟨p, Finset.mem_univ p, rfl⟩⟩ /
        ((A.preimage {A.eval p u} u).card : ℚ)) =
      ∑ _p ∈ A.preimage {y} u, g ⟨y, hy⟩ / ((A.preimage {y} u).card : ℚ) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : A.eval p u = y := by simpa [DFA.mem_preimage] using hp
    simp only [hp']
  rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hpos.ne']

private theorem finrank_ker_fiberMap [Fintype Q] [DecidableEq Q] (A : DFA Q α) (u : List α) :
    Module.finrank ℚ (LinearMap.ker (fiberMap A u)) =
      Fintype.card Q - (A.image Finset.univ u).card := by
  have h := LinearMap.finrank_range_add_finrank_ker (fiberMap A u)
  have hrange : LinearMap.range (fiberMap A u) = ⊤ :=
    LinearMap.range_eq_top.mpr (fiberMap_surjective A u)
  rw [hrange, finrank_top, Module.finrank_pi, Module.finrank_pi, Fintype.card_coe] at h
  have hle : (A.image Finset.univ u).card ≤ Fintype.card Q := Finset.card_le_univ _
  omega

private theorem fiberMap_indVec_eq_one [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (u : List α) (T : Finset Q) (hTcard : T.card = (A.image Finset.univ u).card)
    (hTimg : (A.image T u).card = T.card) (y : {y // y ∈ A.image Finset.univ u}) :
    fiberMap A u (indVec T) y = 1 := by
  have hsub : A.image T u ⊆ A.image Finset.univ u := A.image_mono (Finset.subset_univ T) u
  have heq_img : A.image T u = A.image Finset.univ u :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hinj : Set.InjOn (fun p => A.eval p u) (T : Set Q) :=
    Finset.injOn_of_card_image_eq hTimg
  have hy_mem : y.1 ∈ A.image T u := by rw [heq_img]; exact y.2
  rw [DFA.mem_image] at hy_mem
  obtain ⟨p₀, hp₀T, hp₀eq⟩ := hy_mem
  simp only [fiberMap, LinearMap.coe_mk, AddHom.coe_mk, indVec]
  rw [Finset.sum_eq_single p₀]
  · simp [hp₀T]
  · intro p hp hne
    have hp_eval : A.eval p u = y.1 := by simpa [DFA.mem_preimage] using hp
    by_cases hpT : p ∈ T
    · exact absurd (hinj hpT hp₀T (hp_eval.trans hp₀eq.symm)) hne
    · simp [hpT]
  · intro hnot
    exact absurd (by simpa [DFA.mem_preimage] using hp₀eq) hnot

/-- **Theorem T22 (Exact-Transversal Corank-Gap Lemma)**:
For EVERY synchronizing DFA on `n ≥ 2` states and EVERY `1 ≤ r ≤ n - 2`,
`corankGap A hSync r ≤ minCorankLen A hSync r + r + 1`. -/
theorem corankGap_le_minCorankLen_add_succ [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) {r : ℕ}
    (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ Fintype.card Q) :
    corankGap A hSync r ≤ minCorankLen A hSync r + r + 1 := by
  let n := Fintype.card Q
  have hr_le : r + 1 ≤ n - 1 := by omega
  obtain ⟨u, hulen, hucard⟩ := minCorankLen_spec A hSync (by omega : r ≤ n - 1)
  let S := A.image Finset.univ u
  have hS_le : S.card ≤ n - r := hucard
  -- If u already compresses to corank ≥ r + 1, then δ(r) = 0
  by_cases hskip : S.card ≤ n - (r + 1)
  · have hmin := minCorankLen_le A hSync hr_le hskip
    dsimp only [corankGap]
    omega
  have hS_card : S.card = n - r := by omega
  -- If u ++ u already compresses strictly below S.card, then δ(r) ≤ λ(r)
  by_cases hsq : (A.image S u).card < S.card
  · have hnext : (A.image Finset.univ (u ++ u)).card ≤ n - (r + 1) := by
      rw [DFA.image_append]
      change (A.image S u).card ≤ n - (r + 1)
      omega
    have hmin := minCorankLen_le A hSync hr_le hnext
    rw [List.length_append, hulen] at hmin
    dsimp only [corankGap]
    omega
  have hSu_card : (A.image S u).card = S.card :=
    le_antisymm (A.card_image_le S u) (by omega)
  -- Suppose for contradiction that every word w of length ≤ r + 1 preserves both |S·w| and |S·w·u|
  by_contra hgt
  have hkeep : ∀ w : List α, w.length ≤ r + 1 →
      (A.image S w).card = S.card ∧ (A.image (A.image S w) u).card = S.card := by
    intro w hwlen
    have h1 : S.card ≤ (A.image S w).card := by
      by_contra hlt
      have hnext : (A.image Finset.univ (u ++ w)).card ≤ n - (r + 1) := by
        rw [DFA.image_append]; change (A.image S w).card ≤ n - (r + 1); omega
      have hmin := minCorankLen_le A hSync hr_le hnext
      rw [List.length_append, hulen] at hmin
      dsimp only [corankGap] at hgt
      omega
    have h2 : S.card ≤ (A.image (A.image S w) u).card := by
      by_contra hlt
      have hnext : (A.image Finset.univ (u ++ w ++ u)).card ≤ n - (r + 1) := by
        rw [DFA.image_append, DFA.image_append]
        change (A.image (A.image S w) u).card ≤ n - (r + 1); omega
      have hmin := minCorankLen_le A hSync hr_le hnext
      rw [List.length_append, List.length_append, hulen] at hmin
      dsimp only [corankGap] at hgt
      omega
    exact ⟨le_antisymm (A.card_image_le S w) h1,
      le_antisymm (le_trans (A.card_image_le _ u) (A.card_image_le S w)) h2⟩
  -- Define the ascending subspace chain V t ≤ ker (fiberMap A u)
  let Wker : Submodule ℚ (Q → ℚ) := LinearMap.ker (fiberMap A u)
  have hWker_dim : Module.finrank ℚ Wker = r := by
    dsimp only [Wker]
    rw [finrank_ker_fiberMap]
    change n - S.card = r
    omega
  let V : ℕ → Submodule ℚ (Q → ℚ) := fun t =>
    Submodule.span ℚ {v | ∃ p : List α, p.length ≤ t ∧ v = indVec (A.image S p) - indVec S}
  have hV_mono : ∀ t, V t ≤ V (t + 1) := by
    intro t
    refine Submodule.span_mono ?_
    rintro v ⟨p, hp, rfl⟩
    exact ⟨p, by omega, rfl⟩
  have hV_le_ker : ∀ t ≤ r + 1, V t ≤ Wker := by
    intro t ht
    refine Submodule.span_le.mpr ?_
    rintro v ⟨p, hp, rfl⟩
    have ⟨hSw, hSwu⟩ := hkeep p (by omega)
    change fiberMap A u (indVec (A.image S p) - indVec S) = 0
    ext y
    rw [map_sub, Pi.sub_apply, Pi.zero_apply,
      fiberMap_indVec_eq_one A u (A.image S p) hSw (by rw [hSw]; exact hSwu) y,
      fiberMap_indVec_eq_one A u S rfl hSu_card y, sub_self]
  -- By dimension bound finrank Wker = r, the chain stabilizes at some t ≤ r
  have hstab : ∃ t ≤ r, V t = V (t + 1) := by
    by_contra hnone
    push Not at hnone
    have hgrow : ∀ t ≤ r + 1, t ≤ Module.finrank ℚ (V t) := by
      intro t
      induction t with
      | zero => intro _; exact Nat.zero_le _
      | succ t ih =>
        intro ht
        have hlt_sub : V t < V (t + 1) := lt_of_le_of_ne (hV_mono t) (hnone t (by omega))
        have hlt_dim : Module.finrank ℚ (V t) < Module.finrank ℚ (V (t + 1)) :=
          Submodule.finrank_lt_finrank_of_lt hlt_sub
        have iht := ih (by omega)
        omega
    have hle_dim : Module.finrank ℚ (V (r + 1)) ≤ Module.finrank ℚ Wker :=
      Submodule.finrank_mono (hV_le_ker (r + 1) le_rfl)
    have hge_dim := hgrow (r + 1) le_rfl
    omega
  obtain ⟨t, ht_le, ht_eq⟩ := hstab
  -- V t is invariant under pushMap A [a] for every letter a
  have hV_inv : ∀ (a : α) (z : Q → ℚ), z ∈ V t → pushMap A [a] z ∈ V t := by
    intro a z hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨p, hp, rfl⟩
      have ⟨hSp, _⟩ := hkeep p (by omega)
      have ⟨hSpa, _⟩ := hkeep (p ++ [a]) (by rw [List.length_append]; simp; omega)
      have ⟨hSa, _⟩ := hkeep [a] (by simp)
      have hcard_step : (A.image (A.image S p) [a]).card = (A.image S p).card := by
        rw [← DFA.image_append, hSpa, hSp]
      rw [map_sub, pushMap_indVec_of_card_eq A (A.image S p) [a] hcard_step,
        pushMap_indVec_of_card_eq A S [a] hSa, ← DFA.image_append]
      have heq_sub : indVec (A.image S (p ++ [a])) - indVec (A.image S [a]) =
          (indVec (A.image S (p ++ [a])) - indVec S) - (indVec (A.image S [a]) - indVec S) := by
        ext q; simp
      rw [heq_sub, ht_eq]
      refine Submodule.sub_mem _ ?_ ?_
      · exact Submodule.subset_span ⟨p ++ [a], by rw [List.length_append]; simp; omega, rfl⟩
      · exact Submodule.subset_span ⟨[a], by simp, rfl⟩
    · simp
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
  -- By snoc induction, pushMap A w (indVec S) - indVec S ∈ V t for EVERY word w
  have hall_words : ∀ w : List α, pushMap A w (indVec S) - indVec S ∈ V t := by
    intro w
    induction w using List.reverseRecOn with
    | nil =>
      rw [pushMap_nil, sub_self]
      exact Submodule.zero_mem _
    | append_singleton w a ih =>
      rw [pushMap_append]
      have hdecomp : pushMap A [a] (pushMap A w (indVec S)) - indVec S =
          pushMap A [a] (pushMap A w (indVec S) - indVec S) +
            (pushMap A [a] (indVec S) - indVec S) := by
        rw [map_sub]; abel
      rw [hdecomp]
      refine Submodule.add_mem _ (hV_inv a _ ih) ?_
      have ⟨hSa, _⟩ := hkeep [a] (by simp)
      rw [pushMap_indVec_of_card_eq A S [a] hSa, ht_eq]
      exact Submodule.subset_span ⟨[a], by simp, rfl⟩
  -- Plug in a synchronizing word w_sync (evaluating every state to q₀)
  rcases hSync with ⟨w_sync, q₀, hq₀⟩
  have hmem_ker : pushMap A w_sync (indVec S) - indVec S ∈ Wker :=
    hV_le_ker t (by omega) (hall_words w_sync)
  -- Pick a state y₁ ∈ S distinct from y₀ := A.eval q₀ u (possible since |S| = n - r ≥ 2)
  have hS_gt1 : 1 < S.card := by omega
  obtain ⟨y₁, hy₁, hne_y⟩ : ∃ y₁ ∈ S, y₁ ≠ A.eval q₀ u := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hS_gt1
    by_cases h1 : a = A.eval q₀ u
    · exact ⟨b, hb, by rw [← h1]; exact hab.symm⟩
    · exact ⟨a, ha, h1⟩
  have hzero : fiberMap A u (pushMap A w_sync (indVec S) - indVec S) ⟨y₁, hy₁⟩ = 0 := by
    have hker : fiberMap A u (pushMap A w_sync (indVec S) - indVec S) = 0 := hmem_ker
    rw [hker]; rfl
  rw [map_sub, Pi.sub_apply, fiberMap_indVec_eq_one A u S rfl hSu_card ⟨y₁, hy₁⟩] at hzero
  have hsync_zero : fiberMap A u (pushMap A w_sync (indVec S)) ⟨y₁, hy₁⟩ = 0 := by
    simp only [fiberMap, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [pushMap_sync_indVec A S w_sync q₀ hq₀ p]
    have hp_ne : p ≠ q₀ := by
      intro hpq
      have : A.eval q₀ u = y₁ := by rw [← hpq]; simpa [DFA.mem_preimage] using hp
      exact hne_y this.symm
    simp [hp_ne]
  rw [hsync_zero] at hzero
  norm_num at hzero

/-- Equivalent doubling form of Theorem T22: `λ(r + 1) ≤ 2 * λ(r) + r + 1`. -/
theorem minCorankLen_succ_le_two_mul_add_succ [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) {r : ℕ}
    (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ Fintype.card Q) :
    minCorankLen A hSync (r + 1) ≤ 2 * minCorankLen A hSync r + r + 1 := by
  have hgap := corankGap_le_minCorankLen_add_succ A hSync hr1 hr2
  have hmono := minCorankLen_mono A hSync (Nat.le_add_right r 1) (by omega)
  dsimp only [corankGap] at hgap
  omega

end ExactTransversal

end Cerny
