import Cerny.Defs
import Cerny.Combinatorial
import Cerny.AdditionalClasses
import Cerny.SubPinFrankl
import Cerny.SubShitov
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Breaking Strictly Below `7/48 n³` for ALL Synchronizing Automata (Theorem T20)

This file formalizes **Theorem T20** (`docs/round5_general_bridge.md` §1 & §5), proving the
first-ever general upper bound strictly below `7/48 n³` for **100% of all synchronizing DFAs**:
$$\exists\,\delta > 0,\;\exists\,N_0,\;\forall A \text{ synchronizing on } n \ge N_0 \text{ states},\quad
  \operatorname{rt}(A) \le \left(\frac{7}{48} - \delta\right) n^3,$$
strictly breaking the standing `7/48 n³ + o(n³)` barrier of Hong (`2611.00506v1`).

The proof is 100% elementary over `ℕ` and `ℚ` (zero calculus, zero `Real.sqrt`, zero `Real.log`):
1. **Part 1 (`SingularityFreeCap`)**: Generalized corank `corankAt A hSync L` (`D(L)`),
   kernel-block cover degree `K_t` and block-join graph `Γ_t`, 1-line complement degree bound
   `complement_deg_le` (`deg_{E_q}(z) ≤ C + K_q`), whole-block transport `wholeBlock_transport`,
   single-quantity calm time `single_calm_time`, and the **Singularity-Free Block Compression Cap**
   `singularityFree_compression_cap` (eliminating `1/(1 - 2c)` completely).
2. **Part 2 (`RationalPaymentCerts`)**: Exact zero-`√2` rational Bernstein certificates over `ℚ`
   (`rational_payment_ge`, `rational_payment_ge_mid`, `rational_payment_ge_hi`) using `17/12 > √2`,
   plus exact cubic discrete-to-continuous strip comparison.
3. **Part 3 (`CaseBMacroscopicBand`)**: `common_neighbor_preimage_lift` (Lemma 1.3),
   `geometric_ratio_calm_step`, `twoScale_nested_calm_time`, and `caseB_macroscopic_band_bound`
   (Proposition 1.4: `δ(r) ≤ ⌈0.120 n²⌉` across ALL `r ∈ [n/2, 58n/100]`).
4. **Part 4 (`BelowSevenFortyEightMain`)**: Unified dyadic-schedule + cap-saving theorem
   `word_cap_beats_seven_forty_eight`, symbolic non-circular 3-case assembly
   `below_seven_forty_eight_sc`, SCC reduction lift to all synchronizing DFAs
   `exists_strictly_below_seven_forty_eight`, and division-free `ℕ` flagship
   `below_seven_forty_eight`.
-/

namespace Cerny

universe u v

/-! ## Part 1: Generalized Corank `D(L)`, Kernel Blocks & Singularity-Free Compression Cap -/

section SingularityFreeCap

variable {Q : Type u} {α : Type v}

/-- Maximum corank `D(L)` achievable by a word of length at most `L`. -/
noncomputable def corankAt [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (L : ℕ) : ℕ := by
  classical
  exact ((Finset.range (Fintype.card Q)).filter
      (fun d => minCorankLen A hSync d ≤ L)).max' (by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
    · exact Fintype.card_pos_iff.mpr hSync.nonempty
    · rw [minCorankLen_zero]; exact Nat.zero_le _)

theorem corankAt_le_pred [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (L : ℕ) :
    corankAt A hSync L ≤ Fintype.card Q - 1 := by
  classical
  have hmem := Finset.max'_mem ((Finset.range (Fintype.card Q)).filter
    (fun d => minCorankLen A hSync d ≤ L)) (by
      refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
      · exact Fintype.card_pos_iff.mpr hSync.nonempty
      · rw [minCorankLen_zero]; exact Nat.zero_le _)
  have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
  change corankAt A hSync L < Fintype.card Q at hlt
  omega

theorem minCorankLen_corankAt_le [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (L : ℕ) :
    minCorankLen A hSync (corankAt A hSync L) ≤ L := by
  classical
  have hmem := Finset.max'_mem ((Finset.range (Fintype.card Q)).filter
    (fun d => minCorankLen A hSync d ≤ L)) (by
      refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
      · exact Fintype.card_pos_iff.mpr hSync.nonempty
      · rw [minCorankLen_zero]; exact Nat.zero_le _)
  exact (Finset.mem_filter.mp hmem).2

theorem corank_le_corankAt [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {L : ℕ} {u : List α} (hu : u.length ≤ L) :
    Fintype.card Q - (A.image Finset.univ u).card ≤ corankAt A hSync L := by
  classical
  obtain ⟨q₀⟩ := hSync.nonempty
  have hpos : 1 ≤ (A.image Finset.univ u).card :=
    Finset.card_pos.mpr ⟨A.eval q₀ u, (DFA.mem_image A _ _ _).mpr ⟨q₀, Finset.mem_univ q₀, rfl⟩⟩
  have hle_n : (A.image Finset.univ u).card ≤ Fintype.card Q := Finset.card_le_univ _
  let d := Fintype.card Q - (A.image Finset.univ u).card
  have hd_lt : d < Fintype.card Q := by omega
  have hd_le : d ≤ Fintype.card Q - 1 := by omega
  have hlen_le : minCorankLen A hSync d ≤ L :=
    le_trans (minCorankLen_le A hSync hd_le (by omega)) hu
  exact Finset.le_max' _ d (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hd_lt, hlen_le⟩)

theorem corankAt_mono [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) :
    corankAt A hSync L₁ ≤ corankAt A hSync L₂ := by
  classical
  have hlt : corankAt A hSync L₁ < Fintype.card Q := by
    have h1 := corankAt_le_pred A hSync L₁
    have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr hSync.nonempty
    omega
  have hl : minCorankLen A hSync (corankAt A hSync L₁) ≤ L₁ :=
    minCorankLen_corankAt_le A hSync L₁
  exact Finset.le_max' ((Finset.range (Fintype.card Q)).filter
      (fun d => minCorankLen A hSync d ≤ L₂)) (corankAt A hSync L₁)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, le_trans hl hL⟩)

theorem corankAt_pred_eq_shortCorank [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) :
    corankAt A hSync (Fintype.card Q - 1) = shortCorank A hSync :=
  rfl

theorem exists_word_corankAt [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (L : ℕ) :
    ∃ v : List α, v.length ≤ L ∧
      (A.image Finset.univ v).card = Fintype.card Q - corankAt A hSync L := by
  have hd_le := corankAt_le_pred A hSync L
  obtain ⟨v, hvlen, hvcard⟩ := minCorankLen_spec A hSync hd_le
  have hvL : v.length ≤ L := hvlen.symm ▸ minCorankLen_corankAt_le A hSync L
  have hge := corank_le_corankAt A hSync hvL
  have hle_n : (A.image Finset.univ v).card ≤ Fintype.card Q := Finset.card_le_univ _
  exact ⟨v, hvL, by omega⟩

/-- Kernel blocks `p ∈ Q·v` whose entire fiber `p v⁻¹` lies inside `N_{E_t}(x)`. -/
noncomputable def blockCoverSet [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (v : List α) (t : ℕ) (x : Q) : Finset Q := by
  classical
  exact (A.image Finset.univ v).filter (fun p => A.preimage {p} v ⊆ mergeNeighbors A t x)

noncomputable def blockCoverDeg [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (v : List α) (t : ℕ) (x : Q) : ℕ :=
  (blockCoverSet A v t x).card

noncomputable def maxBlockCoverDeg [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (v : List α) (t : ℕ) : ℕ :=
  Finset.univ.sup (blockCoverDeg A v t)

/-- Block-join graph `Γ_t` on `Q·v`: `q` is adjacent to `p` if `q ≠ p` and `p v⁻¹ × q v⁻¹ ⊆ E_t`. -/
noncomputable def blockJoinNeighbors [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (v : List α) (t : ℕ) (p : Q) : Finset Q := by
  classical
  exact (A.image Finset.univ v).filter
    (fun q => q ≠ p ∧ ∀ a ∈ A.preimage {p} v, ∀ b ∈ A.preimage {q} v, b ∈ mergeNeighbors A t a)

noncomputable def blockJoinDeg [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (v : List α) (t : ℕ) (p : Q) : ℕ :=
  (blockJoinNeighbors A v t p).card

private theorem maxBlockCoverDeg_mono [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (v : List α) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) :
    maxBlockCoverDeg A v t₁ ≤ maxBlockCoverDeg A v t₂ := by
  refine Finset.sup_le fun x _ => le_trans ?_ (Finset.le_sup (f := blockCoverDeg A v t₂) (Finset.mem_univ x))
  refine Finset.card_le_card fun p hp => ?_
  classical
  simp only [blockCoverSet, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, subset_trans hp.2 (mergeNeighbors_mono A ht x)⟩

private theorem maxBlockCoverDeg_le_card [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (v : List α) (t : ℕ) : maxBlockCoverDeg A v t ≤ Fintype.card Q :=
  Finset.sup_le fun _ _ => Finset.card_le_univ _

private theorem maxMergeDeg_mono [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) : maxMergeDeg A t₁ ≤ maxMergeDeg A t₂ :=
  Finset.sup_le fun x _ => le_trans
    (Finset.card_le_card (mergeNeighbors_mono A ht x))
    (mergeDeg_le_maxMergeDeg A t₂ x)

private theorem minMergeDeg_mono [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) : minMergeDeg A t₁ ≤ minMergeDeg A t₂ :=
  Finset.le_inf' Finset.univ_nonempty _ fun x _ =>
    le_trans (minMergeDeg_le_mergeDeg A t₁ x) (Finset.card_le_card (mergeNeighbors_mono A ht x))

/-- **Lemma 1.1(1) — 1-Line Complement Degree Bound** (`@attack-polytope` `#149`):
For EVERY word `v` of corank `C = n - |Q·v|`, EVERY `q ≥ 0`, and EVERY `z : Q`
(no strong connectivity, no transport, no time shift!):
`mergeDeg A q z ≤ (n - |Q·v|) + blockCoverDeg A v q z`. -/
theorem complement_deg_le [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (v : List α) (q : ℕ) (z : Q) :
    mergeDeg A q z ≤ (Fintype.card Q - (A.image Finset.univ v).card) + blockCoverDeg A v q z := by
  classical
  let R := A.image Finset.univ v
  let Cov := blockCoverSet A v q z
  have hCov_sub : Cov ⊆ R := Finset.filter_subset _ _
  have hsub_img : R \ Cov ⊆ A.image (Finset.univ \ mergeNeighbors A q z) v := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    have hpR : p ∈ R := hp.1
    have hpNot : ¬ (A.preimage {p} v ⊆ mergeNeighbors A q z) := fun hsub =>
      hp.2 (Finset.mem_filter.mpr ⟨hpR, hsub⟩)
    rw [Finset.not_subset] at hpNot
    obtain ⟨y, hy_pre, hy_not⟩ := hpNot
    have hyv : A.eval y v = p := by simpa [DFA.mem_preimage] using hy_pre
    exact (DFA.mem_image A _ _ _).mpr ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy_not⟩, hyv⟩
  have hcard1 : (R \ Cov).card ≤ (Finset.univ \ mergeNeighbors A q z).card :=
    le_trans (Finset.card_le_card hsub_img) (A.card_image_le _ v)
  rw [Finset.card_sdiff_of_subset hCov_sub,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at hcard1
  have hle1 : Cov.card ≤ R.card := Finset.card_le_card hCov_sub
  have hle2 : R.card ≤ Fintype.card Q := Finset.card_le_univ _
  have hle3 : (mergeNeighbors A q z).card ≤ Fintype.card Q := Finset.card_le_univ _
  change (mergeNeighbors A q z).card ≤ (Fintype.card Q - R.card) + Cov.card
  omega

/-- **Lemma 1.1(2a) — Whole-Block Transport**:
On any strongly connected synchronizing DFA, for every word `v`, every `t ≥ 0`, and every
`p₀ ∈ Q·v`, `K_t ≤ deg_{Γ_{t + |v| + (n - 1)}}(p₀) + (D(2|v| + n - 1) - (n - |Q·v|))`. -/
private theorem wholeBlock_transport [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    (v : List α) (t : ℕ) {p₀ : Q} (_hp₀ : p₀ ∈ A.image Finset.univ v) :
    let B := v.length + (Fintype.card Q - 1)
    let a₀ := corankAt A hSync (2 * v.length + (Fintype.card Q - 1)) -
      (Fintype.card Q - (A.image Finset.univ v).card)
    maxBlockCoverDeg A v t ≤ blockJoinDeg A v (t + B) p₀ + a₀ := by
  classical
  intro B a₀
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (blockCoverDeg A v t)
  obtain ⟨w, hwlen, hweval⟩ := sc_exists_short_word hSC p₀ x
  let R := A.image Finset.univ v
  let I_vwv := A.image Finset.univ (v ++ w ++ v)
  have hI_sub : I_vwv ⊆ R := by
    intro r hr
    rw [DFA.mem_image] at hr ⊢
    obtain ⟨b, _, rfl⟩ := hr
    exact ⟨A.eval b (v ++ w), Finset.mem_univ _, by simp [DFA.eval_append]⟩
  have hI_corank : Fintype.card Q - I_vwv.card ≤ corankAt A hSync (2 * v.length + (Fintype.card Q - 1)) :=
    corank_le_corankAt A hSync (by rw [List.length_append, List.length_append]; omega)
  have hR_le_n : R.card ≤ Fintype.card Q := Finset.card_le_univ _
  have hI_le_R : I_vwv.card ≤ R.card := Finset.card_le_card hI_sub
  have hsdiff_le : (R \ I_vwv).card ≤ a₀ := by
    rw [Finset.card_sdiff_of_subset hI_sub]
    dsimp only [a₀, R] at hR_le_n hI_le_R ⊢
    omega
  have hCov_sub_R : blockCoverSet A v t x ⊆ R := Finset.filter_subset _ _
  have hsub_img : blockCoverSet A v t x ∩ I_vwv ⊆
      A.image (blockJoinNeighbors A v (t + B) p₀) (w ++ v) := by
    intro r hr
    rw [Finset.mem_inter] at hr
    obtain ⟨hrCov, hrI⟩ := hr
    have hr_sub : A.preimage {r} v ⊆ mergeNeighbors A t x := (Finset.mem_filter.mp hrCov).2
    rw [DFA.mem_image] at hrI
    obtain ⟨b₀, _, hb₀⟩ := hrI
    let q := A.eval b₀ v
    have hqR : q ∈ R := (DFA.mem_image A _ _ _).mpr ⟨b₀, Finset.mem_univ b₀, rfl⟩
    have hq_eval : A.eval q (w ++ v) = r := by
      dsimp only [q]; rw [← DFA.eval_append, ← List.append_assoc]; exact hb₀
    refine (DFA.mem_image A _ _ _).mpr ⟨q, ?_, hq_eval⟩
    simp only [blockJoinNeighbors, Finset.mem_filter]
    have hq_step : A.eval q w ∈ mergeNeighbors A t x := by
      apply hr_sub
      simp only [DFA.mem_preimage, Finset.mem_singleton]
      rw [← DFA.eval_append]; exact hq_eval
    have hq_ne_p₀ : q ≠ p₀ := by
      intro hqp
      have hne := ((mem_mergeNeighbors A t x (A.eval q w)).mp hq_step).1
      rw [hqp, hweval] at hne
      exact hne rfl
    refine ⟨hqR, hq_ne_p₀, fun a ha b hb => ?_⟩
    have hav : A.eval a v = p₀ := by simpa [DFA.mem_preimage] using ha
    have hbv : A.eval b v = q := by simpa [DFA.mem_preimage] using hb
    obtain ⟨_, u', hu'len, hu'eq⟩ := (mem_mergeNeighbors A t x (A.eval q w)).mp hq_step
    rw [mem_mergeNeighbors]
    refine ⟨fun hba => hq_ne_p₀ (by rw [← hbv, hba, hav]), (v ++ w) ++ u', ?_, ?_⟩
    · rw [List.length_append, List.length_append]; dsimp only [B]; omega
    · rw [DFA.eval_append, DFA.eval_append, DFA.eval_append, DFA.eval_append, hbv, hav, hweval]
      exact hu'eq
  have hinter_le : (blockCoverSet A v t x ∩ I_vwv).card ≤ blockJoinDeg A v (t + B) p₀ :=
    le_trans (Finset.card_le_card hsub_img) (A.card_image_le _ (w ++ v))
  have hcover_union : blockCoverSet A v t x ⊆ (blockCoverSet A v t x ∩ I_vwv) ∪ (R \ I_vwv) := by
    intro r hr
    by_cases hrI : r ∈ I_vwv
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hr, hrI⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hCov_sub_R hr, hrI⟩)
  have hcard_le : blockCoverDeg A v t x ≤ (blockCoverSet A v t x ∩ I_vwv).card + (R \ I_vwv).card :=
    le_trans (Finset.card_le_card hcover_union) (Finset.card_union_le _ _)
  dsimp only [maxBlockCoverDeg]
  rw [hx]
  omega

/-- Generic pigeonhole calm-step lemma for any monotone function `f : ℕ → ℕ` bounded by `n`. -/
private theorem exists_calm_step {f : ℕ → ℕ} {n step M start : ℕ}
    (hmono : ∀ t₁ t₂, t₁ ≤ t₂ → f t₁ ≤ f t₂) (hle : ∀ t, f t ≤ n) (hM : 1 ≤ M) :
    ∃ i < M, f (start + (i + 1) * step) - f (start + i * step) ≤ n / M := by
  by_contra hnone
  push Not at hnone
  have hsum_ge : M * (n / M + 1) ≤
      ∑ i ∈ Finset.range M, (f (start + (i + 1) * step) - f (start + i * step)) := by
    calc M * (n / M + 1)
        = ∑ _i ∈ Finset.range M, (n / M + 1) := by simp
      _ ≤ ∑ i ∈ Finset.range M, (f (start + (i + 1) * step) - f (start + i * step)) :=
          Finset.sum_le_sum fun i hi => hnone i (Finset.mem_range.mp hi)
  have htele : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, (f (start + (i + 1) * step) - f (start + i * step))) + f start =
      f (start + m * step) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hm : f (start + m * step) ≤ f (start + (m + 1) * step) :=
        hmono _ _ (by nlinarith)
      omega
  have htop := htele M
  have hfn := hle (start + M * step)
  have hdiv : n < M * (n / M + 1) := by
    have := Nat.lt_mul_div_succ n (by omega : 0 < M)
    linarith
  omega

/-- **Lemma 1.1(2b) — Single-Quantity Calm Time**:
For `M ≥ 1` and `T₀ ≥ (M + 1) * B`, there exists `q ∈ [T₀ - M * B, T₀]` with `B ≤ q` such that
`K_q ≤ deg_{Γ_q}(p₀) + a₀ + n / M` for ALL `p₀ ∈ Q·v`. -/
private theorem single_calm_time [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    (v : List α) {M T₀ : ℕ} (hM : 1 ≤ M)
    (hT₀ : (M + 1) * (v.length + (Fintype.card Q - 1)) ≤ T₀) :
    let B := v.length + (Fintype.card Q - 1)
    let a₀ := corankAt A hSync (2 * v.length + (Fintype.card Q - 1)) -
      (Fintype.card Q - (A.image Finset.univ v).card)
    ∃ q : ℕ, T₀ - M * B ≤ q ∧ q ≤ T₀ ∧ B ≤ q ∧
      ∀ p₀ ∈ A.image Finset.univ v,
        maxBlockCoverDeg A v q ≤ blockJoinDeg A v q p₀ + (a₀ + Fintype.card Q / M) := by
  intro B a₀
  let start := T₀ - M * B
  obtain ⟨i, hiM, hcalm⟩ := exists_calm_step (f := maxBlockCoverDeg A v)
    (n := Fintype.card Q) (step := B) (M := M) (start := start)
    (fun _ _ h => maxBlockCoverDeg_mono A v h) (maxBlockCoverDeg_le_card A v) hM
  let q := start + (i + 1) * B
  have hT₀' : M * B + B ≤ T₀ := by
    have : (M + 1) * B = M * B + B := by ring
    change (M + 1) * B ≤ T₀ at hT₀
    omega
  have hB_le_start : B ≤ start := by dsimp only [start]; omega
  have hq_le : q ≤ T₀ := by
    dsimp only [q, start]
    have : (i + 1) * B ≤ M * B := Nat.mul_le_mul_right B (by omega)
    omega
  refine ⟨q, by omega, hq_le, by omega, fun p₀ hp₀ => ?_⟩
  have htr := wholeBlock_transport A hSync hSC v (start + i * B) hp₀
  have hstep : start + i * B + B = q := by dsimp only [q]; ring
  change maxBlockCoverDeg A v (start + i * B) ≤ blockJoinDeg A v (start + i * B + B) p₀ + a₀ at htr
  rw [hstep] at htr
  have hq_eq : start + (i + 1) * B = q := rfl
  rw [hq_eq] at hcalm
  have hmono : maxBlockCoverDeg A v (start + i * B) ≤ maxBlockCoverDeg A v q :=
    maxBlockCoverDeg_mono A v (by dsimp only [q]; nlinarith)
  omega

/-- Helper: on any synchronizing DFA, `2 * q ≤ ∑ x, mergeDeg A q x` for `q < corankGap A hSync r`
and `r + 1 ≤ n - 1` (proved identically to `SubShitov.two_mul_le_sum_mergeDeg`, plus independent
set extraction). -/
private theorem exists_indep_and_sum_deg [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {r t : ℕ} (hr : r + 1 ≤ Fintype.card Q - 1)
    (ht : t < corankGap A hSync r) :
    (∃ S : Finset Q, S.card = Fintype.card Q - r ∧
      ∀ x ∈ S, ∀ y ∈ mergeNeighbors A t x, y ∉ S) ∧
    2 * t ≤ ∑ x : Q, mergeDeg A t x := by
  have hind : ∀ t' < corankGap A hSync r,
      ∃ S : Finset Q, S.card = Fintype.card Q - r ∧
        ∀ x ∈ S, ∀ y ∈ mergeNeighbors A t' x, y ∉ S := by
    intro t' ht'
    obtain ⟨u, hulen, hucard⟩ := minCorankLen_spec A hSync (by omega : r ≤ Fintype.card Q - 1)
    let S := A.image Finset.univ u
    have hS_le : S.card ≤ Fintype.card Q - r := hucard
    have hS_card : S.card = Fintype.card Q - r := by
      by_contra hne
      have hle : S.card ≤ Fintype.card Q - (r + 1) := by omega
      have hmin := minCorankLen_le A hSync hr hle
      dsimp only [corankGap] at ht'
      omega
    refine ⟨S, hS_card, fun x hx y hy hyS => ?_⟩
    rw [mem_mergeNeighbors] at hy
    obtain ⟨hyx, w, hwlen, hweq⟩ := hy
    have hcard_lt : (A.image S w).card < S.card := by
      have hsub : A.image S w ⊆ A.image (S.erase y) w := by
        intro z hz
        rw [DFA.mem_image] at hz ⊢
        obtain ⟨p, hpS, rfl⟩ := hz
        by_cases hpy : p = y
        · subst hpy
          exact ⟨x, Finset.mem_erase.mpr ⟨hyx.symm, hx⟩, hweq.symm⟩
        · exact ⟨p, Finset.mem_erase.mpr ⟨hpy, hpS⟩, rfl⟩
      calc (A.image S w).card
          ≤ (A.image (S.erase y) w).card := Finset.card_le_card hsub
        _ ≤ (S.erase y).card := A.card_image_le _ w
        _ < S.card := Finset.card_erase_lt_of_mem hyS
    have hnext : (A.image Finset.univ (u ++ w)).card ≤ Fintype.card Q - (r + 1) := by
      rw [DFA.image_append]; change (A.image S w).card ≤ Fintype.card Q - (r + 1); omega
    have hmin := minCorankLen_le A hSync hr hnext
    rw [List.length_append, hulen] at hmin
    have hmono := minCorankLen_mono A hSync (Nat.le_add_right r 1) hr
    dsimp only [corankGap] at ht'
    omega
  refine ⟨hind t ht, ?_⟩
  induction t with
  | zero => simp
  | succ s ih =>
    have ihs : 2 * s ≤ ∑ x : Q, mergeDeg A s x := ih (by omega)
    have hnot_stab : ∃ x y : Q, y ∈ mergeNeighbors A (s + 1) x ∧ y ∉ mergeNeighbors A s x := by
      by_contra hnone
      push Not at hnone
      have hstep : ∀ (w : List α) (x y : Q), x ≠ y → A.eval x w = A.eval y w →
          y ∈ mergeNeighbors A s x := by
        intro w
        induction w with
        | nil => intro x y hne heq; exact absurd heq hne
        | cons a w ihw =>
          intro x y hne heq
          rw [DFA.eval_cons, DFA.eval_cons] at heq
          by_cases h1 : A.step x a = A.step y a
          · refine hnone x y ((mem_mergeNeighbors A (s + 1) x y).mpr ⟨hne.symm, [a], by simp, ?_⟩)
            simpa using h1.symm
          · obtain ⟨_, v', hv'len, hv'eq⟩ :=
              (mem_mergeNeighbors A s (A.step x a) (A.step y a)).mp (ihw _ _ h1 heq)
            refine hnone x y ((mem_mergeNeighbors A (s + 1) x y).mpr ⟨hne.symm, a :: v', ?_, ?_⟩)
            · simp; omega
            · rw [DFA.eval_cons, DFA.eval_cons]; exact hv'eq
      rcases hSync with ⟨w_sync, q₀, hq₀⟩
      obtain ⟨S, hS_card, hSind⟩ := hind s (by omega)
      have hge2 : 1 < S.card := by omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hge2
      exact hSind x hx y (hstep w_sync x y hxy (by rw [hq₀ x, hq₀ y])) hy
    obtain ⟨x₀, y₀, hmem1, hnot0⟩ := hnot_stab
    have hne : x₀ ≠ y₀ := ((mem_mergeNeighbors A (s + 1) x₀ y₀).mp hmem1).1.symm
    have hmem1' : x₀ ∈ mergeNeighbors A (s + 1) y₀ := (mem_mergeNeighbors_symm A (s + 1) x₀ y₀).mp hmem1
    have hnot0' : x₀ ∉ mergeNeighbors A s y₀ := fun h => hnot0 ((mem_mergeNeighbors_symm A s x₀ y₀).mpr h)
    have hlt_x : mergeDeg A s x₀ + 1 ≤ mergeDeg A (s + 1) x₀ :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨mergeNeighbors_mono A (Nat.le_succ s) x₀, fun heq => hnot0 (heq ▸ hmem1)⟩)
    have hlt_y : mergeDeg A s y₀ + 1 ≤ mergeDeg A (s + 1) y₀ :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨mergeNeighbors_mono A (Nat.le_succ s) y₀, fun heq => hnot0' (heq ▸ hmem1')⟩)
    have hpair : ({x₀, y₀} : Finset Q) ⊆ Finset.univ := Finset.subset_univ _
    have hsplit_s : (∑ q : Q, mergeDeg A s q) =
        mergeDeg A s x₀ + mergeDeg A s y₀ + ∑ q ∈ Finset.univ \ {x₀, y₀}, mergeDeg A s q := by
      rw [← Finset.sum_sdiff hpair, Finset.sum_pair hne]; ring
    have hsplit_s1 : (∑ q : Q, mergeDeg A (s + 1) q) =
        mergeDeg A (s + 1) x₀ + mergeDeg A (s + 1) y₀ +
          ∑ q ∈ Finset.univ \ {x₀, y₀}, mergeDeg A (s + 1) q := by
      rw [← Finset.sum_sdiff hpair, Finset.sum_pair hne]; ring
    have hrest : (∑ q ∈ Finset.univ \ {x₀, y₀}, mergeDeg A s q) ≤
        ∑ q ∈ Finset.univ \ {x₀, y₀}, mergeDeg A (s + 1) q :=
      Finset.sum_le_sum fun q _ => Finset.card_le_card (mergeNeighbors_mono A (Nat.le_succ s) q)
    omega

/-- Singleton/non-singleton split of `∑ x, mergeDeg A q x` via `complement_deg_le`. -/
private theorem sum_mergeDeg_le_sing_nonsing [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (v : List α) (q : ℕ) :
    let n := Fintype.card Q
    let C := n - (A.image Finset.univ v).card
    (∑ x : Q, mergeDeg A q x) ≤
      n * maxBlockCoverDeg A v q + min (2 * C) n * (C + maxBlockCoverDeg A v q) := by
  classical
  intro n C
  let R := A.image Finset.univ v
  let S_sing : Finset Q := Finset.univ.filter (fun x => (A.preimage {A.eval x v} v).card = 1)
  have hS_sing_sum : (∑ x ∈ S_sing, mergeDeg A q x) ≤ n * maxBlockCoverDeg A v q := by
    have hrew : (∑ x ∈ S_sing, mergeDeg A q x) =
        ∑ y : Q, (S_sing.filter (fun x => y ∈ mergeNeighbors A q x)).card := by
      have h1 : ∀ x ∈ S_sing,
          mergeDeg A q x = ∑ y : Q, if y ∈ mergeNeighbors A q x then 1 else 0 := by
        intro x _
        simp [mergeDeg]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.card_filter]
    rw [hrew]
    calc (∑ y : Q, (S_sing.filter (fun x => y ∈ mergeNeighbors A q x)).card)
        ≤ ∑ _y : Q, maxBlockCoverDeg A v q := by
          refine Finset.sum_le_sum fun y _ => ?_
          let Ty := S_sing.filter (fun x => y ∈ mergeNeighbors A q x)
          have hinj : Set.InjOn (fun x => A.eval x v) (Ty : Set Q) := by
            intro x₁ hx₁ x₂ hx₂ heq
            have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx₁).1).2
            have hx₁_mem : x₁ ∈ A.preimage {A.eval x₁ v} v := by simp [DFA.mem_preimage]
            have hx₂_mem : x₂ ∈ A.preimage {A.eval x₁ v} v := by simp [DFA.mem_preimage, heq]
            obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h1
            rw [hz, Finset.mem_singleton] at hx₁_mem hx₂_mem
            exact hx₁_mem.trans hx₂_mem.symm
          have hsub_cov : A.image Ty v ⊆ blockCoverSet A v q y := by
            intro p hp
            rw [DFA.mem_image] at hp
            obtain ⟨x, hxTy, rfl⟩ := hp
            have hxS := (Finset.mem_filter.mp hxTy).1
            have hxy := (mem_mergeNeighbors_symm A q x y).mp (Finset.mem_filter.mp hxTy).2
            have hcard1 : (A.preimage {A.eval x v} v).card = 1 := (Finset.mem_filter.mp hxS).2
            refine Finset.mem_filter.mpr ⟨(DFA.mem_image A _ _ _).mpr ⟨x, Finset.mem_univ x, rfl⟩, ?_⟩
            intro z hz
            obtain ⟨z₀, hz₀⟩ := Finset.card_eq_one.mp hcard1
            have hx_mem : x ∈ A.preimage {A.eval x v} v := by simp [DFA.mem_preimage]
            rw [hz₀, Finset.mem_singleton] at hz hx_mem
            rw [hz, ← hx_mem]
            exact hxy
          have hcard_eq : (A.image Ty v).card = Ty.card := Finset.card_image_of_injOn hinj
          calc Ty.card = (A.image Ty v).card := hcard_eq.symm
            _ ≤ (blockCoverSet A v q y).card := Finset.card_le_card hsub_cov
            _ ≤ maxBlockCoverDeg A v q := Finset.le_sup (f := blockCoverDeg A v q) (Finset.mem_univ y)
      _ = n * maxBlockCoverDeg A v q := by simp [n]
  have hnonsing_le : (Finset.univ \ S_sing).card ≤ min (2 * C) n := by
    refine le_min ?_ (Finset.card_le_univ _)
    let R_sing := R.filter (fun p => (A.preimage {p} v).card = 1)
    have hpre_univ : A.preimage R v = Finset.univ := by
      ext x; simp only [DFA.mem_preimage, Finset.mem_univ, iff_true]
      exact (DFA.mem_image A _ _ _).mpr ⟨x, Finset.mem_univ x, rfl⟩
    have htot : n = ∑ p ∈ R, (A.preimage {p} v).card := by
      calc n = (Finset.univ : Finset Q).card := Finset.card_univ.symm
        _ = (A.preimage R v).card := by rw [hpre_univ]
        _ = ∑ p ∈ R, (A.preimage {p} v).card := A.card_preimage_eq_sum_singleton R v
    have hS_eq : S_sing = A.preimage R_sing v := by
      ext x
      simp only [S_sing, R_sing, DFA.mem_preimage, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨(DFA.mem_image A _ _ _).mpr ⟨x, Finset.mem_univ x, rfl⟩, h⟩, fun h => h.2⟩
    have hS_card : S_sing.card = R_sing.card := by
      rw [hS_eq, A.card_preimage_eq_sum_singleton]
      have h1 : (∑ p ∈ R_sing, (A.preimage {p} v).card) = ∑ _p ∈ R_sing, 1 :=
        Finset.sum_congr rfl fun p hp => (Finset.mem_filter.mp hp).2
      rw [h1]; simp
    have hR_sub : R_sing ⊆ R := Finset.filter_subset _ _
    have hsplit_R : (∑ p ∈ R, (A.preimage {p} v).card) =
        R_sing.card + ∑ p ∈ R \ R_sing, (A.preimage {p} v).card := by
      conv_lhs => rw [← Finset.union_sdiff_of_subset hR_sub]
      rw [Finset.sum_union Finset.disjoint_sdiff]
      congr 1
      rw [← A.card_preimage_eq_sum_singleton, ← hS_eq, hS_card]
    have hge2 : ∀ p ∈ R \ R_sing, 2 ≤ (A.preimage {p} v).card := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      have hpR := hp.1
      rw [DFA.mem_image] at hpR
      obtain ⟨x, _, hxv⟩ := hpR
      have hpos : 1 ≤ (A.preimage {p} v).card :=
        Finset.card_pos.mpr ⟨x, by simp [DFA.mem_preimage, hxv]⟩
      have hne1 : (A.preimage {p} v).card ≠ 1 := fun h1 =>
        hp.2 (Finset.mem_filter.mpr ⟨hp.1, h1⟩)
      omega
    have h2sub : (∑ p ∈ R \ R_sing, (A.preimage {p} v).card) ≤
        2 * (∑ p ∈ R \ R_sing, ((A.preimage {p} v).card - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => by have := hge2 p hp; omega
    have hsum_minus : (∑ p ∈ R \ R_sing, ((A.preimage {p} v).card - 1)) + (R \ R_sing).card =
        ∑ p ∈ R \ R_sing, (A.preimage {p} v).card := by
      have h1 : (∑ p ∈ R \ R_sing, ((A.preimage {p} v).card - 1 + 1)) =
          ∑ p ∈ R \ R_sing, (A.preimage {p} v).card :=
        Finset.sum_congr rfl fun p hp => by have := hge2 p hp; omega
      rw [Finset.sum_add_distrib] at h1
      simpa using h1
    have hRsdiff : (R \ R_sing).card = R.card - R_sing.card := Finset.card_sdiff_of_subset hR_sub
    have hRle : R_sing.card ≤ R.card := Finset.card_le_card hR_sub
    have hRle_n : R.card ≤ n := Finset.card_le_univ _
    have hSsdiff : (Finset.univ \ S_sing).card = n - S_sing.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hC_eq : C = n - R.card := rfl
    omega
  have hnonsing_sum : (∑ z ∈ Finset.univ \ S_sing, mergeDeg A q z) ≤
      min (2 * C) n * (C + maxBlockCoverDeg A v q) := by
    calc (∑ z ∈ Finset.univ \ S_sing, mergeDeg A q z)
        ≤ ∑ _z ∈ Finset.univ \ S_sing, (C + maxBlockCoverDeg A v q) := by
          refine Finset.sum_le_sum fun z _ => ?_
          have hc := complement_deg_le A v q z
          have hk : blockCoverDeg A v q z ≤ maxBlockCoverDeg A v q :=
            Finset.le_sup (f := blockCoverDeg A v q) (Finset.mem_univ z)
          change mergeDeg A q z ≤ C + blockCoverDeg A v q z at hc
          omega
      _ = (Finset.univ \ S_sing).card * (C + maxBlockCoverDeg A v q) := by simp
      _ ≤ min (2 * C) n * (C + maxBlockCoverDeg A v q) := Nat.mul_le_mul_right _ hnonsing_le
  have hsplit : (∑ x : Q, mergeDeg A q x) =
      (∑ x ∈ S_sing, mergeDeg A q x) + (∑ z ∈ Finset.univ \ S_sing, mergeDeg A q z) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ S_sing), add_comm]
  omega

/-- **Lemma 1.1(3) — Singularity-Free Block Compression Cap**:
On any strongly connected synchronizing DFA, for every word `v` of corank `C = n - |Q·v|`,
every `M ≥ 1`, and every `r` with `r + 1 ≤ n - 1` and `2 * (n - r) > n - C`:
`δ(r) ≤ min(C², n C / 2) + (n / 2 + min(C, n / 2)) * (b * η₀ / (2b - (n - C))) + Ω`. -/
theorem singularityFree_compression_cap [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    (v : List α) {r M : ℕ} (hr : r + 1 ≤ Fintype.card Q - 1) (hM : 1 ≤ M)
    (h2b : (A.image Finset.univ v).card < 2 * (Fintype.card Q - r)) :
    let n := Fintype.card Q
    let C := n - (A.image Finset.univ v).card
    let b := n - r
    let B := v.length + (n - 1)
    let Ω := (M + 1) * B + 1
    let a₀ := corankAt A hSync (2 * v.length + (n - 1)) - C
    let η₀ := a₀ + n / M
    (corankGap A hSync r : ℚ) ≤
      min ((C : ℚ) ^ 2) ((n : ℚ) * (C : ℚ) / 2) +
      ((n : ℚ) / 2 + min (C : ℚ) ((n : ℚ) / 2)) *
        ((b : ℚ) * (η₀ : ℚ) / (2 * (b : ℚ) - ((n : ℚ) - (C : ℚ)))) +
      (Ω : ℚ) := by
  classical
  intro n C b B Ω a₀ η₀
  let R := A.image Finset.univ v
  have hR_le_n : R.card ≤ n := Finset.card_le_univ _
  have hden_pos : (0 : ℚ) < 2 * (b : ℚ) - ((n : ℚ) - (C : ℚ)) := by
    have hnat : R.card < 2 * b := h2b
    have hq : (R.card : ℚ) < 2 * (b : ℚ) := by exact_mod_cast hnat
    have hC_eq : (n : ℚ) - (C : ℚ) = (R.card : ℚ) := by
      have : C = n - R.card := rfl
      rw [this, Nat.cast_sub hR_le_n]; ring
    linarith
  -- Trivial case: δ(r) ≤ Ω
  by_cases hsmall : corankGap A hSync r ≤ Ω
  · have hq : (corankGap A hSync r : ℚ) ≤ (Ω : ℚ) := by exact_mod_cast hsmall
    have ht1 : (0 : ℚ) ≤ min ((C : ℚ) ^ 2) ((n : ℚ) * (C : ℚ) / 2) :=
      le_min (sq_nonneg _) (by positivity)
    have ht2 : (0 : ℚ) ≤ ((n : ℚ) / 2 + min (C : ℚ) ((n : ℚ) / 2)) *
        ((b : ℚ) * (η₀ : ℚ) / (2 * (b : ℚ) - ((n : ℚ) - (C : ℚ)))) := by
      have hmin : (0 : ℚ) ≤ min (C : ℚ) ((n : ℚ) / 2) := le_min (Nat.cast_nonneg _) (by positivity)
      positivity
    linarith
  -- Main case: T₀ = δ(r) - 1 ≥ (M + 1) * B
  · have hT₀ : (M + 1) * B ≤ corankGap A hSync r - 1 := by dsimp only [Ω] at hsmall; omega
    obtain ⟨q, hq_lo, hq_hi, hB_le_q, hcalm⟩ := single_calm_time A hSync hSC v hM hT₀
    have hq_lt : q < corankGap A hSync r := by omega
    obtain ⟨⟨S, hS_card, hSind⟩, h2q_sum⟩ := exists_indep_and_sum_deg A hSync hr hq_lt
    -- S injects into R via v, forming an independent set I of size b in Γ_q
    have hv_le_q : v.length ≤ q := by omega
    have hinj_S : Set.InjOn (fun x => A.eval x v) (S : Set Q) := by
      intro x hx y hy hxy
      by_contra hne
      exact hSind x hx y ((mem_mergeNeighbors A q x y).mpr ⟨Ne.symm hne, v, hv_le_q, hxy.symm⟩) hy
    let I := A.image S v
    have hI_card : I.card = b := by
      dsimp only [I, DFA.image]; rw [Finset.card_image_of_injOn hinj_S, hS_card]
    have hI_sub : I ⊆ R := A.image_mono (Finset.subset_univ S) v
    have hI_ind : ∀ p ∈ I, ∀ p' ∈ blockJoinNeighbors A v q p, p' ∉ I := by
      intro p hp p' hp' hp'I
      rw [DFA.mem_image] at hp hp'I
      obtain ⟨x, hxS, rfl⟩ := hp
      obtain ⟨y, hyS, rfl⟩ := hp'I
      have hjoin := (Finset.mem_filter.mp hp').2.2
      exact hSind x hxS y (hjoin x (by simp [DFA.mem_preimage]) y (by simp [DFA.mem_preimage])) hyS
    have hjoin_symm : ∀ p ∈ R, ∀ p' ∈ R,
        p' ∈ blockJoinNeighbors A v q p ↔ p ∈ blockJoinNeighbors A v q p' := by
      intro p hpR p' hp'R
      simp only [blockJoinNeighbors, Finset.mem_filter]
      constructor
      · rintro ⟨_, hne, hall⟩
        exact ⟨hpR, hne.symm, fun a ha b hb => (mem_mergeNeighbors_symm A q b a).mp (hall b hb a ha)⟩
      · rintro ⟨_, hne, hall⟩
        exact ⟨hp'R, hne.symm, fun a ha b hb => (mem_mergeNeighbors_symm A q b a).mp (hall b hb a ha)⟩
    have hjoin_le_K : ∀ p' ∈ R, blockJoinDeg A v q p' ≤ maxBlockCoverDeg A v q := by
      intro p' hp'R
      rw [DFA.mem_image] at hp'R
      obtain ⟨z, _, hzv⟩ := hp'R
      have hsub : blockJoinNeighbors A v q p' ⊆ blockCoverSet A v q z := by
        intro p hp
        simp only [blockJoinNeighbors, blockCoverSet, Finset.mem_filter] at hp ⊢
        refine ⟨hp.1, fun b hb => hp.2.2 z (by simp [DFA.mem_preimage, hzv]) b hb⟩
      exact le_trans (Finset.card_le_card hsub)
        (Finset.le_sup (f := blockCoverDeg A v q) (Finset.mem_univ z))
    let K := maxBlockCoverDeg A v q
    -- Double count block-join edges between I and R \ I
    have hsum_I_ge : b * K ≤ (∑ p ∈ I, blockJoinDeg A v q p) + b * η₀ := by
      have h1 : ∀ p ∈ I, K ≤ blockJoinDeg A v q p + η₀ := fun p hp => hcalm p (hI_sub hp)
      have hsum := Finset.sum_le_sum h1
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
        hI_card] at hsum
      exact hsum
    have hsum_I_le : (∑ p ∈ I, blockJoinDeg A v q p) ≤ (R.card - b) * K := by
      have hrew : ∀ p ∈ I, blockJoinDeg A v q p =
          ∑ p' ∈ R \ I, if p' ∈ blockJoinNeighbors A v q p then 1 else 0 := by
        intro p hp
        rw [← Finset.card_filter]
        have hfilt : (R \ I).filter (fun p' => p' ∈ blockJoinNeighbors A v q p) =
            blockJoinNeighbors A v q p := by
          ext p'
          simp only [Finset.mem_filter, Finset.mem_sdiff]
          constructor
          · exact fun h => h.2
          · intro hmem
            have hp'R : p' ∈ R := (Finset.mem_filter.mp hmem).1
            exact ⟨⟨hp'R, hI_ind p hp p' hmem⟩, hmem⟩
        rw [hfilt]; rfl
      calc (∑ p ∈ I, blockJoinDeg A v q p)
          = ∑ p ∈ I, ∑ p' ∈ R \ I, if p' ∈ blockJoinNeighbors A v q p then 1 else 0 :=
            Finset.sum_congr rfl hrew
        _ = ∑ p' ∈ R \ I, ∑ p ∈ I, if p' ∈ blockJoinNeighbors A v q p then 1 else 0 :=
            Finset.sum_comm
        _ ≤ ∑ p' ∈ R \ I, blockJoinDeg A v q p' := by
            refine Finset.sum_le_sum fun p' hp' => ?_
            have hp'R : p' ∈ R := (Finset.mem_sdiff.mp hp').1
            rw [← Finset.card_filter]
            refine Finset.card_le_card fun p hp => ?_
            rw [Finset.mem_filter] at hp
            exact (hjoin_symm p (hI_sub hp.1) p' hp'R).mp hp.2
        _ ≤ ∑ _p' ∈ R \ I, K :=
            Finset.sum_le_sum fun p' hp' => hjoin_le_K p' (Finset.mem_sdiff.mp hp').1
        _ = (R \ I).card * K := by simp
        _ = (R.card - b) * K := by rw [Finset.card_sdiff_of_subset hI_sub, hI_card]
    have h2b' : R.card < 2 * b := h2b
    have hK_nat : (2 * b - R.card) * K ≤ b * η₀ := by
      have hI_le_R : b ≤ R.card := by rw [← hI_card]; exact Finset.card_le_card hI_sub
      zify [hI_le_R, show R.card ≤ 2 * b by omega] at hsum_I_ge hsum_I_le ⊢
      nlinarith
    have hK_q : (K : ℚ) ≤ (b : ℚ) * (η₀ : ℚ) / (2 * (b : ℚ) - ((n : ℚ) - (C : ℚ))) := by
      rw [le_div_iff₀ hden_pos]
      have hcast : (((2 * b - R.card) * K : ℕ) : ℚ) ≤ ((b * η₀ : ℕ) : ℚ) := by
        exact_mod_cast hK_nat
      have hR_eq : (R.card : ℚ) = (n : ℚ) - (C : ℚ) := by
        have : C = n - R.card := rfl
        rw [this, Nat.cast_sub hR_le_n]; ring
      rw [Nat.cast_mul, Nat.cast_sub (by omega : R.card ≤ 2 * b), Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_mul, hR_eq] at hcast
      linarith
    -- Combine 2 * q ≤ n * K + min (2 * C) n * (C + K) and δ(r) ≤ q + Ω
    have hsum_deg := sum_mergeDeg_le_sing_nonsing A v q
    have h2q_nat : 2 * q ≤ n * K + min (2 * C) n * (C + K) := le_trans h2q_sum hsum_deg
    have h2q_q : (2 : ℚ) * (q : ℚ) ≤ (n : ℚ) * (K : ℚ) +
        (min (2 * C) n : ℕ) * ((C : ℚ) + (K : ℚ)) := by
      have hcast : ((2 * q : ℕ) : ℚ) ≤ ((n * K + min (2 * C) n * (C + K) : ℕ) : ℚ) := by
        exact_mod_cast h2q_nat
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_add]
        at hcast
      exact hcast
    have hmin_eq : ((min (2 * C) n : ℕ) : ℚ) = 2 * min (C : ℚ) ((n : ℚ) / 2) := by
      by_cases hcmp : 2 * C ≤ n
      · rw [min_eq_left hcmp]
        have hq : (C : ℚ) ≤ (n : ℚ) / 2 := by
          have : (2 : ℚ) * C ≤ n := by exact_mod_cast hcmp
          linarith
        rw [min_eq_left hq]; push_cast; ring
      · rw [min_eq_right (by omega : n ≤ 2 * C)]
        have hq : (n : ℚ) / 2 ≤ (C : ℚ) := by
          have : (n : ℚ) ≤ 2 * C := by exact_mod_cast (by omega : n ≤ 2 * C)
          linarith
        rw [min_eq_right hq]; ring
    have hmin_mul : min (C : ℚ) ((n : ℚ) / 2) * (C : ℚ) =
        min ((C : ℚ) ^ 2) ((n : ℚ) * (C : ℚ) / 2) := by
      by_cases hcmp : (C : ℚ) ≤ (n : ℚ) / 2
      · rw [min_eq_left hcmp, min_eq_left (by nlinarith)]; ring
      · rw [min_eq_right (by linarith), min_eq_right (by nlinarith)]; ring
    have hq_bound : (q : ℚ) ≤ min ((C : ℚ) ^ 2) ((n : ℚ) * (C : ℚ) / 2) +
        ((n : ℚ) / 2 + min (C : ℚ) ((n : ℚ) / 2)) *
          ((b : ℚ) * (η₀ : ℚ) / (2 * (b : ℚ) - ((n : ℚ) - (C : ℚ)))) := by
      rw [hmin_eq] at h2q_q
      have hcoef_nonneg : (0 : ℚ) ≤ (n : ℚ) / 2 + min (C : ℚ) ((n : ℚ) / 2) := by
        have : (0 : ℚ) ≤ min (C : ℚ) ((n : ℚ) / 2) := le_min (Nat.cast_nonneg _) (by positivity)
        positivity
      have hmul := mul_le_mul_of_nonneg_left hK_q hcoef_nonneg
      linarith only [h2q_q, hmin_mul, hmul]
    have hgap_le_q : corankGap A hSync r ≤ q + Ω := by
      have hΩ_ge : M * (v.length + (Fintype.card Q - 1)) + 1 ≤ Ω := by
        dsimp only [Ω, B, n]
        have : M * (v.length + (Fintype.card Q - 1)) ≤ (M + 1) * (v.length + (Fintype.card Q - 1)) :=
          Nat.mul_le_mul_right _ (Nat.le_succ M)
        omega
      omega
    have hgap_q : (corankGap A hSync r : ℚ) ≤ (q : ℚ) + (Ω : ℚ) := by exact_mod_cast hgap_le_q
    linarith only [hgap_q, hq_bound]

end SingularityFreeCap

/-! ## Part 2: Zero-`√2` Rational Payment Lemma & Exact Cubic Strip Comparison -/

section RationalPaymentCerts

private theorem six_mul_sum_range_choose_two (m : ℕ) :
    6 * ∑ r ∈ Finset.range m, (r + 2).choose 2 = m * (m + 1) * (m + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    have hch : 2 * (m + 2).choose 2 = (m + 2) * (m + 1) := by
      rw [Nat.choose_two_right]
      rcases (Nat.even_mul_succ_self (m + 1)).two_dvd with ⟨t, ht⟩
      have hsub : m + 2 - 1 = m + 1 := by omega
      rw [hsub, show (m + 2) * (m + 1) = 2 * t by linarith]
      omega
    linarith

private theorem six_mul_sum_Ico_choose_two {a b : ℕ} (hab : a ≤ b) :
    6 * ∑ r ∈ Finset.Ico a b, (r + 2).choose 2 =
      b * (b + 1) * (b + 2) - a * (a + 1) * (a + 2) := by
  have hsplit : (∑ r ∈ Finset.range a, (r + 2).choose 2) +
      (∑ r ∈ Finset.Ico a b, (r + 2).choose 2) =
      ∑ r ∈ Finset.range b, (r + 2).choose 2 := by
    rw [← Finset.sum_union]
    · congr 1
      ext x; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
    · rw [Finset.disjoint_left]
      intro x h1 h2; rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
  have ha := six_mul_sum_range_choose_two a
  have hb := six_mul_sum_range_choose_two b
  omega

/-- Shitov prefix weight `W(x) = 1/16` (`x ≤ 1/4`) or `x(1/2 - x)` (`x > 1/4`). -/
private def W_fun (x : ℚ) : ℚ :=
  if x ≤ 1 / 4 then 1 / 16 else x * (1 / 2 - x)

/-- Combined prefix payment `p(c, x) = min(c²(1/2 - x), 2(x - c)_+ W(x))`. -/
private def pay_fun (c x : ℚ) : ℚ :=
  min (c ^ 2 * (1 / 2 - x)) (2 * max (x - c) 0 * W_fun x)

/-- Zero-`√2` rational lower completion saving `S_rat(c)` (using `17/12 > √2`). -/
private def S_rat (c : ℚ) : ℚ :=
  let a := max (1 / 2 : ℚ) ((17 / 12 : ℚ) * c)
  let b := (1 + c) / 2
  (b ^ 3 - a ^ 3) / 6 - c ^ 2 * (b - a)

private theorem pay_fun_le_lo {c x : ℚ} (hc1 : c ≤ 1 / 2) :
    pay_fun c x ≤ c ^ 2 * (1 / 2 - c) / (1 + 8 * c ^ 2) := by
  have hden : (0 : ℚ) < 1 + 8 * c ^ 2 := by positivity
  by_cases hxc : x ≤ c
  · have hmax0 : max (x - c) 0 = 0 := max_eq_right (by linarith)
    have hle0 : pay_fun c x ≤ 0 := by
      dsimp only [pay_fun]; rw [hmax0]; simp
    have hrhs : (0 : ℚ) ≤ c ^ 2 * (1 / 2 - c) / (1 + 8 * c ^ 2) := by
      have : (0 : ℚ) ≤ 1 / 2 - c := by linarith
      positivity
    linarith
  · have hW : W_fun x ≤ 1 / 16 := by
      dsimp only [W_fun]
      split_ifs
      · exact le_rfl
      · nlinarith [sq_nonneg (x - 1 / 4)]
    have h1 : pay_fun c x ≤ c ^ 2 * (1 / 2 - x) := min_le_left _ _
    have h2 : pay_fun c x ≤ (x - c) / 8 := by
      have hm : pay_fun c x ≤ 2 * max (x - c) 0 * W_fun x := min_le_right _ _
      rw [max_eq_left (by linarith : (0 : ℚ) ≤ x - c)] at hm
      have hmul := mul_le_mul_of_nonneg_left hW (show (0 : ℚ) ≤ 2 * (x - c) by linarith)
      linarith
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg c]

private theorem pay_fun_le_amgm {c x : ℚ} (hc : 1 / 3 ≤ c) (_hc1 : c ≤ 1 / 2)
    (_hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    pay_fun c x ≤ (1 / 4 : ℚ) * (1 / 2 - c) ^ 2 := by
  by_cases hxc : x ≤ c
  · have hmax0 : max (x - c) 0 = 0 := max_eq_right (by linarith)
    have hle0 : pay_fun c x ≤ 0 := by dsimp only [pay_fun]; rw [hmax0]; simp
    have hrhs : (0 : ℚ) ≤ (1 / 4 : ℚ) * (1 / 2 - c) ^ 2 := by positivity
    linarith
  · have hgt : ¬ x ≤ 1 / 4 := by linarith
    have hW : W_fun x = x * (1 / 2 - x) := by simp only [W_fun, hgt, ↓reduceIte]
    have hm : pay_fun c x ≤ 2 * max (x - c) 0 * W_fun x := min_le_right _ _
    rw [max_eq_left (by linarith : (0 : ℚ) ≤ x - c), hW] at hm
    have h1 : 2 * (x - c) * (x * (1 / 2 - x)) ≤ (x - c) * (1 / 2 - x) := by
      have : (0 : ℚ) ≤ (x - c) * (1 / 2 - x) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have h2 : (x - c) * (1 / 2 - x) ≤ (1 / 4 : ℚ) * (1 / 2 - c) ^ 2 := by
      nlinarith [sq_nonneg (x - (1 / 2 + c) / 2)]
    linarith

private theorem S_rat_eq_lo {c : ℚ} (hc : c ≤ 6 / 17) :
    S_rat c = (3 * c + 3 * c ^ 2 - 23 * c ^ 3) / 48 := by
  dsimp only [S_rat]
  rw [max_eq_left (by linarith : (17 / 12 : ℚ) * c ≤ 1 / 2)]
  ring

private theorem S_rat_eq_hi {c : ℚ} (hc : 6 / 17 ≤ c) :
    S_rat c = (((1 + c) / 2) ^ 3 - ((17 / 12 : ℚ) * c) ^ 3) / 6 -
      c ^ 2 * ((1 + c) / 2 - (17 / 12 : ℚ) * c) := by
  dsimp only [S_rat]
  rw [max_eq_right (by linarith : (1 / 2 : ℚ) ≤ (17 / 12 : ℚ) * c)]

private theorem bernstein_mid_sub {c : ℚ} (hc1 : 1 / 3 ≤ c) (hc2 : c ≤ 6 / 17) :
    (1 / 400 : ℚ) ≤ S_rat c - (1 / 4 : ℚ) * (1 / 2 - c) ^ 2 := by
  rw [S_rat_eq_lo hc2]
  let t : ℚ := 51 * (c - 1 / 3)
  let u : ℚ := 1 - t
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have hu0 : 0 ≤ u := by dsimp only [u, t]; linarith
  have hid :
      (3 * c + 3 * c ^ 2 - 23 * c ^ 3) / 48 - (1 / 4 : ℚ) * (1 / 2 - c) ^ 2 - 1 / 400 =
      (19 / 32400 : ℚ) * u ^ 3 + 3 * (47 / 61200 : ℚ) * t * u ^ 2 +
      3 * (899 / 1040400 : ℚ) * t ^ 2 * u + (6848 / 7860800 : ℚ) * t ^ 3 := by
    dsimp only [u, t]; ring
  have hnonneg : (0 : ℚ) ≤
      (19 / 32400 : ℚ) * u ^ 3 + 3 * (47 / 61200 : ℚ) * t * u ^ 2 +
      3 * (899 / 1040400 : ℚ) * t ^ 2 * u + (6848 / 7860800 : ℚ) * t ^ 3 := by positivity
  linarith

private theorem bernstein_hi_sub {c : ℚ} (hc1 : 6 / 17 ≤ c) (hc2 : c ≤ 1 / 2) :
    (55 / 82944 : ℚ) ≤ S_rat c - (1 / 4 : ℚ) * (1 / 2 - c) ^ 2 := by
  rw [S_rat_eq_hi hc1]
  let t : ℚ := (34 / 5) * (c - 6 / 17)
  let u : ℚ := 1 - t
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have hu0 : 0 ≤ u := by dsimp only [u, t]; linarith
  have hid :
      (((1 + c) / 2) ^ 3 - ((17 / 12 : ℚ) * c) ^ 3) / 6 -
        c ^ 2 * ((1 + c) / 2 - (17 / 12 : ℚ) * c) -
        (1 / 4 : ℚ) * (1 / 2 - c) ^ 2 - 55 / 82944 =
      ((265 / 78608 - 55 / 82944) : ℚ) * u ^ 3 +
      3 * ((565 / 166464 - 55 / 82944) : ℚ) * t * u ^ 2 +
      3 * ((235 / 117504 - 55 / 82944) : ℚ) * t ^ 2 * u := by
    dsimp only [u, t]; ring
  have hcA : (0 : ℚ) ≤ 265 / 78608 - 55 / 82944 := by norm_num
  have hcB : (0 : ℚ) ≤ 565 / 166464 - 55 / 82944 := by norm_num
  have hcC : (0 : ℚ) ≤ 235 / 117504 - 55 / 82944 := by norm_num
  have hnonneg : (0 : ℚ) ≤
      ((265 / 78608 - 55 / 82944) : ℚ) * u ^ 3 +
      3 * ((565 / 166464 - 55 / 82944) : ℚ) * t * u ^ 2 +
      3 * ((235 / 117504 - 55 / 82944) : ℚ) * t ^ 2 * u := by positivity
  linarith

/-- **Lemma 1.2(1a)**: For ALL `c ∈ [0, 1/2]` and `x ∈ [0, 1/2]`, `S_rat(c) - p(c, x) ≥ c / 1500`. -/
private theorem rational_payment_ge {c x : ℚ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    c / 1500 ≤ S_rat c - pay_fun c x := by
  by_cases h1 : c ≤ 1 / 3
  · have hpay := pay_fun_le_lo (x := x) hc1
    rw [S_rat_eq_lo (by linarith)]
    let t : ℚ := 3 * c
    let u : ℚ := 1 - t
    have ht0 : 0 ≤ t := by dsimp only [t]; linarith
    have hu0 : 0 ≤ u := by dsimp only [u, t]; linarith
    have hQ_id :
        (1 + 8 * c ^ 2) * (3 + 3 * c - 23 * c ^ 2) - 48 * c * (1 / 2 - c) - 5 / 81 =
        (238 / 81 : ℚ) * u ^ 4 + (385 / 81 : ℚ) * t * u ^ 3 +
        (168 / 81 : ℚ) * t ^ 2 * u ^ 2 + (205 / 81 : ℚ) * t ^ 3 * u := by
      dsimp only [u, t]; ring
    have hQ_ge : (5 / 81 : ℚ) ≤
        (1 + 8 * c ^ 2) * (3 + 3 * c - 23 * c ^ 2) - 48 * c * (1 / 2 - c) := by
      have : (0 : ℚ) ≤ (238 / 81 : ℚ) * u ^ 4 + (385 / 81 : ℚ) * t * u ^ 3 +
          (168 / 81 : ℚ) * t ^ 2 * u ^ 2 + (205 / 81 : ℚ) * t ^ 3 * u := by positivity
      linarith
    have hden_pos : (0 : ℚ) < 48 * (1 + 8 * c ^ 2) := by positivity
    have hden_le : 48 * (1 + 8 * c ^ 2) ≤ 48 * (17 / 9 : ℚ) := by nlinarith
    have hdiff_eq :
        48 * (1 + 8 * c ^ 2) *
          ((3 * c + 3 * c ^ 2 - 23 * c ^ 3) / 48 - c ^ 2 * (1 / 2 - c) / (1 + 8 * c ^ 2)) =
        c * ((1 + 8 * c ^ 2) * (3 + 3 * c - 23 * c ^ 2) - 48 * c * (1 / 2 - c)) := by
      have hne : 1 + 8 * c ^ 2 ≠ 0 := by positivity
      field_simp
    have hmul_ge : 48 * (1 + 8 * c ^ 2) * (c / 1500) ≤
        48 * (1 + 8 * c ^ 2) *
          ((3 * c + 3 * c ^ 2 - 23 * c ^ 3) / 48 - c ^ 2 * (1 / 2 - c) / (1 + 8 * c ^ 2)) := by
      rw [hdiff_eq]
      have hA : c * (5 / 81 : ℚ) ≤
          c * ((1 + 8 * c ^ 2) * (3 + 3 * c - 23 * c ^ 2) - 48 * c * (1 / 2 - c)) :=
        mul_le_mul_of_nonneg_left hQ_ge hc0
      nlinarith
    have hmain := le_of_mul_le_mul_left hmul_ge hden_pos
    linarith
  · by_cases h2 : c ≤ 6 / 17
    · have hpay := pay_fun_le_amgm (by linarith) hc1 hx0 hx1
      have hbern := bernstein_mid_sub (by linarith) h2
      linarith
    · have hpay := pay_fun_le_amgm (by linarith) hc1 hx0 hx1
      have hbern := bernstein_hi_sub (by linarith) hc1
      linarith

/-- **Lemma 1.2(1b)**: For ALL `c ∈ [1/10, 1/2]` and `x ∈ [0, 1/2]`, `S_rat(c) - p(c, x) ≥ 1/5000`. -/
private theorem rational_payment_ge_mid {c x : ℚ} (hc0 : 1 / 10 ≤ c) (hc1 : c ≤ 1 / 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (1 / 5000 : ℚ) ≤ S_rat c - pay_fun c x := by
  by_cases h1 : c ≤ 1 / 3
  · have hpay := pay_fun_le_lo (x := x) hc1
    rw [S_rat_eq_lo (by linarith)]
    let t : ℚ := (30 / 7) * (c - 1 / 10)
    let u : ℚ := 1 - t
    have ht0 : 0 ≤ t := by dsimp only [t]; linarith
    have hu0 : 0 ≤ u := by dsimp only [u, t]; linarith
    have hQ_id :
        c * ((1 + 8 * c ^ 2) * (3 + 3 * c - 23 * c ^ 2) - 48 * c * (1 / 2 - c)) -
          (48 / 5000 : ℚ) * (1 + 8 * c ^ 2) =
        (16149 / 125000 : ℚ) * u ^ 5 + 5 * (132433 / 937500 : ℚ) * t * u ^ 4 +
        10 * (1309903 / 11250000 : ℚ) * t ^ 2 * u ^ 3 +
        10 * (148757 / 1406250 : ℚ) * t ^ 3 * u ^ 2 +
        5 * (151949 / 1265625 : ℚ) * t ^ 4 * u + (371 / 151875 : ℚ) * t ^ 5 := by
      dsimp only [u, t]; ring
    have hQ_ge : (0 : ℚ) ≤
        c * ((1 + 8 * c ^ 2) * (3 + 3 * c - 23 * c ^ 2) - 48 * c * (1 / 2 - c)) -
          (48 / 5000 : ℚ) * (1 + 8 * c ^ 2) := by
      rw [hQ_id]; positivity
    have hden_pos : (0 : ℚ) < 48 * (1 + 8 * c ^ 2) := by positivity
    have hdiff_eq :
        48 * (1 + 8 * c ^ 2) *
          ((3 * c + 3 * c ^ 2 - 23 * c ^ 3) / 48 - c ^ 2 * (1 / 2 - c) / (1 + 8 * c ^ 2) -
            1 / 5000) =
        c * ((1 + 8 * c ^ 2) * (3 + 3 * c - 23 * c ^ 2) - 48 * c * (1 / 2 - c)) -
          (48 / 5000 : ℚ) * (1 + 8 * c ^ 2) := by
      have hne : 1 + 8 * c ^ 2 ≠ 0 := by positivity
      field_simp
    have hge0 : (0 : ℚ) ≤
        (3 * c + 3 * c ^ 2 - 23 * c ^ 3) / 48 - c ^ 2 * (1 / 2 - c) / (1 + 8 * c ^ 2) - 1 / 5000 := by
      have hmul : (0 : ℚ) ≤ 48 * (1 + 8 * c ^ 2) *
          ((3 * c + 3 * c ^ 2 - 23 * c ^ 3) / 48 - c ^ 2 * (1 / 2 - c) / (1 + 8 * c ^ 2) -
            1 / 5000) := by rw [hdiff_eq]; exact hQ_ge
      nlinarith
    linarith
  · by_cases h2 : c ≤ 6 / 17
    · have hpay := pay_fun_le_amgm (by linarith) hc1 hx0 hx1
      have hbern := bernstein_mid_sub (by linarith) h2
      linarith
    · have hpay := pay_fun_le_amgm (by linarith) hc1 hx0 hx1
      have hbern := bernstein_hi_sub (by linarith) hc1
      linarith

/-- **Lemma 1.2(2)**: For ALL `c ∈ [1/2, 505/1000]`, the zero-singleton cap saves `≥ 55/82944`. -/
private theorem rational_payment_ge_hi {c : ℚ} (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 505 / 1000) :
    let a := (17 / 12 : ℚ) * c
    let b := (1 + c) / 2
    (55 / 82944 : ℚ) ≤ (c ^ 3 - 1 / 8) / 6 + ((b ^ 3 - a ^ 3) / 6 - (c / 2) * (b - a)) := by
  intro a b
  let t : ℚ := 200 * (c - 1 / 2)
  let u : ℚ := 1 - t
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have hu0 : 0 ≤ u := by dsimp only [u, t]; linarith
  have hid :
      (c ^ 3 - 1 / 8) / 6 + ((b ^ 3 - a ^ 3) / 6 - (c / 2) * (b - a)) - 55 / 82944 =
      3 * ((7139 / 8294400 - 55 / 82944) : ℚ) * t * u ^ 2 +
      3 * ((878431 / 829440000 - 55 / 82944) : ℚ) * t ^ 2 * u +
      ((104356331 / 82944000000 - 55 / 82944) : ℚ) * t ^ 3 := by
    dsimp only [a, b, u, t]; ring
  have hcA : (0 : ℚ) ≤ 7139 / 8294400 - 55 / 82944 := by norm_num
  have hcB : (0 : ℚ) ≤ 878431 / 829440000 - 55 / 82944 := by norm_num
  have hcC : (0 : ℚ) ≤ 104356331 / 82944000000 - 55 / 82944 := by norm_num
  have hnonneg : (0 : ℚ) ≤
      3 * ((7139 / 8294400 - 55 / 82944) : ℚ) * t * u ^ 2 +
      3 * ((878431 / 829440000 - 55 / 82944) : ℚ) * t ^ 2 * u +
      ((104356331 / 82944000000 - 55 / 82944) : ℚ) * t ^ 3 := by positivity
  linarith

/-- Zero-calculus cubic strip bound: for `0 ≤ a ≤ u ≤ v ≤ b` with `cap ≤ a² / 2` and
`b² / 2 ≤ 3 / 10`, `0 ≤ (v³ - u³)/6 - cap*(v - u) ≤ (3/10)*(v - u)`. -/
private theorem cubic_strip_diff_le {a b u v cap : ℚ}
    (ha0 : 0 ≤ a) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hcap_nonneg : 0 ≤ cap) (hcap_le : cap ≤ a ^ 2 / 2) (hb_le : b ^ 2 / 2 ≤ 3 / 10) :
    0 ≤ (v ^ 3 - u ^ 3) / 6 - cap * (v - u) ∧
    (v ^ 3 - u ^ 3) / 6 - cap * (v - u) ≤ (3 / 10 : ℚ) * (v - u) := by
  have hfac : (v ^ 3 - u ^ 3) / 6 - cap * (v - u) =
      (v - u) * ((v ^ 2 + u * v + u ^ 2) / 6 - cap) := by ring
  rw [hfac]
  have h1 : a ^ 2 / 2 ≤ (v ^ 2 + u * v + u ^ 2) / 6 := by nlinarith
  have h2 : (v ^ 2 + u * v + u ^ 2) / 6 ≤ b ^ 2 / 2 := by nlinarith
  constructor
  · exact mul_nonneg (by linarith) (by linarith)
  · rw [mul_comm (3 / 10 : ℚ)]
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

end RationalPaymentCerts

/-! ## Part 3: Preimage Lifting, Geometric-Ratio Calm Step & Case B Macroscopic Band -/

section CaseBMacroscopicBand

variable {Q : Type u} {α : Type v}

/-- **Lemma 1.3 — Common-Neighbor Preimage Lifting**:
For EVERY edge `v ∈ mergeNeighbors A L₀ u` and EVERY `t ≥ 0`, there exists `W ⊆ Q` with
`minMergeDeg A t ≤ W.card + corankAt A hSync L₀` and
`W ⊆ mergeNeighbors A (t + L₀) u ∩ mergeNeighbors A (t + L₀) v`. -/
theorem common_neighbor_preimage_lift [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {t L₀ : ℕ} {u v : Q} (huv : v ∈ mergeNeighbors A L₀ u) :
    ∃ W : Finset Q,
      minMergeDeg A t ≤ W.card + corankAt A hSync L₀ ∧
      W ⊆ mergeNeighbors A (t + L₀) u ∩ mergeNeighbors A (t + L₀) v := by
  rw [mem_mergeNeighbors] at huv
  obtain ⟨_, w, hwlen, hweq⟩ := huv
  let z := A.eval u w
  let W := A.preimage (mergeNeighbors A t z) w
  refine ⟨W, ?_, ?_⟩
  · let N := mergeNeighbors A t z
    let I := A.image Finset.univ w
    have hsub_img : N ∩ I ⊆ A.image W w := by
      intro y hy
      rw [Finset.mem_inter] at hy
      obtain ⟨hyN, hyI⟩ := hy
      rw [DFA.mem_image] at hyI ⊢
      obtain ⟨x, _, hxw⟩ := hyI
      exact ⟨x, by simp only [W, DFA.mem_preimage, hxw]; exact hyN, hxw⟩
    have hinter_le : (N ∩ I).card ≤ W.card :=
      le_trans (Finset.card_le_card hsub_img) (A.card_image_le W w)
    have hN_sub : N ⊆ (N ∩ I) ∪ (Finset.univ \ I) := by
      intro y hy
      by_cases hyI : y ∈ I
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hy, hyI⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyI⟩)
    have hsdiff : (Finset.univ \ I).card = Fintype.card Q - I.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hcor : Fintype.card Q - I.card ≤ corankAt A hSync L₀ := corank_le_corankAt A hSync hwlen
    have hmin_le : minMergeDeg A t ≤ N.card := minMergeDeg_le_mergeDeg A t z
    have hN_le : N.card ≤ (N ∩ I).card + (Finset.univ \ I).card :=
      le_trans (Finset.card_le_card hN_sub) (Finset.card_union_le _ _)
    omega
  · intro x hx
    simp only [W, DFA.mem_preimage] at hx
    rw [mem_mergeNeighbors] at hx
    obtain ⟨hne_z, v', hv'len, hv'eq⟩ := hx
    rw [Finset.mem_inter, mem_mergeNeighbors, mem_mergeNeighbors]
    refine ⟨⟨?_, w ++ v', by rw [List.length_append]; omega, ?_⟩,
            ⟨?_, w ++ v', by rw [List.length_append]; omega, ?_⟩⟩
    · intro hxu; apply hne_z; rw [hxu]
    · rw [DFA.eval_append, DFA.eval_append]; exact hv'eq
    · intro hxv; apply hne_z; rw [hxv, hweq]
    · rw [DFA.eval_append, DFA.eval_append, hweq]; exact hv'eq

/-- **Proposition 1.4 Step 1 — Geometric-Ratio Calm Step** (`@attack-polytope` `#149`):
When `D(h) < n / D_c1` and `D(n² / D_eta) < n / 10` (`D_c1 = 50 * D_eta`), any gap
`δ(r) > ⌈0.120 n²⌉` supplies `L₀ ∈ [0.40 n² / D_eta, n² / D_eta]` with
`95 * Δ_{L₀} ≤ 100 * m_{L₀}` and `0 < Δ_{L₀}`. -/
private theorem geometric_ratio_calm_step [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    {D_eta D_c1 R r : ℕ}
    (hD_eta : 10 ^ 14 ≤ D_eta) (hD_c1 : D_c1 = 50 * D_eta)
    (hR_pow : (D_c1 : ℚ) < (39 / 38 : ℚ) ^ R)
    (hn : 2 * (R + 1) * D_eta + 10 * D_eta ≤ Fintype.card Q)
    (hDh : D_c1 * shortCorank A hSync < Fintype.card Q)
    (hDt : 10 * corankAt A hSync (Fintype.card Q ^ 2 / D_eta) < Fintype.card Q)
    (hr : r + 1 ≤ Fintype.card Q - 1)
    (hgap : (120 * Fintype.card Q ^ 2) / 1000 + 1 < corankGap A hSync r) :
    let n := Fintype.card Q
    ∃ L₀ : ℕ, (40 * n ^ 2) / (100 * D_eta) ≤ L₀ ∧ L₀ ≤ n ^ 2 / D_eta ∧
      95 * maxMergeDeg A L₀ ≤ 100 * minMergeDeg A L₀ ∧ 0 < maxMergeDeg A L₀ ∧
      10 * corankAt A hSync L₀ < n := by
  intro n
  change (120 * n ^ 2) / 1000 + 1 < corankGap A hSync r at hgap
  let h := n - 1
  let t₀ := (40 * n ^ 2) / (100 * D_eta) + 1
  have hn_ge : 10 * D_eta ≤ n := by omega
  have hD_c1_pos : 0 < D_c1 := by omega
  have ht₀_lt : t₀ < corankGap A hSync r := by
    have h1 : (40 * n ^ 2) / (100 * D_eta) ≤ (120 * n ^ 2) / 1000 := by
      refine Nat.div_le_of_le_mul ?_
      have hdiv : 1000 * ((120 * n ^ 2) / 1000) + 1000 ≥ 120 * n ^ 2 := by omega
      have hmul : 1000 * (40 * n ^ 2) ≤ 1000 * ((100 * D_eta) * ((120 * n ^ 2) / 1000)) := by
        nlinarith only [hdiv, hD_eta, hn_ge]
      omega
    dsimp only [t₀]; omega
  -- Lower bound Δ_{t₀} ≥ 40 * n / D_c1 > 40 * D(h)
  have hΔt₀_ge : 40 * n ≤ D_c1 * maxMergeDeg A t₀ := by
    have h2t₀ := (exists_indep_and_sum_deg A hSync hr ht₀_lt).2
    have hsum_le : (∑ x : Q, mergeDeg A t₀ x) ≤ n * maxMergeDeg A t₀ := by
      calc (∑ x : Q, mergeDeg A t₀ x)
          ≤ ∑ _x : Q, maxMergeDeg A t₀ := Finset.sum_le_sum fun x _ => mergeDeg_le_maxMergeDeg A t₀ x
        _ = n * maxMergeDeg A t₀ := by simp [n]
    have h2t₀_ge : 40 * n ^ 2 ≤ D_c1 * (2 * t₀) := by
      have hdiv : 40 * n ^ 2 < (100 * D_eta) * t₀ := by
        dsimp only [t₀]
        have := Nat.lt_mul_div_succ (40 * n ^ 2) (by omega : 0 < 100 * D_eta)
        linarith
      have hrew : D_c1 * (2 * t₀) = (100 * D_eta) * t₀ := by rw [hD_c1]; ring
      omega
    have hmul : 40 * n ^ 2 ≤ n * (D_c1 * maxMergeDeg A t₀) := by
      calc 40 * n ^ 2 ≤ D_c1 * (2 * t₀) := h2t₀_ge
        _ ≤ D_c1 * (n * maxMergeDeg A t₀) := Nat.mul_le_mul_left D_c1 (le_trans h2t₀ hsum_le)
        _ = n * (D_c1 * maxMergeDeg A t₀) := by ring
    have hn_pos : 0 < n := by omega
    nlinarith
  have hΔt₀_gt_40D : 40 * shortCorank A hSync < maxMergeDeg A t₀ := by
    have h1 : 40 * (D_c1 * shortCorank A hSync) < 40 * n := Nat.mul_lt_mul_of_pos_left hDh (by omega)
    nlinarith
  -- s_j = t₀ + j * h stays inside [t₀, n² / D_eta] for all j ≤ R
  let s : ℕ → ℕ := fun j => t₀ + j * h
  have hs_le_tstar : ∀ j ≤ R, s j + h ≤ n ^ 2 / D_eta := by
    intro j hj
    dsimp only [s, t₀, h]
    have hstep : (j + 1) * (n - 1) ≤ (R + 1) * n := Nat.mul_le_mul (by omega) (by omega)
    have h1 : (40 * n ^ 2) / (100 * D_eta) ≤ (2 * n ^ 2) / (5 * D_eta) := by
      have : 100 * D_eta = 20 * (5 * D_eta) := by ring
      have : 40 * n ^ 2 = 20 * (2 * n ^ 2) := by ring
      rw [‹40 * n ^ 2 = _›, ‹100 * D_eta = _›, Nat.mul_div_mul_left _ _ (by omega)]
    have h3 : 2 * ((R + 1) * n * D_eta) ≤ n ^ 2 := by
      have h2R : 2 * (R + 1) * D_eta ≤ n := by omega
      have hmul := Nat.mul_le_mul_right n h2R
      nlinarith only [hmul]
    have h4 : (2 * n ^ 2) / (5 * D_eta) + 1 + (R + 1) * n ≤ n ^ 2 / D_eta := by
      have hmul_D : D_eta * ((2 * n ^ 2) / (5 * D_eta) + 1 + (R + 1) * n) ≤ n ^ 2 := by
        have ha : (5 * D_eta) * ((2 * n ^ 2) / (5 * D_eta)) ≤ 2 * n ^ 2 := Nat.mul_div_le _ _
        have hb : 10 * D_eta ≤ n ^ 2 := by nlinarith only [hD_eta, hn_ge]
        nlinarith only [ha, hb, h3]
      exact (Nat.le_div_iff_mul_le (by omega : 0 < D_eta)).mpr (by linarith only [hmul_D])
    have h5 : j * (n - 1) + (n - 1) = (j + 1) * (n - 1) := by ring
    omega
  -- By contradiction, some j < R must satisfy 95 * Δ_{s j + h} ≤ 100 * m_{s j + h}
  by_contra hnone
  push Not at hnone
  have hgrow : ∀ j < R, 39 * maxMergeDeg A (s j) ≤ 38 * maxMergeDeg A (s (j + 1)) := by
    intro j hj
    have hL₀_lo : (40 * n ^ 2) / (100 * D_eta) ≤ s j + h := by dsimp only [s, t₀]; omega
    have hL₀_hi : s j + h ≤ n ^ 2 / D_eta := hs_le_tstar j (by omega)
    have hΔ_pos : 0 < maxMergeDeg A (s j + h) :=
      lt_of_lt_of_le (by omega : 0 < maxMergeDeg A t₀)
        (maxMergeDeg_mono A (by dsimp only [s]; omega))
    have hD_L₀ : 10 * corankAt A hSync (s j + h) < n :=
      lt_of_le_of_lt (Nat.mul_le_mul_left 10 (corankAt_mono A hSync hL₀_hi)) hDt
    have hfail : 100 * minMergeDeg A (s j + h) < 95 * maxMergeDeg A (s j + h) := by
      by_contra hok
      push Not at hok
      exact absurd hD_L₀ (not_lt.mpr (hnone (s j + h) hL₀_lo hL₀_hi hok hΔ_pos))
    have htr := degree_transport A hSync hSC (s j)
    change maxMergeDeg A (s j) ≤ shortCorank A hSync + minMergeDeg A (s j + h) at htr
    have hΔ_ge : 40 * shortCorank A hSync ≤ maxMergeDeg A (s j) :=
      le_trans (show 40 * shortCorank A hSync ≤ maxMergeDeg A t₀ by omega)
        (maxMergeDeg_mono A (by dsimp only [s]; omega))
    have hs_succ : s (j + 1) = s j + h := by dsimp only [s]; ring
    rw [hs_succ]
    omega
  have hpow_q : ∀ j ≤ R,
      (39 / 38 : ℚ) ^ j * (maxMergeDeg A t₀ : ℚ) ≤ (maxMergeDeg A (s j) : ℚ) := by
    intro j
    induction j with
    | zero => intro _; simp [s]
    | succ j ih =>
      intro hj
      have ihj := ih (by omega)
      have hstep : (39 : ℚ) * (maxMergeDeg A (s j) : ℚ) ≤
          38 * (maxMergeDeg A (s (j + 1)) : ℚ) := by exact_mod_cast hgrow j (by omega)
      rw [pow_succ]
      nlinarith
  have htop := hpow_q R le_rfl
  have hΔR_le : (maxMergeDeg A (s R) : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast maxMergeDeg_le_card A (s R)
  have hΔt₀_q : (n : ℚ) / (D_c1 : ℚ) ≤ (maxMergeDeg A t₀ : ℚ) := by
    have hq : (40 : ℚ) * (n : ℚ) ≤ (D_c1 : ℚ) * (maxMergeDeg A t₀ : ℚ) := by
      exact_mod_cast hΔt₀_ge
    rw [div_le_iff₀ (by positivity : (0 : ℚ) < D_c1)]
    linarith
  have hcontra : (n : ℚ) < (39 / 38 : ℚ) ^ R * (maxMergeDeg A t₀ : ℚ) := by
    have h1 : (D_c1 : ℚ) * ((n : ℚ) / (D_c1 : ℚ)) < (39 / 38 : ℚ) ^ R * ((n : ℚ) / (D_c1 : ℚ)) :=
      mul_lt_mul_of_pos_right hR_pow (by positivity)
    have h2 : (39 / 38 : ℚ) ^ R * ((n : ℚ) / (D_c1 : ℚ)) ≤
        (39 / 38 : ℚ) ^ R * (maxMergeDeg A t₀ : ℚ) :=
      mul_le_mul_of_nonneg_left hΔt₀_q (by positivity)
    have hcancel : (D_c1 : ℚ) * ((n : ℚ) / (D_c1 : ℚ)) = (n : ℚ) :=
      mul_div_cancel₀ _ (by positivity)
    linarith
  linarith

/-- **Proposition 1.4 Step 2 — 2-Scale Nested Calm Time**:
Given `L₀ ∈ [0.40 n² / D_eta, n² / D_eta]` with `10 * D(L₀) < n`, produces `t, T = t + L₀ < δ(r)`
satisfying `Δ_T ≤ 1.06 m_t` and `m_t - D(L₀) ≥ 0.49 m_t` (using `@verifier`'s `#158` L109 bound!). -/
private theorem twoScale_nested_calm_time [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    {D_eta D_c1 L₀ r : ℕ}
    (hD_eta : 10 ^ 14 ≤ D_eta) (hD_c1 : D_c1 = 50 * D_eta)
    (hn : 150 * D_eta ^ 2 ≤ Fintype.card Q)
    (hDh : D_c1 * shortCorank A hSync < Fintype.card Q)
    (hL₀_lo : (40 * Fintype.card Q ^ 2) / (100 * D_eta) ≤ L₀)
    (hL₀_hi : L₀ ≤ Fintype.card Q ^ 2 / D_eta)
    (hD_L₀ : 10 * corankAt A hSync L₀ < Fintype.card Q)
    (hr : r + 1 ≤ Fintype.card Q - 1)
    (hgap : (120 * Fintype.card Q ^ 2) / 1000 + 1 < corankGap A hSync r) :
    ∃ t T : ℕ, T = t + L₀ ∧ T < corankGap A hSync r ∧ 0 < minMergeDeg A t ∧
      (maxMergeDeg A T : ℚ) ≤ (106 / 100 : ℚ) * (minMergeDeg A t : ℚ) ∧
      (49 / 100 : ℚ) * (minMergeDeg A t : ℚ) ≤
        (minMergeDeg A t : ℚ) - (corankAt A hSync L₀ : ℚ) := by
  let n := Fintype.card Q
  change 150 * D_eta ^ 2 ≤ n at hn
  change (40 * n ^ 2) / (100 * D_eta) ≤ L₀ at hL₀_lo
  change L₀ ≤ n ^ 2 / D_eta at hL₀_hi
  change (120 * n ^ 2) / 1000 + 1 < corankGap A hSync r at hgap
  let h := n - 1
  have hn_big : 10000 ≤ n := by nlinarith only [hD_eta, hn]
  -- Outer scale: 100 steps of length 2 * L₀ starting at n² / 10
  let a0 := n ^ 2 / 10
  obtain ⟨j, hj100, hΔ_calm⟩ := exists_calm_step (f := maxMergeDeg A)
    (n := n) (step := 2 * L₀) (M := 100) (start := a0)
    (fun _ _ hle => maxMergeDeg_mono A hle) (maxMergeDeg_le_card A) (by omega)
  let a := a0 + j * (2 * L₀)
  have hΔ_step : maxMergeDeg A (a + 2 * L₀) - maxMergeDeg A a ≤ n / 100 := by
    have heq : a0 + (j + 1) * (2 * L₀) = a + 2 * L₀ := by dsimp only [a]; ring
    rw [heq] at hΔ_calm
    exact hΔ_calm
  -- Inner scale: K = L₀ / h ≥ D_c1 steps of length h inside [a, a + L₀]
  let K := L₀ / h
  have hK_ge : D_c1 ≤ K := by
    have hmul : D_c1 * h ≤ L₀ := by
      have h1 : 40 * n ^ 2 ≤ (100 * D_eta) * ((40 * n ^ 2) / (100 * D_eta)) + 100 * D_eta := by
        have := Nat.lt_mul_div_succ (40 * n ^ 2) (by omega : 0 < 100 * D_eta)
        linarith
      have h1' : 40 * n ^ 2 ≤ (100 * D_eta) * L₀ + 100 * D_eta := by
        have := Nat.mul_le_mul_left (100 * D_eta) hL₀_lo
        omega
      have h2 : (100 * D_eta) * (D_c1 * h) + 100 * D_eta ≤ 40 * n ^ 2 := by
        have hsq : 150 * D_eta ^ 2 * n ≤ n ^ 2 := by
          have := Nat.mul_le_mul_right n hn
          nlinarith only [this]
        have hh : h ≤ n := Nat.sub_le _ _
        have hD : 100 * D_eta * (50 * D_eta * h) ≤ 5000 * D_eta ^ 2 * n := by
          nlinarith only [hh]
        have h100 : 100 * D_eta ≤ n ^ 2 := by nlinarith only [hD_eta, hn_big, hn]
        rw [hD_c1]
        nlinarith only [hsq, hD, h100]
      have h3 : (100 * D_eta) * (D_c1 * h) ≤ (100 * D_eta) * L₀ := by omega
      exact Nat.le_of_mul_le_mul_left h3 (by omega)
    exact (Nat.le_div_iff_mul_le (by omega : 0 < h)).mpr (by linarith only [hmul])
  obtain ⟨i, hiK, hm_calm⟩ := exists_calm_step (f := minMergeDeg A)
    (n := n) (step := h) (M := K) (start := a)
    (fun _ _ hle => minMergeDeg_mono A hle)
    (fun t => le_trans (minMergeDeg_le_mergeDeg A t (Classical.arbitrary Q)) (mergeDeg_le_card A t _))
    (by omega)
  let t := a + i * h
  let T := t + L₀
  have ht_le_aL₀ : t ≤ a + L₀ := by
    have hi_le : i * h ≤ K * h := Nat.mul_le_mul_right h (by omega)
    have hKh : K * h ≤ L₀ := Nat.div_mul_le_self L₀ h
    dsimp only [t]; omega
  have hT_le_a2L₀ : T ≤ a + 2 * L₀ := by dsimp only [T]; omega
  have hT_lt_gap : T < corankGap A hSync r := by
    have h200L₀ : 200 * L₀ ≤ n ^ 2 / 100 := by
      have h1 : D_eta * (n ^ 2 / D_eta) ≤ n ^ 2 := Nat.mul_div_le _ _
      have h2 : 100 * (200 * L₀) ≤ n ^ 2 := by nlinarith only [h1, hL₀_hi, hD_eta]
      exact (Nat.le_div_iff_mul_le (by omega : 0 < 100)).mpr (by linarith only [h2])
    have ha2L₀_le : a + 2 * L₀ ≤ a0 + 200 * L₀ := by
      dsimp only [a]
      have : (j + 1) * (2 * L₀) ≤ 100 * (2 * L₀) := Nat.mul_le_mul_right _ (by omega)
      linarith
    dsimp only [a0] at ha2L₀_le
    omega
  have hm_step : minMergeDeg A (t + h) - minMergeDeg A t ≤ n / D_c1 := by
    have heq : a + (i + 1) * h = t + h := by dsimp only [t]; ring
    rw [heq] at hm_calm
    exact le_trans hm_calm (Nat.div_le_div_left hK_ge (by omega : 0 < D_c1))
  -- Lower bound Δ_t ≥ 2 * t / n ≥ 0.1999 * n, hence m_t ≥ 0.199 * n
  have hΔt_ge : 2 * (n ^ 2 / 10) ≤ n * maxMergeDeg A t := by
    have h2t := (exists_indep_and_sum_deg A hSync hr (by omega : t < corankGap A hSync r)).2
    have hsum_le : (∑ x : Q, mergeDeg A t x) ≤ n * maxMergeDeg A t := by
      calc (∑ x : Q, mergeDeg A t x)
          ≤ ∑ _x : Q, maxMergeDeg A t := Finset.sum_le_sum fun x _ => mergeDeg_le_maxMergeDeg A t x
        _ = n * maxMergeDeg A t := by simp [n]
    have ht_ge : n ^ 2 / 10 ≤ t := by dsimp only [t, a, a0]; omega
    omega
  have htr_t := degree_transport A hSync hSC t
  change maxMergeDeg A t ≤ shortCorank A hSync + minMergeDeg A (t + h) at htr_t
  have hDh_le : shortCorank A hSync ≤ n / D_c1 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < D_c1)).mpr (by linarith only [hDh])
  have hΔt_sub_mt : maxMergeDeg A t ≤ minMergeDeg A t + 2 * (n / D_c1) := by
    have hmono : minMergeDeg A t ≤ minMergeDeg A (t + h) := minMergeDeg_mono A (Nat.le_add_right _ _)
    omega
  have h2div_le : 2 * (n / D_c1) ≤ n / 1000 := by
    have h1 : D_c1 * (n / D_c1) ≤ n := Nat.mul_div_le _ _
    have h2 : 1000 * (2 * (n / D_c1)) ≤ n := by nlinarith only [h1, hD_eta, hD_c1]
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 1000)).mpr (by linarith only [h2])
  have hmt_ge : 199 * n ≤ 1000 * minMergeDeg A t := by
    have hdiv10 : n ^ 2 ≤ 10 * (n ^ 2 / 10) + 10 := by omega
    have hdiv1000 : 1000 * (n / 1000) ≤ n := Nat.mul_div_le _ _
    have h1 : 200 * n ^ 2 ≤ 1000 * (n * maxMergeDeg A t) + 2000 := by
      nlinarith only [hdiv10, hΔt_ge]
    have h2 : 200 * n ^ 2 ≤ 1000 * (n * minMergeDeg A t) + n ^ 2 + 2000 := by
      have hmul := Nat.mul_le_mul_left n (show maxMergeDeg A t ≤ minMergeDeg A t + n / 1000 by omega)
      nlinarith only [h1, hmul, hdiv1000]
    nlinarith only [h2, hn_big]
  have hΔT_le : maxMergeDeg A T ≤ minMergeDeg A t + n / 100 + n / 1000 := by
    have h1 : maxMergeDeg A T ≤ maxMergeDeg A (a + 2 * L₀) := maxMergeDeg_mono A hT_le_a2L₀
    have h2 : maxMergeDeg A a ≤ maxMergeDeg A t := maxMergeDeg_mono A (by dsimp only [t]; omega)
    have h3 : maxMergeDeg A a ≤ maxMergeDeg A (a + 2 * L₀) := maxMergeDeg_mono A (Nat.le_add_right _ _)
    omega
  refine ⟨t, T, rfl, hT_lt_gap, by omega, ?_, ?_⟩
  · have hmt_q : (199 / 1000 : ℚ) * n ≤ (minMergeDeg A t : ℚ) := by
      have hq : (199 : ℚ) * n ≤ 1000 * (minMergeDeg A t : ℚ) := by exact_mod_cast hmt_ge
      linarith
    have hΔT_q : (maxMergeDeg A T : ℚ) ≤ (minMergeDeg A t : ℚ) + (11 / 1000 : ℚ) * n := by
      have hnat : 1000 * maxMergeDeg A T ≤ 1000 * minMergeDeg A t + 11 * n := by
        have : 100 * (n / 100) ≤ n := Nat.mul_div_le _ _
        have : 1000 * (n / 1000) ≤ n := Nat.mul_div_le _ _
        omega
      have hq : (1000 : ℚ) * (maxMergeDeg A T : ℚ) ≤ 1000 * (minMergeDeg A t : ℚ) + 11 * n := by
        exact_mod_cast hnat
      linarith
    linarith
  · have hmt_q : (199 / 1000 : ℚ) * n ≤ (minMergeDeg A t : ℚ) := by
      have hq : (199 : ℚ) * n ≤ 1000 * (minMergeDeg A t : ℚ) := by exact_mod_cast hmt_ge
      linarith
    have hDL₀_q : (corankAt A hSync L₀ : ℚ) ≤ (1 / 10 : ℚ) * n := by
      have hq : (10 : ℚ) * (corankAt A hSync L₀ : ℚ) < n := by exact_mod_cast hD_L₀
      linarith
    linarith

/-- **Proposition 1.4 — Case B Macroscopic Band Bound**:
Under `D(h) < n / D_c1` and `D(n² / D_eta) < n / 10`, EVERY `r ∈ [n / 2, 58 n / 100]`
satisfies `corankGap A hSync r ≤ (120 * n²) / 1000 + 1`! -/
theorem caseB_macroscopic_band_bound [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    {D_eta D_c1 R r : ℕ}
    (hD_eta : 10 ^ 14 ≤ D_eta) (hD_c1 : D_c1 = 50 * D_eta)
    (hR_pow : (D_c1 : ℚ) < (39 / 38 : ℚ) ^ R)
    (hn1 : 2 * (R + 1) * D_eta + 10 * D_eta ≤ Fintype.card Q)
    (hn2 : 150 * D_eta ^ 2 ≤ Fintype.card Q)
    (hDh : D_c1 * shortCorank A hSync < Fintype.card Q)
    (hDt : 10 * corankAt A hSync (Fintype.card Q ^ 2 / D_eta) < Fintype.card Q)
    (hr_lo : Fintype.card Q / 2 ≤ r) (hr_hi : r ≤ (58 * Fintype.card Q) / 100) :
    corankGap A hSync r ≤ (120 * Fintype.card Q ^ 2) / 1000 + 1 := by
  classical
  let n := Fintype.card Q
  have hn_big : 10000 ≤ n := by nlinarith
  have hr_le : r + 1 ≤ n - 1 := by omega
  by_contra hgt
  push Not at hgt
  obtain ⟨L₀, hL₀_lo, hL₀_hi, hreg, hΔL₀_pos, hD_L₀⟩ :=
    geometric_ratio_calm_step A hSync hSC hD_eta hD_c1 hR_pow hn1 hDh hDt hr_le hgt
  obtain ⟨t, T, hT_eq, hT_lt, hmt_pos, hΔT_ratio, hmt_sub⟩ :=
    twoScale_nested_calm_time A hSync hSC hD_eta hD_c1 hn2 hDh hL₀_lo hL₀_hi hD_L₀ hr_le hgt
  obtain ⟨S, hS_card, hSind⟩ := (exists_indep_and_sum_deg A hSync hr_le hT_lt).1
  let S_bar := Finset.univ \ S
  have hSbar_card : S_bar.card = r := by
    dsimp only [S_bar]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hS_card]
    omega
  have hL₀_le_T : L₀ ≤ T := by omega
  have hSind_L₀ : ∀ x ∈ S, ∀ y ∈ mergeNeighbors A L₀ x, y ∉ S :=
    fun x hx y hy => hSind x hx y (mergeNeighbors_mono A hL₀_le_T x hy)
  let V₁ := S_bar.filter (fun v => ∃ u ∈ S, v ∈ mergeNeighbors A L₀ u)
  -- Step 1: |V₁| ≥ 0.95 * |S|
  have hV₁_ge : 95 * S.card ≤ 100 * V₁.card := by
    have hsum_ge : S.card * minMergeDeg A L₀ ≤ ∑ u ∈ S, mergeDeg A L₀ u := by
      calc S.card * minMergeDeg A L₀
          = ∑ _u ∈ S, minMergeDeg A L₀ := by simp
        _ ≤ ∑ u ∈ S, mergeDeg A L₀ u := Finset.sum_le_sum fun u _ => minMergeDeg_le_mergeDeg A L₀ u
    have hsum_le : (∑ u ∈ S, mergeDeg A L₀ u) ≤ V₁.card * maxMergeDeg A L₀ := by
      have hrew : ∀ u ∈ S,
          mergeDeg A L₀ u = ∑ v ∈ V₁, if v ∈ mergeNeighbors A L₀ u then 1 else 0 := by
        intro u hu
        rw [← Finset.card_filter]
        have hfilt : V₁.filter (fun v => v ∈ mergeNeighbors A L₀ u) = mergeNeighbors A L₀ u := by
          ext v
          simp only [V₁, S_bar, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact ⟨fun h => h.2, fun hv => ⟨⟨hSind_L₀ u hu v hv, ⟨u, hu, hv⟩⟩, hv⟩⟩
        rw [hfilt]; rfl
      calc (∑ u ∈ S, mergeDeg A L₀ u)
          = ∑ u ∈ S, ∑ v ∈ V₁, if v ∈ mergeNeighbors A L₀ u then 1 else 0 :=
            Finset.sum_congr rfl hrew
        _ = ∑ v ∈ V₁, ∑ u ∈ S, if v ∈ mergeNeighbors A L₀ u then 1 else 0 := Finset.sum_comm
        _ ≤ ∑ v ∈ V₁, mergeDeg A L₀ v := by
            refine Finset.sum_le_sum fun v _ => ?_
            rw [← Finset.card_filter]
            refine Finset.card_le_card fun u hu => ?_
            rw [Finset.mem_filter] at hu
            exact (mem_mergeNeighbors_symm A L₀ u v).mp hu.2
        _ ≤ ∑ _v ∈ V₁, maxMergeDeg A L₀ :=
            Finset.sum_le_sum fun v _ => mergeDeg_le_maxMergeDeg A L₀ v
        _ = V₁.card * maxMergeDeg A L₀ := by simp
    nlinarith
  -- Step 2: Every v ∈ V₁ has ≥ m_t - D(L₀) neighbors inside S_bar in E_T
  have hV₁_tri : ∀ v ∈ V₁,
      minMergeDeg A t ≤ (mergeNeighbors A T v ∩ S_bar).card + corankAt A hSync L₀ := by
    intro v hv
    obtain ⟨u, huS, huv⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨W, hW_card, hW_sub⟩ := common_neighbor_preimage_lift A hSync (t := t) huv
    have hW_in : W ⊆ mergeNeighbors A T v ∩ S_bar := by
      intro x hx
      have hx' := hW_sub hx
      rw [Finset.mem_inter, ← hT_eq] at hx'
      refine Finset.mem_inter.mpr ⟨hx'.2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, ?_⟩⟩
      exact hSind u huS x hx'.1
    have hle := Finset.card_le_card hW_in
    omega
  -- Step 3: Double count E_T degrees over S_bar
  have hSbar_deg_sum :
      (∑ u ∈ S, mergeDeg A T u) + (∑ v ∈ V₁, (mergeNeighbors A T v ∩ S_bar).card) ≤
      S_bar.card * maxMergeDeg A T := by
    have hcross : (∑ u ∈ S, mergeDeg A T u) = ∑ v ∈ S_bar, (mergeNeighbors A T v ∩ S).card := by
      have hrew : ∀ u ∈ S,
          mergeDeg A T u = ∑ v ∈ S_bar, if v ∈ mergeNeighbors A T u then 1 else 0 := by
        intro u hu
        rw [← Finset.card_filter]
        have hfilt : S_bar.filter (fun v => v ∈ mergeNeighbors A T u) = mergeNeighbors A T u := by
          ext v
          simp only [S_bar, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact ⟨fun h => h.2, fun hv => ⟨hSind u hu v hv, hv⟩⟩
        rw [hfilt]; rfl
      rw [Finset.sum_congr rfl hrew, Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← Finset.card_filter]
      congr 1; ext u
      simp only [Finset.mem_filter, Finset.mem_inter]
      exact ⟨fun h => ⟨(mem_mergeNeighbors_symm A T u v).mp h.2, h.1⟩,
        fun h => ⟨h.2, (mem_mergeNeighbors_symm A T u v).mpr h.1⟩⟩
    have hV₁_sub : V₁ ⊆ S_bar := Finset.filter_subset _ _
    have hinside : (∑ v ∈ V₁, (mergeNeighbors A T v ∩ S_bar).card) ≤
        ∑ v ∈ S_bar, (mergeNeighbors A T v ∩ S_bar).card :=
      Finset.sum_le_sum_of_subset hV₁_sub
    have hsplit_v : ∀ v ∈ S_bar,
        (mergeNeighbors A T v ∩ S).card + (mergeNeighbors A T v ∩ S_bar).card = mergeDeg A T v := by
      intro v _
      have hdisj : Disjoint (mergeNeighbors A T v ∩ S) (mergeNeighbors A T v ∩ S_bar) := by
        rw [Finset.disjoint_left]; intro x h1 h2
        rw [Finset.mem_inter] at h1 h2
        exact (Finset.mem_sdiff.mp h2.2).2 h1.2
      rw [← Finset.card_union_of_disjoint hdisj]
      congr 1; ext x
      simp only [Finset.mem_union, Finset.mem_inter, S_bar, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      tauto
    calc (∑ u ∈ S, mergeDeg A T u) + (∑ v ∈ V₁, (mergeNeighbors A T v ∩ S_bar).card)
        ≤ (∑ v ∈ S_bar, (mergeNeighbors A T v ∩ S).card) +
          (∑ v ∈ S_bar, (mergeNeighbors A T v ∩ S_bar).card) := by omega
      _ = ∑ v ∈ S_bar, ((mergeNeighbors A T v ∩ S).card + (mergeNeighbors A T v ∩ S_bar).card) :=
          (Finset.sum_add_distrib).symm
      _ = ∑ v ∈ S_bar, mergeDeg A T v := Finset.sum_congr rfl hsplit_v
      _ ≤ ∑ _v ∈ S_bar, maxMergeDeg A T :=
          Finset.sum_le_sum fun v _ => mergeDeg_le_maxMergeDeg A T v
      _ = S_bar.card * maxMergeDeg A T := by simp
  -- Cast the final contradiction to ℚ and cancel m_t > 0
  have hS_deg_ge : S.card * minMergeDeg A t ≤ ∑ u ∈ S, mergeDeg A T u := by
    have hmT : minMergeDeg A t ≤ minMergeDeg A T := minMergeDeg_mono A (by omega)
    calc S.card * minMergeDeg A t
        = ∑ _u ∈ S, minMergeDeg A t := by simp
      _ ≤ ∑ u ∈ S, mergeDeg A T u :=
          Finset.sum_le_sum fun u _ => le_trans hmT (minMergeDeg_le_mergeDeg A T u)
  have hV₁_sum_q :
      (V₁.card : ℚ) * ((minMergeDeg A t : ℚ) - (corankAt A hSync L₀ : ℚ)) ≤
      ((∑ v ∈ V₁, (mergeNeighbors A T v ∩ S_bar).card : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    have hpt : ∀ v ∈ V₁,
        (minMergeDeg A t : ℚ) - (corankAt A hSync L₀ : ℚ) ≤
        ((mergeNeighbors A T v ∩ S_bar).card : ℚ) := by
      intro v hv
      have hnat := hV₁_tri v hv
      have hq : (minMergeDeg A t : ℚ) ≤
          ((mergeNeighbors A T v ∩ S_bar).card : ℚ) + (corankAt A hSync L₀ : ℚ) := by
        exact_mod_cast hnat
      linarith
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    exact hsum
  have hmain_q :
      (S.card : ℚ) * (minMergeDeg A t : ℚ) +
        (V₁.card : ℚ) * ((minMergeDeg A t : ℚ) - (corankAt A hSync L₀ : ℚ)) ≤
      (S_bar.card : ℚ) * (maxMergeDeg A T : ℚ) := by
    have h1 : ((S.card * minMergeDeg A t : ℕ) : ℚ) ≤ ((∑ u ∈ S, mergeDeg A T u : ℕ) : ℚ) := by
      exact_mod_cast hS_deg_ge
    have h2 : (((∑ u ∈ S, mergeDeg A T u) + ∑ v ∈ V₁, (mergeNeighbors A T v ∩ S_bar).card : ℕ) : ℚ) ≤
        ((S_bar.card * maxMergeDeg A T : ℕ) : ℚ) := by exact_mod_cast hSbar_deg_sum
    rw [Nat.cast_mul] at h1
    rw [Nat.cast_add, Nat.cast_mul] at h2
    linarith
  have hmt_qpos : (0 : ℚ) < (minMergeDeg A t : ℚ) := by exact_mod_cast hmt_pos
  have hV₁_q : (95 / 100 : ℚ) * (S.card : ℚ) ≤ (V₁.card : ℚ) := by
    have hq : (95 : ℚ) * (S.card : ℚ) ≤ 100 * (V₁.card : ℚ) := by exact_mod_cast hV₁_ge
    linarith
  have hS_ge_42 : (42 / 100 : ℚ) * (n : ℚ) ≤ (S.card : ℚ) := by
    have hnat : 42 * n ≤ 100 * S.card := by omega
    have hq : (42 : ℚ) * (n : ℚ) ≤ 100 * (S.card : ℚ) := by exact_mod_cast hnat
    linarith
  have hSbar_eq : (S_bar.card : ℚ) = (n : ℚ) - (S.card : ℚ) := by
    have hnat : S_bar.card + S.card = n := by omega
    have hq : (S_bar.card : ℚ) + (S.card : ℚ) = (n : ℚ) := by exact_mod_cast hnat
    linarith
  have hStepA : (S.card : ℚ) * (1 + (95 / 100 : ℚ) * (49 / 100 : ℚ)) * (minMergeDeg A t : ℚ) ≤
      (S_bar.card : ℚ) * ((106 / 100 : ℚ) * (minMergeDeg A t : ℚ)) := by
    have h1 := mul_le_mul_of_nonneg_left hΔT_ratio (Nat.cast_nonneg S_bar.card)
    have h2 : (95 / 100 : ℚ) * (S.card : ℚ) * ((49 / 100 : ℚ) * (minMergeDeg A t : ℚ)) ≤
        (V₁.card : ℚ) * ((minMergeDeg A t : ℚ) - (corankAt A hSync L₀ : ℚ)) :=
      mul_le_mul hV₁_q hmt_sub (by positivity) (Nat.cast_nonneg V₁.card)
    linarith
  have hcancel : (S.card : ℚ) * (1 + (95 / 100 : ℚ) * (49 / 100 : ℚ)) ≤
      (S_bar.card : ℚ) * (106 / 100 : ℚ) := by
    have hrew : (S_bar.card : ℚ) * ((106 / 100 : ℚ) * (minMergeDeg A t : ℚ)) =
        ((S_bar.card : ℚ) * (106 / 100 : ℚ)) * (minMergeDeg A t : ℚ) := by ring
    rw [hrew] at hStepA
    exact le_of_mul_le_mul_right hStepA hmt_qpos
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  linarith

end CaseBMacroscopicBand

/-! ## Part 4: Unified Cap Saving, Symbolic 3-Case Assembly & Flagship Theorem T20 -/

section BelowSevenFortyEightMain

variable {Q : Type u} {α : Type v}

/-- Dyadic schedule pigeonhole: starting at any length `ℓ₀` and step count `J ≥ 1`, produces
a word `v` of length `≤ 2 ^ J * (ℓ₀ + n)` with corank `C ≥ D(ℓ₀)` and stability
`D(2|v| + n - 1) - C ≤ n / J`. -/
private theorem dyadic_schedule_exists [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (ℓ₀ : ℕ) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ v : List α,
      v.length ≤ 2 ^ J * (ℓ₀ + Fintype.card Q) ∧
      corankAt A hSync ℓ₀ ≤ Fintype.card Q - (A.image Finset.univ v).card ∧
      corankAt A hSync (2 * v.length + (Fintype.card Q - 1)) -
        (Fintype.card Q - (A.image Finset.univ v).card) ≤ Fintype.card Q / J := by
  let n := Fintype.card Q
  let ℓ : ℕ → ℕ := Nat.rec ℓ₀ (fun _ prev => 2 * prev + (n - 1))
  have hℓ_succ : ∀ i, ℓ (i + 1) = 2 * ℓ i + (n - 1) := fun _ => rfl
  have hℓ_mono : ∀ i, ℓ i ≤ ℓ (i + 1) := fun i => by rw [hℓ_succ]; omega
  have hℓ_le : ∀ i, ℓ i + n ≤ 2 ^ i * (ℓ₀ + n) := by
    intro i
    induction i with
    | zero => simp [ℓ]
    | succ i ih =>
      rw [hℓ_succ, pow_succ]
      have h1 : 2 * ℓ i + (n - 1) + n ≤ 2 * (ℓ i + n) := by omega
      nlinarith only [h1, ih]
  have hD_mono : ∀ i, corankAt A hSync (ℓ i) ≤ corankAt A hSync (ℓ (i + 1)) :=
    fun i => corankAt_mono A hSync (hℓ_mono i)
  have hD_ge0 : ∀ i, corankAt A hSync ℓ₀ ≤ corankAt A hSync (ℓ i) := by
    intro i
    induction i with
    | zero => exact le_rfl
    | succ i ih => exact le_trans ih (hD_mono i)
  have hex_j : ∃ j < J, corankAt A hSync (ℓ (j + 1)) - corankAt A hSync (ℓ j) ≤ n / J := by
    by_contra hnone
    push Not at hnone
    have hsum_ge : J * (n / J + 1) ≤
        ∑ i ∈ Finset.range J, (corankAt A hSync (ℓ (i + 1)) - corankAt A hSync (ℓ i)) := by
      calc J * (n / J + 1)
          = ∑ _i ∈ Finset.range J, (n / J + 1) := by simp
        _ ≤ ∑ i ∈ Finset.range J, (corankAt A hSync (ℓ (i + 1)) - corankAt A hSync (ℓ i)) :=
            Finset.sum_le_sum fun i hi => hnone i (Finset.mem_range.mp hi)
    have htele : ∀ m : ℕ,
        (∑ i ∈ Finset.range m, (corankAt A hSync (ℓ (i + 1)) - corankAt A hSync (ℓ i))) +
          corankAt A hSync (ℓ 0) = corankAt A hSync (ℓ m) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ]
        have hm := hD_mono m
        omega
    have htop := htele J
    have hle_n : corankAt A hSync (ℓ J) ≤ n := le_trans (corankAt_le_pred A hSync _) (Nat.sub_le _ _)
    have hdiv : n < J * (n / J + 1) := by
      have := Nat.lt_mul_div_succ n (by omega : 0 < J)
      linarith
    omega
  obtain ⟨j, hjJ, hstab⟩ := hex_j
  obtain ⟨v, hvlen, hvcard⟩ := exists_word_corankAt A hSync (ℓ j)
  have hC_eq : n - (A.image Finset.univ v).card = corankAt A hSync (ℓ j) := by
    have hle := corankAt_le_pred A hSync (ℓ j)
    change (A.image Finset.univ v).card = n - corankAt A hSync (ℓ j) at hvcard
    omega
  refine ⟨v, ?_, ?_, ?_⟩
  · have h1 := hℓ_le j
    have h2 : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 2 ^ j * (ℓ₀ + n) ≤ 2 ^ J * (ℓ₀ + n) := Nat.mul_le_mul_right _ h2
    change v.length ≤ 2 ^ J * (ℓ₀ + n)
    omega
  · change corankAt A hSync ℓ₀ ≤ n - (A.image Finset.univ v).card
    rw [hC_eq]; exact hD_ge0 j
  · change corankAt A hSync (2 * v.length + (n - 1)) - (n - (A.image Finset.univ v).card) ≤ n / J
    rw [hC_eq]
    have h2v : 2 * v.length + (n - 1) ≤ ℓ (j + 1) := by rw [hℓ_succ]; omega
    have hmono := corankAt_mono A hSync h2v
    omega

/-- Helper: `i * (H - max ρ i) ≤ W_fun (ρ / n) * n²` for `H = n / 2` and `1 ≤ i ≤ k, ρ ≤ k`. -/
private theorem shitov_prefix_weight_le {n H ρ i : ℕ}
    (hn : 0 < n) (hH : 2 * H ≤ n) (hρ : ρ ≤ H) (hi : i ≤ H) :
    (i : ℚ) * ((H : ℚ) - (max ρ i : ℚ)) ≤ W_fun ((ρ : ℚ) / (n : ℚ)) * (n : ℚ) ^ 2 := by
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hH_q : (H : ℚ) ≤ (n : ℚ) / 2 := by
    have : (2 : ℚ) * H ≤ n := by exact_mod_cast hH
    linarith
  have hquad : ∀ t : ℚ, 0 ≤ t → t ≤ (H : ℚ) → t * ((H : ℚ) - t) ≤ (n : ℚ) ^ 2 / 16 := by
    intro t _ _
    have h1 : t * ((H : ℚ) - t) ≤ (H : ℚ) ^ 2 / 4 := by nlinarith [sq_nonneg (t - (H : ℚ) / 2)]
    have h2 : (H : ℚ) ^ 2 / 4 ≤ (n : ℚ) ^ 2 / 16 := by nlinarith
    linarith
  dsimp only [W_fun]
  split_ifs with hcmp
  · by_cases hiρ : i ≤ ρ
    · have hiρ_q : (i : ℚ) ≤ (ρ : ℚ) := by exact_mod_cast hiρ
      rw [max_eq_left hiρ_q]
      have h1 : (i : ℚ) * ((H : ℚ) - (ρ : ℚ)) ≤ (ρ : ℚ) * ((H : ℚ) - (ρ : ℚ)) := by
        have hρH : (0 : ℚ) ≤ (H : ℚ) - (ρ : ℚ) := by
          have : (ρ : ℚ) ≤ H := by exact_mod_cast hρ
          linarith
        exact mul_le_mul_of_nonneg_right hiρ_q hρH
      have h2 := hquad (ρ : ℚ) (Nat.cast_nonneg _) (by exact_mod_cast hρ)
      linarith
    · have hρi_q : (ρ : ℚ) ≤ (i : ℚ) := by exact_mod_cast (by omega : ρ ≤ i)
      rw [max_eq_right hρi_q]
      have h2 := hquad (i : ℚ) (Nat.cast_nonneg _) (by exact_mod_cast hi)
      linarith
  · push Not at hcmp
    have hρ_gt : (n : ℚ) / 4 < (ρ : ℚ) := by
      have := (div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 4) hn_pos).mp hcmp
      linarith
    have h2ρ_ge_H : (H : ℚ) ≤ 2 * (ρ : ℚ) := by linarith
    have hrhs_eq : (ρ : ℚ) / (n : ℚ) * (1 / 2 - (ρ : ℚ) / (n : ℚ)) * (n : ℚ) ^ 2 =
        (ρ : ℚ) * ((n : ℚ) / 2 - (ρ : ℚ)) := by
      have hn_ne : (n : ℚ) ≠ 0 := hn_pos.ne'
      field_simp
    rw [hrhs_eq]
    have hρ_le_rhs : (ρ : ℚ) * ((H : ℚ) - (ρ : ℚ)) ≤ (ρ : ℚ) * ((n : ℚ) / 2 - (ρ : ℚ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    by_cases hiρ : i ≤ ρ
    · have hiρ_q : (i : ℚ) ≤ (ρ : ℚ) := by exact_mod_cast hiρ
      rw [max_eq_left hiρ_q]
      have hρH : (0 : ℚ) ≤ (H : ℚ) - (ρ : ℚ) := by
        have : (ρ : ℚ) ≤ H := by exact_mod_cast hρ
        linarith
      have h1 : (i : ℚ) * ((H : ℚ) - (ρ : ℚ)) ≤ (ρ : ℚ) * ((H : ℚ) - (ρ : ℚ)) :=
        mul_le_mul_of_nonneg_right hiρ_q hρH
      linarith
    · have hρi_q : (ρ : ℚ) ≤ (i : ℚ) := by exact_mod_cast (by omega : ρ ≤ i)
      rw [max_eq_right hρi_q]
      have hdiff : (ρ : ℚ) * ((H : ℚ) - (ρ : ℚ)) - (i : ℚ) * ((H : ℚ) - (i : ℚ)) =
          ((i : ℚ) - (ρ : ℚ)) * ((i : ℚ) + (ρ : ℚ) - (H : ℚ)) := by ring
      have hprod : (0 : ℚ) ≤ ((i : ℚ) - (ρ : ℚ)) * ((i : ℚ) + (ρ : ℚ) - (H : ℚ)) :=
        mul_nonneg (by linarith) (by linarith)
      linarith

/-- Helper 1 for `prefix_bound_of_word`: direct Singularity-Free Cap on `[ρ, H)`. -/
private theorem prefix_bound_direct [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    (v : List α) {J M D_eps ρ : ℕ}
    (hn : 100 ≤ Fintype.card Q) (hJ : 1 ≤ J) (hM : 1 ≤ M) (hDeps : 1 ≤ D_eps)
    (hC_lo : 2 * Fintype.card Q ≤ D_eps * (Fintype.card Q - (A.image Finset.univ v).card))
    (ha₀ : corankAt A hSync (2 * v.length + (Fintype.card Q - 1)) -
      (Fintype.card Q - (A.image Finset.univ v).card) ≤ Fintype.card Q / J)
    (hρ_ge1 : 1 ≤ ρ) (hρ_lt_H : ρ < Fintype.card Q / 2)
    (hlam_ρ_le : minCorankLen A hSync ρ ≤ Fintype.card Q ^ 2) :
    let n := Fintype.card Q
    let C := n - (A.image Finset.univ v).card
    let Ω := (M + 1) * (v.length + (n - 1)) + 1
    let θ : ℚ := ((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (D_eps : ℚ) / 2
    (minCorankLen A hSync (n / 2) : ℚ) ≤
      ((C : ℚ) / (n : ℚ)) ^ 2 * (1 / 2 - (ρ : ℚ) / (n : ℚ)) * (n : ℚ) ^ 3 +
      (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 +
      ((n : ℚ) / 2 + 1) * (Ω : ℚ) + 2 * (n : ℚ) ^ 2 := by
  intro n C Ω θ
  let H := n / 2
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hΩ0 : (0 : ℚ) ≤ (Ω : ℚ) := Nat.cast_nonneg _
  have hC_pos : 1 ≤ C := by
    by_contra h0; push Not at h0
    have hC0 : C = 0 := by omega
    change 2 * n ≤ D_eps * C at hC_lo
    rw [hC0] at hC_lo; omega
  have htele : minCorankLen A hSync H =
      minCorankLen A hSync ρ + ∑ r ∈ Finset.Ico ρ H, corankGap A hSync r :=
    minCorankLen_eq_add_sum_Ico A hSync (by omega) (by omega)
  have htele_q : (minCorankLen A hSync H : ℚ) =
      (minCorankLen A hSync ρ : ℚ) + ∑ r ∈ Finset.Ico ρ H, (corankGap A hSync r : ℚ) := by
    have hcast : ((minCorankLen A hSync H : ℕ) : ℚ) =
        ((minCorankLen A hSync ρ + ∑ r ∈ Finset.Ico ρ H, corankGap A hSync r : ℕ) : ℚ) := by
      exact_mod_cast htele
    rw [Nat.cast_add, Nat.cast_sum] at hcast
    exact hcast
  have hpt : ∀ r ∈ Finset.Ico ρ H,
      (corankGap A hSync r : ℚ) ≤ (C : ℚ) ^ 2 + θ * (n : ℚ) ^ 2 + (Ω : ℚ) := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have h2b : (A.image Finset.univ v).card < 2 * (n - r) := by
      have hRle : (A.image Finset.univ v).card ≤ n := Finset.card_le_univ _
      dsimp only [C, H] at hC_pos hr ⊢; omega
    have hcap := singularityFree_compression_cap A hSync hSC v (r := r) (M := M)
      (by omega) hM h2b
    have hmin1 : min ((C : ℚ) ^ 2) ((n : ℚ) * (C : ℚ) / 2) ≤ (C : ℚ) ^ 2 := min_le_left _ _
    have hcoef : (n : ℚ) / 2 + min (C : ℚ) ((n : ℚ) / 2) ≤ (n : ℚ) := by
      have : min (C : ℚ) ((n : ℚ) / 2) ≤ (n : ℚ) / 2 := min_le_right _ _
      linarith
    have hb_le : ((n - r : ℕ) : ℚ) ≤ (n : ℚ) := by exact_mod_cast (Nat.sub_le n r)
    have hη_le : ((corankAt A hSync (2 * v.length + (n - 1)) - C + n / M : ℕ) : ℚ) ≤
        ((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (n : ℚ) := by
      have h1 : ((corankAt A hSync (2 * v.length + (n - 1)) - C : ℕ) : ℚ) ≤ (n : ℚ) / (J : ℚ) := by
        rw [le_div_iff₀ (by positivity : (0 : ℚ) < J)]
        exact_mod_cast le_trans (Nat.mul_le_mul_right J ha₀) (Nat.div_mul_le_self n J)
      have h2 : ((n / M : ℕ) : ℚ) ≤ (n : ℚ) / (M : ℚ) := by
        rw [le_div_iff₀ (by positivity : (0 : ℚ) < M)]
        exact_mod_cast Nat.div_mul_le_self n M
      have hring : ((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (n : ℚ) =
          (n : ℚ) / (J : ℚ) + (n : ℚ) / (M : ℚ) := by ring
      rw [Nat.cast_add, hring]; linarith only [h1, h2]
    have hden_ge : 2 * (n : ℚ) / (D_eps : ℚ) ≤
        2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ)) := by
      have h1 : (C : ℚ) ≤ 2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ)) := by
        have hnat : n ≤ 2 * (n - r) := by dsimp only [H] at hr; omega
        have hq : (n : ℚ) ≤ 2 * ((n - r : ℕ) : ℚ) := by exact_mod_cast hnat
        linarith
      have h2 : 2 * (n : ℚ) / (D_eps : ℚ) ≤ (C : ℚ) := by
        rw [div_le_iff₀ (by positivity : (0 : ℚ) < D_eps)]
        have hq : (2 : ℚ) * (n : ℚ) ≤ (D_eps : ℚ) * (C : ℚ) := by exact_mod_cast hC_lo
        linarith
      linarith
    have hden_pos : (0 : ℚ) < 2 * (n : ℚ) / (D_eps : ℚ) := by positivity
    have hfrac : ((n - r : ℕ) : ℚ) *
        ((corankAt A hSync (2 * v.length + (n - 1)) - C + n / M : ℕ) : ℚ) /
        (2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ))) ≤
        (n : ℚ) * (((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (n : ℚ)) / (2 * (n : ℚ) / (D_eps : ℚ)) := by
      have hnum := mul_le_mul hb_le hη_le (Nat.cast_nonneg _) (by positivity)
      exact div_le_div₀ (by positivity) hnum hden_pos hden_ge
    have hfrac_simp :
        (n : ℚ) * (((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (n : ℚ)) / (2 * (n : ℚ) / (D_eps : ℚ)) =
        θ * (n : ℚ) := by
      dsimp only [θ]
      have hn_ne : (n : ℚ) ≠ 0 := hn_pos.ne'
      have hD_ne : (D_eps : ℚ) ≠ 0 := by positivity
      field_simp
    have hfrac' : ((n - r : ℕ) : ℚ) *
        ((corankAt A hSync (2 * v.length + (n - 1)) - C + n / M : ℕ) : ℚ) /
        (2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ))) ≤ θ * (n : ℚ) := hfrac_simp ▸ hfrac
    have hterm2 :
        ((n : ℚ) / 2 + min (C : ℚ) ((n : ℚ) / 2)) *
          (((n - r : ℕ) : ℚ) * ((corankAt A hSync (2 * v.length + (n - 1)) - C + n / M : ℕ) : ℚ) /
            (2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ)))) ≤ θ * (n : ℚ) ^ 2 := by
      have hpos_f : (0 : ℚ) ≤ ((n - r : ℕ) : ℚ) *
          ((corankAt A hSync (2 * v.length + (n - 1)) - C + n / M : ℕ) : ℚ) /
          (2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ))) :=
        div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
      have hmul := mul_le_mul hcoef hfrac' hpos_f (by positivity)
      linarith
    change (corankGap A hSync r : ℚ) ≤ _ at hcap
    linarith only [hcap, hmin1, hterm2]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  have hcard_le1 : ((H - ρ : ℕ) : ℚ) ≤ (1 / 2 - (ρ : ℚ) / (n : ℚ)) * (n : ℚ) := by
    rw [Nat.cast_sub (by omega : ρ ≤ H)]
    have hH_q : (H : ℚ) ≤ (n : ℚ) / 2 := by
      have : 2 * H ≤ n := by dsimp only [H]; omega
      have hq : (2 : ℚ) * H ≤ n := by exact_mod_cast this
      linarith
    have hx_eq : ((ρ : ℚ) / (n : ℚ)) * (n : ℚ) = (ρ : ℚ) := div_mul_cancel₀ _ hn_pos.ne'
    linarith
  have hcard_le2 : ((H - ρ : ℕ) : ℚ) ≤ (n : ℚ) / 2 := by
    have : 2 * (H - ρ) ≤ n := by dsimp only [H]; omega
    have hq : (2 : ℚ) * ((H - ρ : ℕ) : ℚ) ≤ n := by exact_mod_cast this
    linarith
  have hC2_eq : ((C : ℚ) / (n : ℚ)) ^ 2 * (1 / 2 - (ρ : ℚ) / (n : ℚ)) * (n : ℚ) ^ 3 =
      ((1 / 2 - (ρ : ℚ) / (n : ℚ)) * (n : ℚ)) * (C : ℚ) ^ 2 := by
    have hn_ne : (n : ℚ) ≠ 0 := hn_pos.ne'
    field_simp
  have hmul1 : ((H - ρ : ℕ) : ℚ) * (C : ℚ) ^ 2 ≤
      ((C : ℚ) / (n : ℚ)) ^ 2 * (1 / 2 - (ρ : ℚ) / (n : ℚ)) * (n : ℚ) ^ 3 := by
    rw [hC2_eq]; exact mul_le_mul_of_nonneg_right hcard_le1 (sq_nonneg _)
  have hmul2 : ((H - ρ : ℕ) : ℚ) * (θ * (n : ℚ) ^ 2) ≤ (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hcard_le2 (show (0 : ℚ) ≤ θ * (n : ℚ) ^ 2 by dsimp only [θ]; positivity)
    linarith
  have hmul3 : ((H - ρ : ℕ) : ℚ) * (Ω : ℚ) ≤ ((n : ℚ) / 2 + 1) * (Ω : ℚ) :=
    mul_le_mul_of_nonneg_right (by linarith) hΩ0
  have hlam_q : (minCorankLen A hSync ρ : ℚ) ≤ (n : ℚ) ^ 2 := by exact_mod_cast hlam_ρ_le
  have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
  linarith only [htele_q, hsum, hmul1, hmul2, hmul3, hlam_q, hn2]

/-- Helper 2 for `prefix_bound_of_word`: Shitov cheap-gap upgrade on `[ρ, H)`. -/
private theorem prefix_bound_shitov [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (v : List α) {M ρ : ℕ}
    (hn : 100 ≤ Fintype.card Q) (hM : 1 ≤ M)
    (hC_le : Fintype.card Q - (A.image Finset.univ v).card ≤ Fintype.card Q / 2)
    (hρ_ge1 : 1 ≤ ρ) (hρ_lt_H : ρ < Fintype.card Q / 2)
    (hρ_big : 2 * ((Fintype.card Q - 2) / 2) < corankGap A hSync ρ)
    (hlam_ρ_le : minCorankLen A hSync ρ ≤ Fintype.card Q ^ 2) :
    let n := Fintype.card Q
    let C := n - (A.image Finset.univ v).card
    let Ω := (M + 1) * (v.length + (n - 1)) + 1
    let x : ℚ := (ρ : ℚ) / (n : ℚ)
    let c : ℚ := (C : ℚ) / (n : ℚ)
    (minCorankLen A hSync (n / 2) : ℚ) ≤
      2 * max (x - c) 0 * W_fun x * (n : ℚ) ^ 3 +
      ((n : ℚ) / 2 + 1) * (Ω : ℚ) + 2 * (n : ℚ) ^ 2 := by
  classical
  intro n C Ω x c
  let H := n / 2
  let k := (n - 2) / 2
  have hH_eq : H = k + 1 := by dsimp only [H, k]; omega
  have hH_le : H ≤ n - 1 := by dsimp only [H]; omega
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hΩ0 : (0 : ℚ) ≤ (Ω : ℚ) := Nat.cast_nonneg _
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hx1 : x ≤ 1 / 2 := by
    dsimp only [x]; rw [div_le_iff₀ hn_pos]
    have : 2 * ρ ≤ n := by omega
    have hq : (2 : ℚ) * ρ ≤ n := by exact_mod_cast this
    linarith
  have hW_nonneg : (0 : ℚ) ≤ W_fun x := by
    dsimp only [W_fun]; split_ifs
    · norm_num
    · exact mul_nonneg hx0 (by linarith)
  have htele : minCorankLen A hSync H =
      minCorankLen A hSync ρ + ∑ r ∈ Finset.Ico ρ H, corankGap A hSync r :=
    minCorankLen_eq_add_sum_Ico A hSync (by omega) hH_le
  have htele_q : (minCorankLen A hSync H : ℚ) =
      (minCorankLen A hSync ρ : ℚ) + ((∑ r ∈ Finset.Ico ρ H, corankGap A hSync r : ℕ) : ℚ) := by
    exact_mod_cast htele
  have hlam_C_le : minCorankLen A hSync C ≤ v.length := by
    have hC_le_n1 : C ≤ n - 1 := by omega
    have hv_card_le : (A.image Finset.univ v).card ≤ n - C := by
      have : (A.image Finset.univ v).card ≤ n := Finset.card_le_univ _
      dsimp only [C]; omega
    exact minCorankLen_le A hSync hC_le_n1 hv_card_le
  have hv_le_Ω : v.length ≤ Ω := by
    dsimp only [Ω]
    have h1 : v.length ≤ v.length + (n - 1) := Nat.le_add_right _ _
    have h2 : v.length + (n - 1) ≤ (M + 1) * (v.length + (n - 1)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h2r_le : (∑ r ∈ Finset.Ico ρ H, 2 * r) ≤ H ^ 2 := by
    have hsub : Finset.Ico ρ H ⊆ Finset.range H := by
      intro r hr; rw [Finset.mem_Ico] at hr; rw [Finset.mem_range]; omega
    have hodd : ∀ m : ℕ, (∑ r ∈ Finset.range m, (2 * r + 1)) = m ^ 2 := by
      intro m; induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    calc (∑ r ∈ Finset.Ico ρ H, (2 * r))
        ≤ ∑ r ∈ Finset.range H, (2 * r) := Finset.sum_le_sum_of_subset hsub
      _ ≤ ∑ r ∈ Finset.range H, (2 * r + 1) := Finset.sum_le_sum fun _ _ => by omega
      _ = H ^ 2 := hodd H
  by_cases hρ_le_C : ρ ≤ C
  · have hlam_ρ_Ω : minCorankLen A hSync ρ ≤ Ω :=
      le_trans (minCorankLen_mono A hSync hρ_le_C (by omega)) (le_trans hlam_C_le hv_le_Ω)
    have hpt : ∀ r ∈ Finset.Ico ρ H, corankGap A hSync r ≤ Ω + 2 * r := by
      intro r hr; rw [Finset.mem_Ico] at hr
      have hsh := shitov_corank_gap A hSync (by omega) (by omega)
        (by omega : ρ + 1 ≤ n - 1) (by omega : 2 * r < corankGap A hSync ρ)
      omega
    have hsum_nat : (∑ r ∈ Finset.Ico ρ H, corankGap A hSync r) ≤ H * Ω + H ^ 2 := by
      have h1 := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul] at h1
      have h3 : (H - ρ) * Ω ≤ H * Ω := Nat.mul_le_mul_right Ω (Nat.sub_le _ _)
      omega
    have hlam_H_nat : minCorankLen A hSync H ≤ (H + 1) * Ω + H ^ 2 := by
      rw [htele]; nlinarith only [hlam_ρ_Ω, hsum_nat]
    have hlam_H_q : (minCorankLen A hSync H : ℚ) ≤ ((H : ℚ) + 1) * (Ω : ℚ) + (H : ℚ) ^ 2 := by
      have hcast : ((minCorankLen A hSync H : ℕ) : ℚ) ≤ (((H + 1) * Ω + H ^ 2 : ℕ) : ℚ) := by
        exact_mod_cast hlam_H_nat
      push_cast at hcast; exact hcast
    have hH_le_half : (H : ℚ) ≤ (n : ℚ) / 2 := by
      have : 2 * H ≤ n := by dsimp only [H]; omega
      have hq : (2 : ℚ) * H ≤ n := by exact_mod_cast this
      linarith
    have hH2_le : (H : ℚ) ^ 2 ≤ (n : ℚ) ^ 2 := by nlinarith only [hH_le_half, hn_pos]
    have hHΩ_le : ((H : ℚ) + 1) * (Ω : ℚ) ≤ ((n : ℚ) / 2 + 1) * (Ω : ℚ) :=
      mul_le_mul_of_nonneg_right (by linarith) hΩ0
    have hterm0 : (0 : ℚ) ≤ 2 * max (x - c) 0 * W_fun x * (n : ℚ) ^ 3 + (n : ℚ) ^ 2 := by
      have : (0 : ℚ) ≤ max (x - c) 0 := le_max_right _ _
      positivity
    linarith only [hlam_H_q, hH2_le, hHΩ_le, hterm0]
  · have hC_lt_ρ : C < ρ := by omega
    let B_C : ℕ → Finset ℕ := fun i =>
      (Finset.Ico C ρ).filter (fun j => 2 * i - 1 ≤ corankGap A hSync j ∧ corankGap A hSync j ≤ 2 * i)
    let s_C : ℕ → ℕ := fun i => (B_C i).card
    have hBC_disj : Set.PairwiseDisjoint (↑(Finset.Icc 1 k) : Set ℕ) B_C := by
      intro i₁ hi₁ i₂ hi₂ hne
      rw [Finset.mem_coe, Finset.mem_Icc] at hi₁ hi₂
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro j h1 h2; simp only [B_C, Finset.mem_filter] at h1 h2; omega
    have hsum_sC : (∑ i ∈ Finset.Icc 1 k, s_C i) ≤ ρ - C := by
      rw [← Finset.card_biUnion hBC_disj]
      have hsub : (Finset.Icc 1 k).biUnion B_C ⊆ Finset.Ico C ρ := by
        intro j hj; rw [Finset.mem_biUnion] at hj; rcases hj with ⟨i, _, hji⟩
        exact (Finset.mem_filter.mp hji).1
      exact le_trans (Finset.card_le_card hsub) (by rw [Nat.card_Ico])
    have hδ_le : ∀ r ∈ Finset.Ico ρ H,
        corankGap A hSync r ≤ Ω + 2 * (∑ i ∈ Finset.Icc 1 r, i * s_C i) + 2 * r := by
      intro r hr; rw [Finset.mem_Ico] at hr
      have hex_τ : ∃ τ : ℕ, τ ≤ n - 2 ∧ 2 * r < corankGap A hSync τ := ⟨ρ, by omega, by omega⟩
      let τ := Nat.find hex_τ
      have hτ_spec : τ ≤ n - 2 ∧ 2 * r < corankGap A hSync τ := Nat.find_spec hex_τ
      have hτ_le_ρ : τ ≤ ρ := Nat.find_min' hex_τ ⟨by omega, by omega⟩
      have hτ_min : ∀ j < τ, corankGap A hSync j ≤ 2 * r := by
        intro j hj; by_contra hgt; push Not at hgt; exact Nat.find_min hex_τ hj ⟨by omega, hgt⟩
      have hsh : corankGap A hSync r ≤ minCorankLen A hSync τ + 2 * r :=
        shitov_corank_gap A hSync (by omega) (by omega) (by omega) hτ_spec.2
      have hlam_τ : minCorankLen A hSync τ ≤ Ω + 2 * ∑ i ∈ Finset.Icc 1 r, i * s_C i := by
        by_cases hτC : τ ≤ C
        · exact le_trans (minCorankLen_mono A hSync hτC (by omega))
            (le_trans (le_trans hlam_C_le hv_le_Ω) (Nat.le_add_right _ _))
        · have htele_τ := minCorankLen_eq_add_sum_Ico A hSync (by omega : C ≤ τ) (by omega : τ ≤ n - 1)
          have hsum_Cτ : (∑ j ∈ Finset.Ico C τ, corankGap A hSync j) ≤
              2 * ∑ i ∈ Finset.Icc 1 r, i * s_C i := by
            have hpos : (∑ j ∈ Finset.Ico C τ, corankGap A hSync j) =
                ∑ j ∈ (Finset.Ico C τ).filter (fun j => 1 ≤ corankGap A hSync j),
                  corankGap A hSync j := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun j _ => ?_
              by_cases h0 : corankGap A hSync j = 0
              · simp [h0]
              · have h1 : 1 ≤ corankGap A hSync j := by omega
                simp [h1]
            rw [hpos]
            have hsub_bi : (Finset.Ico C τ).filter (fun j => 1 ≤ corankGap A hSync j) ⊆
                (Finset.Icc 1 r).biUnion B_C := by
              intro j hj
              rw [Finset.mem_filter, Finset.mem_Ico] at hj
              have hle2r := hτ_min j hj.1.2
              rw [Finset.mem_biUnion]
              refine ⟨(corankGap A hSync j + 1) / 2, Finset.mem_Icc.mpr (by omega), ?_⟩
              simp only [B_C, Finset.mem_filter, Finset.mem_Ico]; omega
            have hdisj_r : Set.PairwiseDisjoint (↑(Finset.Icc 1 r) : Set ℕ) B_C :=
              fun i₁ hi₁ i₂ hi₂ hne =>
                hBC_disj (Finset.Icc_subset_Icc_right (by omega) hi₁)
                  (Finset.Icc_subset_Icc_right (by omega) hi₂) hne
            calc (∑ j ∈ (Finset.Ico C τ).filter (fun j => 1 ≤ corankGap A hSync j),
                    corankGap A hSync j)
                ≤ ∑ j ∈ (Finset.Icc 1 r).biUnion B_C, corankGap A hSync j :=
                  Finset.sum_le_sum_of_subset hsub_bi
              _ = ∑ i ∈ Finset.Icc 1 r, ∑ j ∈ B_C i, corankGap A hSync j :=
                  Finset.sum_biUnion hdisj_r
              _ ≤ ∑ i ∈ Finset.Icc 1 r, ∑ _j ∈ B_C i, (2 * i) :=
                  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2.2
              _ = ∑ i ∈ Finset.Icc 1 r, (B_C i).card * (2 * i) := by simp
              _ = 2 * ∑ i ∈ Finset.Icc 1 r, i * s_C i := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun i _ => by dsimp only [s_C]; ring
          omega
      omega
    have hsum_nat := Finset.sum_le_sum hδ_le
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
      smul_eq_mul, ← Finset.mul_sum] at hsum_nat
    have hswap : (∑ r ∈ Finset.Ico ρ H, ∑ i ∈ Finset.Icc 1 r, i * s_C i) =
        ∑ i ∈ Finset.Icc 1 k, s_C i * (i * (H - max ρ i)) := by
      have hinner : ∀ r ∈ Finset.Ico ρ H,
          (∑ i ∈ Finset.Icc 1 r, i * s_C i) =
          ∑ i ∈ Finset.Icc 1 k, if i ≤ r then s_C i * i else 0 := by
        intro r hr; rw [Finset.mem_Ico] at hr
        rw [← Finset.sum_filter]
        have hf : (Finset.Icc 1 k).filter (fun i => i ≤ r) = Finset.Icc 1 r := by
          ext i; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        rw [hf]; refine Finset.sum_congr rfl fun i _ => Nat.mul_comm _ _
      rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Icc] at hi
      rw [← Finset.sum_filter]
      have hf : (Finset.Ico ρ H).filter (fun r => i ≤ r) = Finset.Ico (max ρ i) H := by
        ext r; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
      rw [hf, Finset.sum_const, Nat.card_Ico, smul_eq_mul]; ring
    have hn_pos_nat : 0 < n := by omega
    have h2H_le : 2 * H ≤ n := by dsimp only [H]; omega
    have hρ_le_H : ρ ≤ H := le_of_lt hρ_lt_H
    have hswap_q :
        ((∑ i ∈ Finset.Icc 1 k, s_C i * (i * (H - max ρ i)) : ℕ) : ℚ) ≤
        (x - c) * W_fun x * (n : ℚ) ^ 3 := by
      rw [Nat.cast_sum]
      have hpt_i : ∀ i ∈ Finset.Icc 1 k,
          ((s_C i * (i * (H - max ρ i)) : ℕ) : ℚ) ≤ (s_C i : ℚ) * (W_fun x * (n : ℚ) ^ 2) := by
        intro i hi; rw [Finset.mem_Icc] at hi
        have hi_le_H : i ≤ H := le_trans hi.2 (by omega)
        have hmax_le : max ρ i ≤ H := max_le hρ_le_H hi_le_H
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hmax_le, Nat.cast_max]
        exact mul_le_mul_of_nonneg_left
          (shitov_prefix_weight_le hn_pos_nat h2H_le hρ_le_H hi_le_H)
          (Nat.cast_nonneg _)
      have h1 := Finset.sum_le_sum hpt_i
      rw [← Finset.sum_mul] at h1
      have hsum_q : (∑ i ∈ Finset.Icc 1 k, (s_C i : ℚ)) ≤ (ρ : ℚ) - (C : ℚ) := by
        have hq : ((∑ i ∈ Finset.Icc 1 k, s_C i : ℕ) : ℚ) ≤ ((ρ - C : ℕ) : ℚ) := by
          exact_mod_cast hsum_sC
        rw [Nat.cast_sum, Nat.cast_sub (le_of_lt hC_lt_ρ)] at hq
        exact hq
      have hmul := mul_le_mul_of_nonneg_right hsum_q (show (0 : ℚ) ≤ W_fun x * (n : ℚ) ^ 2 by positivity)
      have heq : ((ρ : ℚ) - (C : ℚ)) * (W_fun x * (n : ℚ) ^ 2) = (x - c) * W_fun x * (n : ℚ) ^ 3 := by
        dsimp only [x, c]; have hn_ne : (n : ℚ) ≠ 0 := hn_pos.ne'; field_simp
      linarith only [h1, hmul, heq]
    have hsum_q : ((∑ r ∈ Finset.Ico ρ H, corankGap A hSync r : ℕ) : ℚ) ≤
        ((H - ρ : ℕ) : ℚ) * (Ω : ℚ) + 2 * (x - c) * W_fun x * (n : ℚ) ^ 3 + (H : ℚ) ^ 2 := by
      have hcast : ((∑ r ∈ Finset.Ico ρ H, corankGap A hSync r : ℕ) : ℚ) ≤
          (((H - ρ) * Ω + 2 * ∑ i ∈ Finset.Icc 1 k, s_C i * (i * (H - max ρ i)) +
            ∑ r ∈ Finset.Ico ρ H, 2 * r : ℕ) : ℚ) := by
        rw [← hswap]; exact_mod_cast hsum_nat
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat] at hcast
      have h2r_q : ((∑ r ∈ Finset.Ico ρ H, 2 * r : ℕ) : ℚ) ≤ (H : ℚ) ^ 2 := by
        exact_mod_cast h2r_le
      linarith only [hcast, hswap_q, h2r_q]
    have hcard_le : ((H - ρ : ℕ) : ℚ) ≤ (n : ℚ) / 2 := by
      have : 2 * (H - ρ) ≤ n := by dsimp only [H]; omega
      have hq : (2 : ℚ) * ((H - ρ : ℕ) : ℚ) ≤ n := by exact_mod_cast this
      linarith
    have hH2_le : (H : ℚ) ^ 2 ≤ (n : ℚ) ^ 2 := by
      have : (H : ℚ) ≤ n := by exact_mod_cast (by dsimp only [H]; omega : H ≤ n)
      nlinarith only [this, hn_pos]
    have hlam_q : (minCorankLen A hSync ρ : ℚ) ≤ (n : ℚ) ^ 2 := by exact_mod_cast hlam_ρ_le
    have hxc_max : x - c ≤ max (x - c) 0 := le_max_left _ _
    have hxc_mul : 2 * (x - c) * W_fun x * (n : ℚ) ^ 3 ≤
        2 * max (x - c) 0 * W_fun x * (n : ℚ) ^ 3 := by
      have : (0 : ℚ) ≤ 2 * W_fun x * (n : ℚ) ^ 3 := by positivity
      nlinarith only [hxc_max, this]
    have hΩ_le : ((H - ρ : ℕ) : ℚ) * (Ω : ℚ) ≤ ((n : ℚ) / 2 + 1) * (Ω : ℚ) :=
      mul_le_mul_of_nonneg_right (by linarith) hΩ0
    linarith only [htele_q, hsum_q, hlam_q, hH2_le, hΩ_le, hxc_mul]

/-- Prefix bound on `[0, n / 2]` for Subcase 1 (`C ≤ n / 2`), combining the direct
Singularity-Free Cap and the Shitov cheap-gap upgrade into `pay_fun (C / n) x`. -/
private theorem prefix_bound_of_word [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    (v : List α) {J M D_eps : ℕ}
    (hn : 100 ≤ Fintype.card Q) (hJ : 1 ≤ J) (hM : 1 ≤ M) (hDeps : 1 ≤ D_eps)
    (hC_le : Fintype.card Q - (A.image Finset.univ v).card ≤ Fintype.card Q / 2)
    (hC_lo : 2 * Fintype.card Q ≤ D_eps * (Fintype.card Q - (A.image Finset.univ v).card))
    (ha₀ : corankAt A hSync (2 * v.length + (Fintype.card Q - 1)) -
      (Fintype.card Q - (A.image Finset.univ v).card) ≤ Fintype.card Q / J) :
    let n := Fintype.card Q
    let C := n - (A.image Finset.univ v).card
    let Ω := (M + 1) * (v.length + (n - 1)) + 1
    let θ : ℚ := ((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (D_eps : ℚ) / 2
    ∃ x : ℚ, 0 ≤ x ∧ x ≤ 1 / 2 ∧
      (minCorankLen A hSync (n / 2) : ℚ) ≤
        pay_fun ((C : ℚ) / (n : ℚ)) x * (n : ℚ) ^ 3 +
        (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 +
        ((n : ℚ) / 2 + 1) * (Ω : ℚ) + 2 * (n : ℚ) ^ 2 := by
  classical
  intro n C Ω θ
  let H := n / 2
  let k := (n - 2) / 2
  have hH_le : H ≤ n - 1 := by dsimp only [H]; omega
  have hθ0 : (0 : ℚ) ≤ θ := by dsimp only [θ]; positivity
  have hΩ0 : (0 : ℚ) ≤ (Ω : ℚ) := Nat.cast_nonneg _
  have hpay_half : pay_fun ((C : ℚ) / (n : ℚ)) (1 / 2) = 0 := by
    dsimp only [pay_fun]
    have h1 : ((C : ℚ) / (n : ℚ)) ^ 2 * (1 / 2 - 1 / 2) = 0 := by ring
    have hW : W_fun (1 / 2) = 0 := by
      have : ¬ (1 / 2 : ℚ) ≤ 1 / 4 := by norm_num
      simp only [W_fun, this, ↓reduceIte]; ring
    rw [h1, hW]; simp
  by_cases hbig : ∃ j : ℕ, j ≤ n - 2 ∧ 2 * k < corankGap A hSync j
  swap
  · push Not at hbig
    refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
    rw [hpay_half, zero_mul, zero_add]
    have hlam : minCorankLen A hSync H ≤ n ^ 2 := by
      rw [minCorankLen_eq_sum_range A hSync hH_le]
      calc (∑ j ∈ Finset.range H, corankGap A hSync j)
          ≤ ∑ _j ∈ Finset.range H, (2 * k) :=
            Finset.sum_le_sum fun j hj => hbig j (by rw [Finset.mem_range] at hj; omega)
        _ = H * (2 * k) := by simp
        _ ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
        _ = n ^ 2 := by ring
    have hq : (minCorankLen A hSync H : ℚ) ≤ (n : ℚ) ^ 2 := by exact_mod_cast hlam
    have hrest : (0 : ℚ) ≤ (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 + ((n : ℚ) / 2 + 1) * (Ω : ℚ) +
        (n : ℚ) ^ 2 := by positivity
    linarith
  let ρ := Nat.find hbig
  have hρ_spec : ρ ≤ n - 2 ∧ 2 * k < corankGap A hSync ρ := Nat.find_spec hbig
  have hρ_min : ∀ j < ρ, corankGap A hSync j ≤ 2 * k := by
    intro j hj; by_contra hgt; push Not at hgt; exact Nat.find_min hbig hj ⟨by omega, hgt⟩
  have hlam_ρ_le : minCorankLen A hSync ρ ≤ n ^ 2 := by
    rw [minCorankLen_eq_sum_range A hSync (by omega : ρ ≤ n - 1)]
    calc (∑ j ∈ Finset.range ρ, corankGap A hSync j)
        ≤ ∑ _j ∈ Finset.range ρ, (2 * k) :=
          Finset.sum_le_sum fun j hj => hρ_min j (Finset.mem_range.mp hj)
      _ = ρ * (2 * k) := by simp
      _ ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
      _ = n ^ 2 := by ring
  by_cases hH_le_ρ : H ≤ ρ
  · refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
    rw [hpay_half, zero_mul, zero_add]
    have hlam : minCorankLen A hSync H ≤ n ^ 2 :=
      le_trans (minCorankLen_mono A hSync hH_le_ρ (by omega)) hlam_ρ_le
    have hq : (minCorankLen A hSync H : ℚ) ≤ (n : ℚ) ^ 2 := by exact_mod_cast hlam
    have hrest : (0 : ℚ) ≤ (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 + ((n : ℚ) / 2 + 1) * (Ω : ℚ) +
        (n : ℚ) ^ 2 := by positivity
    linarith
  have hρ_lt_H : ρ < H := by omega
  have hρ_ge1 : 1 ≤ ρ := by
    by_contra h0
    have hρ0 : ρ = 0 := by omega
    have hgap0 := corankGap_le_pinFrankl A hSync (by omega : 0 + 1 ≤ n - 1)
    have hch : (0 + 2).choose 2 = 1 := by decide
    have hgt := hρ_spec.2
    rw [hρ0] at hgt; omega
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  let x : ℚ := (ρ : ℚ) / (n : ℚ)
  let c : ℚ := (C : ℚ) / (n : ℚ)
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hx1 : x ≤ 1 / 2 := by
    dsimp only [x]; rw [div_le_iff₀ hn_pos]
    have : 2 * ρ ≤ n := by omega
    have hq : (2 : ℚ) * ρ ≤ n := by exact_mod_cast this
    linarith
  refine ⟨x, hx0, hx1, ?_⟩
  have hBound1 := prefix_bound_direct A hSync hSC v (J := J) (M := M) (D_eps := D_eps) (ρ := ρ)
    hn hJ hM hDeps hC_lo ha₀ hρ_ge1 hρ_lt_H hlam_ρ_le
  have hBound2 := prefix_bound_shitov A hSync v (M := M) (ρ := ρ)
    hn hM hC_le hρ_ge1 hρ_lt_H hρ_spec.2 hlam_ρ_le
  have hθ_term : (0 : ℚ) ≤ (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 := by positivity
  dsimp only [pay_fun]
  by_cases hmin : c ^ 2 * (1 / 2 - x) ≤ 2 * max (x - c) 0 * W_fun x
  · rw [min_eq_left hmin]; exact hBound1
  · rw [min_eq_right (le_of_not_ge hmin)]
    change (minCorankLen A hSync (n / 2) : ℚ) ≤ _ at hBound2
    linarith only [hBound2, hθ_term]

/-- Monotonicity of `a * (a + 1) * (a + 2)` in `ℕ`. -/
private lemma mul_succ_mul_add_two_mono {a b : ℕ} (h : a ≤ b) :
    a * (a + 1) * (a + 2) ≤ b * (b + 1) * (b + 2) :=
  Nat.mul_le_mul (Nat.mul_le_mul h (Nat.add_le_add_right h 1)) (Nat.add_le_add_right h 2)

/-- Helper for `suffix_cap_saving`: Singularity-Free Cap summed over `[A_idx, B_idx)`. -/
private theorem suffix_cap_band [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    (v : List α) {J M D_eps A_idx B_idx : ℕ}
    (hn : 10000 ≤ Fintype.card Q) (hJ : 1 ≤ J) (hM : 1 ≤ M) (hDeps_pos : 1 ≤ D_eps)
    (hA_le_B : A_idx ≤ B_idx) (hB_le_n1 : B_idx ≤ Fintype.card Q - 1)
    (hA_ge : Fintype.card Q / 2 ≤ A_idx)
    (hB_def : B_idx = (Fintype.card Q + (Fintype.card Q - (A.image Finset.univ v).card)) / 2 -
      (Fintype.card Q / D_eps + 1))
    (ha₀ : corankAt A hSync (2 * v.length + (Fintype.card Q - 1)) -
      (Fintype.card Q - (A.image Finset.univ v).card) ≤ Fintype.card Q / J) :
    let n := Fintype.card Q
    let C := n - (A.image Finset.univ v).card
    let c : ℚ := (C : ℚ) / (n : ℚ)
    let cap_r : ℚ := min (c ^ 2) (c / 2)
    let Ω := (M + 1) * (v.length + (n - 1)) + 1
    let θ : ℚ := ((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (D_eps : ℚ) / 2
    (∑ r ∈ Finset.Ico A_idx B_idx, (corankGap A hSync r : ℚ)) ≤
      ((B_idx : ℚ) - (A_idx : ℚ)) * (cap_r * (n : ℚ) ^ 2) +
      (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 + ((n : ℚ) / 2) * (Ω : ℚ) := by
  intro n C c cap_r Ω θ
  change B_idx = (n + C) / 2 - (n / D_eps + 1) at hB_def
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hn_ne : (n : ℚ) ≠ 0 := hn_pos.ne'
  have hpt : ∀ r ∈ Finset.Ico A_idx B_idx,
      (corankGap A hSync r : ℚ) ≤ cap_r * (n : ℚ) ^ 2 + θ * (n : ℚ) ^ 2 + (Ω : ℚ) := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hR_eq : (A.image Finset.univ v).card = n - C := by
      have : (A.image Finset.univ v).card ≤ n := Finset.card_le_univ _
      dsimp only [C]; omega
    have h2b : (A.image Finset.univ v).card < 2 * (n - r) := by
      have : 2 * B_idx + 2 * (n / D_eps + 1) ≤ n + C := by omega
      omega
    have hcap := singularityFree_compression_cap A hSync hSC v (r := r) (M := M)
      (by omega) hM h2b
    have hmin1_eq : min ((C : ℚ) ^ 2) ((n : ℚ) * (C : ℚ) / 2) = cap_r * (n : ℚ) ^ 2 := by
      dsimp only [cap_r, c]
      by_cases hcmp : ((C : ℚ) / (n : ℚ)) ^ 2 ≤ ((C : ℚ) / (n : ℚ)) / 2
      · rw [min_eq_left hcmp, min_eq_left]
        · field_simp
        · have hmul := mul_le_mul_of_nonneg_right hcmp (sq_nonneg (n : ℚ))
          have h1 : ((C : ℚ) / (n : ℚ)) ^ 2 * (n : ℚ) ^ 2 = (C : ℚ) ^ 2 := by field_simp
          have h2 : ((C : ℚ) / (n : ℚ)) / 2 * (n : ℚ) ^ 2 = (n : ℚ) * (C : ℚ) / 2 := by field_simp
          linarith only [hmul, h1, h2]
      · push Not at hcmp
        rw [min_eq_right hcmp.le, min_eq_right]
        · field_simp
        · have hmul := mul_le_mul_of_nonneg_right hcmp.le (sq_nonneg (n : ℚ))
          have h1 : ((C : ℚ) / (n : ℚ)) ^ 2 * (n : ℚ) ^ 2 = (C : ℚ) ^ 2 := by field_simp
          have h2 : ((C : ℚ) / (n : ℚ)) / 2 * (n : ℚ) ^ 2 = (n : ℚ) * (C : ℚ) / 2 := by field_simp
          linarith only [hmul, h1, h2]
    have hcoef : (n : ℚ) / 2 + min (C : ℚ) ((n : ℚ) / 2) ≤ (n : ℚ) := by
      have : min (C : ℚ) ((n : ℚ) / 2) ≤ (n : ℚ) / 2 := min_le_right _ _
      linarith only [this]
    have hb_le : ((n - r : ℕ) : ℚ) ≤ (n : ℚ) := by exact_mod_cast (Nat.sub_le n r)
    have hη_le : ((corankAt A hSync (2 * v.length + (n - 1)) - C + n / M : ℕ) : ℚ) ≤
        ((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (n : ℚ) := by
      have h1 : ((corankAt A hSync (2 * v.length + (n - 1)) - C : ℕ) : ℚ) ≤ (n : ℚ) / (J : ℚ) := by
        rw [le_div_iff₀ (by positivity : (0 : ℚ) < J)]
        exact_mod_cast le_trans (Nat.mul_le_mul_right J ha₀) (Nat.div_mul_le_self n J)
      have h2 : ((n / M : ℕ) : ℚ) ≤ (n : ℚ) / (M : ℚ) := by
        rw [le_div_iff₀ (by positivity : (0 : ℚ) < M)]
        exact_mod_cast Nat.div_mul_le_self n M
      have hring : ((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (n : ℚ) =
          (n : ℚ) / (J : ℚ) + (n : ℚ) / (M : ℚ) := by ring
      rw [Nat.cast_add, hring]; linarith only [h1, h2]
    have hden_ge : 2 * (n : ℚ) / (D_eps : ℚ) ≤
        2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ)) := by
      have hnat1 : 2 * (n / D_eps + 1) ≤ 2 * (n - r) - (n - C) := by
        have : 2 * B_idx + 2 * (n / D_eps + 1) ≤ n + C := by omega
        omega
      have hnat2 : n < D_eps * (n / D_eps + 1) := by
        have := Nat.lt_mul_div_succ n (by omega : 0 < D_eps); linarith
      have hq1 : (2 : ℚ) * ((n / D_eps + 1 : ℕ) : ℚ) ≤
          2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ)) := by
        have hq : ((2 * (n / D_eps + 1) : ℕ) : ℚ) ≤ ((2 * (n - r) - (n - C) : ℕ) : ℚ) := by
          exact_mod_cast hnat1
        rw [Nat.cast_sub (by omega : n - C ≤ 2 * (n - r)), Nat.cast_sub (by omega : C ≤ n)] at hq
        push_cast at hq ⊢; linarith only [hq]
      have hq2 : (n : ℚ) / (D_eps : ℚ) ≤ ((n / D_eps + 1 : ℕ) : ℚ) := by
        rw [div_le_iff₀ (by positivity : (0 : ℚ) < D_eps)]
        have : (n : ℚ) ≤ (D_eps : ℚ) * ((n / D_eps + 1 : ℕ) : ℚ) := by exact_mod_cast hnat2.le
        linarith only [this]
      have hring : 2 * (n : ℚ) / (D_eps : ℚ) = 2 * ((n : ℚ) / (D_eps : ℚ)) := by ring
      linarith only [hq1, hq2, hring]
    have hden_pos : (0 : ℚ) < 2 * (n : ℚ) / (D_eps : ℚ) := by positivity
    have hfrac : ((n - r : ℕ) : ℚ) *
        ((corankAt A hSync (2 * v.length + (n - 1)) - C + n / M : ℕ) : ℚ) /
        (2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ))) ≤
        (n : ℚ) * (((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (n : ℚ)) / (2 * (n : ℚ) / (D_eps : ℚ)) := by
      have hnum := mul_le_mul hb_le hη_le (Nat.cast_nonneg _) (by positivity)
      exact div_le_div₀ (by positivity) hnum hden_pos hden_ge
    have hfrac_simp :
        (n : ℚ) * (((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (n : ℚ)) / (2 * (n : ℚ) / (D_eps : ℚ)) =
        θ * (n : ℚ) := by
      dsimp only [θ]
      have hD_ne : (D_eps : ℚ) ≠ 0 := by positivity
      field_simp
    have hfrac' : ((n - r : ℕ) : ℚ) *
        ((corankAt A hSync (2 * v.length + (n - 1)) - C + n / M : ℕ) : ℚ) /
        (2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ))) ≤ θ * (n : ℚ) := hfrac_simp ▸ hfrac
    have hterm2 :
        ((n : ℚ) / 2 + min (C : ℚ) ((n : ℚ) / 2)) *
          (((n - r : ℕ) : ℚ) * ((corankAt A hSync (2 * v.length + (n - 1)) - C + n / M : ℕ) : ℚ) /
            (2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ)))) ≤ θ * (n : ℚ) ^ 2 := by
      have hpos_f : (0 : ℚ) ≤ ((n - r : ℕ) : ℚ) *
          ((corankAt A hSync (2 * v.length + (n - 1)) - C + n / M : ℕ) : ℚ) /
          (2 * ((n - r : ℕ) : ℚ) - ((n : ℚ) - (C : ℚ))) :=
        div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith only [hden_ge, hden_pos])
      have hmul := mul_le_mul hcoef hfrac' hpos_f (by positivity)
      linarith only [hmul]
    change (corankGap A hSync r : ℚ) ≤ _ at hcap
    linarith only [hcap, hmin1_eq, hterm2]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hA_le_B] at hsum
  have hcard_half : (B_idx : ℚ) - (A_idx : ℚ) ≤ (n : ℚ) / 2 := by
    have : 2 * (B_idx - A_idx) ≤ n := by omega
    have hq : (2 : ℚ) * ((B_idx - A_idx : ℕ) : ℚ) ≤ n := by exact_mod_cast this
    rw [Nat.cast_sub hA_le_B] at hq; linarith only [hq]
  have h1 : ((B_idx : ℚ) - (A_idx : ℚ)) * (θ * (n : ℚ) ^ 2) ≤ (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hcard_half (show (0 : ℚ) ≤ θ * (n : ℚ) ^ 2 by dsimp only [θ]; positivity)
    linarith only [h]
  have h2 : ((B_idx : ℚ) - (A_idx : ℚ)) * (Ω : ℚ) ≤ ((n : ℚ) / 2) * (Ω : ℚ) :=
    mul_le_mul_of_nonneg_right hcard_half (Nat.cast_nonneg _)
  linarith only [hsum, h1, h2]

/-- Unified suffix cap-saving bound for `C ≤ 505 n / 1000` (covers BOTH Subcase 1 `C ≤ n / 2`
and Subcase 2 `n / 2 < C ≤ 505 n / 1000`). -/
private theorem suffix_cap_saving [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    (v : List α) {J M D_eps : ℕ}
    (hn : 10000 ≤ Fintype.card Q) (hJ : 1 ≤ J) (hM : 1 ≤ M)
    (hDeps_ge : 5000 ≤ D_eps) (hDeps_le : 10 * D_eps ≤ Fintype.card Q)
    (hC_lo : 100 * Fintype.card Q ≤ D_eps * (Fintype.card Q - (A.image Finset.univ v).card))
    (hC_hi : 1000 * (Fintype.card Q - (A.image Finset.univ v).card) ≤ 505 * Fintype.card Q)
    (ha₀ : corankAt A hSync (2 * v.length + (Fintype.card Q - 1)) -
      (Fintype.card Q - (A.image Finset.univ v).card) ≤ Fintype.card Q / J) :
    let n := Fintype.card Q
    let C := n - (A.image Finset.univ v).card
    let s := max (n / 2) C
    let c : ℚ := (C : ℚ) / (n : ℚ)
    let a_lo : ℚ := max (1 / 2 : ℚ) ((17 / 12 : ℚ) * c)
    let b_hi : ℚ := (1 + c) / 2
    let cap_r : ℚ := min (c ^ 2) (c / 2)
    let Ω := (M + 1) * (v.length + (n - 1)) + 1
    let θ : ℚ := ((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (D_eps : ℚ) / 2
    (∑ j ∈ Finset.Ico s (n - 1), (corankGap A hSync j : ℚ)) ≤
      ((n : ℚ) ^ 3 - (s : ℚ) ^ 3) / 6 -
        (((b_hi ^ 3 - a_lo ^ 3) / 6 - cap_r * (b_hi - a_lo)) * (n : ℚ) ^ 3) +
      (3 / 10 : ℚ) * (1 / (D_eps : ℚ)) * (n : ℚ) ^ 3 +
      (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 +
      ((n : ℚ) / 2) * (Ω : ℚ) + 4 * (n : ℚ) ^ 2 := by
  intro n C s c a_lo b_hi cap_r Ω θ
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hn_ne : (n : ℚ) ≠ 0 := hn_pos.ne'
  let A_idx := max ((n + 1) / 2) ((17 * C + 11) / 12)
  let B_idx := (n + C) / 2 - (n / D_eps + 1)
  have hdiv_Deps : D_eps * (n / D_eps) ≤ n := Nat.mul_div_le _ _
  have hC_ge_100 : 100 * (n / D_eps) ≤ C := by
    have h1 : D_eps * (100 * (n / D_eps)) ≤ 100 * n := by nlinarith only [hdiv_Deps]
    have h2 : D_eps * (100 * (n / D_eps)) ≤ D_eps * C := le_trans h1 hC_lo
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  have hn_div_ge10 : 10 ≤ n / D_eps :=
    (Nat.le_div_iff_mul_le (by omega : 0 < D_eps)).mpr (by linarith only [hDeps_le])
  have hs_le_A : s ≤ A_idx := by dsimp only [s, A_idx]; omega
  have hA_le_B : A_idx ≤ B_idx := by
    dsimp only [A_idx, B_idx]
    have h5000 : 5000 * (n / D_eps) ≤ n := by nlinarith only [hdiv_Deps, hDeps_ge]
    omega
  have hB_le_n1 : B_idx ≤ n - 1 := by dsimp only [B_idx]; omega
  -- Split Ico s (n - 1) = Ico s A_idx ∪ Ico A_idx B_idx ∪ Ico B_idx (n - 1)
  have hIco_sum :
      (∑ j ∈ Finset.Ico s (n - 1), (corankGap A hSync j : ℚ)) ≤
      ((∑ j ∈ Finset.Ico s (n - 1), (j + 2).choose 2 : ℕ) : ℚ) -
      ((∑ j ∈ Finset.Ico A_idx B_idx, (j + 2).choose 2 : ℕ) : ℚ) +
      (∑ j ∈ Finset.Ico A_idx B_idx, (corankGap A hSync j : ℚ)) := by
    have hsub : Finset.Ico A_idx B_idx ⊆ Finset.Ico s (n - 1) :=
      Finset.Ico_subset_Ico hs_le_A hB_le_n1
    have hpf_out : ∀ j ∈ Finset.Ico s (n - 1) \ Finset.Ico A_idx B_idx,
        (corankGap A hSync j : ℚ) ≤ (((j + 2).choose 2 : ℕ) : ℚ) := by
      intro j hj
      have hj' := (Finset.mem_sdiff.mp hj).1
      exact_mod_cast corankGap_le_pinFrankl A hSync (by rw [Finset.mem_Ico] at hj'; omega)
    have hsplit1 : (∑ j ∈ Finset.Ico s (n - 1), (corankGap A hSync j : ℚ)) =
        (∑ j ∈ Finset.Ico s (n - 1) \ Finset.Ico A_idx B_idx, (corankGap A hSync j : ℚ)) +
        (∑ j ∈ Finset.Ico A_idx B_idx, (corankGap A hSync j : ℚ)) :=
      (Finset.sum_sdiff hsub).symm
    have hsplit2 : ((∑ j ∈ Finset.Ico s (n - 1), (j + 2).choose 2 : ℕ) : ℚ) =
        (∑ j ∈ Finset.Ico s (n - 1) \ Finset.Ico A_idx B_idx, (((j + 2).choose 2 : ℕ) : ℚ)) +
        ((∑ j ∈ Finset.Ico A_idx B_idx, (j + 2).choose 2 : ℕ) : ℚ) := by
      rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sdiff hsub]
    have hle_out := Finset.sum_le_sum hpf_out
    linarith
  -- Pin–Frankl total upper bound on Ico s (n - 1): ≤ (n³ - s³) / 6
  have hPF_tot : ((∑ j ∈ Finset.Ico s (n - 1), (j + 2).choose 2 : ℕ) : ℚ) ≤
      ((n : ℚ) ^ 3 - (s : ℚ) ^ 3) / 6 := by
    have hs_le_n1 : s ≤ n - 1 := le_trans hs_le_A (le_trans hA_le_B hB_le_n1)
    have h6 := six_mul_sum_Ico_choose_two hs_le_n1
    have htop : (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) ≤ n ^ 3 := by zify [show 1 ≤ n by omega]; nlinarith
    have hbot : s ^ 3 ≤ s * (s + 1) * (s + 2) := by nlinarith
    have hmono : s * (s + 1) * (s + 2) ≤ (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) :=
      mul_succ_mul_add_two_mono hs_le_n1
    have hnat : 6 * ∑ j ∈ Finset.Ico s (n - 1), (j + 2).choose 2 + s ^ 3 ≤ n ^ 3 := by omega
    have hq : (6 : ℚ) * ((∑ j ∈ Finset.Ico s (n - 1), (j + 2).choose 2 : ℕ) : ℚ) + (s : ℚ) ^ 3 ≤
        (n : ℚ) ^ 3 := by exact_mod_cast hnat
    linarith
  -- Pin–Frankl lower bound on Ico A_idx B_idx: ≥ (B_idx³ - A_idx³) / 6 - n²
  have hPF_AB : ((B_idx : ℚ) ^ 3 - (A_idx : ℚ) ^ 3) / 6 - (n : ℚ) ^ 2 ≤
      ((∑ j ∈ Finset.Ico A_idx B_idx, (j + 2).choose 2 : ℕ) : ℚ) := by
    have h6 := six_mul_sum_Ico_choose_two hA_le_B
    have hB_ge : B_idx ^ 3 ≤ B_idx * (B_idx + 1) * (B_idx + 2) := by nlinarith
    have hA_le_cub : A_idx * (A_idx + 1) * (A_idx + 2) ≤ A_idx ^ 3 + 6 * n ^ 2 := by
      have hAn : A_idx ≤ n := by omega
      nlinarith
    have hnat : B_idx ^ 3 ≤ 6 * ∑ j ∈ Finset.Ico A_idx B_idx, (j + 2).choose 2 + A_idx ^ 3 + 6 * n ^ 2 := by
      omega
    have hq : (B_idx : ℚ) ^ 3 ≤
        6 * ((∑ j ∈ Finset.Ico A_idx B_idx, (j + 2).choose 2 : ℕ) : ℚ) +
        (A_idx : ℚ) ^ 3 + 6 * (n : ℚ) ^ 2 := by exact_mod_cast hnat
    linarith
  -- Singularity-Free Cap upper bound on Finset.Ico A_idx B_idx (via suffix_cap_band)
  have hCap_AB : (∑ r ∈ Finset.Ico A_idx B_idx, (corankGap A hSync r : ℚ)) ≤
      ((B_idx : ℚ) - (A_idx : ℚ)) * (cap_r * (n : ℚ) ^ 2) +
      (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 + ((n : ℚ) / 2) * (Ω : ℚ) :=
    suffix_cap_band A hSync hSC v (J := J) (M := M) (D_eps := D_eps) (A_idx := A_idx) (B_idx := B_idx)
      hn hJ hM (by omega) hA_le_B hB_le_n1 (by dsimp only [A_idx]; omega) rfl ha₀
  -- Compare discrete [A_idx/n, B_idx/n] saving against continuous [a_lo, b_hi] via cubic_strip_diff_le
  let uA : ℚ := (A_idx : ℚ) / (n : ℚ)
  let uB : ℚ := (B_idx : ℚ) / (n : ℚ)
  have hc_le : c ≤ 505 / 1000 := by
    dsimp only [c]; rw [div_le_iff₀ hn_pos]
    have hq : (1000 : ℚ) * (C : ℚ) ≤ 505 * (n : ℚ) := by exact_mod_cast hC_hi
    linarith
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have ha0 : 0 ≤ a_lo := le_trans (by norm_num) (le_max_left _ _)
  have hcap0 : 0 ≤ cap_r := le_min (sq_nonneg _) (by linarith)
  have hcap_le_a : cap_r ≤ a_lo ^ 2 / 2 := by
    have ha_ge1 : (17 / 12 : ℚ) * c ≤ a_lo := le_max_right _ _
    have hsq : ((17 / 12 : ℚ) * c) ^ 2 ≤ a_lo ^ 2 := by nlinarith only [ha_ge1, hc0, ha0]
    by_cases hcmp : c ≤ 1 / 2
    · have hc_min : cap_r ≤ c ^ 2 := min_le_left _ _
      nlinarith only [hc_min, hsq, hc0]
    · have hc_min : cap_r ≤ c / 2 := min_le_right _ _
      push Not at hcmp
      nlinarith only [hc_min, hsq, hcmp, hc0]
  have hb_le : b_hi ^ 2 / 2 ≤ 3 / 10 := by
    have h1 : b_hi ≤ (1 + 505 / 1000) / 2 := by dsimp only [b_hi]; linarith only [hc_le]
    have h2 : 0 ≤ b_hi := by dsimp only [b_hi]; linarith only [hc0]
    nlinarith only [h1, h2]
  have ha_le_uA : a_lo ≤ uA := by
    dsimp only [a_lo, uA]
    refine max_le ?_ ?_
    · rw [div_le_div_iff₀ (by norm_num) hn_pos]
      have : n ≤ 2 * A_idx := by dsimp only [A_idx]; omega
      have hq : (n : ℚ) ≤ 2 * (A_idx : ℚ) := by exact_mod_cast this
      linarith only [hq]
    · rw [le_div_iff₀ hn_pos]
      have : 17 * C ≤ 12 * A_idx := by dsimp only [A_idx]; omega
      have hq : (17 : ℚ) * (C : ℚ) ≤ 12 * (A_idx : ℚ) := by exact_mod_cast this
      have hc_mul : c * (n : ℚ) = (C : ℚ) := div_mul_cancel₀ _ hn_ne
      linarith only [hq, hc_mul]
  have huA_le_uB : uA ≤ uB := div_le_div_of_nonneg_right (by exact_mod_cast hA_le_B) hn_pos.le
  have huB_le_b : uB ≤ b_hi := by
    dsimp only [uB, b_hi, c]
    rw [div_le_iff₀ hn_pos]
    have : 2 * B_idx ≤ n + C := by dsimp only [B_idx]; omega
    have hq : (2 : ℚ) * (B_idx : ℚ) ≤ (n : ℚ) + (C : ℚ) := by exact_mod_cast this
    have hc_mul : (C : ℚ) / (n : ℚ) * (n : ℚ) = (C : ℚ) := div_mul_cancel₀ _ hn_ne
    have hring : (1 + (C : ℚ) / (n : ℚ)) / 2 * (n : ℚ) = ((n : ℚ) + (C : ℚ) / (n : ℚ) * (n : ℚ)) / 2 := by ring
    linarith only [hq, hc_mul, hring]
  have huA_sub : uA - a_lo ≤ 1 / (n : ℚ) := by
    dsimp only [uA]
    have h1 : (A_idx : ℚ) ≤ a_lo * (n : ℚ) + 1 := by
      by_cases hcmp : (n + 1) / 2 ≤ (17 * C + 11) / 12
      · have hAe : A_idx = (17 * C + 11) / 12 := max_eq_right hcmp
        have hnat : 12 * A_idx ≤ 17 * C + 11 := by rw [hAe]; omega
        have hq : (12 : ℚ) * (A_idx : ℚ) ≤ 17 * (C : ℚ) + 11 := by exact_mod_cast hnat
        have ha_ge : (17 / 12 : ℚ) * (C : ℚ) ≤ a_lo * (n : ℚ) := by
          have hm := mul_le_mul_of_nonneg_right (le_max_right (1 / 2 : ℚ) ((17 / 12 : ℚ) * c)) hn_pos.le
          have hc_mul : (17 / 12 : ℚ) * c * (n : ℚ) = (17 / 12 : ℚ) * (C : ℚ) := by
            dsimp only [c]; field_simp
          linarith only [hm, hc_mul]
        linarith only [hq, ha_ge]
      · have hAe : A_idx = (n + 1) / 2 := max_eq_left (by omega)
        have hnat : 2 * A_idx ≤ n + 1 := by rw [hAe]; omega
        have hq : (2 : ℚ) * (A_idx : ℚ) ≤ (n : ℚ) + 1 := by exact_mod_cast hnat
        have ha_ge : (n : ℚ) / 2 ≤ a_lo * (n : ℚ) := by
          have hm := mul_le_mul_of_nonneg_right (le_max_left (1 / 2 : ℚ) ((17 / 12 : ℚ) * c)) hn_pos.le
          linarith only [hm]
        linarith only [hq, ha_ge]
    have hmul : (uA - a_lo) * (n : ℚ) ≤ 1 := by
      have hu : uA * (n : ℚ) = (A_idx : ℚ) := div_mul_cancel₀ _ hn_ne
      linarith only [h1, hu]
    rw [le_div_iff₀ hn_pos]; exact hmul
  have hb_sub : b_hi - uB ≤ 1 / (D_eps : ℚ) + 2 / (n : ℚ) := by
    have hB_ge : b_hi * (n : ℚ) - (n : ℚ) / (D_eps : ℚ) - 2 ≤ (B_idx : ℚ) := by
      have hnat : n + C ≤ 2 * B_idx + 2 * (n / D_eps) + 3 := by dsimp only [B_idx]; omega
      have hq : (n : ℚ) + (C : ℚ) ≤ 2 * (B_idx : ℚ) + 2 * ((n / D_eps : ℕ) : ℚ) + 3 := by
        exact_mod_cast hnat
      have hdiv_q : ((n / D_eps : ℕ) : ℚ) ≤ (n : ℚ) / (D_eps : ℚ) := by
        rw [le_div_iff₀ (by positivity : (0 : ℚ) < D_eps)]
        exact_mod_cast Nat.div_mul_le_self n D_eps
      have hb_mul : b_hi * (n : ℚ) = ((n : ℚ) + (C : ℚ)) / 2 := by
        dsimp only [b_hi, c]; field_simp
      linarith only [hq, hdiv_q, hb_mul]
    have hmul : (b_hi - uB) * (n : ℚ) ≤ (1 / (D_eps : ℚ) + 2 / (n : ℚ)) * (n : ℚ) := by
      have h1 : uB * (n : ℚ) = (B_idx : ℚ) := div_mul_cancel₀ _ hn_ne
      have h2 : (1 / (D_eps : ℚ) + 2 / (n : ℚ)) * (n : ℚ) = (n : ℚ) / (D_eps : ℚ) + 2 := by
        field_simp
      linarith only [hB_ge, h1, h2]
    exact le_of_mul_le_mul_right hmul hn_pos
  have hstrip1 := (cubic_strip_diff_le ha0 le_rfl ha_le_uA (le_trans huA_le_uB huB_le_b)
    hcap0 hcap_le_a hb_le).2
  have hstrip2 := (cubic_strip_diff_le ha0 (le_trans ha_le_uA huA_le_uB) huB_le_b le_rfl
    hcap0 hcap_le_a hb_le).2
  have hAB_saving_unit :
      (b_hi ^ 3 - a_lo ^ 3) / 6 - cap_r * (b_hi - a_lo) -
        ((3 / 10 : ℚ) * (1 / (D_eps : ℚ)) + 1 / (n : ℚ)) ≤
      (uB ^ 3 - uA ^ 3) / 6 - cap_r * (uB - uA) := by
    have hadd :
        (b_hi ^ 3 - a_lo ^ 3) / 6 - cap_r * (b_hi - a_lo) =
        ((uA ^ 3 - a_lo ^ 3) / 6 - cap_r * (uA - a_lo)) +
        ((uB ^ 3 - uA ^ 3) / 6 - cap_r * (uB - uA)) +
        ((b_hi ^ 3 - uB ^ 3) / 6 - cap_r * (b_hi - uB)) := by ring
    have h2n : (2 : ℚ) / (n : ℚ) = 2 * (1 / (n : ℚ)) := by ring
    have hinv_n : (0 : ℚ) ≤ 1 / (n : ℚ) := by positivity
    linarith only [hadd, hstrip1, hstrip2, huA_sub, hb_sub, h2n, hinv_n]
  have hAB_saving_scaled :
      ((b_hi ^ 3 - a_lo ^ 3) / 6 - cap_r * (b_hi - a_lo)) * (n : ℚ) ^ 3 -
        (3 / 10 : ℚ) * (1 / (D_eps : ℚ)) * (n : ℚ) ^ 3 - (n : ℚ) ^ 2 ≤
      ((B_idx : ℚ) ^ 3 - (A_idx : ℚ) ^ 3) / 6 - ((B_idx : ℚ) - (A_idx : ℚ)) * (cap_r * (n : ℚ) ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right hAB_saving_unit (show (0 : ℚ) ≤ (n : ℚ) ^ 3 by positivity)
    have hlhs : ((b_hi ^ 3 - a_lo ^ 3) / 6 - cap_r * (b_hi - a_lo) -
        ((3 / 10 : ℚ) * (1 / (D_eps : ℚ)) + 1 / (n : ℚ))) * (n : ℚ) ^ 3 =
        ((b_hi ^ 3 - a_lo ^ 3) / 6 - cap_r * (b_hi - a_lo)) * (n : ℚ) ^ 3 -
        (3 / 10 : ℚ) * (1 / (D_eps : ℚ)) * (n : ℚ) ^ 3 - (n : ℚ) ^ 2 := by
      field_simp; ring
    have hrhs : ((uB ^ 3 - uA ^ 3) / 6 - cap_r * (uB - uA)) * (n : ℚ) ^ 3 =
        ((B_idx : ℚ) ^ 3 - (A_idx : ℚ) ^ 3) / 6 -
        ((B_idx : ℚ) - (A_idx : ℚ)) * (cap_r * (n : ℚ) ^ 2) := by
      dsimp only [uA, uB]; field_simp
    linarith only [hmul, hlhs, hrhs]
  have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
  linarith only [hIco_sum, hPF_tot, hPF_AB, hCap_AB, hAB_saving_scaled, hn2]

/-- Unified word-cap theorem covering BOTH Case A and Case C across all 3 subcases
(`C ≤ n / 2`, `n / 2 < C ≤ 505 n / 1000`, `505 n / 1000 < C`). -/
private theorem word_cap_beats_seven_forty_eight [Fintype Q] [Nonempty Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    (v : List α) {J M D_eps : ℕ} {margin : ℚ}
    (hn : 10000 ≤ Fintype.card Q) (hJ : 1 ≤ J) (hM : 1 ≤ M)
    (hDeps_ge : 5000 ≤ D_eps) (hDeps_le : 10 * D_eps ≤ Fintype.card Q)
    (hC_lo : 100 * Fintype.card Q ≤ D_eps * (Fintype.card Q - (A.image Finset.univ v).card))
    (ha₀ : corankAt A hSync (2 * v.length + (Fintype.card Q - 1)) -
      (Fintype.card Q - (A.image Finset.univ v).card) ≤ Fintype.card Q / J)
    (hmargin_le : margin ≤ 1 / 1600)
    (hmargin_sub1 : Fintype.card Q - (A.image Finset.univ v).card ≤ Fintype.card Q / 2 →
      ∀ x : ℚ, 0 ≤ x → x ≤ 1 / 2 →
        margin ≤ S_rat (((Fintype.card Q - (A.image Finset.univ v).card : ℕ) : ℚ) / (Fintype.card Q : ℚ)) -
          pay_fun (((Fintype.card Q - (A.image Finset.univ v).card : ℕ) : ℚ) / (Fintype.card Q : ℚ)) x) :
    let n := Fintype.card Q
    let Ω := (M + 1) * (v.length + (n - 1)) + 1
    let θ : ℚ := ((1 : ℚ) / (J : ℚ) + 1 / (M : ℚ)) * (D_eps : ℚ) / 2
    (minCorankLen A hSync (n - 1) : ℚ) ≤
      (7 / 48 - margin + (3 / 10 : ℚ) * (1 / (D_eps : ℚ)) + θ) * (n : ℚ) ^ 3 +
      ((n : ℚ) + 1) * (Ω : ℚ) + 7 * (n : ℚ) ^ 2 := by
  intro n Ω θ
  let C := n - (A.image Finset.univ v).card
  let c : ℚ := (C : ℚ) / (n : ℚ)
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hn_ne : (n : ℚ) ≠ 0 := hn_pos.ne'
  have hC_le_n1 : C ≤ n - 1 := by
    obtain ⟨q₀⟩ := hSync.nonempty
    have hpos : 1 ≤ (A.image Finset.univ v).card :=
      Finset.card_pos.mpr ⟨A.eval q₀ v, (DFA.mem_image A _ _ _).mpr ⟨q₀, Finset.mem_univ q₀, rfl⟩⟩
    dsimp only [C]; omega
  have hlam_C_le : minCorankLen A hSync C ≤ Ω := by
    have h1 : minCorankLen A hSync C ≤ v.length := by
      have hcard : (A.image Finset.univ v).card ≤ n - C := by
        have : (A.image Finset.univ v).card ≤ n := Finset.card_le_univ _
        dsimp only [C]; omega
      exact minCorankLen_le A hSync hC_le_n1 hcard
    have h2 : v.length ≤ Ω := by
      dsimp only [Ω]
      have : v.length + (n - 1) ≤ (M + 1) * (v.length + (n - 1)) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega
  -- Subcase 1: C ≤ n / 2
  by_cases hC1 : C ≤ n / 2
  · obtain ⟨x, hx0, hx1, hpre⟩ := prefix_bound_of_word A hSync hSC v (J := J) (M := M) (D_eps := D_eps)
      (by omega) hJ hM (by omega) hC1 (by omega) ha₀
    have hsuf := suffix_cap_saving A hSync hSC v (J := J) (M := M) (D_eps := D_eps)
      hn hJ hM hDeps_ge hDeps_le hC_lo (by omega) ha₀
    have hs_eq : max (n / 2) C = n / 2 := max_eq_left hC1
    have htele := minCorankLen_eq_add_sum_Ico A hSync (by omega : n / 2 ≤ n - 1) le_rfl
    have htele_q : (minCorankLen A hSync (n - 1) : ℚ) =
        (minCorankLen A hSync (n / 2) : ℚ) +
        ∑ j ∈ Finset.Ico (n / 2) (n - 1), (corankGap A hSync j : ℚ) := by
      have hcast : ((minCorankLen A hSync (n - 1) : ℕ) : ℚ) =
          ((minCorankLen A hSync (n / 2) + ∑ j ∈ Finset.Ico (n / 2) (n - 1), corankGap A hSync j : ℕ) : ℚ) := by
        exact_mod_cast htele
      rw [Nat.cast_add, Nat.cast_sum] at hcast; exact hcast
    have hc0 : 0 ≤ c := by dsimp only [c]; positivity
    have hc_le_half : c ≤ 1 / 2 := by
      dsimp only [c]; rw [div_le_iff₀ hn_pos]
      have : 2 * C ≤ n := by omega
      have hq : (2 : ℚ) * C ≤ n := by exact_mod_cast this
      linarith
    have hcap_eq : min (c ^ 2) (c / 2) = c ^ 2 := min_eq_left (by nlinarith only [hc0, hc_le_half])
    have hH_cub : ((n : ℚ) ^ 3 - ((n / 2 : ℕ) : ℚ) ^ 3) / 6 ≤ (7 / 48 : ℚ) * (n : ℚ) ^ 3 + (n : ℚ) ^ 2 := by
      have hn_q : (10000 : ℚ) ≤ n := by exact_mod_cast hn
      have h1 : (n : ℚ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℚ) := by
        have : n ≤ 2 * (n / 2) + 1 := by omega
        have hq : (n : ℚ) ≤ 2 * ((n / 2 : ℕ) : ℚ) + 1 := by exact_mod_cast this
        linarith
      have h2 : ((n : ℚ) / 2 - 1 / 2) ^ 3 ≤ ((n / 2 : ℕ) : ℚ) ^ 3 :=
        pow_le_pow_left₀ (by linarith only [hn_q]) h1 3
      have hexp : ((n : ℚ) ^ 3 - ((n : ℚ) / 2 - 1 / 2) ^ 3) / 6 =
          (7 / 48 : ℚ) * (n : ℚ) ^ 3 + (n : ℚ) ^ 2 / 16 - (n : ℚ) / 16 + 1 / 48 := by ring
      have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
      linarith only [h2, hexp, hn_q, hn2]
    have hmargin := hmargin_sub1 hC1 x hx0 hx1
    have hmargin_scaled :
        margin * (n : ℚ) ^ 3 ≤ (S_rat c - pay_fun c x) * (n : ℚ) ^ 3 :=
      mul_le_mul_of_nonneg_right hmargin (by positivity)
    have hSrat_def :
        (((1 + c) / 2) ^ 3 - (max (1 / 2 : ℚ) ((17 / 12 : ℚ) * c)) ^ 3) / 6 -
          c ^ 2 * ((1 + c) / 2 - max (1 / 2 : ℚ) ((17 / 12 : ℚ) * c)) = S_rat c := rfl
    have hpre_c : (minCorankLen A hSync (n / 2) : ℚ) ≤
        pay_fun c x * (n : ℚ) ^ 3 + (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 +
        ((n : ℚ) / 2 + 1) * (Ω : ℚ) + 2 * (n : ℚ) ^ 2 := hpre
    have hsuf_c : (∑ j ∈ Finset.Ico (max (n / 2) C) (n - 1), (corankGap A hSync j : ℚ)) ≤
        ((n : ℚ) ^ 3 - ((max (n / 2) C : ℕ) : ℚ) ^ 3) / 6 -
          ((((1 + c) / 2) ^ 3 - (max (1 / 2 : ℚ) ((17 / 12 : ℚ) * c)) ^ 3) / 6 -
            min (c ^ 2) (c / 2) * ((1 + c) / 2 - max (1 / 2 : ℚ) ((17 / 12 : ℚ) * c))) * (n : ℚ) ^ 3 +
        (3 / 10 : ℚ) * (1 / (D_eps : ℚ)) * (n : ℚ) ^ 3 +
        (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 + ((n : ℚ) / 2) * (Ω : ℚ) + 4 * (n : ℚ) ^ 2 := hsuf
    rw [hs_eq, hcap_eq, hSrat_def] at hsuf_c
    linarith only [htele_q, hpre_c, hsuf_c, hH_cub, hmargin_scaled]
  -- Subcase 2: n / 2 < C ≤ 505 n / 1000
  · by_cases hC2 : 1000 * C ≤ 505 * n
    · have hsuf := suffix_cap_saving A hSync hSC v (J := J) (M := M) (D_eps := D_eps)
        hn hJ hM hDeps_ge hDeps_le hC_lo hC2 ha₀
      have hs_eq : max (n / 2) C = C := max_eq_right (by omega)
      have htele := minCorankLen_eq_add_sum_Ico A hSync hC_le_n1 le_rfl
      have htele_q : (minCorankLen A hSync (n - 1) : ℚ) =
          (minCorankLen A hSync C : ℚ) +
          ∑ j ∈ Finset.Ico C (n - 1), (corankGap A hSync j : ℚ) := by
        have hcast : ((minCorankLen A hSync (n - 1) : ℕ) : ℚ) =
            ((minCorankLen A hSync C + ∑ j ∈ Finset.Ico C (n - 1), corankGap A hSync j : ℕ) : ℚ) := by
          exact_mod_cast htele
        rw [Nat.cast_add, Nat.cast_sum] at hcast; exact hcast
      have hc_ge : 1 / 2 ≤ c := by
        dsimp only [c]; rw [div_le_div_iff₀ (by norm_num) hn_pos]
        have : n ≤ 2 * C := by omega
        have hq : (n : ℚ) ≤ 2 * (C : ℚ) := by exact_mod_cast this
        linarith
      have hc_le : c ≤ 505 / 1000 := by
        dsimp only [c]; rw [div_le_iff₀ hn_pos]
        have hq : (1000 : ℚ) * (C : ℚ) ≤ 505 * (n : ℚ) := by exact_mod_cast hC2
        linarith
      have ha_eq : max (1 / 2 : ℚ) ((17 / 12 : ℚ) * c) = (17 / 12 : ℚ) * c :=
        max_eq_right (by linarith)
      have hcap_eq : min (c ^ 2) (c / 2) = c / 2 := min_eq_right (by nlinarith only [hc_ge])
      have hhi := rational_payment_ge_hi hc_ge hc_le
      have hhi_scaled : (55 / 82944 : ℚ) * (n : ℚ) ^ 3 ≤
          ((c ^ 3 - 1 / 8) / 6 +
            ((((1 + c) / 2) ^ 3 - ((17 / 12 : ℚ) * c) ^ 3) / 6 -
              (c / 2) * ((1 + c) / 2 - (17 / 12 : ℚ) * c))) * (n : ℚ) ^ 3 :=
        mul_le_mul_of_nonneg_right hhi (by positivity)
      have hcub_eq : ((n : ℚ) ^ 3 - (C : ℚ) ^ 3) / 6 =
          (7 / 48 : ℚ) * (n : ℚ) ^ 3 - ((c ^ 3 - 1 / 8) / 6) * (n : ℚ) ^ 3 := by
        dsimp only [c]; field_simp; ring
      have hsuf_c : (∑ j ∈ Finset.Ico (max (n / 2) C) (n - 1), (corankGap A hSync j : ℚ)) ≤
          ((n : ℚ) ^ 3 - ((max (n / 2) C : ℕ) : ℚ) ^ 3) / 6 -
            ((((1 + c) / 2) ^ 3 - (max (1 / 2 : ℚ) ((17 / 12 : ℚ) * c)) ^ 3) / 6 -
              min (c ^ 2) (c / 2) * ((1 + c) / 2 - max (1 / 2 : ℚ) ((17 / 12 : ℚ) * c))) * (n : ℚ) ^ 3 +
          (3 / 10 : ℚ) * (1 / (D_eps : ℚ)) * (n : ℚ) ^ 3 +
          (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 + ((n : ℚ) / 2) * (Ω : ℚ) + 4 * (n : ℚ) ^ 2 := hsuf
      rw [hs_eq, ha_eq, hcap_eq, hcub_eq] at hsuf_c
      have hlam_q : (minCorankLen A hSync C : ℚ) ≤ (Ω : ℚ) := by exact_mod_cast hlam_C_le
      have hθ0 : (0 : ℚ) ≤ (1 / 2 : ℚ) * θ * (n : ℚ) ^ 3 := by dsimp only [θ]; positivity
      have hΩ0 : (0 : ℚ) ≤ (n : ℚ) / 2 * (Ω : ℚ) := by positivity
      have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
      have hn3 : (0 : ℚ) ≤ (n : ℚ) ^ 3 := by positivity
      have hm_le : margin * (n : ℚ) ^ 3 ≤ (55 / 82944 : ℚ) * (n : ℚ) ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) hn3
      linarith only [htele_q, hlam_q, hsuf_c, hhi_scaled, hθ0, hΩ0, hn2, hm_le]
    -- Subcase 3: 505 n / 1000 < C — direct v + Pin–Frankl tail!
    · have htele := minCorankLen_eq_add_sum_Ico A hSync hC_le_n1 le_rfl
      have hpf : (∑ j ∈ Finset.Ico C (n - 1), corankGap A hSync j) ≤
          ∑ j ∈ Finset.Ico C (n - 1), (j + 2).choose 2 :=
        Finset.sum_le_sum fun j hj => corankGap_le_pinFrankl A hSync (by rw [Finset.mem_Ico] at hj; omega)
      have h6 := Nat.mul_le_mul_left 6 hpf
      rw [six_mul_sum_Ico_choose_two hC_le_n1] at h6
      have htop : (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) ≤ n ^ 3 := by zify [show 1 ≤ n by omega]; nlinarith
      have hbot : C ^ 3 ≤ C * (C + 1) * (C + 2) := by nlinarith
      have hmono : C * (C + 1) * (C + 2) ≤ (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) :=
        mul_succ_mul_add_two_mono hC_le_n1
      have htail_nat : 6 * (∑ j ∈ Finset.Ico C (n - 1), corankGap A hSync j) + C ^ 3 ≤ n ^ 3 := by omega
      have htail_q : ((∑ j ∈ Finset.Ico C (n - 1), corankGap A hSync j : ℕ) : ℚ) ≤
          ((n : ℚ) ^ 3 - (C : ℚ) ^ 3) / 6 := by
        have hq : (6 : ℚ) * ((∑ j ∈ Finset.Ico C (n - 1), corankGap A hSync j : ℕ) : ℚ) +
            (C : ℚ) ^ 3 ≤ (n : ℚ) ^ 3 := by exact_mod_cast htail_nat
        linarith
      have hC_ge : (505 / 1000 : ℚ) * (n : ℚ) ≤ (C : ℚ) := by
        have : 505 * n ≤ 1000 * C := by omega
        have hq : (505 : ℚ) * n ≤ 1000 * (C : ℚ) := by exact_mod_cast this
        linarith
      have hn3 : (0 : ℚ) ≤ (n : ℚ) ^ 3 := by positivity
      have hC3_ge : (505 / 1000 : ℚ) ^ 3 * (n : ℚ) ^ 3 ≤ (C : ℚ) ^ 3 := by
        have h1 : ((505 / 1000 : ℚ) * (n : ℚ)) ^ 3 ≤ (C : ℚ) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hC_ge 3
        have h2 : ((505 / 1000 : ℚ) * (n : ℚ)) ^ 3 = (505 / 1000 : ℚ) ^ 3 * (n : ℚ) ^ 3 := by ring
        linarith only [h1, h2]
      have hnum_scaled : (1 - (505 / 1000 : ℚ) ^ 3) / 6 * (n : ℚ) ^ 3 ≤
          (7 / 48 - 1 / 1600 : ℚ) * (n : ℚ) ^ 3 :=
        mul_le_mul_of_nonneg_right (by norm_num) hn3
      have hlam_q : (minCorankLen A hSync C : ℚ) ≤ (Ω : ℚ) := by exact_mod_cast hlam_C_le
      have htele_q : (minCorankLen A hSync (n - 1) : ℚ) =
          (minCorankLen A hSync C : ℚ) +
          ((∑ j ∈ Finset.Ico C (n - 1), corankGap A hSync j : ℕ) : ℚ) := by exact_mod_cast htele
      have hpos_extra : (0 : ℚ) ≤
          ((3 / 10 : ℚ) * (1 / (D_eps : ℚ)) + θ) * (n : ℚ) ^ 3 +
          (n : ℚ) * (Ω : ℚ) + 7 * (n : ℚ) ^ 2 := by dsimp only [θ]; positivity
      have hm_le : margin * (n : ℚ) ^ 3 ≤ (1 / 1600 : ℚ) * (n : ℚ) ^ 3 :=
        mul_le_mul_of_nonneg_right hmargin_le hn3
      linarith only [htele_q, hlam_q, htail_q, hC3_ge, hnum_scaled, hpos_extra, hm_le]

/-- **Case B Total Bound**: Under `D(h) < n / D_c1` and `D(n² / D_eta) < n / 10`,
`λ(n - 1) ≤ (7 / 48 - 1 / 1000) * n³ + (D_c1 + 20) * n²` (zero `ln`, zero `√c₁`!). -/
private theorem caseB_beats_seven_forty_eight [Fintype Q] [Nonempty Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    {D_eta D_c1 R : ℕ}
    (hD_eta : 10 ^ 14 ≤ D_eta) (hD_c1 : D_c1 = 50 * D_eta)
    (hR_pow : (D_c1 : ℚ) < (39 / 38 : ℚ) ^ R)
    (hn1 : 2 * (R + 1) * D_eta + 10 * D_eta ≤ Fintype.card Q)
    (hn2 : 150 * D_eta ^ 2 ≤ Fintype.card Q)
    (hDh : D_c1 * shortCorank A hSync < Fintype.card Q)
    (hDt : 10 * corankAt A hSync (Fintype.card Q ^ 2 / D_eta) < Fintype.card Q) :
    let n := Fintype.card Q
    (minCorankLen A hSync (n - 1) : ℚ) ≤
      (7 / 48 - 1 / 1000 : ℚ) * (n : ℚ) ^ 3 + ((D_c1 : ℚ) + 20) * (n : ℚ) ^ 2 := by
  intro n
  have hn_big : 10000 ≤ n := by nlinarith only [hD_eta, hn2]
  have hn_q : (10000 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn_big
  have hDc1_pos_nat : 0 < D_c1 := by omega
  have hDc1_pos : (0 : ℚ) < (D_c1 : ℚ) := by exact_mod_cast hDc1_pos_nat
  let P := (499 * n) / 1000
  let H := n / 2
  let B_end := (58 * n) / 100
  have hP_le_H : P ≤ H := by dsimp only [P, H]; omega
  have hH_le_B : H ≤ B_end := by dsimp only [H, B_end]; omega
  have hB_le_n1 : B_end ≤ n - 1 := by dsimp only [B_end]; omega
  -- 1. Prefix [0, P): ap_plateau_inequality with M = D_c1
  have hPre1 : (minCorankLen A hSync P : ℚ) ≤
      (250 / (D_c1 : ℚ)) * (n : ℚ) ^ 3 + (D_c1 : ℚ) * (n : ℚ) ^ 2 + (n : ℚ) ^ 2 := by
    rw [minCorankLen_eq_sum_range A hSync (by omega : P ≤ n - 1), Nat.cast_sum]
    have hpt : ∀ r ∈ Finset.range P,
        (corankGap A hSync r : ℚ) ≤ (500 / (D_c1 : ℚ)) * (n : ℚ) ^ 2 + (D_c1 : ℚ) * (n : ℚ) + 1 := by
      intro r hr
      rw [Finset.mem_range] at hr
      by_cases hr0 : r = 0
      · subst hr0
        have h0 := corankGap_le_pinFrankl A hSync (by omega : 0 + 1 ≤ n - 1)
        have hch : (0 + 2).choose 2 = 1 := by decide
        have hq : (corankGap A hSync 0 : ℚ) ≤ 1 := by exact_mod_cast (by omega : corankGap A hSync 0 ≤ 1)
        have hpos : (0 : ℚ) ≤ (500 / (D_c1 : ℚ)) * (n : ℚ) ^ 2 + (D_c1 : ℚ) * (n : ℚ) := by positivity
        linarith
      · have hap := ap_plateau_inequality A hSync hSC (r := r) (M := D_c1)
          (by omega) (by dsimp only [P] at hr; omega) (by omega)
        have hden_ge : (n : ℚ) / 500 ≤ (n : ℚ) - 2 * (r : ℚ) := by
          have : 1000 * r ≤ 499 * n := by dsimp only [P] at hr; omega
          have hq : (1000 : ℚ) * r ≤ 499 * n := by exact_mod_cast this
          linarith
        have hden_pos : (0 : ℚ) < (n : ℚ) / 500 := by positivity
        have hDh_q : (shortCorank A hSync : ℚ) ≤ (n : ℚ) / (D_c1 : ℚ) := by
          rw [le_div_iff₀ hDc1_pos]
          have hq : (D_c1 : ℚ) * (shortCorank A hSync : ℚ) ≤ (n : ℚ) := by exact_mod_cast hDh.le
          linarith
        have hr_le : (r : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : r ≤ n)
        have hnr0 : (0 : ℚ) ≤ (n : ℚ) - (r : ℚ) := by linarith
        have hcomb :
            (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * (shortCorank A hSync : ℚ) +
            (r : ℚ) ^ 2 / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / (D_c1 : ℚ)) ≤
            ((r : ℚ) * (n : ℚ)) / ((n : ℚ) / 500) * ((n : ℚ) / (D_c1 : ℚ)) := by
          have h1 :
              (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * (shortCorank A hSync : ℚ) ≤
              (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / (D_c1 : ℚ)) :=
            mul_le_mul_of_nonneg_left hDh_q
              (div_nonneg (mul_nonneg (Nat.cast_nonneg r) hnr0) (by linarith only [hden_ge, hden_pos]))
          have h2 :
              (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / (D_c1 : ℚ)) +
              (r : ℚ) ^ 2 / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / (D_c1 : ℚ)) =
              ((r : ℚ) * (n : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / (D_c1 : ℚ)) := by ring
          have h3 : ((r : ℚ) * (n : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) ≤ ((r : ℚ) * (n : ℚ)) / ((n : ℚ) / 500) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos hden_ge
          have h4 := mul_le_mul_of_nonneg_right h3 (div_nonneg (Nat.cast_nonneg n) hDc1_pos.le)
          linarith
        have hsimp : ((r : ℚ) * (n : ℚ)) / ((n : ℚ) / 500) * ((n : ℚ) / (D_c1 : ℚ)) ≤
            (500 / (D_c1 : ℚ)) * (n : ℚ) ^ 2 := by
          have hn_ne : (n : ℚ) ≠ 0 := by positivity
          have heq : ((r : ℚ) * (n : ℚ)) / ((n : ℚ) / 500) * ((n : ℚ) / (D_c1 : ℚ)) =
              (500 / (D_c1 : ℚ)) * ((r : ℚ) * (n : ℚ)) := by field_simp
          rw [heq]
          have h500 : (0 : ℚ) ≤ 500 / (D_c1 : ℚ) := div_nonneg (by norm_num) hDc1_pos.le
          have hrn : (r : ℚ) * (n : ℚ) ≤ (n : ℚ) ^ 2 := by nlinarith only [hr_le, hn_q]
          exact mul_le_mul_of_nonneg_left hrn h500
        change (corankGap A hSync r : ℚ) ≤ _ at hap
        linarith
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hP_le : (P : ℚ) ≤ (n : ℚ) / 2 := by
      have : 2 * P ≤ n := by dsimp only [P]; omega
      have hq : (2 : ℚ) * P ≤ n := by exact_mod_cast this
      linarith
    have h1 : (P : ℚ) * ((500 / (D_c1 : ℚ)) * (n : ℚ) ^ 2) ≤ (250 / (D_c1 : ℚ)) * (n : ℚ) ^ 3 := by
      have hmul := mul_le_mul_of_nonneg_right hP_le (by positivity : (0 : ℚ) ≤ (500 / (D_c1 : ℚ)) * (n : ℚ) ^ 2)
      have heq : (n : ℚ) / 2 * ((500 / (D_c1 : ℚ)) * (n : ℚ) ^ 2) = (250 / (D_c1 : ℚ)) * (n : ℚ) ^ 3 := by ring
      linarith only [hmul, heq]
    have h2 : (P : ℚ) * ((D_c1 : ℚ) * (n : ℚ)) ≤ (D_c1 : ℚ) * (n : ℚ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right (show (P : ℚ) ≤ n by linarith only [hP_le, hn_q])
        (by positivity : (0 : ℚ) ≤ (D_c1 : ℚ) * (n : ℚ))
      have heq : (n : ℚ) * ((D_c1 : ℚ) * (n : ℚ)) = (D_c1 : ℚ) * (n : ℚ) ^ 2 := by ring
      linarith only [hmul, heq]
    have h3 : (P : ℚ) * 1 ≤ (n : ℚ) ^ 2 := by nlinarith only [hP_le, hn_q]
    linarith only [hsum, h1, h2, h3]
  -- 2. Strip [P, H): Pin–Frankl ≤ (1 / 4000) * n³ + 2 * n²
  have hPre2 : ((∑ j ∈ Finset.Ico P H, corankGap A hSync j : ℕ) : ℚ) ≤
      (1 / 4000 : ℚ) * (n : ℚ) ^ 3 + 2 * (n : ℚ) ^ 2 := by
    have hpf : (∑ j ∈ Finset.Ico P H, corankGap A hSync j) ≤
        ∑ j ∈ Finset.Ico P H, (j + 2).choose 2 :=
      Finset.sum_le_sum fun j hj => corankGap_le_pinFrankl A hSync (by rw [Finset.mem_Ico] at hj; omega)
    have h6 := Nat.mul_le_mul_left 6 hpf
    rw [six_mul_sum_Ico_choose_two hP_le_H] at h6
    have hH_cub : H * (H + 1) * (H + 2) ≤ H ^ 3 + 4 * n ^ 2 := by
      have : H ≤ n := by omega
      nlinarith
    have hP_cub : P ^ 3 ≤ P * (P + 1) * (P + 2) := by nlinarith
    have hmono : P * (P + 1) * (P + 2) ≤ H * (H + 1) * (H + 2) :=
      mul_succ_mul_add_two_mono hP_le_H
    have hnat : 6 * (∑ j ∈ Finset.Ico P H, corankGap A hSync j) + P ^ 3 ≤ H ^ 3 + 4 * n ^ 2 := by omega
    have hq : (6 : ℚ) * ((∑ j ∈ Finset.Ico P H, corankGap A hSync j : ℕ) : ℚ) + (P : ℚ) ^ 3 ≤
        (H : ℚ) ^ 3 + 4 * (n : ℚ) ^ 2 := by exact_mod_cast hnat
    have hH_le : (H : ℚ) ≤ (n : ℚ) / 2 := by
      have : 2 * H ≤ n := by omega
      have hq' : (2 : ℚ) * H ≤ n := by exact_mod_cast this
      linarith
    have hP_ge : (499 / 1000 : ℚ) * (n : ℚ) - 1 ≤ (P : ℚ) := by
      have : 499 * n ≤ 1000 * P + 999 := by dsimp only [P]; omega
      have hq' : (499 : ℚ) * n ≤ 1000 * (P : ℚ) + 999 := by exact_mod_cast this
      linarith
    have hH3 : (H : ℚ) ^ 3 ≤ ((n : ℚ) / 2) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hH_le 3
    have hP3 : ((499 / 1000 : ℚ) * (n : ℚ) - 1) ^ 3 ≤ (P : ℚ) ^ 3 :=
      pow_le_pow_left₀ (by linarith only [hn_q]) hP_ge 3
    have hexp : ((n : ℚ) / 2) ^ 3 - ((499 / 1000 : ℚ) * (n : ℚ) - 1) ^ 3 + 4 * (n : ℚ) ^ 2 =
        (1 / 8 - (499 / 1000 : ℚ) ^ 3) * (n : ℚ) ^ 3 +
        (4 + 3 * (499 / 1000 : ℚ) ^ 2) * (n : ℚ) ^ 2 -
        3 * (499 / 1000 : ℚ) * (n : ℚ) + 1 := by ring
    have hcoef1 : (1 / 8 - (499 / 1000 : ℚ) ^ 3) * (n : ℚ) ^ 3 ≤ (6 / 4000 : ℚ) * (n : ℚ) ^ 3 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have hcoef2 : (4 + 3 * (499 / 1000 : ℚ) ^ 2) * (n : ℚ) ^ 2 ≤ 12 * (n : ℚ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
    linarith only [hq, hH3, hP3, hexp, hcoef1, hcoef2, hn_q]
  -- 3. Macroscopic band [H, B_end): Prop 1.4 gives ≤ (96 / 10000) * n³ + 2 * n²
  have hBand : ((∑ j ∈ Finset.Ico H B_end, corankGap A hSync j : ℕ) : ℚ) ≤
      (96 / 10000 : ℚ) * (n : ℚ) ^ 3 + 2 * (n : ℚ) ^ 2 := by
    have hpt : ∀ r ∈ Finset.Ico H B_end, corankGap A hSync r ≤ (120 * n ^ 2) / 1000 + 1 :=
      fun r hr => caseB_macroscopic_band_bound A hSync hSC hD_eta hD_c1 hR_pow hn1 hn2 hDh hDt
        (Finset.mem_Ico.mp hr).1 (by have := (Finset.mem_Ico.mp hr).2; omega)
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hsum
    have hq : ((∑ j ∈ Finset.Ico H B_end, corankGap A hSync j : ℕ) : ℚ) ≤
        ((B_end - H : ℕ) : ℚ) * (((120 * n ^ 2) / 1000 : ℕ) : ℚ) + ((B_end - H : ℕ) : ℚ) := by
      have hcast : ((∑ j ∈ Finset.Ico H B_end, corankGap A hSync j : ℕ) : ℚ) ≤
          (((B_end - H) * ((120 * n ^ 2) / 1000 + 1) : ℕ) : ℚ) := by exact_mod_cast hsum
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast; linarith
    have hwidth : ((B_end - H : ℕ) : ℚ) ≤ (8 / 100 : ℚ) * (n : ℚ) + 1 := by
      have : 100 * (B_end - H) ≤ 8 * n + 50 := by dsimp only [B_end, H]; omega
      have hq' : (100 : ℚ) * ((B_end - H : ℕ) : ℚ) ≤ 8 * (n : ℚ) + 50 := by exact_mod_cast this
      linarith
    have hcap : (((120 * n ^ 2) / 1000 : ℕ) : ℚ) ≤ (120 / 1000 : ℚ) * (n : ℚ) ^ 2 := by
      have : 1000 * ((120 * n ^ 2) / 1000) ≤ 120 * n ^ 2 := Nat.mul_div_le _ _
      have hq' : (1000 : ℚ) * (((120 * n ^ 2) / 1000 : ℕ) : ℚ) ≤ 120 * (n : ℚ) ^ 2 := by
        exact_mod_cast this
      linarith
    have hmul := mul_le_mul hwidth hcap (Nat.cast_nonneg _) (by positivity)
    nlinarith only [hq, hmul, hwidth, hn_q]
  -- 4. Tail [B_end, n - 1): Pin–Frankl ≤ (1 - (58/100)³) / 6 * n³ + n²
  have hTail : ((∑ j ∈ Finset.Ico B_end (n - 1), corankGap A hSync j : ℕ) : ℚ) ≤
      (1 - (58 / 100 : ℚ) ^ 3) / 6 * (n : ℚ) ^ 3 + (n : ℚ) ^ 2 := by
    have hpf : (∑ j ∈ Finset.Ico B_end (n - 1), corankGap A hSync j) ≤
        ∑ j ∈ Finset.Ico B_end (n - 1), (j + 2).choose 2 :=
      Finset.sum_le_sum fun j hj => corankGap_le_pinFrankl A hSync (by rw [Finset.mem_Ico] at hj; omega)
    have h6 := Nat.mul_le_mul_left 6 hpf
    rw [six_mul_sum_Ico_choose_two hB_le_n1] at h6
    have htop : (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) ≤ n ^ 3 := by zify [show 1 ≤ n by omega]; nlinarith
    have hbot : B_end ^ 3 ≤ B_end * (B_end + 1) * (B_end + 2) := by nlinarith
    have hmono : B_end * (B_end + 1) * (B_end + 2) ≤ (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) :=
      mul_succ_mul_add_two_mono hB_le_n1
    have hnat : 6 * (∑ j ∈ Finset.Ico B_end (n - 1), corankGap A hSync j) + B_end ^ 3 ≤ n ^ 3 := by omega
    have hq : (6 : ℚ) * ((∑ j ∈ Finset.Ico B_end (n - 1), corankGap A hSync j : ℕ) : ℚ) +
        (B_end : ℚ) ^ 3 ≤ (n : ℚ) ^ 3 := by exact_mod_cast hnat
    have hB_ge : (58 / 100 : ℚ) * (n : ℚ) - 1 ≤ (B_end : ℚ) := by
      have : 58 * n ≤ 100 * B_end + 99 := by dsimp only [B_end]; omega
      have hq' : (58 : ℚ) * n ≤ 100 * (B_end : ℚ) + 99 := by exact_mod_cast this
      linarith
    have hB3 : ((58 / 100 : ℚ) * (n : ℚ) - 1) ^ 3 ≤ (B_end : ℚ) ^ 3 :=
      pow_le_pow_left₀ (by linarith only [hn_q]) hB_ge 3
    have hexp : (n : ℚ) ^ 3 - ((58 / 100 : ℚ) * (n : ℚ) - 1) ^ 3 =
        (1 - (58 / 100 : ℚ) ^ 3) * (n : ℚ) ^ 3 +
        3 * (58 / 100 : ℚ) ^ 2 * (n : ℚ) ^ 2 -
        3 * (58 / 100 : ℚ) * (n : ℚ) + 1 := by ring
    have hcoef2 : 3 * (58 / 100 : ℚ) ^ 2 * (n : ℚ) ^ 2 ≤ 6 * (n : ℚ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
    linarith only [hq, hB3, hexp, hcoef2, hn_q]
  -- Telescope λ(n - 1) = λ(P) + [P, H) + [H, B_end) + [B_end, n - 1)
  have htele1 := minCorankLen_eq_add_sum_Ico A hSync hP_le_H (by omega : H ≤ n - 1)
  have htele2 := minCorankLen_eq_add_sum_Ico A hSync hH_le_B hB_le_n1
  have htele3 := minCorankLen_eq_add_sum_Ico A hSync hB_le_n1 le_rfl
  have htot_q : (minCorankLen A hSync (n - 1) : ℚ) =
      (minCorankLen A hSync P : ℚ) +
      ((∑ j ∈ Finset.Ico P H, corankGap A hSync j : ℕ) : ℚ) +
      ((∑ j ∈ Finset.Ico H B_end, corankGap A hSync j : ℕ) : ℚ) +
      ((∑ j ∈ Finset.Ico B_end (n - 1), corankGap A hSync j : ℕ) : ℚ) := by
    have hnat : minCorankLen A hSync (n - 1) =
        minCorankLen A hSync P +
        (∑ j ∈ Finset.Ico P H, corankGap A hSync j) +
        (∑ j ∈ Finset.Ico H B_end, corankGap A hSync j) +
        (∑ j ∈ Finset.Ico B_end (n - 1), corankGap A hSync j) := by omega
    exact_mod_cast hnat
  have hD_big : (250 / (D_c1 : ℚ)) * (n : ℚ) ^ 3 ≤ (1 / 10000 : ℚ) * (n : ℚ) ^ 3 := by
    have h1 : (250 / (D_c1 : ℚ)) ≤ 1 / 10000 := by
      rw [div_le_div_iff₀ hDc1_pos (by norm_num)]
      have hq : (50 * 10 ^ 14 : ℚ) ≤ (D_c1 : ℚ) := by
        exact_mod_cast (show 50 * 10 ^ 14 ≤ D_c1 by rw [hD_c1]; nlinarith only [hD_eta])
      linarith
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hn2_pos : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
  have hn3_pos : (0 : ℚ) ≤ (n : ℚ) ^ 3 := by positivity
  linarith only [htot_q, hPre1, hPre2, hBand, hTail, hD_big, hn2_pos, hn3_pos]

/-- 4-line Bernoulli lower bound `(39 / 38)^k ≥ 1 + k / 38` (avoids `Real.log` completely!). -/
private theorem pow_39_38_ge (k : ℕ) : 1 + (k : ℚ) / 38 ≤ (39 / 38 : ℚ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have hk0 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
    nlinarith

/-- Parameterized strongly connected core of Theorem T20: all large symbolic constants
are abstract `ℕ` variables so neither tactics nor the kernel ever evaluate `2 ^ (10^8)`. -/
private theorem below_seven_forty_eight_sc_param
    {JA MA Deta Dc1 DepsB JB MB KB Nsc : ℕ}
    (hJA : 1 ≤ JA) (hMA : 1 ≤ MA)
    (hθA : ((1 : ℚ) / (JA : ℚ) + 1 / (MA : ℚ)) * (5000 : ℕ) / 2 ≤ 5 / 10 ^ 5)
    (hDeta_ge : 10 ^ 14 ≤ Deta)
    (hDeta_factor : (MA + 1) * 2 ^ JA * 10 ^ 5 ≤ Deta)
    (hDeta_small : 10 ^ 5 * (MA + 1) ≤ Deta)
    (hDc1_eq : Dc1 = 50 * Deta)
    (hDepsB_eq : DepsB = 10000 * Dc1)
    (hJB_eq : JB = 10 ^ 9 * Dc1 ^ 2)
    (hMB_eq : MB = 10 ^ 9 * Dc1 ^ 2)
    (hKB_eq : KB = (MB + 1) * (2 ^ JB * 2 + 1) + 10)
    (hNsc_part1 : 150 * Deta ^ 2 + 2 * (38 * Dc1 + 1) * Deta + 10 * Deta ≤ Nsc)
    (hNsc_part2 : 10 ^ 6 * Dc1 * (KB + DepsB + Dc1) ≤ Nsc)
    {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    (hn : Nsc ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧
      (w.length : ℚ) ≤ (7 / 48 - 1 / (2000 * (Dc1 : ℚ))) * (Fintype.card Q : ℚ) ^ 3 := by
  classical
  let n := Fintype.card Q
  obtain ⟨w_opt, hw_sync, hw_len⟩ := exists_syncWord_len_minCorankLen A hSync
  refine ⟨w_opt, hw_sync, ?_⟩
  rw [hw_len]
  change (minCorankLen A hSync (n - 1) : ℚ) ≤ (7 / 48 - 1 / (2000 * (Dc1 : ℚ))) * (n : ℚ) ^ 3
  have hDc1_ge : 50 * 10 ^ 14 ≤ Dc1 := by rw [hDc1_eq]; nlinarith only [hDeta_ge]
  have hDc1_pos_nat : 0 < Dc1 := by omega
  have hDc1_pos : (0 : ℚ) < (Dc1 : ℚ) := by exact_mod_cast hDc1_pos_nat
  have hn_part1 : 150 * Deta ^ 2 + 2 * (38 * Dc1 + 1) * Deta + 10 * Deta ≤ n := le_trans hNsc_part1 hn
  have hn_part2 : 10 ^ 6 * Dc1 * (KB + DepsB + Dc1) ≤ n := le_trans hNsc_part2 hn
  have hn_ge_106 : 10 ^ 6 ≤ n := by nlinarith only [hDeta_ge, hn_part1]
  have hn_ge_10000 : 10000 ≤ n := by linarith only [hn_ge_106]
  have hn_q : (10000 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn_ge_10000
  have hn3 : (0 : ℚ) ≤ (n : ℚ) ^ 3 := by positivity
  -- Case A: D(n² / Deta) ≥ n / 10
  by_cases hCaseA : n ≤ 10 * corankAt A hSync (n ^ 2 / Deta)
  · obtain ⟨v, hvlen, hvcor, hvstab⟩ := dyadic_schedule_exists A hSync (n ^ 2 / Deta) hJA
    let C := n - (A.image Finset.univ v).card
    have hC_ge_10 : n ≤ 10 * C := le_trans hCaseA (Nat.mul_le_mul_left 10 hvcor)
    have hcap := word_cap_beats_seven_forty_eight A hSync hSC v (J := JA) (M := MA)
      (D_eps := 5000) (margin := 1 / 5000) hn_ge_10000 hJA hMA le_rfl
      (by linarith only [hn_ge_106])
      (by linarith only [hC_ge_10]) hvstab (by norm_num)
      (fun hC1 x hx0 hx1 => by
        have hc_ge : 1 / 10 ≤ (C : ℚ) / (n : ℚ) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          have hq : (n : ℚ) ≤ 10 * (C : ℚ) := by exact_mod_cast hC_ge_10
          linarith
        have hc_le : (C : ℚ) / (n : ℚ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have : 2 * C ≤ n := by omega
          have hq : (2 : ℚ) * (C : ℚ) ≤ n := by exact_mod_cast this
          linarith
        exact rational_payment_ge_mid hc_ge hc_le hx0 hx1)
    have hΩA_le : (((MA + 1) * (v.length + (n - 1)) + 1 : ℕ) : ℚ) ≤ (2 / 10 ^ 5 : ℚ) * (n : ℚ) ^ 2 := by
      have hv_nat : Deta * v.length ≤ 2 ^ JA * (n ^ 2 + Deta * n) := by
        have h1 : Deta * (n ^ 2 / Deta) ≤ n ^ 2 := Nat.mul_div_le _ _
        have h2 := Nat.mul_le_mul_left Deta hvlen
        have h3 : Deta * (2 ^ JA * (n ^ 2 / Deta + n)) =
            2 ^ JA * (Deta * (n ^ 2 / Deta) + Deta * n) := by ring
        rw [h3] at h2
        exact le_trans h2 (Nat.mul_le_mul_left _ (by omega))
      have h100k_Ω : 10 ^ 5 * ((MA + 1) * (v.length + (n - 1)) + 1) ≤ 2 * n ^ 2 := by
        have hmulD : Deta * (10 ^ 5 * ((MA + 1) * (v.length + (n - 1)) + 1)) ≤ Deta * (2 * n ^ 2) := by
          have hterm1 : 10 ^ 5 * (MA + 1) * (Deta * v.length) ≤ Deta * (n ^ 2 + Deta * n) := by
            have ha := Nat.mul_le_mul_left (10 ^ 5 * (MA + 1)) hv_nat
            have hb : 10 ^ 5 * (MA + 1) * (2 ^ JA * (n ^ 2 + Deta * n)) =
                ((MA + 1) * 2 ^ JA * 10 ^ 5) * (n ^ 2 + Deta * n) := by ring
            rw [hb] at ha
            exact le_trans ha (Nat.mul_le_mul_right _ hDeta_factor)
          have hsmall_n : Deta * n + 10 ^ 5 * (MA + 1) * n + 10 ^ 5 ≤ n ^ 2 := by
            have h1 : 10 * Deta ≤ n := by omega
            nlinarith only [h1, hDeta_small, hDeta_ge]
          have hexp : Deta * (10 ^ 5 * ((MA + 1) * (v.length + (n - 1)) + 1)) ≤
              10 ^ 5 * (MA + 1) * (Deta * v.length) + Deta * (10 ^ 5 * (MA + 1) * n + 10 ^ 5) := by
            have hsub1 : (MA + 1) * (v.length + (n - 1)) + 1 ≤ (MA + 1) * (v.length + n) + 1 :=
              Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.sub_le n 1) _)) 1
            have hsub := Nat.mul_le_mul_left Deta (Nat.mul_le_mul_left (10 ^ 5) hsub1)
            have hring : Deta * (10 ^ 5 * ((MA + 1) * (v.length + n) + 1)) =
                10 ^ 5 * (MA + 1) * (Deta * v.length) + Deta * (10 ^ 5 * (MA + 1) * n + 10 ^ 5) := by ring
            exact hring ▸ hsub
          have hcomb := Nat.mul_le_mul_left Deta hsmall_n
          nlinarith only [hexp, hterm1, hcomb]
        exact Nat.le_of_mul_le_mul_left hmulD (by omega)
      have hq : (10 ^ 5 : ℚ) * (((MA + 1) * (v.length + (n - 1)) + 1 : ℕ) : ℚ) ≤ 2 * (n : ℚ) ^ 2 := by
        exact_mod_cast h100k_Ω
      linarith
    have hΩ_term : ((n : ℚ) + 1) * (((MA + 1) * (v.length + (n - 1)) + 1 : ℕ) : ℚ) + 7 * (n : ℚ) ^ 2 ≤
        (3 / 10 ^ 5 : ℚ) * (n : ℚ) ^ 3 := by
      have h1 := mul_le_mul_of_nonneg_left hΩA_le (by positivity : (0 : ℚ) ≤ (n : ℚ) + 1)
      have hn_106 : (10 ^ 6 : ℚ) ≤ (n : ℚ) := by
        have : 10 ^ 6 ≤ n := by nlinarith only [hDeta_ge, hn_part1]
        exact_mod_cast this
      nlinarith only [h1, hn_106]
    have hδ_small : 1 / (2000 * (Dc1 : ℚ)) ≤ 1 / 10 ^ 5 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℚ) < 2000 * (Dc1 : ℚ)) (by norm_num)]
      have hq : (50 * 10 ^ 14 : ℚ) ≤ (Dc1 : ℚ) := by exact_mod_cast hDc1_ge
      linarith
    have hδ_scaled := mul_le_mul_of_nonneg_right hδ_small hn3
    have hθA_scaled := mul_le_mul_of_nonneg_right hθA hn3
    change (minCorankLen A hSync (n - 1) : ℚ) ≤ _ at hcap
    linarith only [hcap, hΩ_term, hδ_scaled, hθA_scaled, hn3]
  -- Now D(n² / Deta) < n / 10
  push Not at hCaseA
  -- Case C: D(h) ≥ n / Dc1
  by_cases hCaseC : n ≤ Dc1 * shortCorank A hSync
  · have hJB_ge : 1 ≤ JB := by rw [hJB_eq]; nlinarith only [hDc1_ge]
    have hMB_ge : 1 ≤ MB := by rw [hMB_eq]; nlinarith only [hDc1_ge]
    obtain ⟨v, hvlen, hvcor, hvstab⟩ := dyadic_schedule_exists A hSync (n - 1) hJB_ge
    rw [corankAt_pred_eq_shortCorank] at hvcor
    let C := n - (A.image Finset.univ v).card
    have hC_ge_c1 : n ≤ Dc1 * C := le_trans hCaseC (Nat.mul_le_mul_left Dc1 hvcor)
    have hcap := word_cap_beats_seven_forty_eight A hSync hSC v (J := JB) (M := MB)
      (D_eps := DepsB) (margin := 1 / (1500 * (Dc1 : ℚ)))
      hn_ge_10000 hJB_ge hMB_ge
      (by rw [hDepsB_eq]; omega)
      (by nlinarith only [hn_part2, hDc1_ge])
      (by rw [hDepsB_eq]; nlinarith only [hC_ge_c1])
      hvstab
      (by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have hq : (50 * 10 ^ 14 : ℚ) ≤ (Dc1 : ℚ) := by exact_mod_cast hDc1_ge
        linarith)
      (fun hC1 x hx0 hx1 => by
        have hc_ge : 1 / (Dc1 : ℚ) ≤ (C : ℚ) / (n : ℚ) := by
          rw [div_le_div_iff₀ hDc1_pos (by positivity)]
          have hq : (n : ℚ) ≤ (Dc1 : ℚ) * (C : ℚ) := by exact_mod_cast hC_ge_c1
          linarith
        have hc_le : (C : ℚ) / (n : ℚ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have : 2 * C ≤ n := by omega
          have hq : (2 : ℚ) * (C : ℚ) ≤ n := by exact_mod_cast this
          linarith
        have hrat := rational_payment_ge (by positivity) hc_le hx0 hx1
        have h1 : 1 / (1500 * (Dc1 : ℚ)) ≤ ((C : ℚ) / (n : ℚ)) / 1500 := by
          have : 1 / (1500 * (Dc1 : ℚ)) = (1 / (Dc1 : ℚ)) / 1500 := by ring
          rw [this]; linarith
        linarith)
    have hΩB_le : (MB + 1) * (v.length + (n - 1)) + 1 ≤ KB * n := by
      have hv_2n : v.length ≤ 2 ^ JB * (2 * n) :=
        le_trans hvlen (Nat.mul_le_mul_left _ (by omega))
      have hn1 : n - 1 ≤ n := Nat.sub_le n 1
      have h1 : v.length + (n - 1) ≤ (2 ^ JB * 2 + 1) * n := by nlinarith only [hv_2n, hn1]
      have h2 : (MB + 1) * (v.length + (n - 1)) ≤ (MB + 1) * ((2 ^ JB * 2 + 1) * n) :=
        Nat.mul_le_mul_left _ h1
      rw [hKB_eq]; nlinarith only [h2, hn_ge_10000]
    have hΩ_term :
        ((n : ℚ) + 1) * (((MB + 1) * (v.length + (n - 1)) + 1 : ℕ) : ℚ) + 7 * (n : ℚ) ^ 2 ≤
        (1 / (500000 * (Dc1 : ℚ))) * (n : ℚ) ^ 3 := by
      have hΩ_q : (((MB + 1) * (v.length + (n - 1)) + 1 : ℕ) : ℚ) ≤ (KB : ℚ) * (n : ℚ) := by
        exact_mod_cast hΩB_le
      have h1 := mul_le_mul_of_nonneg_left hΩ_q (by positivity : (0 : ℚ) ≤ (n : ℚ) + 1)
      have hn_KB : 10 ^ 6 * (Dc1 : ℚ) * (KB : ℚ) ≤ (n : ℚ) := by
        have : 10 ^ 6 * Dc1 * KB ≤ n := by nlinarith only [hn_part2]
        exact_mod_cast this
      have hKB_ge10 : (10 : ℚ) ≤ (KB : ℚ) := by
        have : 10 ≤ KB := by rw [hKB_eq]; omega
        exact_mod_cast this
      have hbound2 : ((n : ℚ) + 1) * ((KB : ℚ) * (n : ℚ)) + 7 * (n : ℚ) ^ 2 ≤
          2 * (KB : ℚ) * (n : ℚ) ^ 2 := by
        have h_a : (KB : ℚ) * (n : ℚ) ≤ (KB : ℚ) * ((1 / 10 : ℚ) * (n : ℚ) ^ 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith only [hn_q]) (by linarith only [hKB_ge10])
        have h_b : 7 * (n : ℚ) ^ 2 ≤ (9 / 10 : ℚ) * (KB : ℚ) * (n : ℚ) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hKB_ge10]) (sq_nonneg _)
        linarith only [h_a, h_b]
      have hbound3 : 2 * (KB : ℚ) * (n : ℚ) ^ 2 ≤
          (1 / (500000 * (Dc1 : ℚ))) * (n : ℚ) ^ 3 := by
        have hmul := mul_le_mul_of_nonneg_right hn_KB (sq_nonneg (n : ℚ))
        have hdiv_pos : (0 : ℚ) < 500000 * (Dc1 : ℚ) := by positivity
        have heq : 500000 * (Dc1 : ℚ) * (2 * (KB : ℚ) * (n : ℚ) ^ 2) =
            10 ^ 6 * (Dc1 : ℚ) * (KB : ℚ) * (n : ℚ) ^ 2 := by ring
        have hmul2 : 500000 * (Dc1 : ℚ) * (2 * (KB : ℚ) * (n : ℚ) ^ 2) ≤
            500000 * (Dc1 : ℚ) * ((1 / (500000 * (Dc1 : ℚ))) * (n : ℚ) ^ 3) := by
          have hr : 500000 * (Dc1 : ℚ) * ((1 / (500000 * (Dc1 : ℚ))) * (n : ℚ) ^ 3) =
              (n : ℚ) ^ 3 := by field_simp
          rw [heq, hr]; nlinarith only [hmul]
        exact le_of_mul_le_mul_left hmul2 hdiv_pos
      linarith only [h1, hbound2, hbound3]
    have hθB_eq :
        ((1 : ℚ) / (JB : ℚ) + 1 / (MB : ℚ)) * (DepsB : ℚ) / 2 =
        1 / (100000 * (Dc1 : ℚ)) := by
      have hJB_q : (JB : ℚ) = 10 ^ 9 * (Dc1 : ℚ) ^ 2 := by rw [hJB_eq]; push_cast; ring
      have hMB_q : (MB : ℚ) = 10 ^ 9 * (Dc1 : ℚ) ^ 2 := by rw [hMB_eq]; push_cast; ring
      have hDeps_q : (DepsB : ℚ) = 10000 * (Dc1 : ℚ) := by rw [hDepsB_eq]; push_cast; ring
      rw [hJB_q, hMB_q, hDeps_q]
      have hne : (Dc1 : ℚ) ≠ 0 := hDc1_pos.ne'
      field_simp; ring
    have hDepsB_eq_q : (3 / 10 : ℚ) * (1 / (DepsB : ℚ)) = 3 / (100000 * (Dc1 : ℚ)) := by
      have hDeps_q : (DepsB : ℚ) = 10000 * (Dc1 : ℚ) := by rw [hDepsB_eq]; push_cast; ring
      rw [hDeps_q]
      have hne : (Dc1 : ℚ) ≠ 0 := hDc1_pos.ne'
      field_simp; ring
    have hmargin_net :
        (7 / 48 - 1 / (1500 * (Dc1 : ℚ)) + 3 / (100000 * (Dc1 : ℚ)) +
          1 / (100000 * (Dc1 : ℚ)) + 1 / (500000 * (Dc1 : ℚ))) * (n : ℚ) ^ 3 ≤
        (7 / 48 - 1 / (2000 * (Dc1 : ℚ))) * (n : ℚ) ^ 3 := by
      have hcoef :
          7 / 48 - 1 / (1500 * (Dc1 : ℚ)) + 3 / (100000 * (Dc1 : ℚ)) +
            1 / (100000 * (Dc1 : ℚ)) + 1 / (500000 * (Dc1 : ℚ)) ≤
          7 / 48 - 1 / (2000 * (Dc1 : ℚ)) := by
        have hdiff :
            (7 / 48 - 1 / (2000 * (Dc1 : ℚ))) -
            (7 / 48 - 1 / (1500 * (Dc1 : ℚ)) + 3 / (100000 * (Dc1 : ℚ)) +
              1 / (100000 * (Dc1 : ℚ)) + 1 / (500000 * (Dc1 : ℚ))) =
            374 / (3000000 * (Dc1 : ℚ)) := by
          have hne : (Dc1 : ℚ) ≠ 0 := hDc1_pos.ne'
          field_simp; ring
        have hpos : (0 : ℚ) ≤ 374 / (3000000 * (Dc1 : ℚ)) := by positivity
        linarith
      exact mul_le_mul_of_nonneg_right hcoef hn3
    change (minCorankLen A hSync (n - 1) : ℚ) ≤ _ at hcap
    rw [hθB_eq, hDepsB_eq_q] at hcap
    linarith only [hcap, hΩ_term, hmargin_net]
  -- Case B: D(h) < n / Dc1 AND D(n² / Deta) < n / 10
  · push Not at hCaseC
    have hR_pow : (Dc1 : ℚ) < (39 / 38 : ℚ) ^ (38 * Dc1) := by
      have h := pow_39_38_ge (38 * Dc1)
      push_cast at h
      linarith
    have hB := caseB_beats_seven_forty_eight A hSync hSC hDeta_ge hDc1_eq hR_pow
      (by omega) (by omega) hCaseC hCaseA
    have hquad_le : ((Dc1 : ℚ) + 20) * (n : ℚ) ^ 2 ≤ (1 / 2000 : ℚ) * (n : ℚ) ^ 3 := by
      have hn_ge : 2000 * (Dc1 + 20) ≤ n := by
        have : 10 ^ 6 * Dc1 * Dc1 ≤ n := by nlinarith only [hn_part2]
        nlinarith only [this, hDc1_ge]
      have hq : (2000 : ℚ) * ((Dc1 : ℚ) + 20) ≤ (n : ℚ) := by exact_mod_cast hn_ge
      nlinarith only [hq, hn_q]
    have hδ_le : 1 / (2000 * (Dc1 : ℚ)) ≤ 1 / 2000 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℚ) < 2000 * (Dc1 : ℚ)) (by norm_num)]
      have hq : (1 : ℚ) ≤ (Dc1 : ℚ) := by exact_mod_cast hDc1_pos_nat
      linarith
    have hδ_scaled := mul_le_mul_of_nonneg_right hδ_le hn3
    change (minCorankLen A hSync (n - 1) : ℚ) ≤ _ at hB
    linarith only [hB, hquad_le, hδ_scaled, hn3]

/-- Strongly connected core of **Theorem T20**: there exist `δ > 0` and `N₀ : ℕ` such that
EVERY strongly connected synchronizing DFA on `n ≥ N₀` states admits a synchronizing word `w`
with `(w.length : ℚ) ≤ (7 / 48 - δ) * n ^ 3`. -/
theorem below_seven_forty_eight_sc :
    ∃ δ : ℚ, 0 < δ ∧ ∃ N₀ : ℕ,
      ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : DFA Q α),
        N₀ ≤ Fintype.card Q → A.IsSynchronizing → A.IsStronglyConnected →
        ∃ w : List α, A.IsSyncWord w ∧
          (w.length : ℚ) ≤ (7 / 48 - δ) * (Fintype.card Q : ℚ) ^ 3 := by
  let JA : ℕ := 10 ^ 8
  let MA : ℕ := 10 ^ 8
  let Deta : ℕ := 10 ^ 14 * 2 ^ JA
  let Dc1 : ℕ := 50 * Deta
  let DepsB : ℕ := 10000 * Dc1
  let JB : ℕ := 10 ^ 9 * Dc1 ^ 2
  let MB : ℕ := 10 ^ 9 * Dc1 ^ 2
  let KB : ℕ := (MB + 1) * (2 ^ JB * 2 + 1) + 10
  let Nsc : ℕ :=
    max (150 * Deta ^ 2 + 2 * (38 * Dc1 + 1) * Deta + 10 * Deta)
        (10 ^ 6 * Dc1 * (KB + DepsB + Dc1))
  have hpowA_ge1 : 1 ≤ 2 ^ JA := Nat.one_le_pow JA 2 (by decide)
  have hDeta_ge : 10 ^ 14 ≤ Deta := le_mul_of_one_le_right (Nat.zero_le _) hpowA_ge1
  have hDeta_factor : (MA + 1) * 2 ^ JA * 10 ^ 5 ≤ Deta := by
    have hnum : (MA + 1) * 10 ^ 5 ≤ 10 ^ 14 := by dsimp only [MA]; norm_num
    have heq : (MA + 1) * 2 ^ JA * 10 ^ 5 = ((MA + 1) * 10 ^ 5) * 2 ^ JA :=
      Nat.mul_right_comm _ _ _
    rw [heq]; exact Nat.mul_le_mul_right _ hnum
  have hDeta_small : 10 ^ 5 * (MA + 1) ≤ Deta :=
    le_trans (by dsimp only [MA]; norm_num : 10 ^ 5 * (MA + 1) ≤ 10 ^ 14) hDeta_ge
  have hDc1_pos : 0 < Dc1 :=
    Nat.lt_of_lt_of_le (by norm_num : 0 < 50 * 10 ^ 14) (Nat.mul_le_mul_left 50 hDeta_ge)
  have hδ_pos : (0 : ℚ) < 1 / (2000 * (Dc1 : ℚ)) :=
    div_pos one_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hDc1_pos))
  refine ⟨1 / (2000 * (Dc1 : ℚ)), hδ_pos, Nsc, ?_⟩
  intro Q _ _ α A hn hSync hSC
  exact below_seven_forty_eight_sc_param (JA := JA) (MA := MA) (Deta := Deta) (Dc1 := Dc1)
    (DepsB := DepsB) (JB := JB) (MB := MB) (KB := KB) (Nsc := Nsc)
    (by dsimp only [JA]; norm_num) (by dsimp only [MA]; norm_num)
    (by dsimp only [JA, MA]; norm_num)
    hDeta_ge hDeta_factor hDeta_small rfl rfl rfl rfl rfl
    (le_max_left _ _) (le_max_right _ _) A hSync hSC hn

/-- **Flagship Theorem T20 (`ℚ` form — Breaking Strictly Below `7/48 n³` for ALL Synchronizing DFAs!)**:
There exist `δ > 0` and `N₀ : ℕ` such that EVERY synchronizing DFA on `n ≥ N₀` states
(strongly connected or NOT!) admits a synchronizing word `w` with
`(w.length : ℚ) ≤ (7 / 48 - δ) * (n : ℚ) ^ 3`. -/
theorem exists_strictly_below_seven_forty_eight :
    ∃ δ : ℚ, 0 < δ ∧ ∃ N₀ : ℕ,
      ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : DFA Q α),
        N₀ ≤ Fintype.card Q → A.IsSynchronizing →
        ∃ w : List α, A.IsSyncWord w ∧
          (w.length : ℚ) ≤ (7 / 48 - δ) * (Fintype.card Q : ℚ) ^ 3 := by
  obtain ⟨δ_sc, hδ_sc_pos, N_sc, hsc⟩ := below_seven_forty_eight_sc
  let δ : ℚ := min (δ_sc / 2) (1 / 1000)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
  have h2δ_le_sc : 2 * δ ≤ δ_sc := by
    have := min_le_left (δ_sc / 2) (1 / 1000 : ℚ)
    linarith
  have hδ_small : δ ≤ 1 / 1000 := min_le_right _ _
  let N₀ : ℕ := max (max N_sc (δ.den + 2)) (N_sc ^ 3 + 2)
  refine ⟨δ, hδ_pos, N₀, ?_⟩
  intro Q _ _ α A hn hSync
  classical
  let n := Fintype.card Q
  have hC_ne : (sinkSCC A).Nonempty := sinkSCC_nonempty A hSync
  have : Nonempty {q // q ∈ sinkSCC A} := ⟨⟨hC_ne.choose, hC_ne.choose_spec⟩⟩
  have hSyncC := restrictSinkSCC_isSynchronizing A hSync
  have hSCC := restrictSinkSCC_isStronglyConnected A
  obtain ⟨w, hw, hlen⟩ := exists_syncWord_le_sinkSCC_bound A hSync
  refine ⟨w, hw, ?_⟩
  let s := (sinkSCC A).card
  let m := n - s
  have hs_le : s ≤ n := Finset.card_le_univ _
  have hcard_sub : Fintype.card {q // q ∈ sinkSCC A} = s := Fintype.card_coe (sinkSCC A)
  have hn_ge_den2 : δ.den + 2 ≤ n := le_trans (le_max_right N_sc _) (le_trans (le_max_left _ _) hn)
  have hn_ge_N3 : N_sc ^ 3 + 2 ≤ n := le_trans (le_max_right _ _) hn
  have hlen_q : (w.length : ℚ) ≤ (n : ℚ) ^ 2 + ((restrictSinkSCC A).resetThreshold hSyncC : ℚ) := by
    have hm_le : m ≤ n := Nat.sub_le _ _
    have hn_ge2 : 2 ≤ n := by omega
    have hm_sq : m * (m + 1) ≤ 2 * n ^ 2 := by nlinarith only [hm_le, hn_ge2]
    have hnat : w.length ≤ n ^ 2 + (restrictSinkSCC A).resetThreshold hSyncC := by
      have : 2 * w.length ≤ m * (m + 1) + 2 * (restrictSinkSCC A).resetThreshold hSyncC := hlen
      omega
    exact_mod_cast hnat
  have hn2_le_δn3 : (n : ℚ) ^ 2 ≤ δ * (n : ℚ) ^ 3 := by
    have hnum_ge1 : (1 : ℚ) ≤ (δ.num : ℚ) := by
      have hpos : (0 : ℤ) < δ.num := Rat.num_pos.mpr hδ_pos
      exact_mod_cast (show (1 : ℤ) ≤ δ.num by omega)
    have hden_pos : (0 : ℚ) < (δ.den : ℚ) := by exact_mod_cast δ.den_pos
    have h1_le_δden : 1 ≤ δ * (δ.den : ℚ) := by
      have hrat : (δ.num : ℚ) / (δ.den : ℚ) = δ := Rat.num_div_den δ
      calc (1 : ℚ) ≤ (δ.num : ℚ) := hnum_ge1
        _ = (δ.num : ℚ) / (δ.den : ℚ) * (δ.den : ℚ) := (div_mul_cancel₀ _ hden_pos.ne').symm
        _ = δ * (δ.den : ℚ) := by rw [hrat]
    have hden_le_n : (δ.den : ℚ) ≤ (n : ℚ) := by exact_mod_cast (show δ.den ≤ n by omega)
    have h1_le_δn : 1 ≤ δ * (n : ℚ) :=
      le_trans h1_le_δden (mul_le_mul_of_nonneg_left hden_le_n hδ_pos.le)
    have hmul := mul_le_mul_of_nonneg_right h1_le_δn (sq_nonneg (n : ℚ))
    have heq : δ * (n : ℚ) * (n : ℚ) ^ 2 = δ * (n : ℚ) ^ 3 := by ring
    linarith only [hmul, heq]
  -- Split on whether the sink SCC has size ≥ N_sc
  by_cases hs_big : N_sc ≤ s
  · obtain ⟨wC, hwC, hlenC⟩ := hsc (restrictSinkSCC A) (by rw [hcard_sub]; exact hs_big) hSyncC hSCC
    rw [hcard_sub] at hlenC
    have hrtC_q : ((restrictSinkSCC A).resetThreshold hSyncC : ℚ) ≤ (wC.length : ℚ) := by
      exact_mod_cast (restrictSinkSCC A).resetThreshold_le_of_isSyncWord hSyncC hwC
    have hs3_le : (s : ℚ) ^ 3 ≤ (n : ℚ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hs_le) 3
    have hsc_cmp : (7 / 48 - δ_sc) * (s : ℚ) ^ 3 ≤ (7 / 48 - 2 * δ) * (s : ℚ) ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith only [h2δ_le_sc]) (by positivity)
    have hsc_le : (7 / 48 - 2 * δ) * (s : ℚ) ^ 3 ≤ (7 / 48 - 2 * δ) * (n : ℚ) ^ 3 :=
      mul_le_mul_of_nonneg_left hs3_le (by linarith only [hδ_small])
    linarith only [hlen_q, hrtC_q, hlenC, hsc_cmp, hsc_le, hn2_le_δn3]
  · obtain ⟨wC, hwC, hpfC⟩ := pin_frankl_bound (restrictSinkSCC A) hSyncC
    rw [hcard_sub] at hpfC
    have hrtC : (restrictSinkSCC A).resetThreshold hSyncC ≤ s ^ 3 := by
      have h1 := (restrictSinkSCC A).resetThreshold_le_of_isSyncWord hSyncC hwC
      have h2 : 6 * wC.length ≤ s ^ 3 := le_trans hpfC (Nat.sub_le _ _)
      omega
    have hrtC_q : ((restrictSinkSCC A).resetThreshold hSyncC : ℚ) ≤ (N_sc : ℚ) ^ 3 := by
      have h1 : s ^ 3 ≤ N_sc ^ 3 := Nat.pow_le_pow_left (by omega : s ≤ N_sc) 3
      exact_mod_cast le_trans hrtC h1
    have hNsc3_le : (N_sc : ℚ) ^ 3 ≤ (n : ℚ) ^ 2 := by
      have h1 : (N_sc : ℚ) ^ 3 ≤ (n : ℚ) := by exact_mod_cast (show N_sc ^ 3 ≤ n by omega)
      have hn2 : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (show 2 ≤ n by omega)
      nlinarith only [h1, hn2]
    have h2δ_scaled := mul_le_mul_of_nonneg_right (show 2 * δ ≤ 7 / 48 - δ by linarith only [hδ_small])
      (show (0 : ℚ) ≤ (n : ℚ) ^ 3 by positivity)
    linarith only [hlen_q, hrtC_q, hNsc3_le, hn2_le_δn3, h2δ_scaled]

/-- **Flagship Theorem T20 (Division-Free `ℕ` Form)**:
There exist positive integers `p, q > 0` and `N₀ : ℕ` such that EVERY synchronizing DFA on
`n ≥ N₀` states admits a synchronizing word `w` with
`48 * q * w.length ≤ (7 * q - p) * n ^ 3`. -/
theorem below_seven_forty_eight :
    ∃ (p q : ℕ), 0 < p ∧ 0 < q ∧ ∃ N₀ : ℕ,
      ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : DFA Q α),
        A.IsSynchronizing → N₀ ≤ Fintype.card Q →
        ∃ w : List α, A.IsSyncWord w ∧
          48 * q * w.length ≤ (7 * q - p) * (Fintype.card Q) ^ 3 := by
  obtain ⟨δ, hδ_pos, N₀, hmain⟩ := exists_strictly_below_seven_forty_eight
  -- Extract rational numerator/denominator of min(δ, 1/100) so p < 7 * q
  let δ' : ℚ := min δ (1 / 100)
  have hδ'_pos : 0 < δ' := lt_min hδ_pos (by norm_num)
  have hδ'_le : δ' ≤ δ := min_le_left _ _
  have hδ'_small : δ' ≤ 1 / 100 := min_le_right _ _
  have hnum_pos : 0 < δ'.num := Rat.num_pos.mpr hδ'_pos
  let p : ℕ := 48 * δ'.num.toNat
  let q : ℕ := δ'.den
  have hp_pos : 0 < p := by
    have : 0 < δ'.num.toNat := by omega
    dsimp only [p]; omega
  have hq_pos : 0 < q := δ'.den_pos
  have hδ'_eq : δ' = (δ'.num.toNat : ℚ) / (q : ℚ) := by
    have hnum_eq : (δ'.num.toNat : ℚ) = (δ'.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega)
    rw [hnum_eq]
    exact (Rat.num_div_den δ').symm
  have hp_lt_7q : p ≤ 7 * q := by
    have h1 : (δ'.num.toNat : ℚ) / (q : ℚ) ≤ 1 / 100 := by rw [← hδ'_eq]; exact hδ'_small
    have h2 : (δ'.num.toNat : ℚ) * 100 ≤ (q : ℚ) := by
      have := (div_le_div_iff₀ (by positivity : (0 : ℚ) < q) (by norm_num)).mp h1
      linarith
    have hnat : δ'.num.toNat * 100 ≤ q := by exact_mod_cast h2
    dsimp only [p]; omega
  refine ⟨p, q, hp_pos, hq_pos, N₀, ?_⟩
  intro Q _ _ α A hSync hn
  obtain ⟨w, hw, hlen⟩ := hmain A hn hSync
  refine ⟨w, hw, ?_⟩
  have hlen' : (w.length : ℚ) ≤ (7 / 48 - δ') * (Fintype.card Q : ℚ) ^ 3 := by
    have h1 : (7 / 48 - δ) * (Fintype.card Q : ℚ) ^ 3 ≤
        (7 / 48 - δ') * (Fintype.card Q : ℚ) ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hmul : (48 * (q : ℚ)) * (w.length : ℚ) ≤
      (48 * (q : ℚ)) * ((7 / 48 - δ') * (Fintype.card Q : ℚ) ^ 3) :=
    mul_le_mul_of_nonneg_left hlen' (by positivity)
  have hrhs_eq : (48 * (q : ℚ)) * ((7 / 48 - δ') * (Fintype.card Q : ℚ) ^ 3) =
      ((7 * q - p : ℕ) : ℚ) * (Fintype.card Q : ℚ) ^ 3 := by
    rw [Nat.cast_sub hp_lt_7q, Nat.cast_mul, Nat.cast_ofNat, hδ'_eq]
    have hp_q : (p : ℚ) = 48 * (δ'.num.toNat : ℚ) := by dsimp only [p]; push_cast; ring
    rw [hp_q]
    have hq_ne : (q : ℚ) ≠ 0 := by positivity
    field_simp
  rw [hrhs_eq] at hmul
  exact_mod_cast hmul

end BelowSevenFortyEightMain

end Cerny
