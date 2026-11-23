import Cerny.Defs
import Cerny.Combinatorial
import Cerny.AdditionalClasses
import Cerny.SubPinFrankl
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Explicit-`O(n²)` Sub-Shitov & Sub-Hong General Cubic Upper Bound (`24646/149769 n³ + 50 n²`)

This file proves **Theorem T19**, an unconditional general upper bound for EVERY synchronizing
DFA on `n ≥ 1` states with an explicit quadratic remainder:
$$149769 \cdot |w| \le 24646 \cdot n^3 + 7488450 \cdot n^2
  \qquad \left(\frac{24646}{149769}\, n^3 + 50\, n^2 \approx 0.164560\, n^3 + 50\, n^2\right),$$
strictly beating BOTH:
- **Shitov (2019)** (`8257/49923 n³ ≈ 0.165395 n³`) for all `n ≥ 59908`, and
- **Hong (Nov 2026, `2611.00172v1`)** (`8242/49923 n³ ≈ 0.165094 n³`) for all `n ≥ 93606`
(achieving 2.78× greater leading-constant reduction below Shitov 2019 than `2611.00172v1`,
while maintaining a clean explicit `+ 50 n²` remainder!).

The proof is 100% elementary over `ℚ` (zero calculus, zero LP solvers, zero real numbers):
1. **SCC Reduction**: lifts from strongly connected DFAs via `exists_syncWord_le_sinkSCC_bound`.
2. **Degree Transport & Plateau Inequality** (`degree_transport`, `plateau_min_le_max`,
   `plateau_time_le_max`, `ap_plateau_inequality`): on strongly connected DFAs, relates
   the short-word corank `D = shortCorank A hSync` to every corank gap `δ(r)` (`2 * r < n`)
   by telescoping `M = 500` transport steps of length `h = n - 1`.
3. **Telescoping Rational Dual with Mass-Defect Retention & Two-Bin Plateau Saving**:
   - Outer regime (`n / 3 < ρ ≤ γ`): exact cubic-square slack `(186/79507) n³ ≫ (125/149769) n³`.
   - High short-word corank (`n ≤ 18 * D`):
     - If `ρ < D`, `λ(ρ) ≤ 1` and `shitov_corank_gap` at `τ = ρ` yields `(7/48) n³ + O(n²)`.
     - If `D ≤ ρ`, retaining the exact `(i / β)` weight factor on the first `D` gaps saves
       `2 * D * (γ + 1) * (k - γ) ≥ (125/149769) n³ - O(n²)`.
   - Low short-word corank (`18 * D < n`): applying `ap_plateau_inequality` (`M = 500`) on
     two flat rational bins `r/n ∈ [1/3, 38/100]` and `[38/100, 41/100]` saves
     `> 0.000926 n³ - 40 n² > (125/149769) n³ - 40 n²`.
-/

namespace Cerny

universe u v

/-! ## Part 1: Strongly Connected Diameter, Merge Graph, Degree Transport & Plateau Inequality -/

section DegreeTransportAndPlateau

variable {Q : Type u} {α : Type v}

/-- In a strongly connected finite DFA on `n` states, every state `q` is reachable from every
state `p` by a word of length at most `n - 1`. -/
theorem sc_exists_short_word [Fintype Q] [Nonempty Q] {A : DFA Q α}
    (hSC : A.IsStronglyConnected) (p q : Q) :
    ∃ u : List α, u.length ≤ Fintype.card Q - 1 ∧ A.eval p u = q := by
  classical
  have hex : ∃ m : ℕ, ∃ u : List α, u.length = m ∧ A.eval p u = q := by
    obtain ⟨u, hu⟩ := hSC p q
    exact ⟨u.length, u, rfl, hu⟩
  let m := Nat.find hex
  obtain ⟨u, hulen, hueval⟩ := Nat.find_spec hex
  refine ⟨u, ?_, hueval⟩
  rw [hulen]
  have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos
  by_contra hgt
  have hm_ge : Fintype.card Q ≤ m := by omega
  let f : Fin (m + 1) → Q := fun i => A.eval p (u.take i.val)
  have hlt : Fintype.card Q < Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨i, j, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  wlog hij : i.val < j.val generalizing i j
  · exact this j i hne.symm hfeq.symm (by omega)
  let u' : List α := u.take i.val ++ u.drop j.val
  have hu'_len : u'.length < m := by
    dsimp only [u']
    rw [List.length_append, List.length_take, List.length_drop, hulen]
    have hi : i.val ≤ m := by omega
    have hj : j.val ≤ m := by omega
    omega
  have hu'_eval : A.eval p u' = q := by
    dsimp only [u']
    rw [DFA.eval_append]
    change A.eval (f i) (u.drop j.val) = q
    rw [hfeq]
    dsimp only [f]
    rw [← DFA.eval_append, List.take_append_drop]
    exact hueval
  exact Nat.find_min hex hu'_len ⟨u', rfl, hu'_eval⟩

/-- Maximum corank `D` achievable by a word of length at most `n - 1`. -/
noncomputable def shortCorank [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) : ℕ := by
  classical
  exact ((Finset.range (Fintype.card Q)).filter
      (fun d => minCorankLen A hSync d ≤ Fintype.card Q - 1)).max' (by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
    · exact Fintype.card_pos_iff.mpr hSync.nonempty
    · rw [minCorankLen_zero]; exact Nat.zero_le _)

theorem shortCorank_le [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) : shortCorank A hSync ≤ Fintype.card Q - 1 := by
  classical
  have hmem := Finset.max'_mem ((Finset.range (Fintype.card Q)).filter
    (fun d => minCorankLen A hSync d ≤ Fintype.card Q - 1)) (by
      refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
      · exact Fintype.card_pos_iff.mpr hSync.nonempty
      · rw [minCorankLen_zero]; exact Nat.zero_le _)
  have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
  change shortCorank A hSync < Fintype.card Q at hlt
  omega

theorem minCorankLen_shortCorank_le [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) :
    minCorankLen A hSync (shortCorank A hSync) ≤ Fintype.card Q - 1 := by
  classical
  have hmem := Finset.max'_mem ((Finset.range (Fintype.card Q)).filter
    (fun d => minCorankLen A hSync d ≤ Fintype.card Q - 1)) (by
      refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
      · exact Fintype.card_pos_iff.mpr hSync.nonempty
      · rw [minCorankLen_zero]; exact Nat.zero_le _)
  exact (Finset.mem_filter.mp hmem).2

theorem corank_le_shortCorank [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {u : List α} (hu : u.length ≤ Fintype.card Q - 1) :
    Fintype.card Q - (A.image Finset.univ u).card ≤ shortCorank A hSync := by
  classical
  obtain ⟨q₀⟩ := hSync.nonempty
  have hpos : 1 ≤ (A.image Finset.univ u).card :=
    Finset.card_pos.mpr ⟨A.eval q₀ u, by rw [DFA.mem_image]; exact ⟨q₀, Finset.mem_univ q₀, rfl⟩⟩
  have hle_n : (A.image Finset.univ u).card ≤ Fintype.card Q := Finset.card_le_univ _
  let d := Fintype.card Q - (A.image Finset.univ u).card
  have hd_lt : d < Fintype.card Q := by omega
  have hd_le : d ≤ Fintype.card Q - 1 := by omega
  have hlen_le : minCorankLen A hSync d ≤ Fintype.card Q - 1 :=
    le_trans (minCorankLen_le A hSync hd_le (by omega)) hu
  exact Finset.le_max' _ d (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hd_lt, hlen_le⟩)

/-- States `y ≠ q` mergeable with `q` by a word of length at most `t`. -/
noncomputable def mergeNeighbors [Fintype Q] [DecidableEq Q] (A : DFA Q α) (t : ℕ) (q : Q) :
    Finset Q := by
  classical
  exact Finset.univ.filter (fun y => y ≠ q ∧ ∃ w : List α, w.length ≤ t ∧ A.eval y w = A.eval q w)

theorem mem_mergeNeighbors [Fintype Q] [DecidableEq Q] (A : DFA Q α) (t : ℕ) (q y : Q) :
    y ∈ mergeNeighbors A t q ↔
      y ≠ q ∧ ∃ w : List α, w.length ≤ t ∧ A.eval y w = A.eval q w := by
  classical
  simp [mergeNeighbors]

theorem mem_mergeNeighbors_symm [Fintype Q] [DecidableEq Q] (A : DFA Q α) (t : ℕ) (q y : Q) :
    y ∈ mergeNeighbors A t q ↔ q ∈ mergeNeighbors A t y := by
  simp only [mem_mergeNeighbors]
  constructor
  · rintro ⟨hne, w, hw, heq⟩; exact ⟨hne.symm, w, hw, heq.symm⟩
  · rintro ⟨hne, w, hw, heq⟩; exact ⟨hne.symm, w, hw, heq.symm⟩

theorem mergeNeighbors_mono [Fintype Q] [DecidableEq Q] (A : DFA Q α) {t₁ t₂ : ℕ}
    (ht : t₁ ≤ t₂) (q : Q) : mergeNeighbors A t₁ q ⊆ mergeNeighbors A t₂ q := by
  intro y hy
  rw [mem_mergeNeighbors] at hy ⊢
  rcases hy with ⟨hne, w, hw, heq⟩
  exact ⟨hne, w, le_trans hw ht, heq⟩

noncomputable def mergeDeg [Fintype Q] [DecidableEq Q] (A : DFA Q α) (t : ℕ) (q : Q) : ℕ :=
  (mergeNeighbors A t q).card

theorem mergeDeg_le_card [Fintype Q] [DecidableEq Q] (A : DFA Q α) (t : ℕ) (q : Q) :
    mergeDeg A t q ≤ Fintype.card Q :=
  Finset.card_le_univ _

noncomputable def maxMergeDeg [Fintype Q] [DecidableEq Q] (A : DFA Q α) (t : ℕ) : ℕ :=
  Finset.univ.sup (mergeDeg A t)

noncomputable def minMergeDeg [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (t : ℕ) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (mergeDeg A t)

theorem mergeDeg_le_maxMergeDeg [Fintype Q] [DecidableEq Q] (A : DFA Q α) (t : ℕ) (q : Q) :
    mergeDeg A t q ≤ maxMergeDeg A t :=
  Finset.le_sup (f := mergeDeg A t) (Finset.mem_univ q)

theorem minMergeDeg_le_mergeDeg [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (t : ℕ) (q : Q) : minMergeDeg A t ≤ mergeDeg A t q :=
  Finset.inf'_le (f := mergeDeg A t) (Finset.mem_univ q)

theorem maxMergeDeg_le_card [Fintype Q] [DecidableEq Q] (A : DFA Q α) (t : ℕ) :
    maxMergeDeg A t ≤ Fintype.card Q := by
  exact Finset.sup_le fun q _ => mergeDeg_le_card A t q

theorem exists_eq_maxMergeDeg [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (t : ℕ) :
    ∃ c : Q, mergeDeg A t c = maxMergeDeg A t := by
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (mergeDeg A t)
  exact ⟨c, hc.symm⟩

theorem exists_eq_minMergeDeg [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α) (t : ℕ) :
    ∃ q : Q, mergeDeg A t q = minMergeDeg A t := by
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (mergeDeg A t)
  exact ⟨q, hq.symm⟩

/-- **Degree Transport Lemma** (Hong `2611.00172v1`):
On any strongly connected synchronizing DFA, `Δ_t ≤ D + m_{t + (n - 1)}`. -/
theorem degree_transport [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected) (t : ℕ) :
    maxMergeDeg A t ≤ shortCorank A hSync + minMergeDeg A (t + (Fintype.card Q - 1)) := by
  obtain ⟨c, hc⟩ := exists_eq_maxMergeDeg A t
  obtain ⟨q, hq⟩ := exists_eq_minMergeDeg A (t + (Fintype.card Q - 1))
  obtain ⟨u, hulen, hueval⟩ := sc_exists_short_word hSC q c
  let N := mergeNeighbors A t c
  let I := A.image Finset.univ u
  have hsub_img : N ∩ I ⊆ A.image (mergeNeighbors A (t + (Fintype.card Q - 1)) q) u := by
    intro y hy
    rw [Finset.mem_inter] at hy
    obtain ⟨hyN, hyI⟩ := hy
    rw [mem_mergeNeighbors] at hyN
    obtain ⟨hy_ne_c, w, hwlen, hweq⟩ := hyN
    rw [DFA.mem_image] at hyI ⊢
    obtain ⟨z, _, hzu⟩ := hyI
    refine ⟨z, ?_, hzu⟩
    rw [mem_mergeNeighbors]
    refine ⟨?_, u ++ w, ?_, ?_⟩
    · intro hzq
      apply hy_ne_c
      rw [← hzu, hzq, hueval]
    · rw [List.length_append]; omega
    · rw [DFA.eval_append, DFA.eval_append, hzu, hueval, hweq]
  have hinter_le : (N ∩ I).card ≤ minMergeDeg A (t + (Fintype.card Q - 1)) := by
    calc (N ∩ I).card
        ≤ (A.image (mergeNeighbors A (t + (Fintype.card Q - 1)) q) u).card :=
          Finset.card_le_card hsub_img
      _ ≤ (mergeNeighbors A (t + (Fintype.card Q - 1)) q).card := A.card_image_le _ u
      _ = minMergeDeg A (t + (Fintype.card Q - 1)) := hq
  have hN_sub : N ⊆ (N ∩ I) ∪ (Finset.univ \ I) := by
    intro y hy
    by_cases hyI : y ∈ I
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hy, hyI⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyI⟩)
  have hcard_sdiff : (Finset.univ \ I).card = Fintype.card Q - I.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have hcorank : Fintype.card Q - I.card ≤ shortCorank A hSync :=
    corank_le_shortCorank A hSync hulen
  have hN_le : N.card ≤ (N ∩ I).card + (Finset.univ \ I).card :=
    le_trans (Finset.card_le_card hN_sub) (Finset.card_union_le _ _)
  change N.card = maxMergeDeg A t at hc
  omega

/-- Every shortest corank-`r` image `S` (`|S| = n - r`) is an independent set in the merge
graph at any time `t < δ(r)`. -/
private theorem exists_indep_of_lt_corankGap [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {r t : ℕ} (hr : r + 1 ≤ Fintype.card Q - 1)
    (ht : t < corankGap A hSync r) :
    ∃ S : Finset Q, S.card = Fintype.card Q - r ∧
      ∀ x ∈ S, ∀ y ∈ mergeNeighbors A t x, y ∉ S := by
  obtain ⟨u, hulen, hucard⟩ := minCorankLen_spec A hSync (by omega : r ≤ Fintype.card Q - 1)
  let S := A.image Finset.univ u
  have hS_le : S.card ≤ Fintype.card Q - r := hucard
  have hS_card : S.card = Fintype.card Q - r := by
    by_contra hne
    have hle : S.card ≤ Fintype.card Q - (r + 1) := by omega
    have hmin := minCorankLen_le A hSync hr hle
    dsimp only [corankGap] at ht
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
    rw [DFA.image_append]
    change (A.image S w).card ≤ Fintype.card Q - (r + 1)
    omega
  have hmin := minCorankLen_le A hSync hr hnext
  rw [List.length_append, hulen] at hmin
  have hmono := minCorankLen_mono A hSync (Nat.le_add_right r 1) hr
  dsimp only [corankGap] at ht
  omega

/-- On any independent set `S` of `mergeNeighbors A t`, the sum of merge degrees over `S`
is bounded by `|Q \ S| * Δ_t`. -/
private theorem sum_mergeDeg_on_indep_le [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    {t : ℕ} {S : Finset Q} (hind : ∀ x ∈ S, ∀ y ∈ mergeNeighbors A t x, y ∉ S) :
    (∑ x ∈ S, mergeDeg A t x) ≤ (Finset.univ \ S).card * maxMergeDeg A t := by
  let B := Finset.univ \ S
  have hdeg_eq : ∀ x ∈ S,
      mergeDeg A t x = ∑ y ∈ B, if y ∈ mergeNeighbors A t x then 1 else 0 := by
    intro x hx
    rw [← Finset.card_filter]
    have hfilt : B.filter (fun y => y ∈ mergeNeighbors A t x) = mergeNeighbors A t x := by
      ext y
      simp only [B, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun hy => ⟨hind x hx y hy, hy⟩⟩
    rw [hfilt]
    rfl
  calc (∑ x ∈ S, mergeDeg A t x)
      = ∑ x ∈ S, ∑ y ∈ B, if y ∈ mergeNeighbors A t x then 1 else 0 :=
        Finset.sum_congr rfl hdeg_eq
    _ = ∑ y ∈ B, ∑ x ∈ S, if y ∈ mergeNeighbors A t x then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ y ∈ B, mergeDeg A t y := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [← Finset.card_filter]
        refine Finset.card_le_card fun x hx => ?_
        rw [Finset.mem_filter] at hx
        exact (mem_mergeNeighbors_symm A t x y).mp hx.2
    _ ≤ ∑ _y ∈ B, maxMergeDeg A t :=
        Finset.sum_le_sum fun y _ => mergeDeg_le_maxMergeDeg A t y
    _ = B.card * maxMergeDeg A t := by simp

/-- Plateau degree ratio: `(n - r) * m_t ≤ r * Δ_t` for every `t < δ(r)`. -/
theorem plateau_min_le_max [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {r t : ℕ} (hr : r + 1 ≤ Fintype.card Q - 1)
    (ht : t < corankGap A hSync r) :
    (Fintype.card Q - r) * minMergeDeg A t ≤ r * maxMergeDeg A t := by
  obtain ⟨S, hS_card, hind⟩ := exists_indep_of_lt_corankGap A hSync hr ht
  have hB_card : (Finset.univ \ S).card = r := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hS_card]
    omega
  calc (Fintype.card Q - r) * minMergeDeg A t
      = ∑ _x ∈ S, minMergeDeg A t := by rw [Finset.sum_const, smul_eq_mul, hS_card]
    _ ≤ ∑ x ∈ S, mergeDeg A t x := Finset.sum_le_sum fun x _ => minMergeDeg_le_mergeDeg A t x
    _ ≤ (Finset.univ \ S).card * maxMergeDeg A t := sum_mergeDeg_on_indep_le A hind
    _ = r * maxMergeDeg A t := by rw [hB_card]

/-- If the merge relation stabilizes from `s` to `s + 1`, then every synchronizing pair is
already mergeable in at most `s` steps. -/
private theorem mergeNeighbors_all_of_stabilize [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {s : ℕ}
    (hstab : ∀ x y : Q, y ∈ mergeNeighbors A (s + 1) x → y ∈ mergeNeighbors A s x) :
    ∀ x y : Q, x ≠ y → y ∈ mergeNeighbors A s x := by
  have hstep : ∀ (w : List α) (x y : Q), x ≠ y → A.eval x w = A.eval y w →
      y ∈ mergeNeighbors A s x := by
    intro w
    induction w with
    | nil => intro x y hne heq; exact absurd heq hne
    | cons a w ih =>
      intro x y hne heq
      rw [DFA.eval_cons, DFA.eval_cons] at heq
      by_cases h1 : A.step x a = A.step y a
      · refine hstab x y ((mem_mergeNeighbors A (s + 1) x y).mpr ⟨hne.symm, [a], by simp, ?_⟩)
        simpa using h1.symm
      · have hmem := ih (A.step x a) (A.step y a) h1 heq
        rw [mem_mergeNeighbors] at hmem
        obtain ⟨_, v, hvlen, hveq⟩ := hmem
        refine hstab x y ((mem_mergeNeighbors A (s + 1) x y).mpr ⟨hne.symm, a :: v, ?_, ?_⟩)
        · simp; omega
        · rw [DFA.eval_cons, DFA.eval_cons]; exact hveq
  rcases hSync with ⟨w, q₀, hq₀⟩
  intro x y hne
  exact hstep w x y hne (by rw [hq₀ x, hq₀ y])

/-- Until the merge graph saturates, the sum of merge degrees grows by at least `2` per step. -/
private theorem two_mul_le_sum_mergeDeg [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {r t : ℕ} (hr : r + 1 ≤ Fintype.card Q - 1)
    (ht : t < corankGap A hSync r) :
    2 * t ≤ ∑ x : Q, mergeDeg A t x := by
  induction t with
  | zero => simp
  | succ s ih =>
    have ihs : 2 * s ≤ ∑ x : Q, mergeDeg A s x := ih (by omega)
    have hnot_stab : ∃ x y : Q, y ∈ mergeNeighbors A (s + 1) x ∧ y ∉ mergeNeighbors A s x := by
      by_contra hnone
      push Not at hnone
      have hall := mergeNeighbors_all_of_stabilize A hSync hnone
      obtain ⟨S, hS_card, hind⟩ := exists_indep_of_lt_corankGap A hSync hr (by omega : s < corankGap A hSync r)
      have hge2 : 1 < S.card := by omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hge2
      exact hind x hx y (hall x y hxy) hy
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
    have hmono : ∀ q : Q, mergeDeg A s q ≤ mergeDeg A (s + 1) q :=
      fun q => Finset.card_le_card (mergeNeighbors_mono A (Nat.le_succ s) q)
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
      Finset.sum_le_sum fun q _ => hmono q
    omega

/-- Plateau edge-count bound: `t ≤ r * Δ_t` for every `t < δ(r)`. -/
theorem plateau_time_le_max [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {r t : ℕ} (hr : r + 1 ≤ Fintype.card Q - 1)
    (ht : t < corankGap A hSync r) :
    t ≤ r * maxMergeDeg A t := by
  obtain ⟨S, hS_card, hind⟩ := exists_indep_of_lt_corankGap A hSync hr ht
  have hB_card : (Finset.univ \ S).card = r := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hS_card]
    omega
  have h2t := two_mul_le_sum_mergeDeg A hSync hr ht
  have hsplit : (∑ x : Q, mergeDeg A t x) =
      (∑ x ∈ S, mergeDeg A t x) + (∑ x ∈ Finset.univ \ S, mergeDeg A t x) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ S), add_comm]
  have hS_le : (∑ x ∈ S, mergeDeg A t x) ≤ r * maxMergeDeg A t := by
    rw [← hB_card]; exact sum_mergeDeg_on_indep_le A hind
  have hB_le : (∑ x ∈ Finset.univ \ S, mergeDeg A t x) ≤ r * maxMergeDeg A t := by
    calc (∑ x ∈ Finset.univ \ S, mergeDeg A t x)
        ≤ ∑ _x ∈ Finset.univ \ S, maxMergeDeg A t :=
          Finset.sum_le_sum fun x _ => mergeDeg_le_maxMergeDeg A t x
      _ = (Finset.univ \ S).card * maxMergeDeg A t := by simp
      _ = r * maxMergeDeg A t := by rw [hB_card]
  omega

/-- **Unconditional Telescoping Plateau Inequality** (Catch 7 Fix A):
On any strongly connected synchronizing DFA on `n` states, for every `1 ≤ r` with `2 * r < n`
and every `1 ≤ M`:
`δ(r) ≤ (r * (n - r) / (n - 2 * r)) * D + (r^2 / (n - 2 * r)) * (n / M) + M * n`. -/
theorem ap_plateau_inequality [Fintype Q] [Nonempty Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected)
    {r M : ℕ} (hr1 : 1 ≤ r) (h2r : 2 * r < Fintype.card Q) (hM1 : 1 ≤ M) :
    let n := Fintype.card Q
    (corankGap A hSync r : ℚ) ≤
      (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * (shortCorank A hSync : ℚ) +
      (r : ℚ) ^ 2 / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / (M : ℚ)) +
      (M : ℚ) * (n : ℚ) := by
  intro n
  have hn_pos : (0 : ℚ) < (n : ℚ) := by
    have : 0 < n := by omega
    positivity
  have hden_pos : (0 : ℚ) < (n : ℚ) - 2 * (r : ℚ) := by
    have : (2 * r : ℕ) < n := h2r
    have hq : (2 : ℚ) * r < n := by exact_mod_cast this
    linarith
  have hM_pos : (0 : ℚ) < (M : ℚ) := by positivity
  have hnr_pos : (0 : ℚ) ≤ (n : ℚ) - (r : ℚ) := by
    have : (r : ℚ) ≤ n := by exact_mod_cast (by omega : r ≤ n)
    linarith
  let h := n - 1
  -- Case A: small gap δ(r) ≤ M * h + 1 ≤ M * n
  by_cases hsmall : corankGap A hSync r ≤ M * h + 1
  · have hle_Mn : corankGap A hSync r ≤ M * n := by
      have : M * h + 1 ≤ M * n := by
        have h1 : 1 ≤ M := hM1
        have h2 : M * h + M = M * n := by
          dsimp only [h]
          zify [show 1 ≤ n by omega]
          ring
        omega
      omega
    have hq_Mn : (corankGap A hSync r : ℚ) ≤ (M : ℚ) * (n : ℚ) := by exact_mod_cast hle_Mn
    have ht1 : (0 : ℚ) ≤ (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) *
        (shortCorank A hSync : ℚ) := by positivity
    have ht2 : (0 : ℚ) ≤ (r : ℚ) ^ 2 / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / (M : ℚ)) := by
      positivity
    linarith
  -- Case B: M * h + 1 < δ(r), telescope M transport steps
  · have hlarge : M * h ≤ corankGap A hSync r - 1 := by omega
    have hr_le : r + 1 ≤ n - 1 := by omega
    let t : ℕ → ℕ := fun j => (corankGap A hSync r - 1) - (M - j) * h
    have ht_lt : ∀ j ≤ M, t j < corankGap A hSync r := by
      intro j _
      dsimp only [t]
      omega
    have ht_step : ∀ j < M, t j + h = t (j + 1) := by
      intro j hj
      dsimp only [t]
      have hle1 : (M - j) * h ≤ corankGap A hSync r - 1 :=
        le_trans (Nat.mul_le_mul_right h (by omega : M - j ≤ M)) hlarge
      have hle2 : (M - (j + 1)) * h ≤ corankGap A hSync r - 1 :=
        le_trans (Nat.mul_le_mul_right h (by omega : M - (j + 1) ≤ M)) hlarge
      have hsub : (M - j) * h = (M - (j + 1)) * h + h := by
        have : M - j = M - (j + 1) + 1 := by omega
        rw [this, Nat.add_mul, one_mul]
      omega
    have hstep_ineq : ∀ j ∈ Finset.range M,
        (n - r) * maxMergeDeg A (t j) ≤
          (n - r) * shortCorank A hSync + r * maxMergeDeg A (t (j + 1)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have htr := degree_transport A hSync hSC (t j)
      change maxMergeDeg A (t j) ≤ shortCorank A hSync + minMergeDeg A (t j + h) at htr
      rw [ht_step j hj] at htr
      have hpm := plateau_min_le_max A hSync hr_le (ht_lt (j + 1) (by omega))
      change (n - r) * minMergeDeg A (t (j + 1)) ≤ r * maxMergeDeg A (t (j + 1)) at hpm
      have hmul := Nat.mul_le_mul_left (n - r) htr
      rw [Nat.mul_add] at hmul
      omega
    have hsum_step := Finset.sum_le_sum hstep_ineq
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, ← Finset.mul_sum] at hsum_step
    have htele_gen : ∀ (g : ℕ → ℕ) (m : ℕ),
        (∑ j ∈ Finset.range m, g (j + 1)) + g 0 = (∑ j ∈ Finset.range m, g j) + g m := by
      intro g m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        omega
    have htele_sum := htele_gen (fun j => maxMergeDeg A (t j)) M
    have htop_le : maxMergeDeg A (t M) ≤ n := maxMergeDeg_le_card A (t M)
    have hsum_shift_le : (∑ j ∈ Finset.range M, maxMergeDeg A (t (j + 1))) ≤
        (∑ j ∈ Finset.range M, maxMergeDeg A (t j)) + n := by omega
    have htele_nat : (n - 2 * r) * (∑ j ∈ Finset.range M, maxMergeDeg A (t j)) ≤
        M * ((n - r) * shortCorank A hSync) + r * n := by
      have hr_shift := Nat.mul_le_mul_left r hsum_shift_le
      rw [Nat.mul_add] at hr_shift
      have hsub_mul : (n - r) * (∑ j ∈ Finset.range M, maxMergeDeg A (t j)) =
          (n - 2 * r) * (∑ j ∈ Finset.range M, maxMergeDeg A (t j)) +
          r * (∑ j ∈ Finset.range M, maxMergeDeg A (t j)) := by
        rw [← Nat.add_mul]
        congr 1; omega
      omega
    have hsum_t_le : (∑ j ∈ Finset.range M, t j) ≤
        r * (∑ j ∈ Finset.range M, maxMergeDeg A (t j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj =>
        plateau_time_le_max A hSync hr_le (ht_lt j (by rw [Finset.mem_range] at hj; omega))
    have hsum_t_ge : M * (corankGap A hSync r - 1 - M * h) ≤ ∑ j ∈ Finset.range M, t j := by
      calc M * (corankGap A hSync r - 1 - M * h)
          = ∑ _j ∈ Finset.range M, (corankGap A hSync r - 1 - M * h) := by simp
        _ ≤ ∑ j ∈ Finset.range M, t j := by
            refine Finset.sum_le_sum fun j hj => ?_
            rw [Finset.mem_range] at hj
            dsimp only [t]
            have : (M - j) * h ≤ M * h := Nat.mul_le_mul_right h (by omega)
            omega
    have hcore_nat : (n - 2 * r) * (M * (corankGap A hSync r - 1 - M * h)) ≤
        r * (M * ((n - r) * shortCorank A hSync) + r * n) := by
      calc (n - 2 * r) * (M * (corankGap A hSync r - 1 - M * h))
          ≤ (n - 2 * r) * (∑ j ∈ Finset.range M, t j) := Nat.mul_le_mul_left _ hsum_t_ge
        _ ≤ (n - 2 * r) * (r * (∑ j ∈ Finset.range M, maxMergeDeg A (t j))) :=
            Nat.mul_le_mul_left _ hsum_t_le
        _ = r * ((n - 2 * r) * (∑ j ∈ Finset.range M, maxMergeDeg A (t j))) := by ring
        _ ≤ r * (M * ((n - r) * shortCorank A hSync) + r * n) := Nat.mul_le_mul_left _ htele_nat
    have hcore_q :
        ((n : ℚ) - 2 * (r : ℚ)) * ((M : ℚ) * ((corankGap A hSync r : ℚ) - (M : ℚ) * (n : ℚ))) ≤
        (r : ℚ) * ((M : ℚ) * (((n : ℚ) - (r : ℚ)) * (shortCorank A hSync : ℚ)) +
          (r : ℚ) * (n : ℚ)) := by
      have hcast :
          (((n - 2 * r) * (M * (corankGap A hSync r - 1 - M * h)) : ℕ) : ℚ) ≤
          ((r * (M * ((n - r) * shortCorank A hSync) + r * n) : ℕ) : ℚ) := by
        exact_mod_cast hcore_nat
      have hle_sub : M * h + 1 ≤ corankGap A hSync r := by omega
      have hgap_ge : (corankGap A hSync r : ℚ) - (M : ℚ) * (n : ℚ) ≤
          ((corankGap A hSync r - 1 - M * h : ℕ) : ℚ) := by
        have hMn_ge : M * h + 1 ≤ M * n := by
          have : M * h + M = M * n := by
            dsimp only [h]; zify [show 1 ≤ n by omega]; ring
          omega
        have hnat : corankGap A hSync r - M * n ≤ corankGap A hSync r - 1 - M * h := by omega
        have hq : ((corankGap A hSync r - M * n : ℕ) : ℚ) ≤
            ((corankGap A hSync r - 1 - M * h : ℕ) : ℚ) := by exact_mod_cast hnat
        by_cases hcmp : M * n ≤ corankGap A hSync r
        · rw [Nat.cast_sub hcmp, Nat.cast_mul] at hq
          exact hq
        · have hlt_q : (corankGap A hSync r : ℚ) ≤ (M : ℚ) * (n : ℚ) := by
            exact_mod_cast (by omega : corankGap A hSync r ≤ M * n)
          have h0 : (0 : ℚ) ≤ ((corankGap A hSync r - 1 - M * h : ℕ) : ℚ) := Nat.cast_nonneg _
          linarith
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 * r ≤ n), Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_sub (by omega : r ≤ n), Nat.cast_mul] at hcast
      have hmono_q :
          ((n : ℚ) - 2 * (r : ℚ)) * ((M : ℚ) * ((corankGap A hSync r : ℚ) - (M : ℚ) * (n : ℚ))) ≤
          ((n : ℚ) - 2 * (r : ℚ)) * ((M : ℚ) * ((corankGap A hSync r - 1 - M * h : ℕ) : ℚ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgap_ge hM_pos.le) hden_pos.le
      linarith
    have hdiv_pos : (0 : ℚ) < ((n : ℚ) - 2 * (r : ℚ)) * (M : ℚ) := mul_pos hden_pos hM_pos
    have hrew_rhs :
        ((n : ℚ) - 2 * (r : ℚ)) * (M : ℚ) *
          ((r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * (shortCorank A hSync : ℚ) +
           (r : ℚ) ^ 2 / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / (M : ℚ))) =
        (r : ℚ) * ((M : ℚ) * (((n : ℚ) - (r : ℚ)) * (shortCorank A hSync : ℚ)) +
          (r : ℚ) * (n : ℚ)) := by
      have hden_ne : (n : ℚ) - 2 * (r : ℚ) ≠ 0 := hden_pos.ne'
      have hM_ne : (M : ℚ) ≠ 0 := hM_pos.ne'
      field_simp
    have hmul_le :
        ((n : ℚ) - 2 * (r : ℚ)) * (M : ℚ) * ((corankGap A hSync r : ℚ) - (M : ℚ) * (n : ℚ)) ≤
        ((n : ℚ) - 2 * (r : ℚ)) * (M : ℚ) *
          ((r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * (shortCorank A hSync : ℚ) +
           (r : ℚ) ^ 2 / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / (M : ℚ))) := by
      rw [hrew_rhs]
      linarith
    have hcancel := le_of_mul_le_mul_left hmul_le hdiv_pos
    linarith

end DegreeTransportAndPlateau

/-! ## Part 2: Telescoping Rational Dual, Mass-Defect Retention & Two-Bin Plateau Helpers -/

section SubShitovDualHelpers

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
      ext x
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    · rw [Finset.disjoint_left]
      intro x h1 h2
      rw [Finset.mem_range] at h1
      rw [Finset.mem_Ico] at h2
      omega
  have ha := six_mul_sum_range_choose_two a
  have hb := six_mul_sum_range_choose_two b
  omega

private theorem eight_mul_cube_ge {n k : ℕ} (hn : 100 ≤ n) (hk : n ≤ 2 * k + 3) :
    n ^ 3 ≤ 8 * ((k + 1) * ((k + 1) + 1) * ((k + 1) + 2)) := by
  have h1 : n - 1 ≤ 2 * (k + 1) := by omega
  have h2 : n + 1 ≤ 2 * ((k + 1) + 1) := by omega
  have h3 : n + 3 ≤ 2 * ((k + 1) + 2) := by omega
  have hprod : (n - 1) * (n + 1) * (n + 3) ≤
      (2 * (k + 1)) * (2 * ((k + 1) + 1)) * (2 * ((k + 1) + 2)) :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hcub : n ^ 3 ≤ (n - 1) * (n + 1) * (n + 3) := by
    zify [show 1 ≤ n by omega]
    have hn' : (100 : ℤ) ≤ n := by omega
    nlinarith
  linarith

private theorem sum_Icc_inv_mul_succ {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ r ∈ Finset.Icc a b, (1 : ℚ) / ((r : ℚ) * ((r : ℚ) + 1))) =
      1 / (a : ℚ) - 1 / ((b : ℚ) + 1) := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have ha_ne : (a : ℚ) ≠ 0 := by positivity
    have ha1_ne : (a : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  | succ b hab ih =>
    have hsplit : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : b + 1 ∉ Finset.Icc a b := by simp
    rw [hsplit, Finset.sum_insert hnot, ih]
    have hb1_ne : (b : ℚ) + 1 ≠ 0 := by positivity
    have hb2_ne : (b : ℚ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private theorem sum_Icc_div_succ_ge {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ((b : ℚ) - (a : ℚ)) * (1 - 1 / (a : ℚ)) ≤
      ∑ r ∈ Finset.Icc a b, (r : ℚ) / ((r : ℚ) + 1) := by
  have ha_pos : (0 : ℚ) < (a : ℚ) := by positivity
  have hterm : ∀ r ∈ Finset.Icc a b, 1 - 1 / (a : ℚ) ≤ (r : ℚ) / ((r : ℚ) + 1) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr_ge : (a : ℚ) ≤ (r : ℚ) := by exact_mod_cast hr.1
    have hr1_pos : (0 : ℚ) < (r : ℚ) + 1 := by positivity
    have hprod_pos : (0 : ℚ) < (a : ℚ) * ((r : ℚ) + 1) := mul_pos ha_pos hr1_pos
    have hmul : (1 - 1 / (a : ℚ)) * ((a : ℚ) * ((r : ℚ) + 1)) ≤
        ((r : ℚ) / ((r : ℚ) + 1)) * ((a : ℚ) * ((r : ℚ) + 1)) := by
      have h1 : (1 - 1 / (a : ℚ)) * ((a : ℚ) * ((r : ℚ) + 1)) =
          ((a : ℚ) - 1) * ((r : ℚ) + 1) := by field_simp
      have h2 : ((r : ℚ) / ((r : ℚ) + 1)) * ((a : ℚ) * ((r : ℚ) + 1)) =
          (r : ℚ) * (a : ℚ) := by field_simp
      rw [h1, h2]
      nlinarith
    exact le_of_mul_le_mul_right hmul hprod_pos
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
  have hcard_ge : (b : ℚ) - (a : ℚ) ≤ ((b + 1 - a : ℕ) : ℚ) := by
    have hq : ((b + 1 - a : ℕ) : ℚ) = (b : ℚ) + 1 - (a : ℚ) := by
      rw [Nat.cast_sub (by omega : a ≤ b + 1)]; push_cast; ring
    linarith
  have h1_nonneg : (0 : ℚ) ≤ 1 - 1 / (a : ℚ) := by
    have ha1 : (1 : ℚ) ≤ a := by exact_mod_cast ha
    have : 1 / (a : ℚ) ≤ 1 := by rw [div_le_one ha_pos]; exact ha1
    linarith
  exact le_trans (mul_le_mul_of_nonneg_right hcard_ge h1_nonneg) hsum

/-- Telescoping rational dual weight `α_r ∈ [0, 1]` shared across all Sub-Shitov regimes. -/
private def dualAlpha (k γ β r : ℕ) : ℚ :=
  let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
  if r < β then 0
  else if r ≤ γ then M / ((r : ℚ) * ((r : ℚ) + 1))
  else 1

private theorem dualAlpha_bounds {n k γ ρ β : ℕ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hβ : β = max ρ (n / 10)) (r : ℕ) :
    (0 : ℚ) ≤ dualAlpha k γ β r ∧ dualAlpha k γ β r ≤ 1 := by
  dsimp only [dualAlpha]
  split_ifs with h1 h2
  · exact ⟨le_rfl, zero_le_one⟩
  · have hr_geβ : β ≤ r := by omega
    have hM_nonneg : (0 : ℚ) ≤ (γ : ℚ) * ((k : ℚ) - (γ : ℚ)) := by
      have : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
      nlinarith
    have hr_pos : (0 : ℚ) < (r : ℚ) * ((r : ℚ) + 1) := by
      have : 0 < r := by omega
      positivity
    refine ⟨div_nonneg hM_nonneg hr_pos.le, ?_⟩
    rw [div_le_one hr_pos]
    have hM_nat : 66564 * (γ * (k - γ)) ≤ 500 * n ^ 2 := by
      have h1' : 258 * γ ≤ 125 * n := by omega
      have h2' : 258 * (k - γ) ≤ 4 * n := by omega
      have hprod : (258 * γ) * (258 * (k - γ)) ≤ (125 * n) * (4 * n) :=
        Nat.mul_le_mul h1' h2'
      linarith
    have hr_nat : 500 * n ^ 2 ≤ 66564 * (r * (r + 1)) := by
      have h10r1 : n ≤ 10 * (r + 1) := by omega
      have hprod : (n - 9) * n ≤ (10 * r) * (10 * (r + 1)) :=
        Nat.mul_le_mul (by omega) h10r1
      zify [show 9 ≤ n by omega] at hprod ⊢
      nlinarith
    have hnat : γ * (k - γ) ≤ r * (r + 1) := by omega
    have hq : ((γ * (k - γ) : ℕ) : ℚ) ≤ ((r * (r + 1) : ℕ) : ℚ) := by exact_mod_cast hnat
    rw [Nat.cast_mul, Nat.cast_sub (by omega : γ ≤ k), Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hq
    exact hq
  · exact ⟨zero_le_one, le_rfl⟩

/-- Uniform telescoping bound `W_i ≤ (γ + 1) * (k - γ)` for all `1 ≤ i ≤ k`. -/
private theorem dual_weight_le {β γ k i : ℕ}
    (hβ1 : 1 ≤ β) (hβγ : β ≤ γ) (hγk : γ < k) (h2γ : k ≤ 2 * γ)
    (hi1 : 1 ≤ i) (hik : i ≤ k) :
    (i : ℚ) * (∑ r ∈ Finset.Icc (max β i) k, dualAlpha k γ β r) ≤
      ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
  let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
  have hM_nonneg : (0 : ℚ) ≤ M := by
    dsimp only [M]
    have : (γ : ℚ) ≤ (k : ℚ) := by exact_mod_cast (by omega : γ ≤ k)
    nlinarith
  have hk_sub_γ_nonneg : (0 : ℚ) ≤ (k : ℚ) - (γ : ℚ) := by
    have : (γ : ℚ) ≤ (k : ℚ) := by exact_mod_cast (by omega : γ ≤ k)
    linarith
  by_cases hiγ : γ < i
  · have hmax : max β i = i := max_eq_right (by omega)
    rw [hmax]
    have hsum1 : (∑ r ∈ Finset.Icc i k, dualAlpha k γ β r) = (k : ℚ) - (i : ℚ) + 1 := by
      have hconst : ∀ r ∈ Finset.Icc i k, dualAlpha k γ β r = 1 := by
        intro r hr
        rw [Finset.mem_Icc] at hr
        have h1 : ¬ r < β := by omega
        have h2 : ¬ r ≤ γ := by omega
        simp [dualAlpha, h1, h2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      rw [Nat.cast_sub (by omega : i ≤ k + 1)]; push_cast; ring
    rw [hsum1]
    have hdiff : ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) - (i : ℚ) * ((k : ℚ) - (i : ℚ) + 1) =
        ((i : ℚ) - ((γ : ℚ) + 1)) * ((i : ℚ) + (γ : ℚ) - (k : ℚ)) := by ring
    have h1 : (0 : ℚ) ≤ (i : ℚ) - ((γ : ℚ) + 1) := by
      have : γ + 1 ≤ i := by omega
      have hq : (γ : ℚ) + 1 ≤ (i : ℚ) := by exact_mod_cast this
      linarith
    have h2 : (0 : ℚ) ≤ (i : ℚ) + (γ : ℚ) - (k : ℚ) := by
      have : k ≤ i + γ := by omega
      have hq : (k : ℚ) ≤ (i : ℚ) + (γ : ℚ) := by exact_mod_cast this
      linarith
    have hprod : (0 : ℚ) ≤ ((i : ℚ) - ((γ : ℚ) + 1)) * ((i : ℚ) + (γ : ℚ) - (k : ℚ)) :=
      mul_nonneg h1 h2
    linarith
  · push Not at hiγ
    let a := max β i
    have ha1 : 1 ≤ a := by omega
    have haγ : a ≤ γ := by omega
    have hsplit : Finset.Icc a k = Finset.Icc a γ ∪ Finset.Icc (γ + 1) k := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc a γ) (Finset.Icc (γ + 1) k) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2; simp only [Finset.mem_Icc] at hx1 hx2; omega
    have hpart1 : (∑ r ∈ Finset.Icc a γ, dualAlpha k γ β r) =
        M * (1 / (a : ℚ) - 1 / ((γ : ℚ) + 1)) := by
      have hrew : ∀ r ∈ Finset.Icc a γ,
          dualAlpha k γ β r = M * (1 / ((r : ℚ) * ((r : ℚ) + 1))) := by
        intro r hr
        rw [Finset.mem_Icc] at hr
        have h1 : ¬ r < β := by omega
        have h2 : r ≤ γ := hr.2
        simp only [dualAlpha, h1, h2, ↓reduceIte]
        dsimp only [M]; ring
      rw [Finset.sum_congr rfl hrew, ← Finset.mul_sum, sum_Icc_inv_mul_succ ha1 haγ]
    have hpart2 : (∑ r ∈ Finset.Icc (γ + 1) k, dualAlpha k γ β r) = (k : ℚ) - (γ : ℚ) := by
      have hconst : ∀ r ∈ Finset.Icc (γ + 1) k, dualAlpha k γ β r = 1 := by
        intro r hr
        rw [Finset.mem_Icc] at hr
        have h1 : ¬ r < β := by omega
        have h2 : ¬ r ≤ γ := by omega
        simp [dualAlpha, h1, h2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      rw [Nat.cast_sub (by omega : γ + 1 ≤ k + 1)]; push_cast; ring
    change (i : ℚ) * (∑ r ∈ Finset.Icc a k, dualAlpha k γ β r) ≤ _
    rw [hsplit, Finset.sum_union hdisj, hpart1, hpart2]
    have hγ1_pos : (0 : ℚ) < (γ : ℚ) + 1 := by positivity
    have ha_pos : (0 : ℚ) < (a : ℚ) := by positivity
    have hsimp : M * (1 / (a : ℚ) - 1 / ((γ : ℚ) + 1)) + ((k : ℚ) - (γ : ℚ)) =
        M / (a : ℚ) + ((k : ℚ) - (γ : ℚ)) / ((γ : ℚ) + 1) := by
      dsimp only [M]; field_simp; ring
    rw [hsimp, mul_add]
    have h1 : (i : ℚ) * (M / (a : ℚ)) ≤ M := by
      rw [mul_div_left_comm]
      have hratio : (i : ℚ) / (a : ℚ) ≤ 1 := by
        rw [div_le_one ha_pos]
        exact_mod_cast (le_max_right β i : i ≤ a)
      nlinarith
    have h2 : (i : ℚ) * (((k : ℚ) - (γ : ℚ)) / ((γ : ℚ) + 1)) ≤ (k : ℚ) - (γ : ℚ) := by
      rw [mul_div_left_comm]
      have hratio : (i : ℚ) / ((γ : ℚ) + 1) ≤ 1 := by
        rw [div_le_one hγ1_pos]
        exact_mod_cast (by omega : i ≤ γ + 1)
      nlinarith
    have hsum_eq : M + ((k : ℚ) - (γ : ℚ)) = ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
      dsimp only [M]; ring
    linarith

/-- Sharp mass-defect bound `W_i ≤ (i / β) * (γ + 1) * (k - γ)` for ALL `1 ≤ i ≤ k`. -/
private theorem dual_weight_le_div_beta {β γ k i : ℕ}
    (hβ1 : 1 ≤ β) (hβγ : β ≤ γ) (hγk : γ < k) (h2γ : k ≤ 2 * γ)
    (hi1 : 1 ≤ i) (hik : i ≤ k) :
    (i : ℚ) * (∑ r ∈ Finset.Icc (max β i) k, dualAlpha k γ β r) ≤
      ((i : ℚ) / (β : ℚ)) * (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) := by
  have hβ_pos : (0 : ℚ) < (β : ℚ) := by positivity
  have hfac_nonneg : (0 : ℚ) ≤ ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
    have : (γ : ℚ) ≤ (k : ℚ) := by exact_mod_cast (by omega : γ ≤ k)
    nlinarith
  by_cases hcmp : β ≤ i
  · have hge1 : (1 : ℚ) ≤ (i : ℚ) / (β : ℚ) := by
      rw [one_le_div hβ_pos]
      exact_mod_cast hcmp
    have hbase := dual_weight_le hβ1 hβγ hγk h2γ hi1 hik
    have hmul := mul_le_mul_of_nonneg_right hge1 hfac_nonneg
    linarith
  · have hmax : max β i = β := max_eq_left (by omega)
    rw [hmax]
    have hbase := dual_weight_le hβ1 hβγ hγk h2γ hβ1 (by omega : β ≤ k)
    rw [max_self] at hbase
    have hsum_le : (∑ r ∈ Finset.Icc β k, dualAlpha k γ β r) ≤
        (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) / (β : ℚ) := by
      rw [le_div_iff₀ hβ_pos]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum_le (Nat.cast_nonneg i)
    have hrw : (i : ℚ) * ((((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) / (β : ℚ)) =
        ((i : ℚ) / (β : ℚ)) * (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) := by ring
    linarith

/-- Piece A base bound: `∑_{r ∈ Icc ρ k} (1 - α_r) * (r^2 / 2)`. -/
private theorem pieceA_base {n k γ ρ β : ℕ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ_le_γ : ρ ≤ γ) (hβ : β = max ρ (n / 10)) :
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    (∑ r ∈ Finset.Icc ρ k, (1 - dualAlpha k γ β r) * ((r : ℚ) ^ 2 / 2)) ≤
      ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
        (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) := by
  intro M
  have hγ_lt_k : γ < k := by omega
  have hβ_ge10 : 10 ≤ β := by omega
  have hβ_le_γ : β ≤ γ := by omega
  have hρ_le_β : ρ ≤ β := by omega
  have hM_nonneg : (0 : ℚ) ≤ M := by
    dsimp only [M]
    have : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
    nlinarith
  have hsplit1 : Finset.Icc ρ k = Finset.Icc ρ γ ∪ Finset.Icc (γ + 1) k := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj1 : Disjoint (Finset.Icc ρ γ) (Finset.Icc (γ + 1) k) := by
    rw [Finset.disjoint_left]; intro r h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
  have hzero_hi :
      (∑ r ∈ Finset.Icc (γ + 1) k, (1 - dualAlpha k γ β r) * ((r : ℚ) ^ 2 / 2)) = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [Finset.mem_Icc] at hr
    have h1 : ¬ r < β := by omega
    have h2 : ¬ r ≤ γ := by omega
    simp [dualAlpha, h1, h2]
  have hsplit2 : Finset.Icc ρ γ = Finset.Ico ρ β ∪ Finset.Icc β γ := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_Ico, Finset.mem_union]; omega
  have hdisj2 : Disjoint (Finset.Ico ρ β) (Finset.Icc β γ) := by
    rw [Finset.disjoint_left]; intro r h1 h2
    simp only [Finset.mem_Ico, Finset.mem_Icc] at h1 h2; omega
  have hrew_sub :
      (∑ r ∈ Finset.Icc ρ γ, (1 - dualAlpha k γ β r) * ((r : ℚ) ^ 2 / 2)) =
      (∑ r ∈ Finset.Icc ρ γ, (r : ℚ) ^ 2 / 2) -
      (M / 2) * (∑ r ∈ Finset.Icc β γ, (r : ℚ) / ((r : ℚ) + 1)) := by
    rw [hsplit2, Finset.sum_union hdisj2, Finset.sum_union hdisj2]
    have hlo : (∑ r ∈ Finset.Ico ρ β, (1 - dualAlpha k γ β r) * ((r : ℚ) ^ 2 / 2)) =
        ∑ r ∈ Finset.Ico ρ β, (r : ℚ) ^ 2 / 2 := by
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_Ico] at hr
      simp [dualAlpha, hr.2]
    have hhi : (∑ r ∈ Finset.Icc β γ, (1 - dualAlpha k γ β r) * ((r : ℚ) ^ 2 / 2)) =
        (∑ r ∈ Finset.Icc β γ, (r : ℚ) ^ 2 / 2) -
        (M / 2) * (∑ r ∈ Finset.Icc β γ, (r : ℚ) / ((r : ℚ) + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_Icc] at hr
      have h1 : ¬ r < β := by omega
      have h2 : r ≤ γ := hr.2
      have hr_ne : (r : ℚ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
      have hr1_ne : (r : ℚ) + 1 ≠ 0 := by positivity
      simp only [dualAlpha, h1, h2, ↓reduceIte]
      dsimp only [M]
      field_simp
    rw [hlo, hhi]
    ring
  have hsq_sum : (∑ r ∈ Finset.Icc ρ γ, (r : ℚ) ^ 2 / 2) ≤
      ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 := by
    have hle_choose : (∑ r ∈ Finset.Icc ρ γ, (r : ℚ) ^ 2 / 2) ≤
        ((∑ r ∈ Finset.Ico ρ (γ + 1), (r + 2).choose 2 : ℕ) : ℚ) := by
      have hIco : Finset.Icc ρ γ = Finset.Ico ρ (γ + 1) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hIco, Nat.cast_sum]
      refine Finset.sum_le_sum fun r _ => ?_
      have hch : 2 * (r + 2).choose 2 = (r + 2) * (r + 1) := by
        rw [Nat.choose_two_right]
        rcases (Nat.even_mul_succ_self (r + 1)).two_dvd with ⟨t, ht⟩
        have hsub : r + 2 - 1 = r + 1 := by omega
        rw [hsub, show (r + 2) * (r + 1) = 2 * t by linarith]
        omega
      have hq : (2 : ℚ) * ((r + 2).choose 2 : ℕ) = ((r : ℚ) + 2) * ((r : ℚ) + 1) := by
        exact_mod_cast hch
      have hr0 : (0 : ℚ) ≤ r := Nat.cast_nonneg r
      nlinarith only [hq, hr0]
    have h6 := six_mul_sum_Ico_choose_two (by omega : ρ ≤ γ + 1)
    have hsub_le : ρ * (ρ + 1) * (ρ + 2) ≤ (γ + 1) * ((γ + 1) + 1) * ((γ + 1) + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    have h6q : (6 : ℚ) * ((∑ r ∈ Finset.Ico ρ (γ + 1), (r + 2).choose 2 : ℕ) : ℚ) =
        ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) - (ρ : ℚ) * ((ρ : ℚ) + 1) * ((ρ : ℚ) + 2) := by
      have hcast : ((6 * ∑ r ∈ Finset.Ico ρ (γ + 1), (r + 2).choose 2 : ℕ) : ℚ) =
          (((γ + 1) * ((γ + 1) + 1) * ((γ + 1) + 2) - ρ * (ρ + 1) * (ρ + 2) : ℕ) : ℚ) := by
        exact_mod_cast h6
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hsub_le] at hcast
      rw [hcast]
      push_cast
      ring
    have hρ_nonneg : (0 : ℚ) ≤ ρ := Nat.cast_nonneg ρ
    nlinarith only [hle_choose, h6q, hρ_nonneg]
  have hdiv_ge := sum_Icc_div_succ_ge (by omega : 1 ≤ β) hβ_le_γ
  have hM_half : (0 : ℚ) ≤ M / 2 := by linarith only [hM_nonneg]
  have hsub_ge : (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) ≤
      (M / 2) * (∑ r ∈ Finset.Icc β γ, (r : ℚ) / ((r : ℚ) + 1)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hdiv_ge hM_half
  rw [hsplit1, Finset.sum_union hdisj1, hzero_hi, add_zero, hrew_sub]
  linarith only [hsq_sum, hsub_ge]

/-- Double-sum swap for Piece B (reused by both `pieceB_base` and `pieceB_mass_defect`). -/
private theorem pieceB_swap {k γ ρ β : ℕ} (s : ℕ → ℕ) (hρ_le_β : ρ ≤ β) :
    (∑ r ∈ Finset.Icc ρ k,
        2 * dualAlpha k γ β r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ))) =
    2 * ∑ i ∈ Finset.Icc 1 k,
        (s i : ℚ) * ((i : ℚ) * ∑ r ∈ Finset.Icc (max β i) k, dualAlpha k γ β r) := by
  have hinner : ∀ r ∈ Finset.Icc ρ k,
      2 * dualAlpha k γ β r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) =
      ∑ i ∈ Finset.Icc 1 k, if i ≤ r then 2 * (s i : ℚ) * ((i : ℚ) * dualAlpha k γ β r) else 0 := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    rw [← Finset.sum_filter, Finset.mul_sum]
    have hfilt : (Finset.Icc 1 k).filter (fun i => i ≤ r) = Finset.Icc 1 r := by
      ext i; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hfilt]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  rw [← Finset.sum_filter]
  have hfilt : (Finset.Icc ρ k).filter (fun r => i ≤ r) = Finset.Icc (max ρ i) k := by
    ext r; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hfilt]
  have hdrop : (∑ r ∈ Finset.Icc (max ρ i) k, 2 * (s i : ℚ) * ((i : ℚ) * dualAlpha k γ β r)) =
      ∑ r ∈ Finset.Icc (max β i) k, 2 * (s i : ℚ) * ((i : ℚ) * dualAlpha k γ β r) := by
    have hsub : Finset.Icc (max β i) k ⊆ Finset.Icc (max ρ i) k := by
      intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
    symm
    refine Finset.sum_subset hsub fun r hr hnot => ?_
    simp only [Finset.mem_Icc] at hr hnot
    have hltβ : r < β := by omega
    simp [dualAlpha, hltβ]
  rw [hdrop, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Standard Piece B bound: `≤ 2 * ρ * (γ + 1) * (k - γ)`. -/
private theorem pieceB_base {n k γ ρ β : ℕ} {s : ℕ → ℕ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ_le_γ : ρ ≤ γ) (hβ : β = max ρ (n / 10))
    (hsum_s_le : (∑ i ∈ Finset.Icc 1 k, s i) ≤ ρ) :
    (∑ r ∈ Finset.Icc ρ k,
        2 * dualAlpha k γ β r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ))) ≤
      2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
  have hγ_lt_k : γ < k := by omega
  have h2γ_ge_k : k ≤ 2 * γ := by omega
  have hβ_le_γ : β ≤ γ := by omega
  have hρ_le_β : ρ ≤ β := by omega
  rw [pieceB_swap s hρ_le_β]
  have hle_sum :
      (∑ i ∈ Finset.Icc 1 k,
          (s i : ℚ) * ((i : ℚ) * ∑ r ∈ Finset.Icc (max β i) k, dualAlpha k γ β r)) ≤
      ∑ i ∈ Finset.Icc 1 k, (s i : ℚ) * (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    exact mul_le_mul_of_nonneg_left
      (dual_weight_le (by omega) hβ_le_γ hγ_lt_k h2γ_ge_k hi.1 hi.2)
      (Nat.cast_nonneg _)
  rw [← Finset.sum_mul] at hle_sum
  have hsum_s_q : (∑ i ∈ Finset.Icc 1 k, (s i : ℚ)) ≤ (ρ : ℚ) := by exact_mod_cast hsum_s_le
  have hfactor_nonneg : (0 : ℚ) ≤ ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
    have hγ0 : (0 : ℚ) ≤ γ := Nat.cast_nonneg γ
    have hγk : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
    nlinarith only [hγ0, hγk]
  have hmul := mul_le_mul_of_nonneg_right hsum_s_q hfactor_nonneg
  linarith only [hle_sum, hmul]

/-- Mass-defect Piece B bound (Case 3b, `D ≤ ρ`): splits `s = s_lo + s_hi` where
`∑ s_hi ≤ ρ - D` and `∑ i * s_lo ≤ n`, saving `2 * D * (γ + 1) * (k - γ)` up to `O(n²)`! -/
private theorem pieceB_mass_defect {n k γ ρ β D : ℕ} {s s_lo s_hi : ℕ → ℕ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ_le_γ : ρ ≤ γ) (hβ : β = max ρ (n / 10)) (hD_le_ρ : D ≤ ρ)
    (hs_eq : ∀ i, s i = s_lo i + s_hi i)
    (hsum_hi : (∑ i ∈ Finset.Icc 1 k, s_hi i) ≤ ρ - D)
    (hsum_lo : (∑ i ∈ Finset.Icc 1 k, i * s_lo i) ≤ n) :
    (∑ r ∈ Finset.Icc ρ k,
        2 * dualAlpha k γ β r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ))) ≤
      2 * ((ρ : ℚ) - (D : ℚ)) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) +
      2 * ((n : ℚ) / (β : ℚ)) * (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) := by
  have hγ_lt_k : γ < k := by omega
  have h2γ_ge_k : k ≤ 2 * γ := by omega
  have hβ_le_γ : β ≤ γ := by omega
  have hρ_le_β : ρ ≤ β := by omega
  have hβ_pos : (0 : ℚ) < (β : ℚ) := by
    have : 0 < β := by omega
    positivity
  have hfac_nonneg : (0 : ℚ) ≤ ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
    have hγ0 : (0 : ℚ) ≤ γ := Nat.cast_nonneg γ
    have hγk : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
    nlinarith only [hγ0, hγk]
  rw [pieceB_swap s hρ_le_β]
  let F : ℚ := ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))
  have hpt_le : ∀ i ∈ Finset.Icc 1 k,
      (s i : ℚ) * ((i : ℚ) * ∑ r ∈ Finset.Icc (max β i) k, dualAlpha k γ β r) ≤
        ((i : ℚ) * (s_lo i : ℚ)) / (β : ℚ) * F + (s_hi i : ℚ) * F := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hs_q : (s i : ℚ) = (s_lo i : ℚ) + (s_hi i : ℚ) := by exact_mod_cast hs_eq i
    rw [hs_q, add_mul]
    have hlo_w := dual_weight_le_div_beta (by omega) hβ_le_γ hγ_lt_k h2γ_ge_k hi.1 hi.2
    have hhi_w := dual_weight_le (by omega) hβ_le_γ hγ_lt_k h2γ_ge_k hi.1 hi.2
    have h1 := mul_le_mul_of_nonneg_left hlo_w (Nat.cast_nonneg (s_lo i))
    have h2 := mul_le_mul_of_nonneg_left hhi_w (Nat.cast_nonneg (s_hi i))
    have heq : (s_lo i : ℚ) * ((i : ℚ) / (β : ℚ) * F) = ((i : ℚ) * (s_lo i : ℚ)) / (β : ℚ) * F := by
      ring
    linarith only [h1, h2, heq]
  have hsum_le := Finset.sum_le_sum hpt_le
  have hsum_div : (∑ i ∈ Finset.Icc 1 k, (i : ℚ) * (s_lo i : ℚ) / (β : ℚ)) =
      (∑ i ∈ Finset.Icc 1 k, (i : ℚ) * (s_lo i : ℚ)) / (β : ℚ) := by
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hsum_div] at hsum_le
  have hhi_q : (∑ i ∈ Finset.Icc 1 k, (s_hi i : ℚ)) ≤ (ρ : ℚ) - (D : ℚ) := by
    have hq : ((∑ i ∈ Finset.Icc 1 k, s_hi i : ℕ) : ℚ) ≤ ((ρ - D : ℕ) : ℚ) := by
      exact_mod_cast hsum_hi
    rw [Nat.cast_sum, Nat.cast_sub hD_le_ρ] at hq
    exact hq
  have hlo_q : (∑ i ∈ Finset.Icc 1 k, (i : ℚ) * (s_lo i : ℚ)) ≤ (n : ℚ) := by
    have hq : ((∑ i ∈ Finset.Icc 1 k, i * s_lo i : ℕ) : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast hsum_lo
    push_cast at hq
    exact hq
  have hlo_div : (∑ i ∈ Finset.Icc 1 k, (i : ℚ) * (s_lo i : ℚ)) / (β : ℚ) ≤ (n : ℚ) / (β : ℚ) :=
    div_le_div_of_nonneg_right hlo_q hβ_pos.le
  have hm1 := mul_le_mul_of_nonneg_right hlo_div hfac_nonneg
  have hm2 := mul_le_mul_of_nonneg_right hhi_q hfac_nonneg
  dsimp only [F] at hsum_le hm1 hm2
  linarith only [hsum_le, hm1, hm2]

/-- Piece C base bound: `∑_{r ∈ Icc ρ k} (2 * r + 1) ≤ (k + 1)^2`. -/
private theorem pieceC_base (ρ k : ℕ) :
    (∑ r ∈ Finset.Icc ρ k, (2 * (r : ℚ) + 1)) ≤ ((k : ℚ) + 1) ^ 2 := by
  have hnat : (∑ r ∈ Finset.Icc ρ k, (2 * r + 1)) ≤ (k + 1) ^ 2 := by
    have hsub : Finset.Icc ρ k ⊆ Finset.range (k + 1) := by
      intro r hr; rw [Finset.mem_Icc] at hr; rw [Finset.mem_range]; omega
    have hsum_odd : ∀ m : ℕ, (∑ r ∈ Finset.range m, (2 * r + 1)) = m ^ 2 := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm => rw [Finset.sum_range_succ, ihm]; ring
    calc (∑ r ∈ Finset.Icc ρ k, (2 * r + 1))
        ≤ ∑ r ∈ Finset.range (k + 1), (2 * r + 1) := Finset.sum_le_sum_of_subset hsub
      _ = (k + 1) ^ 2 := hsum_odd (k + 1)
  have hq : ((∑ r ∈ Finset.Icc ρ k, (2 * r + 1) : ℕ) : ℚ) ≤ (((k + 1) ^ 2 : ℕ) : ℚ) := by
    exact_mod_cast hnat
  push_cast at hq
  exact hq

/-- Concave-cubic rational certificate for plateau saving on `[a, b]`:
proves `u^2/2 - c ≥ u(1-u)/(18(1-2u)) + u^2/(500(1-2u))` with zero calculus via the exact
polynomial identity `P(u) = ((b-u)/(b-a)) P(a) + ((u-a)/(b-a)) P(b) + (u-a)(b-u)(u+a+b-2491/4500)`. -/
private theorem concave_cubic_bin_cert {a b c u : ℚ}
    (hab : a < b) (hua : a ≤ u) (hub : u ≤ b) (hu_half : 2 * u < 1)
    (hPa : 0 ≤ (1 - 2 * a) * (a ^ 2 / 2 - c) - a * (1 - a) / 18 - a ^ 2 / 500)
    (hPb : 0 ≤ (1 - 2 * b) * (b ^ 2 / 2 - c) - b * (1 - b) / 18 - b ^ 2 / 500)
    (hA : 0 ≤ a + a + b - 2491 / 4500) :
    u * (1 - u) / (1 - 2 * u) * (1 / 18) + u ^ 2 / (1 - 2 * u) * (1 / 500) ≤
      u ^ 2 / 2 - c := by
  have hden_pos : (0 : ℚ) < 1 - 2 * u := by linarith
  have hba_pos : (0 : ℚ) < b - a := by linarith
  have hP_id :
      (1 - 2 * u) * (u ^ 2 / 2 - c) - u * (1 - u) / 18 - u ^ 2 / 500 =
      ((b - u) / (b - a)) * ((1 - 2 * a) * (a ^ 2 / 2 - c) - a * (1 - a) / 18 - a ^ 2 / 500) +
      ((u - a) / (b - a)) * ((1 - 2 * b) * (b ^ 2 / 2 - c) - b * (1 - b) / 18 - b ^ 2 / 500) +
      (u - a) * (b - u) * (u + a + b - 2491 / 4500) := by
    have hba_ne : b - a ≠ 0 := hba_pos.ne'
    field_simp
    ring
  have h1 : 0 ≤ (b - u) / (b - a) *
      ((1 - 2 * a) * (a ^ 2 / 2 - c) - a * (1 - a) / 18 - a ^ 2 / 500) :=
    mul_nonneg (div_nonneg (by linarith) hba_pos.le) hPa
  have h2 : 0 ≤ (u - a) / (b - a) *
      ((1 - 2 * b) * (b ^ 2 / 2 - c) - b * (1 - b) / 18 - b ^ 2 / 500) :=
    mul_nonneg (div_nonneg (by linarith) hba_pos.le) hPb
  have h3 : 0 ≤ (u - a) * (b - u) * (u + a + b - 2491 / 4500) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hPu : 0 ≤ (1 - 2 * u) * (u ^ 2 / 2 - c) - u * (1 - u) / 18 - u ^ 2 / 500 := by
    linarith only [hP_id, h1, h2, h3]
  have hmul : (1 - 2 * u) *
      (u * (1 - u) / (1 - 2 * u) * (1 / 18) + u ^ 2 / (1 - 2 * u) * (1 / 500)) ≤
      (1 - 2 * u) * (u ^ 2 / 2 - c) := by
    have hrew : (1 - 2 * u) *
        (u * (1 - u) / (1 - 2 * u) * (1 / 18) + u ^ 2 / (1 - 2 * u) * (1 / 500)) =
        u * (1 - u) / 18 + u ^ 2 / 500 := by
      have hne : 1 - 2 * u ≠ 0 := hden_pos.ne'
      field_simp
    linarith only [hPu, hrew]
  exact le_of_mul_le_mul_left hmul hden_pos

/-- Scaling helper converting a unit-interval plateau saving into `(r, n)` form. -/
private theorem plateau_saving_of_unit {n r D : ℕ} {c : ℚ}
    (hn : 0 < n) (h2r : 2 * r < n) (hD : 18 * D < n)
    (hunit : let u := (r : ℚ) / (n : ℚ)
      u * (1 - u) / (1 - 2 * u) * (1 / 18) + u ^ 2 / (1 - 2 * u) * (1 / 500) ≤ u ^ 2 / 2 - c) :
    (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * (D : ℚ) +
      (r : ℚ) ^ 2 / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / 500) ≤
    (r : ℚ) ^ 2 / 2 - c * (n : ℚ) ^ 2 := by
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hn_ne : (n : ℚ) ≠ 0 := hn_pos.ne'
  have hden_pos : (0 : ℚ) < (n : ℚ) - 2 * (r : ℚ) := by
    have : (2 : ℚ) * r < n := by exact_mod_cast h2r
    linarith
  have hD_le : (D : ℚ) ≤ (n : ℚ) / 18 := by
    have : (18 : ℚ) * D < n := by exact_mod_cast hD
    linarith
  have hcoef_nonneg : (0 : ℚ) ≤ (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) := by
    have hnr : (0 : ℚ) ≤ (n : ℚ) - (r : ℚ) := by
      have : (r : ℚ) ≤ n := by exact_mod_cast (by omega : r ≤ n)
      linarith
    positivity
  have hstep1 :
      (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * (D : ℚ) ≤
      (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / 18) :=
    mul_le_mul_of_nonneg_left hD_le hcoef_nonneg
  have hmul := mul_le_mul_of_nonneg_right hunit (sq_nonneg (n : ℚ))
  have hden_ne : (n : ℚ) - 2 * (r : ℚ) ≠ 0 := hden_pos.ne'
  have h12_ne : (1 : ℚ) - 2 * ((r : ℚ) / (n : ℚ)) ≠ 0 := by
    have : (1 : ℚ) - 2 * ((r : ℚ) / (n : ℚ)) = ((n : ℚ) - 2 * (r : ℚ)) / (n : ℚ) := by
      field_simp
    rw [this]
    exact div_ne_zero hden_ne hn_ne
  have hlhs_eq :
      (((r : ℚ) / (n : ℚ)) * (1 - (r : ℚ) / (n : ℚ)) / (1 - 2 * ((r : ℚ) / (n : ℚ))) * (1 / 18) +
       ((r : ℚ) / (n : ℚ)) ^ 2 / (1 - 2 * ((r : ℚ) / (n : ℚ))) * (1 / 500)) * (n : ℚ) ^ 2 =
      (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / 18) +
      (r : ℚ) ^ 2 / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / 500) := by
    field_simp
  have hrhs_eq : (((r : ℚ) / (n : ℚ)) ^ 2 / 2 - c) * (n : ℚ) ^ 2 =
      (r : ℚ) ^ 2 / 2 - c * (n : ℚ) ^ 2 := by
    field_simp
  linarith only [hstep1, hmul, hlhs_eq, hrhs_eq]

/-- Bin 1 (`u = r/n ∈ [1/3, 38/100]`) exact weight and plateau saving bounds. -/
private theorem bin1_bounds {n k γ ρ β r D : ℕ}
    (hn : 23700 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ : ρ ≤ n / 3) (hβ : β = max ρ (n / 10)) (hD : 18 * D < n)
    (hr : r ∈ Finset.Icc ((n + 2) / 3) ((38 * n) / 100)) :
    (932 / 1000 : ℚ) ≤ 1 - dualAlpha k γ β r ∧
    (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * (D : ℚ) +
      (r : ℚ) ^ 2 / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / 500) ≤
    (r : ℚ) ^ 2 / 2 - (164 / 10000 : ℚ) * (n : ℚ) ^ 2 := by
  rw [Finset.mem_Icc] at hr
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hr_ge : (n : ℚ) / 3 ≤ (r : ℚ) := by
    have : n ≤ 3 * r := by omega
    have hq : (n : ℚ) ≤ 3 * r := by exact_mod_cast this
    linarith
  have hr_le : (r : ℚ) ≤ (38 / 100 : ℚ) * (n : ℚ) := by
    have : 100 * r ≤ 38 * n := by omega
    have hq : (100 : ℚ) * r ≤ 38 * n := by exact_mod_cast this
    linarith
  constructor
  · have h1 : ¬ r < β := by omega
    have h2 : r ≤ γ := by omega
    simp only [dualAlpha, h1, h2, ↓reduceIte]
    have hγ_le : (γ : ℚ) ≤ (125 / 258 : ℚ) * n := by
      have : 258 * γ ≤ 125 * n := by omega
      have hq : (258 : ℚ) * γ ≤ 125 * n := by exact_mod_cast this
      linarith
    have hkg_le : (k : ℚ) - γ ≤ (2 / 129 : ℚ) * n := by
      have h1' : 258 * k + 258 ≤ 129 * n := by omega
      have h2' : 125 * n ≤ 258 * γ + 257 := by omega
      have hq1 : (258 : ℚ) * k + 258 ≤ 129 * n := by exact_mod_cast h1'
      have hq2 : (125 : ℚ) * n ≤ 258 * γ + 257 := by exact_mod_cast h2'
      linarith
    have hM_le : (γ : ℚ) * ((k : ℚ) - γ) ≤ (125 / 16641 : ℚ) * (n : ℚ) ^ 2 := by
      have hkg0 : (0 : ℚ) ≤ (k : ℚ) - γ := by
        have : γ ≤ k := by omega
        have hq : (γ : ℚ) ≤ k := by exact_mod_cast this
        linarith
      have hprod := mul_le_mul hγ_le hkg_le hkg0 (by positivity)
      linarith
    have hr_pos : (0 : ℚ) < (r : ℚ) := by linarith
    have hrr1_ge : (n : ℚ) ^ 2 / 9 ≤ (r : ℚ) * ((r : ℚ) + 1) := by nlinarith
    have hrr1_pos : (0 : ℚ) < (r : ℚ) * ((r : ℚ) + 1) := by positivity
    have hdiv_le : (γ : ℚ) * ((k : ℚ) - γ) / ((r : ℚ) * ((r : ℚ) + 1)) ≤ 68 / 1000 := by
      rw [div_le_iff₀ hrr1_pos]
      nlinarith
    linarith
  · refine plateau_saving_of_unit (by omega) (by omega) hD ?_
    have hua : (1 / 3 : ℚ) ≤ (r : ℚ) / (n : ℚ) := by rw [div_le_div_iff₀] <;> linarith
    have hub : (r : ℚ) / (n : ℚ) ≤ 38 / 100 := by rw [div_le_iff₀ hn_pos]; linarith
    exact concave_cubic_bin_cert (by norm_num) hua hub (by linarith)
      (by norm_num) (by norm_num) (by norm_num)

/-- Bin 2 (`u = r/n ∈ [38/100, 41/100]`) exact weight and plateau saving bounds. -/
private theorem bin2_bounds {n k γ ρ β r D : ℕ}
    (hn : 23700 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ : ρ ≤ n / 3) (hβ : β = max ρ (n / 10)) (hD : 18 * D < n)
    (hr : r ∈ Finset.Icc ((38 * n) / 100 + 1) ((41 * n) / 100)) :
    (947 / 1000 : ℚ) ≤ 1 - dualAlpha k γ β r ∧
    (r : ℚ) * ((n : ℚ) - (r : ℚ)) / ((n : ℚ) - 2 * (r : ℚ)) * (D : ℚ) +
      (r : ℚ) ^ 2 / ((n : ℚ) - 2 * (r : ℚ)) * ((n : ℚ) / 500) ≤
    (r : ℚ) ^ 2 / 2 - (75 / 10000 : ℚ) * (n : ℚ) ^ 2 := by
  rw [Finset.mem_Icc] at hr
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hr_ge : (38 / 100 : ℚ) * (n : ℚ) ≤ (r : ℚ) := by
    have : 38 * n ≤ 100 * r := by omega
    have hq : (38 : ℚ) * n ≤ 100 * r := by exact_mod_cast this
    linarith
  have hr_le : (r : ℚ) ≤ (41 / 100 : ℚ) * (n : ℚ) := by
    have : 100 * r ≤ 41 * n := by omega
    have hq : (100 : ℚ) * r ≤ 41 * n := by exact_mod_cast this
    linarith
  constructor
  · have h1 : ¬ r < β := by omega
    have h2 : r ≤ γ := by omega
    simp only [dualAlpha, h1, h2, ↓reduceIte]
    have hγ_le : (γ : ℚ) ≤ (125 / 258 : ℚ) * n := by
      have : 258 * γ ≤ 125 * n := by omega
      have hq : (258 : ℚ) * γ ≤ 125 * n := by exact_mod_cast this
      linarith
    have hkg_le : (k : ℚ) - γ ≤ (2 / 129 : ℚ) * n := by
      have h1' : 258 * k + 258 ≤ 129 * n := by omega
      have h2' : 125 * n ≤ 258 * γ + 257 := by omega
      have hq1 : (258 : ℚ) * k + 258 ≤ 129 * n := by exact_mod_cast h1'
      have hq2 : (125 : ℚ) * n ≤ 258 * γ + 257 := by exact_mod_cast h2'
      linarith
    have hM_le : (γ : ℚ) * ((k : ℚ) - γ) ≤ (125 / 16641 : ℚ) * (n : ℚ) ^ 2 := by
      have hkg0 : (0 : ℚ) ≤ (k : ℚ) - γ := by
        have : γ ≤ k := by omega
        have hq : (γ : ℚ) ≤ k := by exact_mod_cast this
        linarith
      have hprod := mul_le_mul hγ_le hkg_le hkg0 (by positivity)
      linarith
    have hr_pos : (0 : ℚ) < (r : ℚ) := by linarith
    have hrr1_ge : (361 / 2500 : ℚ) * (n : ℚ) ^ 2 ≤ (r : ℚ) * ((r : ℚ) + 1) := by nlinarith
    have hrr1_pos : (0 : ℚ) < (r : ℚ) * ((r : ℚ) + 1) := by positivity
    have hdiv_le : (γ : ℚ) * ((k : ℚ) - γ) / ((r : ℚ) * ((r : ℚ) + 1)) ≤ 53 / 1000 := by
      rw [div_le_iff₀ hrr1_pos]
      nlinarith
    linarith
  · refine plateau_saving_of_unit (by omega) (by omega) hD ?_
    have hua : (38 / 100 : ℚ) ≤ (r : ℚ) / (n : ℚ) := by rw [le_div_iff₀ hn_pos]; linarith
    have hub : (r : ℚ) / (n : ℚ) ≤ 41 / 100 := by rw [div_le_iff₀ hn_pos]; linarith
    exact concave_cubic_bin_cert (by norm_num) hua hub (by linarith)
      (by norm_num) (by norm_num) (by norm_num)

/-- Exact rational square identity (general Shitov `8257/49923`, plus outer `ρ ≥ n/3` slack
yielding `24646/149769`). -/
private theorem cubic_poly_bound_general {n ρ β : ℚ} (hn : 0 ≤ n) (hρ : 0 ≤ ρ)
    (hcases : β = ρ ∨ (ρ ≤ n / 10 ∧ β ≤ n / 10)) :
    (7 / 48 : ℚ) * n ^ 3 + ((125 / 258 : ℚ) ^ 3 * n ^ 3 - ρ ^ 3) / 6 -
      (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - β) +
      (250 / 16641 : ℚ) * ρ * n ^ 2 ≤ (8257 / 49923 : ℚ) * n ^ 3 := by
  have hsq_bound : ∀ x : ℚ, 0 ≤ x →
      (7 / 48 : ℚ) * n ^ 3 + ((125 / 258 : ℚ) ^ 3 * n ^ 3 - x ^ 3) / 6 -
        (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - x) +
        (250 / 16641 : ℚ) * x * n ^ 2 ≤ (8257 / 49923 : ℚ) * n ^ 3 := by
    intro x hx
    have hid :
        (8257 / 49923 : ℚ) * n ^ 3 -
          ((7 / 48 : ℚ) * n ^ 3 + ((125 / 258 : ℚ) ^ 3 * n ^ 3 - x ^ 3) / 6 -
            (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - x) +
            (250 / 16641 : ℚ) * x * n ^ 2) =
        (1 / 6 : ℚ) * (x - (25 / 129 : ℚ) * n) ^ 2 * (x + (50 / 129 : ℚ) * n) := by ring
    have hnonneg : (0 : ℚ) ≤
        (1 / 6 : ℚ) * (x - (25 / 129 : ℚ) * n) ^ 2 * (x + (50 / 129 : ℚ) * n) := by positivity
    linarith
  rcases hcases with hβρ | ⟨hρ_le, hβ_le⟩
  · rw [hβρ]; exact hsq_bound ρ hρ
  · let c : ℚ := n / 10
    have hc_eq : c = n / 10 := rfl
    have hc_nonneg : 0 ≤ c := by positivity
    have hmono_β :
        (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - c) ≤
        (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - β) := by
      have hcoef : (0 : ℚ) ≤ (125 / 33282 : ℚ) * n ^ 2 := by positivity
      have hbc : β ≤ c := hβ_le
      nlinarith
    have hmono_ρ :
        (250 / 16641 : ℚ) * ρ * n ^ 2 - ρ ^ 3 / 6 ≤
        (250 / 16641 : ℚ) * c * n ^ 2 - c ^ 3 / 6 := by
      have hfac :
          ((250 / 16641 : ℚ) * c * n ^ 2 - c ^ 3 / 6) -
            ((250 / 16641 : ℚ) * ρ * n ^ 2 - ρ ^ 3 / 6) =
          (c - ρ) * ((250 / 16641 : ℚ) * n ^ 2 - (c ^ 2 + c * ρ + ρ ^ 2) / 6) := by ring
      have hpos2 : (0 : ℚ) ≤ (250 / 16641 : ℚ) * n ^ 2 - (c ^ 2 + c * ρ + ρ ^ 2) / 6 := by
        rw [hc_eq]; nlinarith
      have hprod : (0 : ℚ) ≤ (c - ρ) * ((250 / 16641 : ℚ) * n ^ 2 - (c ^ 2 + c * ρ + ρ ^ 2) / 6) :=
        mul_nonneg (by linarith) hpos2
      linarith
    have hbase := hsq_bound c hc_nonneg
    linarith

/-- Outer-regime (`ρ ≥ n / 3`, `β = ρ`) exact cubic slack strictly beats `24646/149769`. -/
private theorem cubic_poly_bound_outer {n ρ : ℚ} (hn : 0 ≤ n) (hρ : n / 3 ≤ ρ) :
    (7 / 48 : ℚ) * n ^ 3 + ((125 / 258 : ℚ) ^ 3 * n ^ 3 - ρ ^ 3) / 6 -
      (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - ρ) +
      (250 / 16641 : ℚ) * ρ * n ^ 2 ≤ (24646 / 149769 : ℚ) * n ^ 3 := by
  have hid :
      (8257 / 49923 : ℚ) * n ^ 3 -
        ((7 / 48 : ℚ) * n ^ 3 + ((125 / 258 : ℚ) ^ 3 * n ^ 3 - ρ ^ 3) / 6 -
          (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - ρ) +
          (250 / 16641 : ℚ) * ρ * n ^ 2) =
      (1 / 6 : ℚ) * (ρ - (25 / 129 : ℚ) * n) ^ 2 * (ρ + (50 / 129 : ℚ) * n) := by ring
  have h1 : (6 / 43 : ℚ) * n ≤ ρ - (25 / 129 : ℚ) * n := by linarith
  have h2 : (31 / 43 : ℚ) * n ≤ ρ + (50 / 129 : ℚ) * n := by linarith
  have hsq : ((6 / 43 : ℚ) * n) ^ 2 ≤ (ρ - (25 / 129 : ℚ) * n) ^ 2 := by nlinarith
  have hslack : (186 / 79507 : ℚ) * n ^ 3 ≤
      (1 / 6 : ℚ) * (ρ - (25 / 129 : ℚ) * n) ^ 2 * (ρ + (50 / 129 : ℚ) * n) := by
    have hprod := mul_le_mul hsq h2 (by positivity) (by positivity)
    nlinarith
  have hn3 : (0 : ℚ) ≤ n ^ 3 := by positivity
  linarith only [hid, hslack, hn3]

/-- Rounding-error assembly lemma over `ℚ` (parameterized by the cubic ceiling `C₃`). -/
private theorem rounding_assembly_core {n k γ ρ β : ℕ} {C₃ : ℚ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ_le_γ : ρ ≤ γ) (hβ : β = max ρ (n / 10))
    (hcubic :
      (7 / 48 : ℚ) * (n : ℚ) ^ 3 + ((125 / 258 : ℚ) ^ 3 * (n : ℚ) ^ 3 - (ρ : ℚ) ^ 3) / 6 -
        (125 / 33282 : ℚ) * (n : ℚ) ^ 2 * ((125 / 258 : ℚ) * (n : ℚ) - (β : ℚ)) +
        (250 / 16641 : ℚ) * (ρ : ℚ) * (n : ℚ) ^ 2 ≤ C₃ * (n : ℚ) ^ 3) :
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
      (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) +
      2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) +
      (7 / 48 : ℚ) * (n : ℚ) ^ 3 + (n : ℚ) ^ 2 + ((k : ℚ) + 1) ^ 2 ≤
    C₃ * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 2 := by
  intro M
  have hn_q : (100 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn100
  have hγ_le : (γ : ℚ) ≤ (125 / 258 : ℚ) * n := by
    have : 258 * γ ≤ 125 * n := by omega
    have hq : (258 : ℚ) * γ ≤ 125 * n := by exact_mod_cast this
    linarith
  have hγ_ge : (125 / 258 : ℚ) * n - 1 ≤ (γ : ℚ) := by
    have : 125 * n ≤ 258 * γ + 257 := by omega
    have hq : (125 : ℚ) * n ≤ 258 * γ + 257 := by exact_mod_cast this
    linarith
  have hk_le : (k : ℚ) ≤ (n : ℚ) / 2 - 1 := by
    have : 2 * k + 2 ≤ n := by omega
    have hq : (2 : ℚ) * k + 2 ≤ n := by exact_mod_cast this
    linarith
  have hk_ge : (n : ℚ) / 2 - 3 / 2 ≤ (k : ℚ) := by
    have : n ≤ 2 * k + 3 := by omega
    have hq : (n : ℚ) ≤ 2 * k + 3 := by exact_mod_cast this
    linarith
  have hkg_le : (k : ℚ) - γ ≤ (2 / 129 : ℚ) * n := by
    have h1 : 258 * k + 258 ≤ 129 * n := by omega
    have h2 : 125 * n ≤ 258 * γ + 257 := by omega
    have hq1 : (258 : ℚ) * k + 258 ≤ 129 * n := by exact_mod_cast h1
    have hq2 : (125 : ℚ) * n ≤ 258 * γ + 257 := by exact_mod_cast h2
    linarith
  have hkg_ge : (2 / 129 : ℚ) * n - 3 / 2 ≤ (k : ℚ) - γ := by linarith
  have hM_le : M ≤ (125 / 16641 : ℚ) * (n : ℚ) ^ 2 := by
    dsimp only [M]
    have h2 : (0 : ℚ) ≤ (k : ℚ) - γ := by linarith
    have hprod := mul_le_mul hγ_le hkg_le h2 (by positivity)
    linarith
  have hM_ge : (125 / 16641 : ℚ) * (n : ℚ) ^ 2 - (n : ℚ) ≤ M := by
    dsimp only [M]
    have h2 : (0 : ℚ) ≤ (2 / 129 : ℚ) * n - 3 / 2 := by linarith
    have hprod := mul_le_mul hγ_ge hkg_ge h2 (by linarith)
    nlinarith only [hprod, hn_q]
  have hγ_cub : ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 ≤
      (125 / 258 : ℚ) ^ 3 * (n : ℚ) ^ 3 / 6 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 := by
    have h1 : ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) ≤
        ((125 / 258 : ℚ) * n + 1) * ((125 / 258 : ℚ) * n + 2) * ((125 / 258 : ℚ) * n + 3) := by
      exact mul_le_mul (mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity))
        (by linarith) (by positivity) (by positivity)
    nlinarith only [h1, hn_q]
  have hβ_le_γ : (β : ℚ) ≤ γ := by exact_mod_cast (by omega : β ≤ γ)
  have hβ_pos : (0 : ℚ) < β := by exact_mod_cast (show 0 < β by omega)
  have hratio_le6 : ((γ : ℚ) - β) / (β : ℚ) ≤ 6 := by
    rw [div_le_iff₀ hβ_pos]
    have hq : (γ : ℚ) ≤ 7 * β := by exact_mod_cast (by omega : γ ≤ 7 * β)
    linarith
  have hM_nonneg : (0 : ℚ) ≤ M := by
    dsimp only [M]
    exact mul_nonneg (Nat.cast_nonneg γ) (by linarith)
  have hM_div : (M / 2) * ((γ : ℚ) - β) * (1 / (β : ℚ)) ≤ (1 / 40 : ℚ) * (n : ℚ) ^ 2 := by
    have heq : (M / 2) * ((γ : ℚ) - β) * (1 / (β : ℚ)) = (M / 2) * (((γ : ℚ) - β) / (β : ℚ)) := by
      ring
    rw [heq]
    have h1 := mul_le_mul_of_nonneg_left hratio_le6 (show (0 : ℚ) ≤ M / 2 by linarith)
    have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
    linarith only [h1, hM_le, hn2]
  have hM_main :
      (125 / 33282 : ℚ) * (n : ℚ) ^ 2 * ((125 / 258 : ℚ) * n - β) -
        (1 / 2 : ℚ) * (n : ℚ) ^ 2 ≤ (M / 2) * ((γ : ℚ) - β) := by
    have hdiff_nonneg : (0 : ℚ) ≤ (γ : ℚ) - β := by linarith only [hβ_le_γ]
    have hdiff_le : (γ : ℚ) - β ≤ (n : ℚ) / 2 := by
      have hβ0 : (0 : ℚ) ≤ β := Nat.cast_nonneg β
      linarith only [hγ_le, hβ0, hn_q]
    have h1 : ((125 / 16641 : ℚ) * (n : ℚ) ^ 2 - (n : ℚ)) / 2 * ((γ : ℚ) - β) ≤
        (M / 2) * ((γ : ℚ) - β) :=
      mul_le_mul_of_nonneg_right (by linarith only [hM_ge]) hdiff_nonneg
    have h2 : (n : ℚ) / 2 * ((γ : ℚ) - β) ≤ (1 / 4 : ℚ) * (n : ℚ) ^ 2 := by
      nlinarith only [hdiff_le, hn_q]
    have h3 : (125 / 33282 : ℚ) * (n : ℚ) ^ 2 * ((125 / 258 : ℚ) * n - 1 - β) ≤
        (125 / 33282 : ℚ) * (n : ℚ) ^ 2 * ((γ : ℚ) - β) := by
      have hc : (0 : ℚ) ≤ (125 / 33282 : ℚ) * (n : ℚ) ^ 2 := by positivity
      nlinarith only [hc, hγ_ge]
    nlinarith only [h1, h2, h3, hn_q]
  have hρ_le_half : (ρ : ℚ) ≤ (n : ℚ) / 2 := by
    have hρ_q : (ρ : ℚ) ≤ γ := by exact_mod_cast hρ_le_γ
    linarith only [hρ_q, hγ_le, hn_q]
  have hρ_term : 2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - γ) ≤
      (250 / 16641 : ℚ) * (ρ : ℚ) * (n : ℚ) ^ 2 + (1 / 50 : ℚ) * (n : ℚ) ^ 2 := by
    have heq : ((γ : ℚ) + 1) * ((k : ℚ) - γ) = M + ((k : ℚ) - γ) := by dsimp only [M]; ring
    rw [mul_assoc (2 * (ρ : ℚ)), heq]
    have h1 : 2 * (ρ : ℚ) * (M + ((k : ℚ) - γ)) ≤
        2 * (ρ : ℚ) * ((125 / 16641 : ℚ) * (n : ℚ) ^ 2 + (2 / 129 : ℚ) * n) :=
      mul_le_mul_of_nonneg_left (by linarith only [hM_le, hkg_le]) (by positivity)
    nlinarith only [h1, hρ_le_half, hn_q]
  have hk1_sq : ((k : ℚ) + 1) ^ 2 ≤ (1 / 4 : ℚ) * (n : ℚ) ^ 2 := by
    have hk0 : (0 : ℚ) ≤ (k : ℚ) + 1 := by positivity
    nlinarith only [hk0, hk_le]
  have hexpand :
      (M / 2) * ((γ : ℚ) - β) * (1 - 1 / (β : ℚ)) =
      (M / 2) * ((γ : ℚ) - β) - (M / 2) * ((γ : ℚ) - β) * (1 / (β : ℚ)) := by ring
  have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
  linarith only [hγ_cub, hM_div, hM_main, hρ_term, hk1_sq, hcubic, hexpand, hn2]

private theorem rounding_assembly_general {n k γ ρ β : ℕ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ_le_γ : ρ ≤ γ) (hβ : β = max ρ (n / 10)) :
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
      (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) +
      2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) +
      (7 / 48 : ℚ) * (n : ℚ) ^ 3 + (n : ℚ) ^ 2 + ((k : ℚ) + 1) ^ 2 ≤
    (8257 / 49923 : ℚ) * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 2 := by
  have hpoly_cases : (β : ℚ) = ρ ∨ ((ρ : ℚ) ≤ n / 10 ∧ (β : ℚ) ≤ n / 10) := by
    by_cases hcmp : n / 10 ≤ ρ
    · left; exact_mod_cast (by rw [hβ, max_eq_left hcmp] : β = ρ)
    · right
      have hβ_eq : β = n / 10 := by rw [hβ, max_eq_right (by omega : ρ ≤ n / 10)]
      have h1 : (10 : ℚ) * ρ ≤ n := by exact_mod_cast (by omega : 10 * ρ ≤ n)
      have h2 : (10 : ℚ) * β ≤ n := by exact_mod_cast (by rw [hβ_eq]; omega : 10 * β ≤ n)
      exact ⟨by linarith only [h1], by linarith only [h2]⟩
  exact rounding_assembly_core hn100 hk hγ hρ_le_γ hβ
    (cubic_poly_bound_general (Nat.cast_nonneg n) (Nat.cast_nonneg ρ) hpoly_cases)

private theorem rounding_assembly_outer {n k γ ρ β : ℕ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ_gt : n / 3 < ρ) (hρ_le_γ : ρ ≤ γ) (hβ : β = max ρ (n / 10)) :
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
      (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) +
      2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) +
      (7 / 48 : ℚ) * (n : ℚ) ^ 3 + (n : ℚ) ^ 2 + ((k : ℚ) + 1) ^ 2 ≤
    (24646 / 149769 : ℚ) * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 2 := by
  have hβ_eq : (β : ℚ) = ρ := by
    have : β = ρ := by rw [hβ, max_eq_left (by omega)]
    exact_mod_cast this
  have hρ_ge : (n : ℚ) / 3 ≤ ρ := by
    have : n ≤ 3 * ρ := by omega
    have hq : (n : ℚ) ≤ 3 * ρ := by exact_mod_cast this
    linarith
  refine rounding_assembly_core hn100 hk hγ hρ_le_γ hβ ?_
  rw [hβ_eq]
  exact cubic_poly_bound_outer (Nat.cast_nonneg n) hρ_ge

/-- Case 3b (`n ≤ 18 * D`, `D ≤ ρ`) final arithmetic saving assembly. -/
private theorem case3b_saving_bound {n k γ ρ β D : ℕ}
    (hn : 23700 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hβ : β = max ρ (n / 10)) (hD : n ≤ 18 * D) :
    2 * ((n : ℚ) / (β : ℚ)) * (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) -
      2 * (D : ℚ) * (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) ≤
    -(125 / 149769 : ℚ) * (n : ℚ) ^ 3 + (n : ℚ) ^ 2 := by
  have hn_q : (23700 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hβ_pos : (0 : ℚ) < (β : ℚ) := by
    have : 0 < β := by omega
    positivity
  have hγ1_ge : (125 / 258 : ℚ) * n ≤ (γ : ℚ) + 1 := by
    have : 125 * n ≤ 258 * (γ + 1) := by omega
    have hq : (125 : ℚ) * n ≤ 258 * ((γ : ℚ) + 1) := by exact_mod_cast this
    linarith
  have hγ1_le : (γ : ℚ) + 1 ≤ (125 / 258 : ℚ) * n + 1 := by
    have : 258 * γ ≤ 125 * n := by omega
    have hq : (258 : ℚ) * γ ≤ 125 * n := by exact_mod_cast this
    linarith
  have hkg_ge : (2 / 129 : ℚ) * n - 3 / 2 ≤ (k : ℚ) - γ := by
    have h1 : n ≤ 2 * k + 3 := by omega
    have h2 : 258 * γ ≤ 125 * n := by omega
    have hq1 : (n : ℚ) ≤ 2 * k + 3 := by exact_mod_cast h1
    have hq2 : (258 : ℚ) * γ ≤ 125 * n := by exact_mod_cast h2
    linarith
  have hkg_le : (k : ℚ) - γ ≤ (2 / 129 : ℚ) * n := by
    have h1 : 258 * k + 258 ≤ 129 * n := by omega
    have h2 : 125 * n ≤ 258 * γ + 257 := by omega
    have hq1 : (258 : ℚ) * k + 258 ≤ 129 * n := by exact_mod_cast h1
    have hq2 : (125 : ℚ) * n ≤ 258 * γ + 257 := by exact_mod_cast h2
    linarith
  have hfac_ge : (125 / 16641 : ℚ) * (n : ℚ) ^ 2 - (n : ℚ) ≤
      ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
    have hprod := mul_le_mul hγ1_ge hkg_ge (by linarith) (by positivity)
    nlinarith
  have hfac_le : ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) ≤ (1 / 100 : ℚ) * (n : ℚ) ^ 2 := by
    have hkg0 : (0 : ℚ) ≤ (k : ℚ) - γ := by linarith
    have hprod := mul_le_mul hγ1_le hkg_le hkg0 (by positivity)
    nlinarith
  have hD_ge : (n : ℚ) / 18 ≤ (D : ℚ) := by
    have hq : (n : ℚ) ≤ 18 * D := by exact_mod_cast hD
    linarith
  have hsave : (125 / 149769 : ℚ) * (n : ℚ) ^ 3 - (1 / 9 : ℚ) * (n : ℚ) ^ 2 ≤
      2 * (D : ℚ) * (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) := by
    have hprod := mul_le_mul (show 2 * ((n : ℚ) / 18) ≤ 2 * (D : ℚ) by linarith)
      hfac_ge (by nlinarith) (by positivity)
    linarith
  have hratio_le : (n : ℚ) / (β : ℚ) ≤ 11 := by
    rw [div_le_iff₀ hβ_pos]
    have : n ≤ 11 * β := by omega
    exact_mod_cast this
  have hextra : 2 * ((n : ℚ) / (β : ℚ)) * (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) ≤
      (22 / 100 : ℚ) * (n : ℚ) ^ 2 := by
    have hfac0 : (0 : ℚ) ≤ ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right (show 2 * ((n : ℚ) / (β : ℚ)) ≤ 22 by linarith) hfac0
    linarith
  have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
  linarith only [hsave, hextra, hn2]

/-- Case 4 (`18 * D < n`) Bin 1 + Bin 2 total saving bound. -/
private theorem case4_bin_saving_bound {n : ℕ} (hn : 23700 ≤ n) :
    let B1 := Finset.Icc ((n + 2) / 3) ((38 * n) / 100)
    let B2 := Finset.Icc ((38 * n) / 100 + 1) ((41 * n) / 100)
    (B1.card : ℚ) * (-(932 / 1000 : ℚ) * ((164 / 10000 : ℚ) * (n : ℚ) ^ 2) + 500 * (n : ℚ)) +
    (B2.card : ℚ) * (-(947 / 1000 : ℚ) * ((75 / 10000 : ℚ) * (n : ℚ) ^ 2) + 500 * (n : ℚ)) ≤
    -(125 / 149769 : ℚ) * (n : ℚ) ^ 3 + 45 * (n : ℚ) ^ 2 := by
  intro B1 B2
  have hn_q : (23700 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hB1_card : B1.card = (38 * n) / 100 + 1 - (n + 2) / 3 := Nat.card_Icc _ _
  have hB2_card : B2.card = (41 * n) / 100 - (38 * n) / 100 := by
    dsimp only [B2]; rw [Nat.card_Icc]; omega
  have hB1_ge : (7 / 150 : ℚ) * n - 1 ≤ (B1.card : ℚ) := by
    have hnat : 14 * n ≤ 300 * B1.card + 300 := by rw [hB1_card]; omega
    have hq : (14 : ℚ) * n ≤ 300 * (B1.card : ℚ) + 300 := by exact_mod_cast hnat
    linarith
  have hB1_le : (B1.card : ℚ) ≤ (7 / 150 : ℚ) * n + 1 := by
    have hnat : 300 * B1.card ≤ 14 * n + 300 := by rw [hB1_card]; omega
    have hq : (300 : ℚ) * (B1.card : ℚ) ≤ 14 * n + 300 := by exact_mod_cast hnat
    linarith
  have hB2_ge : (3 / 100 : ℚ) * n - 1 ≤ (B2.card : ℚ) := by
    have hnat : 3 * n ≤ 100 * B2.card + 100 := by rw [hB2_card]; omega
    have hq : (3 : ℚ) * n ≤ 100 * (B2.card : ℚ) + 100 := by exact_mod_cast hnat
    linarith
  have hB2_le : (B2.card : ℚ) ≤ (3 / 100 : ℚ) * n + 1 := by
    have hnat : 100 * B2.card ≤ 3 * n + 100 := by rw [hB2_card]; omega
    have hq : (100 : ℚ) * (B2.card : ℚ) ≤ 3 * n + 100 := by exact_mod_cast hnat
    linarith
  have h1_neg :
      (B1.card : ℚ) * (-(932 / 1000 : ℚ) * ((164 / 10000 : ℚ) * (n : ℚ) ^ 2)) ≤
      ((7 / 150 : ℚ) * n - 1) * (-(932 / 1000 : ℚ) * ((164 / 10000 : ℚ) * (n : ℚ) ^ 2)) := by
    have hc : (0 : ℚ) ≤ (932 / 1000 : ℚ) * ((164 / 10000 : ℚ) * (n : ℚ) ^ 2) := by positivity
    nlinarith only [hB1_ge, hc]
  have h2_neg :
      (B2.card : ℚ) * (-(947 / 1000 : ℚ) * ((75 / 10000 : ℚ) * (n : ℚ) ^ 2)) ≤
      ((3 / 100 : ℚ) * n - 1) * (-(947 / 1000 : ℚ) * ((75 / 10000 : ℚ) * (n : ℚ) ^ 2)) := by
    have hc : (0 : ℚ) ≤ (947 / 1000 : ℚ) * ((75 / 10000 : ℚ) * (n : ℚ) ^ 2) := by positivity
    nlinarith only [hB2_ge, hc]
  have hpos : ((B1.card : ℚ) + (B2.card : ℚ)) * (500 * (n : ℚ)) ≤ 40 * (n : ℚ) ^ 2 := by
    nlinarith only [hB1_le, hB2_le, hn_q]
  have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
  have hn3 : (0 : ℚ) ≤ (n : ℚ) ^ 3 := by positivity
  have hexpand :
      (B1.card : ℚ) * (-(932 / 1000 : ℚ) * ((164 / 10000 : ℚ) * (n : ℚ) ^ 2) + 500 * (n : ℚ)) +
      (B2.card : ℚ) * (-(947 / 1000 : ℚ) * ((75 / 10000 : ℚ) * (n : ℚ) ^ 2) + 500 * (n : ℚ)) =
      (B1.card : ℚ) * (-(932 / 1000 : ℚ) * ((164 / 10000 : ℚ) * (n : ℚ) ^ 2)) +
      (B2.card : ℚ) * (-(947 / 1000 : ℚ) * ((75 / 10000 : ℚ) * (n : ℚ) ^ 2)) +
      ((B1.card : ℚ) + (B2.card : ℚ)) * (500 * (n : ℚ)) := by ring
  linarith only [hexpand, h1_neg, h2_neg, hpos, hn2, hn3]

/-- Pointwise Pin–Frankl + Shitov convex combination for a single index `r ∈ [ρ, k]`. -/
private theorem pointwise_pf_shitov {n k γ ρ β : ℕ} {δ s : ℕ → ℕ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hβ : β = max ρ (n / 10)) (r : ℕ)
    (hpf : δ r ≤ (r + 2).choose 2)
    (hsh : δ r ≤ 2 * (∑ i ∈ Finset.Icc 1 r, i * s i) + 2 * r) :
    (δ r : ℚ) ≤
      (1 - dualAlpha k γ β r) * ((r : ℚ) ^ 2 / 2) +
      2 * dualAlpha k γ β r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) +
      (2 * (r : ℚ) + 1) := by
  have hpf_2 : 2 * δ r ≤ (r + 2) * (r + 1) := by
    have hch : 2 * (r + 2).choose 2 = (r + 2) * (r + 1) := by
      rw [Nat.choose_two_right]
      rcases (Nat.even_mul_succ_self (r + 1)).two_dvd with ⟨t, ht⟩
      have hsub : r + 2 - 1 = r + 1 := by omega
      rw [hsub, show (r + 2) * (r + 1) = 2 * t by linarith]
      omega
    omega
  have hpf_q : (δ r : ℚ) ≤ (r : ℚ) ^ 2 / 2 + (2 * (r : ℚ) + 1) := by
    have h2q : (2 : ℚ) * δ r ≤ ((r : ℚ) + 2) * ((r : ℚ) + 1) := by exact_mod_cast hpf_2
    linarith
  have hsh_q : (δ r : ℚ) ≤
      2 * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) + (2 * (r : ℚ) + 1) := by
    have hq : (δ r : ℚ) ≤ ((2 * (∑ i ∈ Finset.Icc 1 r, i * s i) + 2 * r : ℕ) : ℚ) := by
      exact_mod_cast hsh
    push_cast at hq
    linarith
  have ⟨hα0, hα1⟩ := dualAlpha_bounds hn100 hk hγ hβ r
  have h1 := mul_le_mul_of_nonneg_left hpf_q (show (0 : ℚ) ≤ 1 - dualAlpha k γ β r by linarith)
  have h2 := mul_le_mul_of_nonneg_left hsh_q hα0
  linarith

/-- Pointwise convex combination with an extra Bin-1 or Bin-2 plateau saving. -/
private theorem pointwise_plateau_shitov {n k γ ρ β : ℕ} {δ s : ℕ → ℕ} {w c : ℚ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hβ : β = max ρ (n / 10)) (r : ℕ) (hc0 : 0 ≤ c)
    (hw : w ≤ 1 - dualAlpha k γ β r)
    (hplat : (δ r : ℚ) ≤ (r : ℚ) ^ 2 / 2 - c * (n : ℚ) ^ 2 + 500 * (n : ℚ))
    (hsh : δ r ≤ 2 * (∑ i ∈ Finset.Icc 1 r, i * s i) + 2 * r) :
    (δ r : ℚ) ≤
      (1 - dualAlpha k γ β r) * ((r : ℚ) ^ 2 / 2) +
      (-w * (c * (n : ℚ) ^ 2) + 500 * (n : ℚ)) +
      2 * dualAlpha k γ β r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) +
      (2 * (r : ℚ) + 1) := by
  have hplat' : (δ r : ℚ) ≤ (r : ℚ) ^ 2 / 2 - c * (n : ℚ) ^ 2 + 500 * (n : ℚ) + (2 * (r : ℚ) + 1) := by
    have hr0 : (0 : ℚ) ≤ 2 * (r : ℚ) + 1 := by positivity
    linarith
  have hsh_q : (δ r : ℚ) ≤
      2 * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) + (2 * (r : ℚ) + 1) := by
    have hq : (δ r : ℚ) ≤ ((2 * (∑ i ∈ Finset.Icc 1 r, i * s i) + 2 * r : ℕ) : ℚ) := by
      exact_mod_cast hsh
    push_cast at hq
    linarith
  have ⟨hα0, hα1⟩ := dualAlpha_bounds hn100 hk hγ hβ r
  have h1 := mul_le_mul_of_nonneg_left hplat' (show (0 : ℚ) ≤ 1 - dualAlpha k γ β r by linarith)
  have h2 := mul_le_mul_of_nonneg_left hsh_q hα0
  have hneg : (1 - dualAlpha k γ β r) * (-(c * (n : ℚ) ^ 2)) ≤ w * (-(c * (n : ℚ) ^ 2)) := by
    have hcn : (0 : ℚ) ≤ c * (n : ℚ) ^ 2 := mul_nonneg hc0 (sq_nonneg _)
    nlinarith only [hw, hcn]
  have hpos : (1 - dualAlpha k γ β r) * (500 * (n : ℚ)) ≤ 500 * (n : ℚ) := by
    have h500 : (0 : ℚ) ≤ 500 * (n : ℚ) := by positivity
    nlinarith only [hα0, h500]
  linarith

end SubShitovDualHelpers

/-! ## Part 3: Main Sub-Shitov & Sub-Hong Theorems (Theorem T19) -/

section MainSubShitovTheorems

/-- Strongly connected case of **Theorem T19**:
every strongly connected synchronizing DFA on `n ≥ 1` states admits a synchronizing word `w`
with `149769 * w.length ≤ 24646 * n ^ 3 + 7488450 * n ^ 2` (`(24646/149769) n³ + 50 n²`). -/
theorem sub_shitov_sc_bound {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing) (hSC : A.IsStronglyConnected) :
    ∃ w : List α, A.IsSyncWord w ∧
      149769 * w.length ≤ 24646 * (Fintype.card Q) ^ 3 + 7488450 * (Fintype.card Q) ^ 2 := by
  classical
  let n := Fintype.card Q
  have hn1 : 1 ≤ n := Fintype.card_pos
  -- Small n < 23700: directly from verified Pin–Frankl (6 * L ≤ n^3)
  by_cases hsmall : n < 23700
  · obtain ⟨w, hw, hpf⟩ := pin_frankl_bound A hSync
    refine ⟨w, hw, ?_⟩
    change 6 * w.length ≤ n ^ 3 - n at hpf
    have h6 : 6 * w.length ≤ n ^ 3 := le_trans hpf (Nat.sub_le _ _)
    have hn_le : n ≤ 23699 := by omega
    nlinarith
  -- Main regime: n ≥ 23700
  have hn : 23700 ≤ n := by omega
  have hn100 : 100 ≤ n := by omega
  obtain ⟨w_opt, hw_opt_sync, hw_opt_len⟩ := exists_syncWord_len_minCorankLen A hSync
  refine ⟨w_opt, hw_opt_sync, ?_⟩
  rw [hw_opt_len]
  change 149769 * minCorankLen A hSync (n - 1) ≤ 24646 * n ^ 3 + 7488450 * n ^ 2
  let k := (n - 2) / 2
  have hk_2le : 2 * k + 2 ≤ n := by omega
  have hk_2ge : n ≤ 2 * k + 3 := by omega
  -- Case 0: every corank gap δ_j (j ≤ n - 2) is at most 2 * k
  by_cases hbig : ∃ j : ℕ, j ≤ n - 2 ∧ 2 * k < corankGap A hSync j
  swap
  · push Not at hbig
    have hlam_le : minCorankLen A hSync (n - 1) ≤ n ^ 2 := by
      rw [minCorankLen_eq_sum_range A hSync le_rfl]
      calc (∑ j ∈ Finset.range (n - 1), corankGap A hSync j)
          ≤ ∑ _j ∈ Finset.range (n - 1), (2 * k) :=
            Finset.sum_le_sum fun j hj => hbig j (by rw [Finset.mem_range] at hj; omega)
        _ = (n - 1) * (2 * k) := by simp
        _ ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
        _ = n ^ 2 := by ring
    nlinarith
  -- Otherwise let ρ = min {j : δ_j > 2 * k}
  let ρ := Nat.find hbig
  have hρ_spec : ρ ≤ n - 2 ∧ 2 * k < corankGap A hSync ρ := Nat.find_spec hbig
  have hρ_min : ∀ j < ρ, corankGap A hSync j ≤ 2 * k := by
    intro j hj
    by_contra hgt
    push Not at hgt
    exact Nat.find_min hbig hj ⟨by omega, hgt⟩
  have hρ_ge1 : 1 ≤ ρ := by
    by_contra h0
    have hρ0 : ρ = 0 := by omega
    have hgap0 := corankGap_le_pinFrankl A hSync (by omega : 0 + 1 ≤ n - 1)
    have hch : (0 + 2).choose 2 = 1 := by decide
    have hgt := hρ_spec.2
    rw [hρ0] at hgt
    omega
  have hlam_ρ_le : minCorankLen A hSync ρ ≤ n ^ 2 := by
    rw [minCorankLen_eq_sum_range A hSync (by omega : ρ ≤ n - 1)]
    calc (∑ j ∈ Finset.range ρ, corankGap A hSync j)
        ≤ ∑ _j ∈ Finset.range ρ, (2 * k) :=
          Finset.sum_le_sum fun j hj => hρ_min j (Finset.mem_range.mp hj)
      _ = ρ * (2 * k) := by simp
      _ ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
      _ = n ^ 2 := by ring
  let γ := (125 * n) / 258
  -- Case 1: γ < ρ ⇒ ρ ≥ (2/5) n, pure Pin–Frankl gives ≤ (117/750) n³ + n²
  by_cases hρ_gt_γ : γ < ρ
  · have h5ρ : 2 * n ≤ 5 * ρ := by omega
    have htail : 6 * (∑ j ∈ Finset.Ico ρ (n - 1), corankGap A hSync j) ≤ n ^ 3 - ρ ^ 3 := by
      have hpf : (∑ j ∈ Finset.Ico ρ (n - 1), corankGap A hSync j) ≤
          ∑ j ∈ Finset.Ico ρ (n - 1), (j + 2).choose 2 :=
        Finset.sum_le_sum fun j hj =>
          corankGap_le_pinFrankl A hSync (by rw [Finset.mem_Ico] at hj; omega)
      have h6 := Nat.mul_le_mul_left 6 hpf
      rw [six_mul_sum_Ico_choose_two (by omega : ρ ≤ n - 1)] at h6
      have htop : (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) ≤ n ^ 3 := by zify [hn1]; nlinarith
      have hbot : ρ ^ 3 ≤ ρ * (ρ + 1) * (ρ + 2) := by nlinarith
      omega
    have htele := minCorankLen_eq_add_sum_Ico A hSync (by omega : ρ ≤ n - 1) le_rfl
    have hcub : ρ ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left (by omega : ρ ≤ n) 3
    have h5cub : (2 * n) ^ 3 ≤ (5 * ρ) ^ 3 := Nat.pow_le_pow_left h5ρ 3
    zify [hcub] at htail
    zify at h5cub hlam_ρ_le htele ⊢
    nlinarith
  -- Now ρ ≤ γ: prepare shared decomposition λ(n-1) = λ(ρ) + S_mid + S_tail & bucket counts
  have hρ_le_γ : ρ ≤ γ := by omega
  let β := max ρ (n / 10)
  have hk1_le_n1 : k + 1 ≤ n - 1 := by omega
  let S_mid := ∑ r ∈ Finset.Icc ρ k, corankGap A hSync r
  let S_tail := ∑ j ∈ Finset.Ico (k + 1) (n - 1), corankGap A hSync j
  have hdecomp : minCorankLen A hSync (n - 1) = minCorankLen A hSync ρ + S_mid + S_tail := by
    have h1 := minCorankLen_eq_add_sum_Ico A hSync (by omega : ρ ≤ k + 1) hk1_le_n1
    have h2 := minCorankLen_eq_add_sum_Ico A hSync hk1_le_n1 le_rfl
    have hIco_eq : Finset.Ico ρ (k + 1) = Finset.Icc ρ k := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco_eq] at h1
    omega
  have hS_tail_48 : 48 * S_tail ≤ 7 * n ^ 3 := by
    have hpf : S_tail ≤ ∑ j ∈ Finset.Ico (k + 1) (n - 1), (j + 2).choose 2 :=
      Finset.sum_le_sum fun j hj =>
        corankGap_le_pinFrankl A hSync (by rw [Finset.mem_Ico] at hj; omega)
    have h6 := Nat.mul_le_mul_left 6 hpf
    rw [six_mul_sum_Ico_choose_two hk1_le_n1] at h6
    have htop : (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) ≤ n ^ 3 := by zify [hn1]; nlinarith
    have hbot := eight_mul_cube_ge hn100 hk_2ge
    omega
  have hS_tail_q : (S_tail : ℚ) ≤ (7 / 48 : ℚ) * (n : ℚ) ^ 3 := by
    have hq : (48 : ℚ) * S_tail ≤ 7 * (n : ℚ) ^ 3 := by exact_mod_cast hS_tail_48
    linarith
  have hlam_ρ_q : (minCorankLen A hSync ρ : ℚ) ≤ (n : ℚ) ^ 2 := by exact_mod_cast hlam_ρ_le
  have hdecomp_q : (minCorankLen A hSync (n - 1) : ℚ) =
      (minCorankLen A hSync ρ : ℚ) + (S_mid : ℚ) + (S_tail : ℚ) := by exact_mod_cast hdecomp
  -- Bucket counts s_i = |{j < ρ : 2i - 1 ≤ δ_j ≤ 2i}|
  let B : ℕ → Finset ℕ := fun i =>
    (Finset.range ρ).filter (fun j => 2 * i - 1 ≤ corankGap A hSync j ∧ corankGap A hSync j ≤ 2 * i)
  let s : ℕ → ℕ := fun i => (B i).card
  have hB_disj : ∀ i₁ ∈ Finset.Icc 1 k, ∀ i₂ ∈ Finset.Icc 1 k, i₁ ≠ i₂ → Disjoint (B i₁) (B i₂) := by
    intro i₁ hi₁ i₂ hi₂ hne
    rw [Finset.mem_Icc] at hi₁ hi₂
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    simp only [B, Finset.mem_filter] at hj₁ hj₂
    omega
  have hsum_s_le : (∑ i ∈ Finset.Icc 1 k, s i) ≤ ρ := by
    have hcard_bi : ((Finset.Icc 1 k).biUnion B).card = ∑ i ∈ Finset.Icc 1 k, s i :=
      Finset.card_biUnion fun i₁ hi₁ i₂ hi₂ hne => hB_disj i₁ hi₁ i₂ hi₂ hne
    rw [← hcard_bi]
    have hsub : (Finset.Icc 1 k).biUnion B ⊆ Finset.range ρ := by
      intro j hj
      rw [Finset.mem_biUnion] at hj
      rcases hj with ⟨i, _, hji⟩
      exact (Finset.mem_filter.mp hji).1
    exact le_trans (Finset.card_le_card hsub) (by rw [Finset.card_range])
  have hdelta_shitov : ∀ r ∈ Finset.Icc ρ k,
      corankGap A hSync r ≤ 2 * (∑ i ∈ Finset.Icc 1 r, i * s i) + 2 * r := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hex_τ : ∃ τ : ℕ, τ ≤ n - 2 ∧ 2 * r < corankGap A hSync τ := ⟨ρ, hρ_spec.1, by omega⟩
    let τ := Nat.find hex_τ
    have hτ_spec : τ ≤ n - 2 ∧ 2 * r < corankGap A hSync τ := Nat.find_spec hex_τ
    have hτ_le_ρ : τ ≤ ρ := Nat.find_min' hex_τ ⟨hρ_spec.1, by omega⟩
    have hτ_min : ∀ j < τ, corankGap A hSync j ≤ 2 * r := by
      intro j hj
      by_contra hgt
      push Not at hgt
      exact Nat.find_min hex_τ hj ⟨by omega, hgt⟩
    have hshitov : corankGap A hSync r ≤ minCorankLen A hSync τ + 2 * r :=
      shitov_corank_gap A hSync (by omega) (by omega) (by omega) hτ_spec.2
    have hlam_τ_le : minCorankLen A hSync τ ≤ 2 * ∑ i ∈ Finset.Icc 1 r, i * s i := by
      rw [minCorankLen_eq_sum_range A hSync (by omega : τ ≤ n - 1)]
      have hpos_sum : (∑ j ∈ Finset.range τ, corankGap A hSync j) =
          ∑ j ∈ (Finset.range τ).filter (fun j => 1 ≤ corankGap A hSync j),
            corankGap A hSync j := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h0 : corankGap A hSync j = 0
        · simp [h0]
        · have h1 : 1 ≤ corankGap A hSync j := by omega
          simp [h1]
      rw [hpos_sum]
      have hsub_bi : (Finset.range τ).filter (fun j => 1 ≤ corankGap A hSync j) ⊆
          (Finset.Icc 1 r).biUnion B := by
        intro j hj
        rw [Finset.mem_filter, Finset.mem_range] at hj
        have hle2r := hτ_min j hj.1
        rw [Finset.mem_biUnion]
        refine ⟨(corankGap A hSync j + 1) / 2, Finset.mem_Icc.mpr (by omega), ?_⟩
        simp only [B, Finset.mem_filter, Finset.mem_range]
        omega
      have hdisj_r : Set.PairwiseDisjoint (↑(Finset.Icc 1 r) : Set ℕ) B := fun i₁ hi₁ i₂ hi₂ hne =>
        hB_disj i₁ (Finset.Icc_subset_Icc_right (by omega) hi₁)
          i₂ (Finset.Icc_subset_Icc_right (by omega) hi₂) hne
      calc (∑ j ∈ (Finset.range τ).filter (fun j => 1 ≤ corankGap A hSync j),
              corankGap A hSync j)
          ≤ ∑ j ∈ (Finset.Icc 1 r).biUnion B, corankGap A hSync j :=
            Finset.sum_le_sum_of_subset hsub_bi
        _ = ∑ i ∈ Finset.Icc 1 r, ∑ j ∈ B i, corankGap A hSync j :=
            Finset.sum_biUnion hdisj_r
        _ ≤ ∑ i ∈ Finset.Icc 1 r, ∑ _j ∈ B i, (2 * i) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2.2
        _ = ∑ i ∈ Finset.Icc 1 r, (B i).card * (2 * i) := by simp
        _ = 2 * ∑ i ∈ Finset.Icc 1 r, i * s i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by dsimp only [s]; ring
    omega
  -- Helper closing the final rational bound into integer multiplication
  have finish_q : (minCorankLen A hSync (n - 1) : ℚ) ≤
      (24646 / 149769 : ℚ) * (n : ℚ) ^ 3 + 50 * (n : ℚ) ^ 2 →
      149769 * minCorankLen A hSync (n - 1) ≤ 24646 * n ^ 3 + 7488450 * n ^ 2 := by
    intro hq
    have hmul : (149769 : ℚ) * (minCorankLen A hSync (n - 1) : ℚ) ≤
        24646 * (n : ℚ) ^ 3 + 7488450 * (n : ℚ) ^ 2 := by linarith only [hq]
    exact_mod_cast hmul
  -- Case 2: Outer ρ-range (n / 3 < ρ ≤ γ) — exact cubic-square slack beats 24646/149769!
  by_cases hρ_outer : n / 3 < ρ
  · refine finish_q ?_
    have hpt : ∀ r ∈ Finset.Icc ρ k,
        (corankGap A hSync r : ℚ) ≤
          (1 - dualAlpha k γ β r) * ((r : ℚ) ^ 2 / 2) +
          2 * dualAlpha k γ β r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) +
          (2 * (r : ℚ) + 1) :=
      fun r hr => pointwise_pf_shitov hn100 rfl rfl rfl r
        (corankGap_le_pinFrankl A hSync (by rw [Finset.mem_Icc] at hr; omega))
        (hdelta_shitov r hr)
    have hsum_pt := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_pt
    have hcast_mid : (S_mid : ℚ) = ∑ r ∈ Finset.Icc ρ k, (corankGap A hSync r : ℚ) := by
      dsimp only [S_mid]; rw [Nat.cast_sum]
    have hA := pieceA_base hn100 rfl rfl hρ_le_γ rfl
    have hB := pieceB_base hn100 rfl rfl hρ_le_γ rfl hsum_s_le
    have hC := pieceC_base ρ k
    have hasm := rounding_assembly_outer hn100 rfl rfl hρ_outer hρ_le_γ rfl
    have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
    linarith only [hdecomp_q, hlam_ρ_q, hS_tail_q, hcast_mid, hsum_pt, hA, hB, hC, hasm, hn2]
  -- Central ρ-range: ρ ≤ n / 3
  have hρ_central : ρ ≤ n / 3 := by omega
  let D := shortCorank A hSync
  have hD_le : D ≤ n - 1 := shortCorank_le A hSync
  have hlam_D_le : minCorankLen A hSync D ≤ n - 1 := minCorankLen_shortCorank_le A hSync
  by_cases hD_big : n ≤ 18 * D
  · -- Case 3a (Catch 8): ρ < D ⇒ λ(ρ) ≤ 1 ⇒ direct Shitov at τ = ρ gives (7/48) n³ + O(n²)
    by_cases hρ_lt_D : ρ < D
    · have hlam_ρ1_le : minCorankLen A hSync (ρ + 1) ≤ n - 1 :=
        le_trans (minCorankLen_mono A hSync (by omega : ρ + 1 ≤ D) hD_le) hlam_D_le
      have hlam_ρ_le1 : minCorankLen A hSync ρ ≤ 1 := by
        have hmono := minCorankLen_mono A hSync (Nat.le_add_right ρ 1) (by omega : ρ + 1 ≤ n - 1)
        have hgap := hρ_spec.2
        dsimp only [corankGap] at hgap
        omega
      have hS_mid_le : S_mid ≤ (k + 1) ^ 2 := by
        have hpt : ∀ r ∈ Finset.Icc ρ k, corankGap A hSync r ≤ 2 * r + 1 := by
          intro r hr
          rw [Finset.mem_Icc] at hr
          have hsh := shitov_corank_gap A hSync (by omega) (by omega)
            (by omega : ρ + 1 ≤ n - 1) (by omega : 2 * r < corankGap A hSync ρ)
          omega
        have hsum_le : S_mid ≤ ∑ r ∈ Finset.Icc ρ k, (2 * r + 1) := Finset.sum_le_sum hpt
        have hq : ((∑ r ∈ Finset.Icc ρ k, (2 * r + 1) : ℕ) : ℚ) ≤ (((k + 1) ^ 2 : ℕ) : ℚ) := by
          have := pieceC_base ρ k
          push_cast at this ⊢
          exact this
        have hnat : (∑ r ∈ Finset.Icc ρ k, (2 * r + 1)) ≤ (k + 1) ^ 2 := by exact_mod_cast hq
        omega
      have hk1_le : (k + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (by omega : k + 1 ≤ n) 2
      omega
    -- Case 3b: D ≤ ρ and n ≤ 18 * D — Mass-Defect Retention saves (125/149769) n³!
    · refine finish_q ?_
      have hD_le_ρ : D ≤ ρ := by omega
      let B_lo : ℕ → Finset ℕ := fun i =>
        (Finset.range D).filter (fun j => 2 * i - 1 ≤ corankGap A hSync j ∧ corankGap A hSync j ≤ 2 * i)
      let B_hi : ℕ → Finset ℕ := fun i =>
        (Finset.Ico D ρ).filter (fun j => 2 * i - 1 ≤ corankGap A hSync j ∧ corankGap A hSync j ≤ 2 * i)
      let s_lo : ℕ → ℕ := fun i => (B_lo i).card
      let s_hi : ℕ → ℕ := fun i => (B_hi i).card
      have hs_eq : ∀ i, s i = s_lo i + s_hi i := by
        intro i
        dsimp only [s, s_lo, s_hi]
        have hunion : B i = B_lo i ∪ B_hi i := by
          ext j
          simp only [B, B_lo, B_hi, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
          omega
        have hdisj : Disjoint (B_lo i) (B_hi i) := by
          rw [Finset.disjoint_left]
          intro j h1 h2
          simp only [B_lo, B_hi, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at h1 h2
          omega
        rw [hunion, Finset.card_union_of_disjoint hdisj]
      have hhi_disj : Set.PairwiseDisjoint (↑(Finset.Icc 1 k) : Set ℕ) B_hi := by
        intro i₁ hi₁ i₂ hi₂ hne
        rw [Finset.mem_coe, Finset.mem_Icc] at hi₁ hi₂
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro j h1 h2
        simp only [B_hi, Finset.mem_filter] at h1 h2
        omega
      have hsum_hi : (∑ i ∈ Finset.Icc 1 k, s_hi i) ≤ ρ - D := by
        have hcard_bi : ((Finset.Icc 1 k).biUnion B_hi).card = ∑ i ∈ Finset.Icc 1 k, s_hi i :=
          Finset.card_biUnion hhi_disj
        rw [← hcard_bi]
        have hsub : (Finset.Icc 1 k).biUnion B_hi ⊆ Finset.Ico D ρ := by
          intro j hj
          rw [Finset.mem_biUnion] at hj
          rcases hj with ⟨i, _, hji⟩
          exact (Finset.mem_filter.mp hji).1
        exact le_trans (Finset.card_le_card hsub) (by rw [Nat.card_Ico])
      have hlo_disj : Set.PairwiseDisjoint (↑(Finset.Icc 1 k) : Set ℕ) B_lo := by
        intro i₁ hi₁ i₂ hi₂ hne
        rw [Finset.mem_coe, Finset.mem_Icc] at hi₁ hi₂
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro j h1 h2
        simp only [B_lo, Finset.mem_filter] at h1 h2
        omega
      have hsum_lo : (∑ i ∈ Finset.Icc 1 k, i * s_lo i) ≤ n := by
        have h2le : 2 * (∑ i ∈ Finset.Icc 1 k, i * s_lo i) ≤ 2 * n := by
          have hrew : 2 * (∑ i ∈ Finset.Icc 1 k, i * s_lo i) =
              ∑ i ∈ Finset.Icc 1 k, ∑ _j ∈ B_lo i, (2 * i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by simp [s_lo]; ring
          have hsub : (Finset.Icc 1 k).biUnion B_lo ⊆ Finset.range D := by
            intro j hj
            rw [Finset.mem_biUnion] at hj
            rcases hj with ⟨i, _, hji⟩
            exact (Finset.mem_filter.mp hji).1
          calc 2 * (∑ i ∈ Finset.Icc 1 k, i * s_lo i)
              = ∑ i ∈ Finset.Icc 1 k, ∑ _j ∈ B_lo i, (2 * i) := hrew
            _ ≤ ∑ i ∈ Finset.Icc 1 k, ∑ j ∈ B_lo i, (corankGap A hSync j + 1) := by
                refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
                have := (Finset.mem_filter.mp hj).2.1
                omega
            _ = ∑ j ∈ (Finset.Icc 1 k).biUnion B_lo, (corankGap A hSync j + 1) :=
                (Finset.sum_biUnion hlo_disj).symm
            _ ≤ ∑ j ∈ Finset.range D, (corankGap A hSync j + 1) :=
                Finset.sum_le_sum_of_subset hsub
            _ = (∑ j ∈ Finset.range D, corankGap A hSync j) + D := by
                rw [Finset.sum_add_distrib]; simp
            _ = minCorankLen A hSync D + D := by
                rw [minCorankLen_eq_sum_range A hSync hD_le]
            _ ≤ 2 * n := by omega
        omega
      have hpt : ∀ r ∈ Finset.Icc ρ k,
          (corankGap A hSync r : ℚ) ≤
            (1 - dualAlpha k γ β r) * ((r : ℚ) ^ 2 / 2) +
            2 * dualAlpha k γ β r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) +
            (2 * (r : ℚ) + 1) :=
        fun r hr => pointwise_pf_shitov hn100 rfl rfl rfl r
          (corankGap_le_pinFrankl A hSync (by rw [Finset.mem_Icc] at hr; omega))
          (hdelta_shitov r hr)
      have hsum_pt := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_pt
      have hcast_mid : (S_mid : ℚ) = ∑ r ∈ Finset.Icc ρ k, (corankGap A hSync r : ℚ) := by
        dsimp only [S_mid]; rw [Nat.cast_sum]
      have hA := pieceA_base hn100 rfl rfl hρ_le_γ rfl
      have hB := pieceB_mass_defect hn100 rfl rfl hρ_le_γ rfl hD_le_ρ hs_eq hsum_hi hsum_lo
      have hC := pieceC_base ρ k
      have hasm := rounding_assembly_general hn100 rfl rfl hρ_le_γ rfl
      have hsave := case3b_saving_bound (ρ := ρ) hn rfl rfl rfl hD_big
      have hexp :
          2 * ((ρ : ℚ) - (D : ℚ)) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) =
          2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) -
            2 * (D : ℚ) * (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) := by ring
      have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
      linarith only [hdecomp_q, hlam_ρ_q, hS_tail_q, hcast_mid, hsum_pt, hA, hB, hC,
        hasm, hsave, hexp, hn2]
  -- Case 4: 18 * D < n and ρ ≤ n / 3 — Two-Bin AP Plateau Saving!
  · refine finish_q ?_
    have hD_lt : 18 * D < n := by omega
    let B1 := Finset.Icc ((n + 2) / 3) ((38 * n) / 100)
    let B2 := Finset.Icc ((38 * n) / 100 + 1) ((41 * n) / 100)
    let c1 : ℚ := -(932 / 1000 : ℚ) * ((164 / 10000 : ℚ) * (n : ℚ) ^ 2) + 500 * (n : ℚ)
    let c2 : ℚ := -(947 / 1000 : ℚ) * ((75 / 10000 : ℚ) * (n : ℚ) ^ 2) + 500 * (n : ℚ)
    let extra : ℕ → ℚ := fun r => if r ∈ B1 then c1 else if r ∈ B2 then c2 else 0
    have hB1_sub : B1 ⊆ Finset.Icc ρ k := by
      intro r hr; simp only [B1, Finset.mem_Icc] at hr ⊢; omega
    have hB2_sub : B2 ⊆ Finset.Icc ρ k := by
      intro r hr; simp only [B2, Finset.mem_Icc] at hr ⊢; omega
    have hB12_disj : Disjoint B1 B2 := by
      rw [Finset.disjoint_left]; intro r h1 h2
      simp only [B1, B2, Finset.mem_Icc] at h1 h2; omega
    have hpt : ∀ r ∈ Finset.Icc ρ k,
        (corankGap A hSync r : ℚ) ≤
          (1 - dualAlpha k γ β r) * ((r : ℚ) ^ 2 / 2) + extra r +
          2 * dualAlpha k γ β r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) +
          (2 * (r : ℚ) + 1) := by
      intro r hr
      by_cases h1 : r ∈ B1
      · have ⟨hw1, hpl1⟩ := bin1_bounds hn rfl rfl hρ_central rfl hD_lt h1
        have hap := ap_plateau_inequality A hSync hSC (r := r) (M := 500)
          (by simp only [B1, Finset.mem_Icc] at h1; omega)
          (by simp only [B1, Finset.mem_Icc] at h1; omega)
          (by omega)
        have hplat : (corankGap A hSync r : ℚ) ≤
            (r : ℚ) ^ 2 / 2 - (164 / 10000 : ℚ) * (n : ℚ) ^ 2 + 500 * (n : ℚ) := by
          change (corankGap A hSync r : ℚ) ≤ _ at hap
          linarith only [hap, hpl1]
        have hconv := pointwise_plateau_shitov hn100 rfl rfl rfl r (by norm_num) hw1 hplat
          (hdelta_shitov r hr)
        simp only [extra, h1, ↓reduceIte, c1]
        linarith only [hconv]
      · by_cases h2 : r ∈ B2
        · have ⟨hw2, hpl2⟩ := bin2_bounds hn rfl rfl hρ_central rfl hD_lt h2
          have hap := ap_plateau_inequality A hSync hSC (r := r) (M := 500)
            (by simp only [B2, Finset.mem_Icc] at h2; omega)
            (by simp only [B2, Finset.mem_Icc] at h2; omega)
            (by omega)
          have hplat : (corankGap A hSync r : ℚ) ≤
              (r : ℚ) ^ 2 / 2 - (75 / 10000 : ℚ) * (n : ℚ) ^ 2 + 500 * (n : ℚ) := by
            change (corankGap A hSync r : ℚ) ≤ _ at hap
            linarith only [hap, hpl2]
          have hconv := pointwise_plateau_shitov hn100 rfl rfl rfl r (by norm_num) hw2 hplat
            (hdelta_shitov r hr)
          simp only [extra, h1, h2, ↓reduceIte, c2]
          linarith only [hconv]
        · have hconv := pointwise_pf_shitov (ρ := ρ) hn100 rfl rfl rfl r
            (corankGap_le_pinFrankl A hSync (by rw [Finset.mem_Icc] at hr; omega))
            (hdelta_shitov r hr)
          simp only [extra, h1, h2, ↓reduceIte, add_zero]
          exact hconv
    have hsum_extra : (∑ r ∈ Finset.Icc ρ k, extra r) =
        (B1.card : ℚ) * c1 + (B2.card : ℚ) * c2 := by
      have hunion_sub : B1 ∪ B2 ⊆ Finset.Icc ρ k := Finset.union_subset hB1_sub hB2_sub
      have hzero : (∑ r ∈ Finset.Icc ρ k, extra r) = ∑ r ∈ B1 ∪ B2, extra r := by
        symm
        refine Finset.sum_subset hunion_sub fun r _ hnot => ?_
        rw [Finset.mem_union] at hnot
        push Not at hnot
        simp [extra, hnot.1, hnot.2]
      rw [hzero, Finset.sum_union hB12_disj]
      have hs1 : (∑ r ∈ B1, extra r) = (B1.card : ℚ) * c1 := by
        have : ∀ r ∈ B1, extra r = c1 := fun r hr => by simp [extra, hr]
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      have hs2 : (∑ r ∈ B2, extra r) = (B2.card : ℚ) * c2 := by
        have : ∀ r ∈ B2, extra r = c2 := fun r hr => by
          have hnot1 : r ∉ B1 := Finset.disjoint_right.mp hB12_disj hr
          simp [extra, hnot1, hr]
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      rw [hs1, hs2]
    have hsum_pt := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_pt
    have hcast_mid : (S_mid : ℚ) = ∑ r ∈ Finset.Icc ρ k, (corankGap A hSync r : ℚ) := by
      dsimp only [S_mid]; rw [Nat.cast_sum]
    have hA := pieceA_base hn100 rfl rfl hρ_le_γ rfl
    have hB := pieceB_base hn100 rfl rfl hρ_le_γ rfl hsum_s_le
    have hC := pieceC_base ρ k
    have hasm := rounding_assembly_general hn100 rfl rfl hρ_le_γ rfl
    have hsave : (B1.card : ℚ) * c1 + (B2.card : ℚ) * c2 ≤
        -(125 / 149769 : ℚ) * (n : ℚ) ^ 3 + 45 * (n : ℚ) ^ 2 :=
      case4_bin_saving_bound hn
    have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
    linarith only [hdecomp_q, hlam_ρ_q, hS_tail_q, hcast_mid, hsum_pt, hsum_extra,
      hA, hB, hC, hasm, hsave, hn2]

/-- **Theorem T19 — Explicit-`O(n²)` Sub-Shitov & Sub-Hong General Cubic Upper Bound**:
For EVERY synchronizing DFA on `n ≥ 1` states, there exists a synchronizing word `w` with
`149769 * w.length ≤ 24646 * n ^ 3 + 7488450 * n ^ 2`
(`(24646 / 149769) n³ + 50 n² ≈ 0.164560 n³ + 50 n²`). -/
theorem sub_shitov_bound {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧
      149769 * w.length ≤ 24646 * (Fintype.card Q) ^ 3 + 7488450 * (Fintype.card Q) ^ 2 := by
  classical
  have hC_ne : (sinkSCC A).Nonempty := sinkSCC_nonempty A hSync
  have : Nonempty {q // q ∈ sinkSCC A} := ⟨⟨hC_ne.choose, hC_ne.choose_spec⟩⟩
  have hSyncC := restrictSinkSCC_isSynchronizing A hSync
  have hSCC := restrictSinkSCC_isStronglyConnected A
  obtain ⟨w, hw, hlen⟩ := exists_syncWord_le_sinkSCC_bound A hSync
  obtain ⟨wC, hwC, hlenC⟩ := sub_shitov_sc_bound (restrictSinkSCC A) hSyncC hSCC
  have hrtC : (restrictSinkSCC A).resetThreshold hSyncC ≤ wC.length :=
    (restrictSinkSCC A).resetThreshold_le_of_isSyncWord hSyncC hwC
  refine ⟨w, hw, ?_⟩
  let n := Fintype.card Q
  let s := (sinkSCC A).card
  let m := n - s
  have hs_pos : 1 ≤ s := Finset.card_pos.mpr hC_ne
  have hs_le : s ≤ n := Finset.card_le_univ _
  have hcard_sub : Fintype.card {q // q ∈ sinkSCC A} = s := Fintype.card_coe (sinkSCC A)
  rw [hcard_sub] at hlenC
  have hrtC_mul : 149769 * (restrictSinkSCC A).resetThreshold hSyncC ≤
      24646 * s ^ 3 + 7488450 * s ^ 2 :=
    le_trans (Nat.mul_le_mul_left 149769 hrtC) hlenC
  have hlen' : 2 * w.length ≤ m * (m + 1) + 2 * (restrictSinkSCC A).resetThreshold hSyncC := hlen
  have h149 := Nat.mul_le_mul_left 149769 hlen'
  have hms : m + s = n := by omega
  have hcub : s ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hs_le 3
  nlinarith

/-- Explicit threshold corollary strictly beating **Shitov (2019)** (`8257 / 49923 n³`)
for EVERY synchronizing DFA on `n ≥ 59908` states. -/
theorem sub_shitov_strictly_beats_shitov {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing) (hn : 59908 ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ 49923 * w.length < 8257 * (Fintype.card Q) ^ 3 := by
  obtain ⟨w, hw, hsh⟩ := sub_shitov_bound A hSync
  refine ⟨w, hw, ?_⟩
  have hlt : 24646 * (Fintype.card Q) ^ 3 + 7488450 * (Fintype.card Q) ^ 2 <
      3 * (8257 * (Fintype.card Q) ^ 3) := by
    have h1 : (59908 : ℕ) ≤ Fintype.card Q := hn
    nlinarith
  omega

/-- Explicit threshold corollary strictly beating **Hong (`2611.00172v1`)** (`8242 / 49923 n³`)
for EVERY synchronizing DFA on `n ≥ 93606` states. -/
theorem sub_shitov_strictly_beats_hong {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing) (hn : 93606 ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧ 49923 * w.length < 8242 * (Fintype.card Q) ^ 3 := by
  obtain ⟨w, hw, hsh⟩ := sub_shitov_bound A hSync
  refine ⟨w, hw, ?_⟩
  have hlt : 24646 * (Fintype.card Q) ^ 3 + 7488450 * (Fintype.card Q) ^ 2 <
      3 * (8242 * (Fintype.card Q) ^ 3) := by
    have h1 : (93606 : ℕ) ≤ Fintype.card Q := hn
    nlinarith
  omega

end MainSubShitovTheorems

end Cerny
