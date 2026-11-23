import Cerny.Defs
import Cerny.Combinatorial
import Cerny.AdditionalClasses
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# General Sub-Pin–Frankl Cubic Upper Bound — Exact Shitov (2019) `8257/49923 n³ + 3 n²`

This file proves **Shitov's standing peer-reviewed general upper bound (2019, `arXiv:1901.06542`)**:
for EVERY synchronizing DFA on `n ≥ 1` states, there exists a synchronizing word `w` with
$$49923 \cdot |w| \le 8257 \cdot n^3 + 149769 \cdot n^2 \qquad \left(\frac{8257}{49923} n^3 + 3 n^2 \approx 0.165395\, n^3 + 3 n^2\right),$$
strictly beating both Pin–Frankl's `(n³ - n) / 6 ≈ 0.166667 n³` (for all `n ≥ 2359`) and
Szykuła's STACS 2018 bound `85059/511104 n³ ≈ 0.166422 n³`.

Remarkably, the proof uses **ZERO calculus, ZERO LP solvers, and ZERO real numbers**:
1. **Corank-Gap Framework**: `minCorankLen` (`λ_i`), `corankGap` (`δ_j = λ_{j+1} - λ_j`),
   telescoping identity `minCorankLen_eq_add_sum_Ico`, and Pin–Frankl step bound
   `corankGap_le_pinFrankl`.
2. **Shitov's Corank-Gap Upgrade Theorem (2019, Theorem 2)**: `shitov_corank_gap`
   (`δ_r ≤ λ_τ + 2 * r` whenever `2 * r < δ_τ`), proved directly from our verified
   `szykula_avoiding_lemma`.
3. **Zero-Calculus Telescoping Rational Dual**: explicit dual weights `α_r = 0` (`r < β`),
   `α_r = M / (r * (r + 1))` (`β ≤ r ≤ γ`), `α_r = 1` (`r > γ`) at `γ = ⌊125 n / 258⌋`,
   `β = max ρ ⌊n / 10⌋`, collapsing the Shitov LP via telescoping `1/(r(r+1)) = 1/r - 1/(r+1)`
   and the exact rational square identity
   `(8257/49923) n³ - (...) = (1/6) (ρ - (25/129) n)² (ρ + (50/129) n) ≥ 0`!
-/

namespace Cerny

universe u v

/-! ## Part 1: Corank-Gap Framework -/

section CorankFramework

variable {Q : Type u} {α : Type v}

theorem exists_corank_word [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (i : ℕ) (hi : i ≤ Fintype.card Q - 1) :
    ∃ m : ℕ, ∃ w : List α, w.length = m ∧ (A.image Finset.univ w).card ≤ Fintype.card Q - i := by
  rcases hSync with ⟨w, hw⟩
  have h1 : (A.image Finset.univ w).card = 1 :=
    (A.isSyncWord_iff_card_image_univ_eq_one w).mp hw
  have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr hw.nonempty
  exact ⟨w.length, w, rfl, by omega⟩

/-- Minimum length `λ_i` of a word achieving corank at least `i` (rank `≤ n - i`). -/
noncomputable def minCorankLen [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (i : ℕ) : ℕ := by
  classical
  exact if hi : i ≤ Fintype.card Q - 1 then Nat.find (exists_corank_word A hSync i hi) else 0

/-- Corank gap `δ_j = λ_{j+1} - λ_j`. -/
noncomputable def corankGap [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (j : ℕ) : ℕ :=
  minCorankLen A hSync (j + 1) - minCorankLen A hSync j

theorem minCorankLen_spec [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {i : ℕ} (hi : i ≤ Fintype.card Q - 1) :
    ∃ w : List α, w.length = minCorankLen A hSync i ∧
      (A.image Finset.univ w).card ≤ Fintype.card Q - i := by
  classical
  unfold minCorankLen
  simp only [hi, ↓reduceDIte]
  exact Nat.find_spec (exists_corank_word A hSync i hi)

theorem minCorankLen_le [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {i : ℕ} (hi : i ≤ Fintype.card Q - 1)
    {w : List α} (hw : (A.image Finset.univ w).card ≤ Fintype.card Q - i) :
    minCorankLen A hSync i ≤ w.length := by
  classical
  unfold minCorankLen
  simp only [hi, ↓reduceDIte]
  exact Nat.find_min' (exists_corank_word A hSync i hi) ⟨w, rfl, hw⟩

theorem minCorankLen_zero [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) :
    minCorankLen A hSync 0 = 0 := by
  have hle : minCorankLen A hSync 0 ≤ ([] : List α).length :=
    minCorankLen_le A hSync (Nat.zero_le _) (by simp)
  simpa using hle

theorem minCorankLen_mono [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ Fintype.card Q - 1) :
    minCorankLen A hSync i ≤ minCorankLen A hSync j := by
  obtain ⟨w, hwlen, hwcard⟩ := minCorankLen_spec A hSync hj
  rw [← hwlen]
  exact minCorankLen_le A hSync (le_trans hij hj) (by omega)

theorem exists_syncWord_len_minCorankLen [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length = minCorankLen A hSync (Fintype.card Q - 1) := by
  obtain ⟨q⟩ := hSync.nonempty
  have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q⟩
  obtain ⟨w, hwlen, hwcard⟩ := minCorankLen_spec A hSync le_rfl
  have hge1 : 1 ≤ (A.image Finset.univ w).card :=
    Finset.card_pos.mpr ⟨A.eval q w, by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩⟩
  have heq1 : (A.image Finset.univ w).card = 1 := by omega
  exact ⟨w, (A.isSyncWord_iff_card_image_univ_eq_one w).mpr heq1, hwlen⟩

theorem minCorankLen_eq_add_sum_Ico [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ Fintype.card Q - 1) :
    minCorankLen A hSync b =
      minCorankLen A hSync a + ∑ j ∈ Finset.Ico a b, corankGap A hSync j := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    simp
  | succ b ih =>
    by_cases heq : a = b + 1
    · subst heq; simp
    · have hab' : a ≤ b := by omega
      have hsplit : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      have hb_not : b ∉ Finset.Ico a b := by simp
      rw [hsplit, Finset.sum_insert hb_not, add_comm (corankGap A hSync b),
        ← add_assoc, ← ih hab' (by omega)]
      have hmono := minCorankLen_mono A hSync (Nat.le_add_right b 1) hb
      dsimp only [corankGap]
      omega

theorem minCorankLen_eq_sum_range [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {b : ℕ} (hb : b ≤ Fintype.card Q - 1) :
    minCorankLen A hSync b = ∑ j ∈ Finset.range b, corankGap A hSync j := by
  have h := minCorankLen_eq_add_sum_Ico A hSync (Nat.zero_le b) hb
  rw [minCorankLen_zero, zero_add, Nat.Ico_zero_eq_range] at h
  exact h

/-- Pin–Frankl upper bound on every individual corank gap: `δ_j ≤ (j + 2).choose 2`. -/
theorem corankGap_le_pinFrankl [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {j : ℕ} (hj : j + 1 ≤ Fintype.card Q - 1) :
    corankGap A hSync j ≤ (j + 2).choose 2 := by
  obtain ⟨u, hulen, hucard⟩ := minCorankLen_spec A hSync (by omega : j ≤ Fintype.card Q - 1)
  by_cases hskip : (A.image Finset.univ u).card ≤ Fintype.card Q - (j + 1)
  · have hle := minCorankLen_le A hSync hj hskip
    dsimp only [corankGap]
    omega
  · have heq : (A.image Finset.univ u).card = Fintype.card Q - j := by omega
    have hge2 : 2 ≤ (A.image Finset.univ u).card := by omega
    obtain ⟨w, hwlen, hwcomp⟩ := pin_compression_bound A hSync (A.image Finset.univ u) hge2
    have hcard' : (A.image Finset.univ (u ++ w)).card ≤ Fintype.card Q - (j + 1) := by
      rw [DFA.image_append]
      omega
    have hle := minCorankLen_le A hSync hj hcard'
    rw [List.length_append, hulen] at hle
    rw [heq] at hwlen
    have hsub : Fintype.card Q - (Fintype.card Q - j) + 2 = j + 2 := by omega
    rw [hsub] at hwlen
    dsimp only [corankGap]
    omega

end CorankFramework

/-! ## Part 2: Shitov's Corank-Gap Upgrade Theorem (2019, Theorem 2) -/

section ShitovTheorem

variable {Q : Type u} {α : Type v}

/-- **Shitov's Corank-Gap Upgrade Theorem (2019, Theorem 2)**:
If `1 ≤ r`, `2 * r + 2 ≤ n`, `τ + 1 ≤ n - 1`, and `2 * r < δ_τ`, then
`δ_r ≤ λ_τ + 2 * r`. Proved via singleton-preimage counting and `szykula_avoiding_lemma`. -/
theorem shitov_corank_gap [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {r τ : ℕ}
    (hr1 : 1 ≤ r) (hr2 : 2 * r + 2 ≤ Fintype.card Q)
    (hτ : τ + 1 ≤ Fintype.card Q - 1) (hgap : 2 * r < corankGap A hSync τ) :
    corankGap A hSync r ≤ minCorankLen A hSync τ + 2 * r := by
  classical
  let n := Fintype.card Q
  have hr_le : r + 1 ≤ n - 1 := by omega
  obtain ⟨u, hulen, hucard⟩ := minCorankLen_spec A hSync (by omega : r ≤ n - 1)
  by_cases hskip : (A.image Finset.univ u).card ≤ n - (r + 1)
  · have hle := minCorankLen_le A hSync hr_le hskip
    dsimp only [corankGap]
    omega
  have hImg_card : (A.image Finset.univ u).card = n - r := by omega
  let Img := A.image Finset.univ u
  obtain ⟨v, hvlen, hvcard⟩ := minCorankLen_spec A hSync (by omega : τ ≤ n - 1)
  let S := A.image Finset.univ v
  have hS_le : S.card ≤ n - τ := hvcard
  have hS_card : S.card = n - τ := by
    by_contra hne
    have hlt : S.card ≤ n - (τ + 1) := by omega
    have hle := minCorankLen_le A hSync hτ hlt
    dsimp only [corankGap] at hgap
    omega
  have hS_no_comp : ∀ w : List α, w.length ≤ 2 * r → S.card ≤ (A.image S w).card := by
    intro w hwlen
    by_contra hlt
    have hle_next : (A.image Finset.univ (v ++ w)).card ≤ n - (τ + 1) := by
      rw [DFA.image_append]
      change (A.image S w).card ≤ n - (τ + 1)
      omega
    have hmin := minCorankLen_le A hSync hτ hle_next
    rw [List.length_append, hvlen] at hmin
    have hmono := minCorankLen_mono A hSync (Nat.le_succ τ) hτ
    dsimp only [corankGap] at hgap
    omega
  let Sing : Finset Q := Img.filter (fun y => (A.preimage {y} u).card = 1)
  let Aset : Finset Q := A.preimage Sing u
  have hAset_eq_Sing : Aset.card = Sing.card := by
    dsimp only [Aset]
    rw [A.card_preimage_eq_sum_singleton]
    have hsum : ∑ y ∈ Sing, (A.preimage {y} u).card = ∑ _y ∈ Sing, 1 := by
      refine Finset.sum_congr rfl fun y hy => (Finset.mem_filter.mp hy).2
    rw [hsum]
    simp
  have hAset_ge : n - 2 * r ≤ Aset.card := by
    have hpre_univ : A.preimage Img u = Finset.univ := by
      ext q
      simp only [DFA.mem_preimage, Finset.mem_univ, iff_true]
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
    have htotal : n = ∑ y ∈ Img, (A.preimage {y} u).card := by
      calc n = (Finset.univ : Finset Q).card := Finset.card_univ.symm
        _ = (A.preimage Img u).card := by rw [hpre_univ]
        _ = ∑ y ∈ Img, (A.preimage {y} u).card := A.card_preimage_eq_sum_singleton Img u
    have hSing_sub : Sing ⊆ Img := Finset.filter_subset _ _
    have hsplit : (∑ y ∈ Img, (A.preimage {y} u).card) =
        (∑ y ∈ Sing, (A.preimage {y} u).card) +
        (∑ y ∈ Img \ Sing, (A.preimage {y} u).card) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hSing_sub]
    have hpart1 : (∑ y ∈ Sing, (A.preimage {y} u).card) = Sing.card := by
      rw [← A.card_preimage_eq_sum_singleton]
      exact hAset_eq_Sing
    have hpart2 : 2 * (Img \ Sing).card ≤ ∑ y ∈ Img \ Sing, (A.preimage {y} u).card := by
      calc 2 * (Img \ Sing).card
          = ∑ _y ∈ Img \ Sing, 2 := by simp [mul_comm]
        _ ≤ ∑ y ∈ Img \ Sing, (A.preimage {y} u).card := by
            refine Finset.sum_le_sum fun y hy => ?_
            rw [Finset.mem_sdiff] at hy
            have hy_img : y ∈ Img := hy.1
            have hy_not : y ∉ Sing := hy.2
            have hge1 : 1 ≤ (A.preimage {y} u).card := by
              rw [DFA.mem_image] at hy_img
              rcases hy_img with ⟨q, _, hqu⟩
              exact Finset.card_pos.mpr ⟨q, by simp [DFA.mem_preimage, hqu]⟩
            have hne1 : (A.preimage {y} u).card ≠ 1 := fun h1 =>
              hy_not (Finset.mem_filter.mpr ⟨hy_img, h1⟩)
            omega
    have hsdiff_card : (Img \ Sing).card = Img.card - Sing.card :=
      Finset.card_sdiff_of_subset hSing_sub
    have hSing_le_Img : Sing.card ≤ Img.card := Finset.card_le_card hSing_sub
    change Img.card = n - r at hImg_card
    omega
  have hAset_ge2 : 2 ≤ Aset.card := by omega
  have hAset_ne : Aset.Nonempty := Finset.card_pos.mp (by omega)
  have hAset_ne_univ : Aset ≠ Finset.univ := by
    intro huniv
    have hSing_le : Sing.card ≤ Img.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hcard_eq : Aset.card = n := by rw [huniv, Finset.card_univ]
    change Img.card = n - r at hImg_card
    omega
  have hex_avoid_w : ∃ w : List α, w.length ≤ 2 * r ∧ ¬ (Aset ⊆ A.image S w) := by
    by_cases hsub : Aset ⊆ S
    · have hAvoid_sync : ∃ w₀ : List α, ¬ (Aset ⊆ A.image S w₀) := by
        rcases hSync with ⟨w₀, hw₀⟩
        refine ⟨w₀, fun hAsub => ?_⟩
        have hle1 : (A.image S w₀).card ≤ 1 := by
          calc (A.image S w₀).card
              ≤ (A.image Finset.univ w₀).card :=
                Finset.card_le_card (A.image_mono (Finset.subset_univ S) w₀)
            _ = 1 := (A.isSyncWord_iff_card_image_univ_eq_one w₀).mp hw₀
        have hle := Finset.card_le_card hAsub
        omega
      obtain ⟨w, hwlen, hwres⟩ :=
        szykula_avoiding_lemma A S Aset hAset_ne hsub hAset_ne_univ hAvoid_sync
      have hwlen2r : w.length ≤ 2 * r := by omega
      rcases hwres with hnot_sub | hcomp
      · exact ⟨w, hwlen2r, hnot_sub⟩
      · exfalso
        have := hS_no_comp w hwlen2r
        omega
    · exact ⟨[], by simp, by simpa using hsub⟩
  obtain ⟨w, hwlen, hnot_sub⟩ := hex_avoid_w
  have hex_x : ∃ x ∈ Aset, x ∉ A.image S w := by
    by_contra hall
    push Not at hall
    exact hnot_sub hall
  obtain ⟨x, hxAset, hxNot⟩ := hex_x
  have hxu_Sing : A.eval x u ∈ Sing := (A.mem_preimage Sing u x).mp hxAset
  have hxu_Img : A.eval x u ∈ Img := (Finset.mem_filter.mp hxu_Sing).1
  have hxu_card1 : (A.preimage {A.eval x u} u).card = 1 := (Finset.mem_filter.mp hxu_Sing).2
  have hxu_not_img : A.eval x u ∉ A.image Finset.univ (v ++ w ++ u) := by
    intro hmem
    rw [DFA.mem_image] at hmem
    rcases hmem with ⟨p, _, hpev⟩
    rw [DFA.eval_append] at hpev
    have hpre1 : x ∈ A.preimage {A.eval x u} u := by simp [DFA.mem_preimage]
    have hpre2 : A.eval p (v ++ w) ∈ A.preimage {A.eval x u} u := by
      rw [DFA.mem_preimage, Finset.mem_singleton]
      exact hpev
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hxu_card1
    rw [hz, Finset.mem_singleton] at hpre1 hpre2
    have hxeq : A.eval p (v ++ w) = x := hpre2.trans hpre1.symm
    apply hxNot
    rw [← DFA.image_append]
    exact (A.mem_image Finset.univ (v ++ w) x).mpr ⟨p, Finset.mem_univ p, hxeq⟩
  have hsub_erase : A.image Finset.univ (v ++ w ++ u) ⊆ Img.erase (A.eval x u) := by
    intro y hy
    rw [Finset.mem_erase]
    refine ⟨fun h => hxu_not_img (h ▸ hy), ?_⟩
    rw [DFA.image_append] at hy
    exact A.image_mono (Finset.subset_univ _) u hy
  have hcard_new : (A.image Finset.univ (v ++ w ++ u)).card ≤ n - (r + 1) := by
    have hle := Finset.card_le_card hsub_erase
    rw [Finset.card_erase_of_mem hxu_Img] at hle
    change Img.card = n - r at hImg_card
    omega
  have hle_next := minCorankLen_le A hSync hr_le hcard_new
  simp only [List.length_append, hvlen, hulen] at hle_next
  dsimp only [corankGap]
  omega

end ShitovTheorem

/-! ## Part 3: Zero-Calculus Telescoping Rational Dual for Exact Shitov (2019) -/

section TelescopingDualHelpers

private theorem six_mul_sum_range_choose_two (m : ℕ) :
    6 * (∑ r ∈ Finset.range m, (r + 2).choose 2) = m * (m + 1) * (m + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hch : 2 * (m + 2).choose 2 = (m + 2) * (m + 1) := by
      rw [Nat.choose_two_right]
      have heven : 2 ∣ (m + 2) * (m + 1) := by
        rcases (Nat.even_mul_succ_self (m + 1)).two_dvd with ⟨t, ht⟩
        exact ⟨t, by linarith⟩
      rcases heven with ⟨t, ht⟩
      have hsub : m + 2 - 1 = m + 1 := by omega
      rw [hsub, ht]
      omega
    linarith

private theorem six_mul_sum_Ico_choose_two {a b : ℕ} (hab : a ≤ b) :
    6 * (∑ r ∈ Finset.Ico a b, (r + 2).choose 2) =
      b * (b + 1) * (b + 2) - a * (a + 1) * (a + 2) := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun r => (r + 2).choose 2) hab
  have ha := six_mul_sum_range_choose_two a
  have hb := six_mul_sum_range_choose_two b
  omega

/-- Pure rational telescoping identity:
`∑_{r=a}^b 1 / (r * (r + 1)) = 1 / a - 1 / (b + 1)` for `1 ≤ a ≤ b`. -/
private theorem sum_Icc_inv_mul_succ {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ r ∈ Finset.Icc a b, (1 : ℚ) / ((r : ℚ) * ((r : ℚ) + 1))) =
      1 / (a : ℚ) - 1 / ((b : ℚ) + 1) := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases heq : a = b + 1
    · subst heq
      rw [Finset.Icc_self, Finset.sum_singleton]
      have hpos : (b : ℚ) + 1 ≠ 0 := by positivity
      have hpos2 : (b : ℚ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · have hab' : a ≤ b := by omega
      have hsplit : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : b + 1 ∉ Finset.Icc a b := by simp
      rw [hsplit, Finset.sum_insert hnot, ih hab']
      push_cast
      have h1 : (b : ℚ) + 1 ≠ 0 := by positivity
      have h2 : (b : ℚ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- Lower bound on `∑_{r=β}^γ r / (r + 1)` via `r / (r + 1) ≥ 1 - 1 / β`. -/
private theorem sum_Icc_div_succ_ge {β γ : ℕ} (hβ : 1 ≤ β) (hβγ : β ≤ γ) :
    ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) ≤
      ∑ r ∈ Finset.Icc β γ, (r : ℚ) / ((r : ℚ) + 1) := by
  have hβ_pos : (0 : ℚ) < β := by exact_mod_cast (show 0 < β by omega)
  have hterm : ∀ r ∈ Finset.Icc β γ, 1 - 1 / (β : ℚ) ≤ (r : ℚ) / ((r : ℚ) + 1) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr_ge : (β : ℚ) ≤ r := by exact_mod_cast hr.1
    have hr1_pos : (0 : ℚ) < (r : ℚ) + 1 := by positivity
    rw [sub_le_iff_le_add]
    have hmul : (1 : ℚ) * ((β : ℚ) * ((r : ℚ) + 1)) ≤
        ((r : ℚ) / ((r : ℚ) + 1) + 1 / (β : ℚ)) * ((β : ℚ) * ((r : ℚ) + 1)) := by
      have hβ_ne : (β : ℚ) ≠ 0 := ne_of_gt hβ_pos
      have hr1_ne : (r : ℚ) + 1 ≠ 0 := ne_of_gt hr1_pos
      have hrhs : ((r : ℚ) / ((r : ℚ) + 1) + 1 / (β : ℚ)) * ((β : ℚ) * ((r : ℚ) + 1)) =
          (r : ℚ) * (β : ℚ) + ((r : ℚ) + 1) := by
        field_simp
      rw [hrhs]
      have hβ1 : (1 : ℚ) ≤ (β : ℚ) := by exact_mod_cast hβ
      nlinarith
    exact le_of_mul_le_mul_right hmul (mul_pos hβ_pos hr1_pos)
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
  have hcard : ((γ : ℚ) - (β : ℚ)) ≤ ((γ + 1 - β : ℕ) : ℚ) := by
    have : γ - β ≤ γ + 1 - β := by omega
    have hcast : ((γ - β : ℕ) : ℚ) = (γ : ℚ) - (β : ℚ) := Nat.cast_sub hβγ
    rw [← hcast]
    exact_mod_cast this
  have hnonneg : (0 : ℚ) ≤ 1 - 1 / (β : ℚ) := by
    rw [sub_nonneg, div_le_one hβ_pos]
    exact_mod_cast hβ
  exact le_trans (mul_le_mul_of_nonneg_right hcard hnonneg) hsum

/-- Telescoping dual weight bound:
for `1 ≤ β ≤ γ < k`, `k ≤ 2 * γ`, `M = γ * (k - γ)`, and `1 ≤ i ≤ k`,
`i * ∑_{r ∈ Icc (max β i) k} α_r ≤ (γ + 1) * (k - γ)`. -/
private theorem shitov_dual_weight_le {β γ k i : ℕ}
    (hβ1 : 1 ≤ β) (hβγ : β ≤ γ) (hγk : γ < k) (h2γ : k ≤ 2 * γ)
    (hi1 : 1 ≤ i) (hik : i ≤ k) :
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    let α : ℕ → ℚ := fun r =>
      if r < β then 0
      else if r ≤ γ then M / ((r : ℚ) * ((r : ℚ) + 1))
      else 1
    (i : ℚ) * (∑ r ∈ Finset.Icc (max β i) k, α r) ≤
      ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
  intro M α
  by_cases hi_gt : γ < i
  · -- Case i > γ: max β i = i, every r ∈ Icc i k has r > γ so α r = 1
    have hmax : max β i = i := max_eq_right (by omega)
    rw [hmax]
    have hsum1 : (∑ r ∈ Finset.Icc i k, α r) = ((k + 1 - i : ℕ) : ℚ) := by
      have hcongr : (∑ r ∈ Finset.Icc i k, α r) = ∑ _r ∈ Finset.Icc i k, (1 : ℚ) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Icc] at hr
        have h1 : ¬ r < β := by omega
        have h2 : ¬ r ≤ γ := by omega
        simp only [α, h1, h2, ↓reduceIte]
      rw [hcongr, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    rw [hsum1]
    have hcast : ((k + 1 - i : ℕ) : ℚ) = (k : ℚ) + 1 - (i : ℚ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    rw [hcast]
    have hi_ge : (γ : ℚ) + 1 ≤ (i : ℚ) := by exact_mod_cast (show γ + 1 ≤ i by omega)
    have h2γ' : (k : ℚ) ≤ 2 * (γ : ℚ) := by exact_mod_cast h2γ
    nlinarith
  · -- Case i ≤ γ: split Icc (max β i) k = Icc (max β i) γ ∪ Icc (γ + 1) k
    let m := max β i
    have hm_ge1 : 1 ≤ m := by omega
    have hm_geβ : β ≤ m := le_max_left β i
    have hm_gei : i ≤ m := le_max_right β i
    have hm_leγ : m ≤ γ := by omega
    have hsplit : Finset.Icc m k = Finset.Icc m γ ∪ Finset.Icc (γ + 1) k := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc m γ) (Finset.Icc (γ + 1) k) := by
      rw [Finset.disjoint_left]; intro r h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    have hpart1 : (∑ r ∈ Finset.Icc m γ, α r) =
        M * (1 / (m : ℚ) - 1 / ((γ : ℚ) + 1)) := by
      have hcongr : (∑ r ∈ Finset.Icc m γ, α r) =
          ∑ r ∈ Finset.Icc m γ, M * (1 / ((r : ℚ) * ((r : ℚ) + 1))) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Icc] at hr
        have h1 : ¬ r < β := by omega
        have h2 : r ≤ γ := hr.2
        simp only [α, h1, h2, ↓reduceIte]
        ring
      rw [hcongr, ← Finset.mul_sum, sum_Icc_inv_mul_succ hm_ge1 hm_leγ]
    have hpart2 : (∑ r ∈ Finset.Icc (γ + 1) k, α r) = (k : ℚ) - (γ : ℚ) := by
      have hcongr : (∑ r ∈ Finset.Icc (γ + 1) k, α r) = ∑ _r ∈ Finset.Icc (γ + 1) k, (1 : ℚ) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Icc] at hr
        have h1 : ¬ r < β := by omega
        have h2 : ¬ r ≤ γ := by omega
        simp only [α, h1, h2, ↓reduceIte]
      rw [hcongr, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      have hsub : k + 1 - (γ + 1) = k - γ := by omega
      rw [hsub, Nat.cast_sub (by omega)]
    change (i : ℚ) * (∑ r ∈ Finset.Icc m k, α r) ≤ ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))
    rw [hsplit, Finset.sum_union hdisj, hpart1, hpart2]
    have hsimp : M * (1 / (m : ℚ) - 1 / ((γ : ℚ) + 1)) + ((k : ℚ) - (γ : ℚ)) =
        M / (m : ℚ) + ((k : ℚ) - (γ : ℚ)) / ((γ : ℚ) + 1) := by
      dsimp only [M]
      have hγ1_ne : (γ : ℚ) + 1 ≠ 0 := by positivity
      have hm_ne : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      field_simp
      ring
    rw [hsimp, mul_add]
    have hm_pos : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
    have hγ1_pos : (0 : ℚ) < (γ : ℚ) + 1 := by positivity
    have hM_nonneg : (0 : ℚ) ≤ M := by
      dsimp only [M]
      have hkg : (0 : ℚ) ≤ (k : ℚ) - (γ : ℚ) := by
        have : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
        linarith
      exact mul_nonneg (by positivity) hkg
    have hkg_nonneg : (0 : ℚ) ≤ (k : ℚ) - (γ : ℚ) := by
      have : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
      linarith
    have h1 : (i : ℚ) * (M / (m : ℚ)) ≤ M := by
      rw [mul_div_left_comm]
      have hratio : (i : ℚ) / (m : ℚ) ≤ 1 := by
        rw [div_le_one hm_pos]
        exact_mod_cast hm_gei
      nlinarith
    have h2 : (i : ℚ) * (((k : ℚ) - (γ : ℚ)) / ((γ : ℚ) + 1)) ≤ (k : ℚ) - (γ : ℚ) := by
      rw [mul_div_left_comm]
      have hratio : (i : ℚ) / ((γ : ℚ) + 1) ≤ 1 := by
        rw [div_le_one hγ1_pos]
        have : i ≤ γ + 1 := by omega
        exact_mod_cast this
      nlinarith
    have hsum_eq : M + ((k : ℚ) - (γ : ℚ)) = ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
      dsimp only [M]; ring
    linarith

/-- Exact rational square identity yielding Shitov's `8257 / 49923` cubic coefficient
with zero calculus! -/
private theorem shitov_cubic_poly_bound {n ρ β : ℚ} (hn : 0 ≤ n) (hρ : 0 ≤ ρ)
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
        (1 / 6 : ℚ) * (x - (25 / 129 : ℚ) * n) ^ 2 * (x + (50 / 129 : ℚ) * n) := by
      ring
    have hnonneg : (0 : ℚ) ≤
        (1 / 6 : ℚ) * (x - (25 / 129 : ℚ) * n) ^ 2 * (x + (50 / 129 : ℚ) * n) := by
      positivity
    linarith
  rcases hcases with hβρ | ⟨hρ_le, hβ_le⟩
  · rw [hβρ]
    exact hsq_bound ρ hρ
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
          (c - ρ) * ((250 / 16641 : ℚ) * n ^ 2 - (c ^ 2 + c * ρ + ρ ^ 2) / 6) := by
        ring
      have hpos2 : (0 : ℚ) ≤ (250 / 16641 : ℚ) * n ^ 2 - (c ^ 2 + c * ρ + ρ ^ 2) / 6 := by
        rw [hc_eq]
        nlinarith
      have hρc : ρ ≤ c := hρ_le
      have hprod : (0 : ℚ) ≤ (c - ρ) * ((250 / 16641 : ℚ) * n ^ 2 - (c ^ 2 + c * ρ + ρ ^ 2) / 6) :=
        mul_nonneg (by linarith) hpos2
      linarith
    have hbase := hsq_bound c hc_nonneg
    linarith

/-- Clean standalone rounding-error assembly lemma over `ℚ` for `n ≥ 100`. -/
private theorem shitov_rounding_assembly {n k γ ρ β : ℕ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ_le_γ : ρ ≤ γ) (hβ : β = max ρ (n / 10)) :
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
      (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) +
      2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) +
      (7 / 48 : ℚ) * (n : ℚ) ^ 3 + (n : ℚ) ^ 2 + ((k : ℚ) + 1) ^ 2 ≤
    (8257 / 49923 : ℚ) * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 2 := by
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
    have h1 : (0 : ℚ) ≤ γ := Nat.cast_nonneg γ
    have h2 : (0 : ℚ) ≤ (k : ℚ) - γ := by linarith
    have hprod : (γ : ℚ) * ((k : ℚ) - γ) ≤ ((125 / 258 : ℚ) * n) * ((2 / 129 : ℚ) * n) :=
      mul_le_mul hγ_le hkg_le h2 (by positivity)
    linarith
  have hM_ge : (125 / 16641 : ℚ) * (n : ℚ) ^ 2 - (n : ℚ) ≤ M := by
    dsimp only [M]
    have h1 : (0 : ℚ) ≤ (125 / 258 : ℚ) * n - 1 := by linarith
    have h2 : (0 : ℚ) ≤ (2 / 129 : ℚ) * n - 3 / 2 := by linarith
    have hprod : ((125 / 258 : ℚ) * n - 1) * ((2 / 129 : ℚ) * n - 3 / 2) ≤ (γ : ℚ) * ((k : ℚ) - γ) :=
      mul_le_mul hγ_ge hkg_ge h2 (by linarith)
    nlinarith
  have hγ_cub : ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 ≤
      (125 / 258 : ℚ) ^ 3 * (n : ℚ) ^ 3 / 6 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 := by
    have hγ0 : (0 : ℚ) ≤ γ := Nat.cast_nonneg γ
    have h1 : ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) ≤
        ((125 / 258 : ℚ) * n + 1) * ((125 / 258 : ℚ) * n + 2) * ((125 / 258 : ℚ) * n + 3) := by
      have ha : (γ : ℚ) + 1 ≤ (125 / 258 : ℚ) * n + 1 := by linarith
      have hb : (γ : ℚ) + 2 ≤ (125 / 258 : ℚ) * n + 2 := by linarith
      have hc : (γ : ℚ) + 3 ≤ (125 / 258 : ℚ) * n + 3 := by linarith
      exact mul_le_mul (mul_le_mul ha hb (by positivity) (by positivity)) hc
        (by positivity) (by positivity)
    nlinarith
  have hβ_le_γ : (β : ℚ) ≤ γ := by
    have : β ≤ γ := by omega
    exact_mod_cast this
  have hβ_pos : (0 : ℚ) < β := by
    have : 1 ≤ β := by omega
    exact_mod_cast (show 0 < β by omega)
  have hratio_le6 : ((γ : ℚ) - β) / (β : ℚ) ≤ 6 := by
    rw [div_le_iff₀ hβ_pos]
    have : γ ≤ 7 * β := by omega
    have hq : (γ : ℚ) ≤ 7 * β := by exact_mod_cast this
    linarith
  have hM_nonneg : (0 : ℚ) ≤ M := by
    dsimp only [M]
    have hγ0 : (0 : ℚ) ≤ γ := Nat.cast_nonneg γ
    have hkg0 : (0 : ℚ) ≤ (k : ℚ) - γ := by linarith
    exact mul_nonneg hγ0 hkg0
  have hM_div : (M / 2) * ((γ : ℚ) - β) * (1 / (β : ℚ)) ≤ (1 / 40 : ℚ) * (n : ℚ) ^ 2 := by
    have heq : (M / 2) * ((γ : ℚ) - β) * (1 / (β : ℚ)) = (M / 2) * (((γ : ℚ) - β) / (β : ℚ)) := by
      ring
    rw [heq]
    have h1 : (M / 2) * (((γ : ℚ) - β) / (β : ℚ)) ≤ (M / 2) * 6 :=
      mul_le_mul_of_nonneg_left hratio_le6 (by positivity)
    linarith
  have hM_main :
      (125 / 33282 : ℚ) * (n : ℚ) ^ 2 * ((125 / 258 : ℚ) * n - β) -
        (1 / 2 : ℚ) * (n : ℚ) ^ 2 ≤ (M / 2) * ((γ : ℚ) - β) := by
    have hdiff_nonneg : (0 : ℚ) ≤ (γ : ℚ) - β := by linarith
    have hdiff_le : (γ : ℚ) - β ≤ (n : ℚ) / 2 := by linarith
    have h1 : ((125 / 16641 : ℚ) * (n : ℚ) ^ 2 - (n : ℚ)) / 2 * ((γ : ℚ) - β) ≤
        (M / 2) * ((γ : ℚ) - β) :=
      mul_le_mul_of_nonneg_right (by linarith) hdiff_nonneg
    have h2 : (n : ℚ) / 2 * ((γ : ℚ) - β) ≤ (1 / 4 : ℚ) * (n : ℚ) ^ 2 := by nlinarith
    have h3 : (125 / 33282 : ℚ) * (n : ℚ) ^ 2 * ((125 / 258 : ℚ) * n - 1 - β) ≤
        (125 / 33282 : ℚ) * (n : ℚ) ^ 2 * ((γ : ℚ) - β) := by
      have hc : (0 : ℚ) ≤ (125 / 33282 : ℚ) * (n : ℚ) ^ 2 := by positivity
      nlinarith
    nlinarith
  have hρ_le_half : (ρ : ℚ) ≤ (n : ℚ) / 2 := by
    have hρ_q : (ρ : ℚ) ≤ γ := by exact_mod_cast hρ_le_γ
    linarith
  have hρ_nonneg : (0 : ℚ) ≤ ρ := Nat.cast_nonneg ρ
  have hρ_term : 2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - γ) ≤
      (250 / 16641 : ℚ) * (ρ : ℚ) * (n : ℚ) ^ 2 + (1 / 50 : ℚ) * (n : ℚ) ^ 2 := by
    have heq : ((γ : ℚ) + 1) * ((k : ℚ) - γ) = M + ((k : ℚ) - γ) := by
      dsimp only [M]; ring
    rw [mul_assoc (2 * (ρ : ℚ)), heq]
    have h1 : 2 * (ρ : ℚ) * (M + ((k : ℚ) - γ)) ≤
        2 * (ρ : ℚ) * ((125 / 16641 : ℚ) * (n : ℚ) ^ 2 + (2 / 129 : ℚ) * n) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hk1_sq : ((k : ℚ) + 1) ^ 2 ≤ (1 / 4 : ℚ) * (n : ℚ) ^ 2 := by
    have hk0 : (0 : ℚ) ≤ (k : ℚ) + 1 := by positivity
    nlinarith
  have hpoly_cases : (β : ℚ) = ρ ∨ ((ρ : ℚ) ≤ n / 10 ∧ (β : ℚ) ≤ n / 10) := by
    by_cases hcmp : n / 10 ≤ ρ
    · left
      have hβ_eq : β = ρ := by rw [hβ, max_eq_left hcmp]
      exact_mod_cast hβ_eq
    · right
      have hβ_eq : β = n / 10 := by rw [hβ, max_eq_right (by omega : ρ ≤ n / 10)]
      have h10ρ : 10 * ρ ≤ n := by omega
      have h10β : 10 * β ≤ n := by rw [hβ_eq]; omega
      have h1 : (10 : ℚ) * ρ ≤ n := by exact_mod_cast h10ρ
      have h2 : (10 : ℚ) * β ≤ n := by exact_mod_cast h10β
      exact ⟨by linarith only [h1], by linarith only [h2]⟩
  have hcubic := shitov_cubic_poly_bound (by positivity) hρ_nonneg hpoly_cases
  have hexpand :
      (M / 2) * ((γ : ℚ) - β) * (1 - 1 / (β : ℚ)) =
      (M / 2) * ((γ : ℚ) - β) - (M / 2) * ((γ : ℚ) - β) * (1 / (β : ℚ)) := by
    ring
  have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
  linarith only [hγ_cub, hM_div, hM_main, hρ_term, hk1_sq, hcubic, hexpand, hn2]

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

/-- Middle-sum telescoping dual bound over `r ∈ [ρ, k]` in Case 2 (`ρ ≤ γ`). -/
private theorem shitov_case2_mid_bound {n k γ ρ β : ℕ} {δ s : ℕ → ℕ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ_ge1 : 1 ≤ ρ) (hρ_le_γ : ρ ≤ γ) (hβ : β = max ρ (n / 10))
    (hsum_s_le : (∑ i ∈ Finset.Icc 1 k, s i) ≤ ρ)
    (hδ_pf : ∀ r ∈ Finset.Icc ρ k, δ r ≤ (r + 2).choose 2)
    (hδ_sh : ∀ r ∈ Finset.Icc ρ k, δ r ≤ 2 * (∑ i ∈ Finset.Icc 1 r, i * s i) + 2 * r) :
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    ((∑ r ∈ Finset.Icc ρ k, δ r : ℕ) : ℚ) ≤
      ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
        (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) +
      2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) +
      ((k : ℚ) + 1) ^ 2 := by
  intro M
  have hγ_lt_k : γ < k := by omega
  have h2γ_ge_k : k ≤ 2 * γ := by omega
  have hβ_ge10 : 10 ≤ β := by omega
  have hβ_le_γ : β ≤ γ := by omega
  have hρ_le_β : ρ ≤ β := by omega
  let α : ℕ → ℚ := fun r =>
    if r < β then 0
    else if r ≤ γ then M / ((r : ℚ) * ((r : ℚ) + 1))
    else 1
  have hM_nonneg : (0 : ℚ) ≤ M := by
    dsimp only [M]
    have : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
    nlinarith
  have hα_bounds : ∀ r ∈ Finset.Icc ρ k, (0 : ℚ) ≤ α r ∧ α r ≤ 1 := by
    intro r _hr
    dsimp only [α]
    split_ifs with h1 h2
    · exact ⟨le_rfl, zero_le_one⟩
    · have hr_geβ : β ≤ r := by omega
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
        have h10r : n ≤ 10 * r + 9 := by omega
        have hprod : (n - 9) * n ≤ (10 * r) * (10 * (r + 1)) :=
          Nat.mul_le_mul (by omega) h10r1
        zify [show 9 ≤ n by omega] at hprod ⊢
        nlinarith
      have hnat : γ * (k - γ) ≤ r * (r + 1) := by omega
      have hq : ((γ * (k - γ) : ℕ) : ℚ) ≤ ((r * (r + 1) : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hq
      exact hq
    · exact ⟨zero_le_one, le_rfl⟩
  have hpt : ∀ r ∈ Finset.Icc ρ k,
      (δ r : ℚ) ≤
        (1 - α r) * ((r : ℚ) ^ 2 / 2) +
        2 * α r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) +
        (2 * (r : ℚ) + 1) := by
    intro r hr
    have hpf_nat : δ r ≤ (r + 2).choose 2 := hδ_pf r hr
    have hpf_2 : 2 * δ r ≤ (r + 2) * (r + 1) := by
      have hch : 2 * (r + 2).choose 2 = (r + 2) * (r + 1) := by
        rw [Nat.choose_two_right]
        rcases (Nat.even_mul_succ_self (r + 1)).two_dvd with ⟨t, ht⟩
        have hsub : r + 2 - 1 = r + 1 := by omega
        rw [hsub, show (r + 2) * (r + 1) = 2 * t by linarith]
        omega
      omega
    have hpf_q : (δ r : ℚ) ≤ (r : ℚ) ^ 2 / 2 + (2 * (r : ℚ) + 1) := by
      have h2q : (2 : ℚ) * δ r ≤ ((r : ℚ) + 2) * ((r : ℚ) + 1) := by
        exact_mod_cast hpf_2
      linarith
    have hsh_nat := hδ_sh r hr
    have hsh_q : (δ r : ℚ) ≤
        2 * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) + (2 * (r : ℚ) + 1) := by
      have hq : (δ r : ℚ) ≤
          ((2 * (∑ i ∈ Finset.Icc 1 r, i * s i) + 2 * r : ℕ) : ℚ) := by exact_mod_cast hsh_nat
      push_cast at hq
      linarith
    have ⟨hα0, hα1⟩ := hα_bounds r hr
    have h1 : (1 - α r) * (δ r : ℚ) ≤
        (1 - α r) * ((r : ℚ) ^ 2 / 2 + (2 * (r : ℚ) + 1)) :=
      mul_le_mul_of_nonneg_left hpf_q (by linarith)
    have h2 : α r * (δ r : ℚ) ≤
        α r * (2 * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) + (2 * (r : ℚ) + 1)) :=
      mul_le_mul_of_nonneg_left hsh_q hα0
    linarith
  have hPieceA :
      (∑ r ∈ Finset.Icc ρ k, (1 - α r) * ((r : ℚ) ^ 2 / 2)) ≤
        ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
          (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) := by
    have hsplit1 : Finset.Icc ρ k = Finset.Icc ρ γ ∪ Finset.Icc (γ + 1) k := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj1 : Disjoint (Finset.Icc ρ γ) (Finset.Icc (γ + 1) k) := by
      rw [Finset.disjoint_left]; intro r h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    have hzero_hi : (∑ r ∈ Finset.Icc (γ + 1) k, (1 - α r) * ((r : ℚ) ^ 2 / 2)) = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [Finset.mem_Icc] at hr
      have h1 : ¬ r < β := by omega
      have h2 : ¬ r ≤ γ := by omega
      simp [α, h1, h2]
    have hsplit2 : Finset.Icc ρ γ = Finset.Ico ρ β ∪ Finset.Icc β γ := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_Ico, Finset.mem_union]; omega
    have hdisj2 : Disjoint (Finset.Ico ρ β) (Finset.Icc β γ) := by
      rw [Finset.disjoint_left]; intro r h1 h2
      simp only [Finset.mem_Ico, Finset.mem_Icc] at h1 h2; omega
    have hrew_sub :
        (∑ r ∈ Finset.Icc ρ γ, (1 - α r) * ((r : ℚ) ^ 2 / 2)) =
        (∑ r ∈ Finset.Icc ρ γ, (r : ℚ) ^ 2 / 2) -
        (M / 2) * (∑ r ∈ Finset.Icc β γ, (r : ℚ) / ((r : ℚ) + 1)) := by
      rw [hsplit2, Finset.sum_union hdisj2, Finset.sum_union hdisj2]
      have hlo : (∑ r ∈ Finset.Ico ρ β, (1 - α r) * ((r : ℚ) ^ 2 / 2)) =
          ∑ r ∈ Finset.Ico ρ β, (r : ℚ) ^ 2 / 2 := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Ico] at hr
        simp [α, hr.2]
      have hhi : (∑ r ∈ Finset.Icc β γ, (1 - α r) * ((r : ℚ) ^ 2 / 2)) =
          (∑ r ∈ Finset.Icc β γ, (r : ℚ) ^ 2 / 2) -
          (M / 2) * (∑ r ∈ Finset.Icc β γ, (r : ℚ) / ((r : ℚ) + 1)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Icc] at hr
        have h1 : ¬ r < β := by omega
        have h2 : r ≤ γ := hr.2
        have hr_ne : (r : ℚ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
        have hr1_ne : (r : ℚ) + 1 ≠ 0 := by positivity
        simp only [α, h1, h2, ↓reduceIte]
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
  have hPieceB :
      (∑ r ∈ Finset.Icc ρ k, 2 * α r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ))) ≤
        2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
    have hswap :
        (∑ r ∈ Finset.Icc ρ k, 2 * α r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ))) =
        2 * ∑ i ∈ Finset.Icc 1 k, (s i : ℚ) * ((i : ℚ) * ∑ r ∈ Finset.Icc (max β i) k, α r) := by
      have hinner : ∀ r ∈ Finset.Icc ρ k,
          2 * α r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) =
          ∑ i ∈ Finset.Icc 1 k, if i ≤ r then 2 * (s i : ℚ) * ((i : ℚ) * α r) else 0 := by
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
      have hdrop : (∑ r ∈ Finset.Icc (max ρ i) k, 2 * (s i : ℚ) * ((i : ℚ) * α r)) =
          ∑ r ∈ Finset.Icc (max β i) k, 2 * (s i : ℚ) * ((i : ℚ) * α r) := by
        have hsub : Finset.Icc (max β i) k ⊆ Finset.Icc (max ρ i) k := by
          intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
        symm
        refine Finset.sum_subset hsub fun r hr hnot => ?_
        simp only [Finset.mem_Icc] at hr hnot
        have hltβ : r < β := by omega
        simp [α, hltβ]
      rw [hdrop, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [hswap]
    have hle_sum :
        (∑ i ∈ Finset.Icc 1 k, (s i : ℚ) * ((i : ℚ) * ∑ r ∈ Finset.Icc (max β i) k, α r)) ≤
        ∑ i ∈ Finset.Icc 1 k, (s i : ℚ) * (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [Finset.mem_Icc] at hi
      exact mul_le_mul_of_nonneg_left
        (shitov_dual_weight_le (by omega) hβ_le_γ hγ_lt_k h2γ_ge_k hi.1 hi.2)
        (Nat.cast_nonneg _)
    rw [← Finset.sum_mul] at hle_sum
    have hsum_s_q : (∑ i ∈ Finset.Icc 1 k, (s i : ℚ)) ≤ (ρ : ℚ) := by
      exact_mod_cast hsum_s_le
    have hfactor_nonneg : (0 : ℚ) ≤ ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
      have hγ0 : (0 : ℚ) ≤ γ := Nat.cast_nonneg γ
      have hγk : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
      nlinarith only [hγ0, hγk]
    have hmul := mul_le_mul_of_nonneg_right hsum_s_q hfactor_nonneg
    linarith only [hle_sum, hmul]
  have hPieceC : (∑ r ∈ Finset.Icc ρ k, (2 * (r : ℚ) + 1)) ≤ ((k : ℚ) + 1) ^ 2 := by
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
  have hsum_pt := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_pt
  rw [Nat.cast_sum]
  linarith only [hsum_pt, hPieceA, hPieceB, hPieceC]

end TelescopingDualHelpers

/-! ## Part 4: Main Sub-Pin–Frankl Theorems -/

section MainTheorems

/-- **Exact Shitov (2019) General Cubic Upper Bound (`8257 / 49923 n³ + 3 n²`)**:
For every synchronizing DFA on `n ≥ 1` states, there exists a synchronizing word `w` with
`49923 * w.length ≤ 8257 * n ^ 3 + 149769 * n ^ 2` (`8257/49923 ≈ 0.165395 < 1/6 ≈ 0.166667`). -/
theorem sub_pin_frankl_shitov_bound {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧
      49923 * w.length ≤ 8257 * (Fintype.card Q) ^ 3 + 149769 * (Fintype.card Q) ^ 2 := by
  classical
  let n := Fintype.card Q
  have hn1 : 1 ≤ n := Fintype.card_pos
  -- Small n < 100: directly from verified Pin–Frankl (6 * L ≤ n^3)
  by_cases hsmall : n < 100
  · obtain ⟨w, hw, hpf⟩ := pin_frankl_bound A hSync
    refine ⟨w, hw, ?_⟩
    change 6 * w.length ≤ n ^ 3 - n at hpf
    have h6 : 6 * w.length ≤ n ^ 3 := le_trans hpf (Nat.sub_le _ _)
    have hn_le : n ≤ 99 := by omega
    -- 6 * 49923 * L ≤ 49923 * n^3 = 49542 * n^3 + 381 * n^3 ≤ 49542 * n^3 + 381 * 99 * n^2
    -- and 381 * 99 = 37719 ≤ 6 * 149769 = 898614
    nlinarith
  -- Main regime: n ≥ 100
  have hn100 : 100 ≤ n := by omega
  obtain ⟨w_opt, hw_opt_sync, hw_opt_len⟩ := exists_syncWord_len_minCorankLen A hSync
  refine ⟨w_opt, hw_opt_sync, ?_⟩
  rw [hw_opt_len]
  change 49923 * minCorankLen A hSync (n - 1) ≤ 8257 * n ^ 3 + 149769 * n ^ 2
  let k := (n - 2) / 2
  have hk_ge49 : 49 ≤ k := by omega
  have hk_2le : 2 * k + 2 ≤ n := by omega
  have hk_2ge : n ≤ 2 * k + 3 := by omega
  -- Case 0: every corank gap δ_j (j ≤ n - 2) is at most 2 * k
  by_cases hbig : ∃ j : ℕ, j ≤ n - 2 ∧ 2 * k < corankGap A hSync j
  swap
  · push Not at hbig
    have hlam_le : minCorankLen A hSync (n - 1) ≤ n ^ 2 := by
      rw [minCorankLen_eq_sum_range A hSync le_rfl]
      calc (∑ j ∈ Finset.range (n - 1), corankGap A hSync j)
          ≤ ∑ _j ∈ Finset.range (n - 1), (2 * k) := by
            refine Finset.sum_le_sum fun j hj => hbig j (by rw [Finset.mem_range] at hj; omega)
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
  -- Case 1: γ < ρ ⇒ ρ ≥ (2/5) n, pure Pin–Frankl gives ≤ (117/750) n³ < (8257/49923) n³!
  by_cases hρ_gt_γ : γ < ρ
  · have h5ρ : 2 * n ≤ 5 * ρ := by omega
    have htail : 6 * (∑ j ∈ Finset.Ico ρ (n - 1), corankGap A hSync j) ≤ n ^ 3 - ρ ^ 3 := by
      have hpf : (∑ j ∈ Finset.Ico ρ (n - 1), corankGap A hSync j) ≤
          ∑ j ∈ Finset.Ico ρ (n - 1), (j + 2).choose 2 := by
        refine Finset.sum_le_sum fun j hj => corankGap_le_pinFrankl A hSync
          (by rw [Finset.mem_Ico] at hj; omega)
      have h6 := Nat.mul_le_mul_left 6 hpf
      rw [six_mul_sum_Ico_choose_two (by omega : ρ ≤ n - 1)] at h6
      have htop : (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) ≤ n ^ 3 := by
        zify [hn1]; nlinarith
      have hbot : ρ ^ 3 ≤ ρ * (ρ + 1) * (ρ + 2) := by nlinarith
      omega
    have htele := minCorankLen_eq_add_sum_Ico A hSync (by omega : ρ ≤ n - 1) le_rfl
    have hρ_le_n : ρ ≤ n := by omega
    have hcub : ρ ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hρ_le_n 3
    have h5cub : (2 * n) ^ 3 ≤ (5 * ρ) ^ 3 := Nat.pow_le_pow_left h5ρ 3
    zify [hcub] at htail
    zify at h5cub hlam_ρ_le htele ⊢
    nlinarith
  -- Case 2: ρ ≤ γ — apply the Zero-Calculus Telescoping Rational Dual!
  · have hρ_le_γ : ρ ≤ γ := by omega
    let β := max ρ (n / 10)
    have hk1_le_n1 : k + 1 ≤ n - 1 := by omega
    -- Telescoping split: lam(n - 1) = lam(ρ) + S_mid + S_tail
    let S_mid := ∑ r ∈ Finset.Icc ρ k, corankGap A hSync r
    let S_tail := ∑ j ∈ Finset.Ico (k + 1) (n - 1), corankGap A hSync j
    have hdecomp : minCorankLen A hSync (n - 1) = minCorankLen A hSync ρ + S_mid + S_tail := by
      have h1 := minCorankLen_eq_add_sum_Ico A hSync (by omega : ρ ≤ k + 1) hk1_le_n1
      have h2 := minCorankLen_eq_add_sum_Ico A hSync hk1_le_n1 le_rfl
      have hIco_eq : Finset.Ico ρ (k + 1) = Finset.Icc ρ k := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
      rw [hIco_eq] at h1
      omega
    -- Tail bound: S_tail ≤ (7/48) n^3 (in ℚ)
    have hS_tail_q : (S_tail : ℚ) ≤ (7 / 48 : ℚ) * (n : ℚ) ^ 3 := by
      have hpf : S_tail ≤ ∑ j ∈ Finset.Ico (k + 1) (n - 1), (j + 2).choose 2 := by
        refine Finset.sum_le_sum fun j hj => corankGap_le_pinFrankl A hSync
          (by rw [Finset.mem_Ico] at hj; omega)
      have h6 := Nat.mul_le_mul_left 6 hpf
      rw [six_mul_sum_Ico_choose_two hk1_le_n1] at h6
      have htop : (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) ≤ n ^ 3 := by
        zify [hn1]; nlinarith
      have hbot : n ^ 3 ≤ 8 * ((k + 1) * ((k + 1) + 1) * ((k + 1) + 2)) :=
        eight_mul_cube_ge hn100 hk_2ge
      have h48 : 48 * S_tail ≤ 7 * n ^ 3 := by omega
      have hq : (48 : ℚ) * S_tail ≤ 7 * (n : ℚ) ^ 3 := by exact_mod_cast h48
      linarith
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
        Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hne => hB_disj i₁ hi₁ i₂ hi₂ hne)
      rw [← hcard_bi]
      have hsub : (Finset.Icc 1 k).biUnion B ⊆ Finset.range ρ := by
        intro j hj
        rw [Finset.mem_biUnion] at hj
        rcases hj with ⟨i, _, hji⟩
        exact (Finset.mem_filter.mp hji).1
      calc ((Finset.Icc 1 k).biUnion B).card
          ≤ (Finset.range ρ).card := Finset.card_le_card hsub
        _ = ρ := Finset.card_range ρ
    -- Both bounds on each δ_r (r ∈ Icc ρ k)
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
    -- Apply the standalone telescoping rational dual middle-sum bound
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    have hS_mid_q :
        (S_mid : ℚ) ≤
          ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
            (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) +
          2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) +
          ((k : ℚ) + 1) ^ 2 :=
      shitov_case2_mid_bound hn100 rfl rfl hρ_ge1 hρ_le_γ rfl hsum_s_le
        (fun r hr => corankGap_le_pinFrankl A hSync (by rw [Finset.mem_Icc] at hr; omega))
        hdelta_shitov
    have hlam_ρ_q : (minCorankLen A hSync ρ : ℚ) ≤ (n : ℚ) ^ 2 := by exact_mod_cast hlam_ρ_le
    have hdecomp_q : (minCorankLen A hSync (n - 1) : ℚ) =
        (minCorankLen A hSync ρ : ℚ) + (S_mid : ℚ) + (S_tail : ℚ) := by
      exact_mod_cast hdecomp
    have hasm := shitov_rounding_assembly hn100 rfl rfl hρ_le_γ rfl
    have hfinal_q : (minCorankLen A hSync (n - 1) : ℚ) ≤
        (8257 / 49923 : ℚ) * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 2 := by
      linarith only [hdecomp_q, hlam_ρ_q, hS_mid_q, hS_tail_q, hasm]
    have hmul_q : (49923 : ℚ) * (minCorankLen A hSync (n - 1) : ℚ) ≤
        8257 * (n : ℚ) ^ 3 + 149769 * (n : ℚ) ^ 2 := by
      linarith only [hfinal_q]
    exact_mod_cast hmul_q

/-- Clean rational corollary (`333 / 2000 = 0.16650 < 1/6`):
every synchronizing DFA on `n ≥ 1` states admits a synchronizing word `w` with
`2000 * w.length ≤ 333 * n ^ 3 + 6000 * n ^ 2`. -/
theorem sub_pin_frankl_333_2000 {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧
      2000 * w.length ≤ 333 * (Fintype.card Q) ^ 3 + 6000 * (Fintype.card Q) ^ 2 := by
  obtain ⟨w, hw, hsh⟩ := sub_pin_frankl_shitov_bound A hSync
  exact ⟨w, hw, by omega⟩

/-- Explicit threshold corollary: for EVERY synchronizing DFA on `n ≥ 2359` states,
there exists a synchronizing word strictly shorter than Pin–Frankl's `(n ^ 3 - n) / 6`. -/
theorem sub_pin_frankl_strictly_beats_pin_frankl {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing) (hn : 2359 ≤ Fintype.card Q) :
    ∃ w : List α, A.IsSyncWord w ∧
      6 * w.length < (Fintype.card Q) ^ 3 - Fintype.card Q ∧
      w.length < ((Fintype.card Q) ^ 3 - Fintype.card Q) / 6 := by
  obtain ⟨w, hw, hsh⟩ := sub_pin_frankl_shitov_bound A hSync
  have hn3 : Fintype.card Q ≤ (Fintype.card Q) ^ 3 := Nat.le_self_pow (by omega) _
  have hlt : 6 * (8257 * (Fintype.card Q) ^ 3 + 149769 * (Fintype.card Q) ^ 2) +
      49923 * Fintype.card Q < 49923 * (Fintype.card Q) ^ 3 := by
    have h1 : (2359 : ℕ) ≤ Fintype.card Q := hn
    nlinarith
  have h6lt : 6 * w.length < (Fintype.card Q) ^ 3 - Fintype.card Q := by omega
  refine ⟨w, hw, h6lt, ?_⟩
  have hdvd : 6 ∣ (Fintype.card Q) ^ 3 - Fintype.card Q := by
    have hprod : (Fintype.card Q - 1) * Fintype.card Q * (Fintype.card Q + 1) =
        (Fintype.card Q) ^ 3 - Fintype.card Q := by
      zify [show 1 ≤ Fintype.card Q by omega, hn3]
      ring
    rw [← hprod]
    have hsum := six_mul_sum_range_choose_two (Fintype.card Q - 1)
    have heq1 : Fintype.card Q - 1 + 1 = Fintype.card Q := by omega
    have heq2 : Fintype.card Q - 1 + 2 = Fintype.card Q + 1 := by omega
    rw [heq1, heq2] at hsum
    exact ⟨∑ r ∈ Finset.range (Fintype.card Q - 1), (r + 2).choose 2, hsum.symm⟩
  rcases hdvd with ⟨q, hq⟩
  rw [hq] at h6lt ⊢
  omega

/-- Asymptotic statement: there exists `N₀` such that for all `n ≥ N₀`, every synchronizing
`n`-state DFA admits a synchronizing word with `6 * w.length < n ^ 3 - n`. -/
theorem exists_sub_pin_frankl_threshold :
    ∃ N₀ : ℕ, ∀ {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v} (A : DFA Q α),
      N₀ ≤ Fintype.card Q → A.IsSynchronizing →
      ∃ w : List α, A.IsSyncWord w ∧ 6 * w.length < (Fintype.card Q) ^ 3 - Fintype.card Q :=
  ⟨2359, fun A hn hSync =>
    let ⟨w, hw, h6, _⟩ := sub_pin_frankl_strictly_beats_pin_frankl A hSync hn
    ⟨w, hw, h6⟩⟩

end MainTheorems

end Cerny
