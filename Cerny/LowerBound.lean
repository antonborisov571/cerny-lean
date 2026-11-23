import Cerny.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

/-!
# Černý's Lower Bound Theorem (1964)

This file proves Černý's theorem for the extremal automaton family `cernyDFA n hn` (`n ≥ 2`):
* `cernyDFA_isSynchronizing`: `cernyDFA n hn` admits an explicit synchronizing word
  `cernySyncWord n` of length `(n - 1) ^ 2`.
* `cernyDFA_syncWord_length_ge`: every synchronizing word of `cernyDFA n hn` has length
  at least `(n - 1) ^ 2` (in fact `(n - 1) ^ 2 + q₀.val` if it resets to `q₀`), proved via
  the cyclic-interval potential `Φ(I(r, k)) = n * k - 1 - r`, `Φ(univ) = n * (n - 1)`.
* `cernyDFA_resetThreshold`: the exact reset threshold of `cernyDFA n hn` is `(n - 1) ^ 2`.
-/

namespace Cerny

section UpperBound

/-- One compression block `b^(n-1) a` (`false` repeated `n - 1` times, followed by `true`). -/
def cernyBlock (n : ℕ) : List Bool :=
  List.replicate (n - 1) false ++ [true]

/-- Repeated compression block `(b^(n-1) a)^k`. -/
def cernyIterBlock (n : ℕ) : ℕ → List Bool
  | 0 => []
  | k + 1 => cernyBlock n ++ cernyIterBlock n k

/-- Černý's explicit synchronizing word `a (b^(n-1) a)^(n-2)` of length `(n - 1) ^ 2`. -/
def cernySyncWord (n : ℕ) : List Bool :=
  true :: cernyIterBlock n (n - 2)

theorem cernyBlock_length (n : ℕ) (hn : 2 ≤ n) : (cernyBlock n).length = n := by
  simp [cernyBlock]
  omega

theorem cernyIterBlock_length (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    (cernyIterBlock n k).length = k * n := by
  induction k with
  | zero => simp [cernyIterBlock]
  | succ k ih =>
    simp [cernyIterBlock, cernyBlock_length n hn, ih]
    ring

theorem cernySyncWord_length (n : ℕ) (hn : 2 ≤ n) :
    (cernySyncWord n).length = (n - 1) ^ 2 := by
  simp only [cernySyncWord, List.length_cons, cernyIterBlock_length n hn]
  have h1 : n - 1 = (n - 2) + 1 := by omega
  have h2 : n = (n - 2) + 2 := by omega
  zify [hn, show 1 ≤ n by omega]
  ring

theorem cernyDFA_eval_block_val (n : ℕ) (hn : 2 ≤ n) (q : Fin n) :
    ((cernyDFA n hn).eval q (cernyBlock n)).val = q.val - 1 := by
  simp only [cernyBlock, DFA.eval_append, DFA.eval_replicate, DFA.eval_singleton,
    cernyDFA_step_true]
  have hrot : (((fun x => (cernyDFA n hn).step x false)^[n - 1] q)).val =
      (q.val + (n - 1)) % n :=
    cernyDFA_iterate_false n hn (n - 1) q
  have hq := q.isLt
  by_cases h0 : q.val = 0
  · have hval : (((fun x => (cernyDFA n hn).step x false)^[n - 1] q)).val = n - 1 := by
      rw [hrot, h0, zero_add, Nat.mod_eq_of_lt (by omega)]
    split_ifs
    simp [h0]
  · have hval : (((fun x => (cernyDFA n hn).step x false)^[n - 1] q)).val = q.val - 1 := by
      rw [hrot]
      have heq : q.val + (n - 1) = (q.val - 1) + n := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hne : (((fun x => (cernyDFA n hn).step x false)^[n - 1] q)).val ≠ n - 1 := by
      omega
    split_ifs with hc
    · exact absurd hc hne
    · exact hval

theorem cernyDFA_eval_iterBlock_val (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (q : Fin n) :
    ((cernyDFA n hn).eval q (cernyIterBlock n k)).val = q.val - k := by
  induction k generalizing q with
  | zero => simp [cernyIterBlock]
  | succ k ih =>
    rw [cernyIterBlock, DFA.eval_append, ih, cernyDFA_eval_block_val]
    omega

theorem cernyDFA_eval_syncWord (n : ℕ) (hn : 2 ≤ n) (q : Fin n) :
    (cernyDFA n hn).eval q (cernySyncWord n) = ⟨0, by omega⟩ := by
  ext
  rw [cernySyncWord, DFA.eval_cons, cernyDFA_eval_iterBlock_val, cernyDFA_step_true]
  have hq := q.isLt
  split_ifs with h
  · simp
  · dsimp
    omega

theorem cernyDFA_isSyncWord_cernySyncWord (n : ℕ) (hn : 2 ≤ n) :
    (cernyDFA n hn).IsSyncWord (cernySyncWord n) :=
  ⟨⟨0, by omega⟩, cernyDFA_eval_syncWord n hn⟩

theorem cernyDFA_isSynchronizing (n : ℕ) (hn : 2 ≤ n) :
    (cernyDFA n hn).IsSynchronizing :=
  ⟨cernySyncWord n, cernyDFA_isSyncWord_cernySyncWord n hn⟩

end UpperBound

section LowerBound

/-- Cyclic interval `I(r, k) = {(r + j) mod n : 0 ≤ j < k}` as a `Finset (Fin n)`. -/
def cycInt (n r k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun q : Fin n => (q.val + n - r) % n < k)

@[simp]
theorem mem_cycInt (n r k : ℕ) (q : Fin n) :
    q ∈ cycInt n r k ↔ (q.val + n - r) % n < k := by
  simp [cycInt]

theorem cycInt_ne_univ (n r k : ℕ) (hn : 2 ≤ n) (hr : r < n) (hk : k ≤ n - 1) :
    cycInt n r k ≠ Finset.univ := by
  intro heq
  let q : Fin n := ⟨(r + k) % n, Nat.mod_lt _ (by omega)⟩
  have hmem : q ∈ cycInt n r k := by
    rw [heq]
    exact Finset.mem_univ q
  rw [mem_cycInt] at hmem
  have hval : (q.val + n - r) % n = k := by
    change ((r + k) % n + n - r) % n = k
    by_cases hlt : r + k < n
    · rw [Nat.mod_eq_of_lt hlt]
      have : r + k + n - r = k + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have hmod : (r + k) % n = r + k - n := by
        have heq' : r + k = (r + k - n) + n := by omega
        conv_lhs => rw [heq']
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      have : r + k - n + n - r = k := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
  omega

theorem cycInt_singleton (n : ℕ) (hn : 2 ≤ n) (q₀ : Fin n) :
    cycInt n q₀.val 1 = {q₀} := by
  ext q
  simp only [mem_cycInt, Finset.mem_singleton]
  have hq := q.isLt
  have hq₀ := q₀.isLt
  constructor
  · intro hlt
    have h0 : (q.val + n - q₀.val) % n = 0 := by omega
    by_cases hle : q₀.val ≤ q.val
    · have : q.val + n - q₀.val = (q.val - q₀.val) + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h0
      ext
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h0
      omega
  · rintro rfl
    have : q.val + n - q.val = n := by omega
    rw [this, Nat.mod_self]
    omega

theorem preimage_cycInt_false (n : ℕ) (hn : 2 ≤ n) (r k : ℕ) (hr : r < n) :
    (cernyDFA n hn).preimage (cycInt n r k) [false] =
      cycInt n ((r + n - 1) % n) k := by
  ext q
  simp only [DFA.mem_preimage, DFA.eval_singleton, cernyDFA_step_false, mem_cycInt]
  have hq := q.isLt
  have hkey : ((q.val + 1) % n + n - r) % n = (q.val + n - (r + n - 1) % n) % n := by
    by_cases hr0 : r = 0
    · subst hr0
      have h1 : (0 + n - 1) % n = n - 1 := by
        rw [zero_add, Nat.mod_eq_of_lt (by omega)]
      rw [h1]
      by_cases hq' : q.val + 1 < n
      · rw [Nat.mod_eq_of_lt hq']
        have h2 : q.val + 1 + n - 0 = (q.val + 1) + n := by omega
        have h3 : q.val + n - (n - 1) = q.val + 1 := by omega
        rw [h2, Nat.add_mod_right, h3]
      · have hqn : q.val + 1 = n := by omega
        rw [hqn, Nat.mod_self]
        have h3 : q.val + n - (n - 1) = n := by omega
        rw [h3]
        simp
    · have h1 : (r + n - 1) % n = r - 1 := by
        have : r + n - 1 = (r - 1) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1]
      by_cases hq' : q.val + 1 < n
      · rw [Nat.mod_eq_of_lt hq']
        congr 1
        omega
      · have hqn : q.val + 1 = n := by omega
        rw [hqn, Nat.mod_self]
        have h2 : q.val + n - (r - 1) = (n - r) + n := by omega
        rw [h2, Nat.add_mod_right]
        simp
  rw [hkey]

/-- Cyclic-interval potential predicate: `S` is either `univ` with potential `n * (n - 1)`,
or a proper nonempty cyclic interval `I(r, k)` with potential `n * k - 1 - r`. -/
def HasCernyPotential (n : ℕ) (S : Finset (Fin n)) (P : ℕ) : Prop :=
  (S = Finset.univ ∧ P = n * (n - 1)) ∨
    ∃ r k : ℕ, r < n ∧ 1 ≤ k ∧ k ≤ n - 1 ∧ S = cycInt n r k ∧ P = n * k - 1 - r

theorem hasCernyPotential_step (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin n)) (P : ℕ)
    (x : Bool) (hP : HasCernyPotential n S P)
    (hne : ((cernyDFA n hn).preimage S [x]).Nonempty) :
    ∃ P' : ℕ, HasCernyPotential n ((cernyDFA n hn).preimage S [x]) P' ∧ P' ≤ P + 1 := by
  rcases hP with ⟨rfl, rfl⟩ | ⟨r, k, hr, hk1, hkn, rfl, rfl⟩
  · refine ⟨n * (n - 1), Or.inl ⟨by simp, rfl⟩, by omega⟩
  · cases x with
    | false =>
      rw [preimage_cycInt_false n hn r k hr]
      let r' := (r + n - 1) % n
      refine ⟨n * k - 1 - r', Or.inr ⟨r', k, Nat.mod_lt _ (by omega), hk1, hkn, rfl, rfl⟩, ?_⟩
      by_cases hr0 : r = 0
      · subst hr0
        have hr' : r' = n - 1 := by
          dsimp [r']
          rw [zero_add, Nat.mod_eq_of_lt (by omega)]
        rw [hr']
        omega
      · have hr' : r' = r - 1 := by
          dsimp [r']
          have : r + n - 1 = (r - 1) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hr']
        have hnk : n ≤ n * k := Nat.le_mul_of_pos_right n (by omega)
        omega
    | true =>
      by_cases hr0 : r = 0
      · subst hr0
        by_cases hkeq : k = n - 1
        · subst hkeq
          have huniv : (cernyDFA n hn).preimage (cycInt n 0 (n - 1)) [true] = Finset.univ := by
            ext q
            simp only [DFA.mem_preimage, DFA.eval_singleton, cernyDFA_step_true, mem_cycInt,
              Finset.mem_univ, iff_true]
            have hq := q.isLt
            split_ifs with hq'
            · simp
              omega
            · have : q.val + n - 0 = q.val + n := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hq]
              omega
          refine ⟨n * (n - 1), Or.inl ⟨huniv, rfl⟩, ?_⟩
          have hpos : 1 ≤ n * (n - 1) := by
            have : 1 * 1 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
            omega
          omega
        · have hpre : (cernyDFA n hn).preimage (cycInt n 0 k) [true] =
              cycInt n (n - 1) (k + 1) := by
            ext q
            simp only [DFA.mem_preimage, DFA.eval_singleton, cernyDFA_step_true, mem_cycInt]
            have hq := q.isLt
            split_ifs with hq'
            · have h1 : (0 + n - 0) % n = 0 := by simp
              have h2 : (q.val + n - (n - 1)) % n = 0 := by
                have : q.val + n - (n - 1) = n := by omega
                rw [this, Nat.mod_self]
              rw [h1, h2]
              omega
            · have h1 : (q.val + n - 0) % n = q.val := by
                have : q.val + n - 0 = q.val + n := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hq]
              have h2 : (q.val + n - (n - 1)) % n = q.val + 1 := by
                have : q.val + n - (n - 1) = q.val + 1 := by omega
                rw [this, Nat.mod_eq_of_lt (by omega)]
              rw [h1, h2]
              omega
          refine ⟨n * (k + 1) - 1 - (n - 1),
            Or.inr ⟨n - 1, k + 1, by omega, by omega, by omega, hpre, rfl⟩, ?_⟩
          have hnk : n ≤ n * k := Nat.le_mul_of_pos_right n (by omega)
          have hmul : n * (k + 1) = n * k + n := by ring
          omega
      · by_cases hrk : r + k = n
        · by_cases hkone : k = 1
          · exfalso
            rcases hne with ⟨q, hqmem⟩
            simp only [DFA.mem_preimage, DFA.eval_singleton, cernyDFA_step_true,
              mem_cycInt] at hqmem
            have hq := q.isLt
            split_ifs at hqmem with hq'
            · have : (0 + n - r) % n = n - r := by
                rw [zero_add, Nat.mod_eq_of_lt (by omega)]
              rw [this] at hqmem
              omega
            · have : (q.val + n - r) % n = q.val + 1 := by
                have heq : q.val + n - r = q.val + 1 := by omega
                rw [heq, Nat.mod_eq_of_lt (by omega)]
              rw [this] at hqmem
              omega
          · have hpre : (cernyDFA n hn).preimage (cycInt n r k) [true] = cycInt n r (k - 1) := by
              ext q
              simp only [DFA.mem_preimage, DFA.eval_singleton, cernyDFA_step_true, mem_cycInt]
              have hq := q.isLt
              split_ifs with hq'
              · have h1 : (0 + n - r) % n = k := by
                  have : 0 + n - r = k := by omega
                  rw [this, Nat.mod_eq_of_lt (by omega)]
                have h2 : (q.val + n - r) % n = k - 1 := by
                  have : q.val + n - r = (k - 1) + n := by omega
                  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                rw [h1, h2]
                omega
              · by_cases hle : r ≤ q.val
                · have hmod : (q.val + n - r) % n = q.val - r := by
                    have : q.val + n - r = (q.val - r) + n := by omega
                    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                  rw [hmod]
                  omega
                · have hmod : (q.val + n - r) % n = q.val + k := by
                    have : q.val + n - r = q.val + k := by omega
                    rw [this, Nat.mod_eq_of_lt (by omega)]
                  rw [hmod]
                  omega
            refine ⟨n * (k - 1) - 1 - r,
              Or.inr ⟨r, k - 1, hr, by omega, by omega, hpre, rfl⟩, ?_⟩
            have hle : n * (k - 1) ≤ n * k := Nat.mul_le_mul_left n (by omega)
            omega
        · have hpre : (cernyDFA n hn).preimage (cycInt n r k) [true] = cycInt n r k := by
            ext q
            simp only [DFA.mem_preimage, DFA.eval_singleton, cernyDFA_step_true, mem_cycInt]
            have hq := q.isLt
            split_ifs with hq'
            · have h1 : (0 + n - r) % n = n - r := by
                rw [zero_add, Nat.mod_eq_of_lt (by omega)]
              have h2 : (q.val + n - r) % n = n - 1 - r := by
                have : q.val + n - r = (n - 1 - r) + n := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              rw [h1, h2]
              omega
            · rfl
          exact ⟨n * k - 1 - r, Or.inr ⟨r, k, hr, hk1, hkn, hpre, rfl⟩, by omega⟩

theorem hasCernyPotential_word (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin n)) (P : ℕ)
    (w : List Bool) (hP : HasCernyPotential n S P)
    (hne : ((cernyDFA n hn).preimage S w).Nonempty) :
    ∃ P' : ℕ, HasCernyPotential n ((cernyDFA n hn).preimage S w) P' ∧ P' ≤ P + w.length := by
  induction w with
  | nil =>
    exact ⟨P, by simpa using hP, by simp⟩
  | cons x w ih =>
    rw [DFA.preimage_cons] at hne ⊢
    have hne_w : ((cernyDFA n hn).preimage S w).Nonempty := by
      rcases hne with ⟨q, hq⟩
      rw [DFA.mem_preimage, DFA.eval_singleton] at hq
      exact ⟨(cernyDFA n hn).step q x, hq⟩
    obtain ⟨P₁, hP₁, hle₁⟩ := ih hne_w
    obtain ⟨P₂, hP₂, hle₂⟩ := hasCernyPotential_step n hn _ P₁ x hP₁ hne
    exact ⟨P₂, hP₂, by simp only [List.length_cons]; omega⟩

/-- Sharp lower bound: every word resetting `cernyDFA n hn` to `q₀` has length
at least `(n - 1) ^ 2 + q₀.val`. -/
theorem cernyDFA_syncWord_length_ge_add (n : ℕ) (hn : 2 ≤ n) (w : List Bool) (q₀ : Fin n)
    (hw : ∀ q : Fin n, (cernyDFA n hn).eval q w = q₀) :
    (n - 1) ^ 2 + q₀.val ≤ w.length := by
  have hpre : (cernyDFA n hn).preimage {q₀} w = Finset.univ := by
    ext q
    simp [hw q]
  have hP0 : HasCernyPotential n {q₀} (n - 1 - q₀.val) := by
    refine Or.inr ⟨q₀.val, 1, q₀.isLt, le_rfl, by omega, (cycInt_singleton n hn q₀).symm, ?_⟩
    simp
  have hne : ((cernyDFA n hn).preimage {q₀} w).Nonempty := by
    rw [hpre]
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨P', hP', hle⟩ := hasCernyPotential_word n hn {q₀} (n - 1 - q₀.val) w hP0 hne
  rw [hpre] at hP'
  have hP'eq : P' = n * (n - 1) := by
    rcases hP' with ⟨_, h⟩ | ⟨r, k, hr, _, hkn, huniv, _⟩
    · exact h
    · exact absurd huniv.symm (cycInt_ne_univ n r k hn hr hkn)
  rw [hP'eq] at hle
  have hq₀ := q₀.isLt
  zify [hn, show 1 ≤ n by omega, show q₀.val ≤ n - 1 by omega] at hle ⊢
  nlinarith

/-- Černý's Lower Bound (1964): every synchronizing word of `cernyDFA n hn` has length
at least `(n - 1) ^ 2`. -/
theorem cernyDFA_syncWord_length_ge (n : ℕ) (hn : 2 ≤ n) (w : List Bool)
    (hw : (cernyDFA n hn).IsSyncWord w) : (n - 1) ^ 2 ≤ w.length := by
  rcases hw with ⟨q₀, hq₀⟩
  exact le_trans (Nat.le_add_right _ _) (cernyDFA_syncWord_length_ge_add n hn w q₀ hq₀)

/-- Černý's Theorem (1964): the reset threshold of `cernyDFA n hn` is exactly `(n - 1) ^ 2`. -/
theorem cernyDFA_resetThreshold (n : ℕ) (hn : 2 ≤ n) :
    (cernyDFA n hn).resetThreshold (cernyDFA_isSynchronizing n hn) = (n - 1) ^ 2 := by
  apply le_antisymm
  · calc
      (cernyDFA n hn).resetThreshold (cernyDFA_isSynchronizing n hn)
          ≤ (cernySyncWord n).length :=
        DFA.resetThreshold_le_of_isSyncWord _ _ (cernyDFA_isSyncWord_cernySyncWord n hn)
      _ = (n - 1) ^ 2 := cernySyncWord_length n hn
  · rw [DFA.le_resetThreshold_iff]
    exact cernyDFA_syncWord_length_ge n hn

end LowerBound

end Cerny
