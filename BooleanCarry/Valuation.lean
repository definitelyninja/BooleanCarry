/-
  2-adic valuation helpers for A and Nat.
-/

import BooleanCarry.Core

namespace BooleanCarry

/--
  2-adic valuation (trailing zeros in binary).
  Convention: `v2 0 = 0`.
-/
def v2 (n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 1 then 0
  else v2 (n / 2) + 1
termination_by n
decreasing_by
  simp_wf
  apply Nat.div_lt_self
  · exact Nat.pos_of_ne_zero (by assumption)
  · decide


/-- Odd ⇒ valuation 0. -/
theorem v2_of_odd (u : Nat) (hu : Odd u) : v2 u = 0 := by
  change u % 2 = 1 at hu
  rw [v2.eq_def]
  have hne : u ≠ 0 := by intro h; simp [h] at hu
  simp only [hne, ↓reduceIte, hu]


/-- Even positive ⇒ `v2 n = v2 (n/2) + 1`. -/
theorem v2_even (n : Nat) (he : n % 2 = 0) (hp : 0 < n) :
    v2 n = v2 (n / 2) + 1 := by
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hp
  have hnot : ¬ n % 2 = 1 := by omega
  rw [v2.eq_def]
  simp only [hne, ↓reduceIte, hnot]


/-- `v2 (2 * n) = v2 n + 1` for `n ≠ 0`. -/
theorem v2_mul_two (n : Nat) (hn : n ≠ 0) : v2 (2 * n) = v2 n + 1 := by
  have he : (2 * n) % 2 = 0 := by omega
  have hp : 0 < 2 * n := by omega
  have hdiv : 2 * n / 2 = n := by omega
  rw [v2_even (2 * n) he hp, hdiv]


/-- Odd `x` ⇒ `v2 (A x) ≥ 1`. -/
theorem v2_A_ge_one_of_odd (x : Nat) (hx : Odd x) : 1 ≤ v2 (A x) := by
  have he := A_even_of_odd x hx
  have hp := A_pos x
  rw [v2_even (A x) he hp]
  omega


private theorem two_pow_ne_zero (v : Nat) : 2 ^ v ≠ 0 := by
  induction v with
  | zero => decide
  | succ v ih =>
    rw [Nat.pow_succ]
    omega


/-- `v2 (2^v * u) = v` when `u` is odd and nonzero. -/
theorem v2_pow_mul_odd (v u : Nat) (hu : Odd u) (hup : u ≠ 0) :
    v2 (2 ^ v * u) = v := by
  induction v with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul]
    exact v2_of_odd u hu
  | succ v ih =>
    have hne : 2 ^ v * u ≠ 0 := by
      intro h
      rcases Nat.mul_eq_zero.mp h with hpow | hu0
      · exact two_pow_ne_zero v hpow
      · exact hup hu0
    have hrewrite : 2 ^ (v + 1) * u = 2 * (2 ^ v * u) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [hrewrite, v2_mul_two _ hne, ih]


/-! ### Factorization via v2 -/

theorem two_pow_dvd_of_v2 (n : Nat) (hn : n ≠ 0) : 2 ^ v2 n ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hodd : n % 2 = 1
    · have hv : v2 n = 0 := v2_of_odd n hodd
      rw [hv, Nat.pow_zero]
      exact ⟨n, by omega⟩
    · have he : n % 2 = 0 := by omega
      have hp : 0 < n := Nat.pos_of_ne_zero hn
      have hv : v2 n = v2 (n / 2) + 1 := v2_even n he hp
      have hne : n / 2 ≠ 0 := by
        intro hz
        rcases Nat.div_eq_zero_iff.mp hz with h2 | hlt
        · exact absurd h2 (by decide : 2 ≠ 0)
        · omega
      have ih' := ih (n / 2) (Nat.div_lt_self hp (by decide)) hne
      rw [hv, Nat.pow_succ]
      have hsplit : n = 2 * (n / 2) := by omega
      have hmul : 2 * 2 ^ v2 (n / 2) ∣ 2 * (n / 2) := Nat.mul_dvd_mul_left 2 ih'
      rw [Nat.mul_comm] at hmul
      rwa [← hsplit] at hmul

theorem eq_v2_mul_div (n : Nat) (hn : n ≠ 0) :
    n = 2 ^ v2 n * (n / 2 ^ v2 n) :=
  (Nat.mul_div_cancel' (two_pow_dvd_of_v2 n hn)).symm

theorem div_v2_odd (n : Nat) (hn : n ≠ 0) : Odd (n / 2 ^ v2 n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hodd : n % 2 = 1
    · have hv : v2 n = 0 := v2_of_odd n hodd
      simp [hv, Odd, hodd]
    · have he : n % 2 = 0 := by omega
      have hp : 0 < n := Nat.pos_of_ne_zero hn
      have hv : v2 n = v2 (n / 2) + 1 := v2_even n he hp
      have hne : n / 2 ≠ 0 := by
        intro hz
        rcases Nat.div_eq_zero_iff.mp hz with h2 | hlt
        · exact absurd h2 (by decide : 2 ≠ 0)
        · omega
      have ih' := ih (n / 2) (Nat.div_lt_self hp (by decide)) hne
      have hdiv : n / 2 ^ v2 n = (n / 2) / 2 ^ v2 (n / 2) := by
        rw [hv, Nat.pow_succ, Nat.mul_comm]
        exact (Nat.div_div_eq_div_mul n 2 (2 ^ v2 (n / 2))).symm
      rw [hdiv]; exact ih'

end BooleanCarry
