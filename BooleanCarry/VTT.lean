/-
  Valuation Transition Theorem (full Lean proof).
-/

import BooleanCarry.Core
import BooleanCarry.Valuation
import BooleanCarry.XorBridge

namespace BooleanCarry

/-! ### Additive factor cases -/

theorem vtt_high_add (v u s : Nat) (hu : Odd u) (_hup : u ≠ 0) (hs : v < s) :
    v2 (2 ^ v * u + 3 * 2 ^ s) = v := by
  have hpow : 2 ^ s = 2 ^ v * 2 ^ (s - v) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hs)]
  have hfactor : 2 ^ v * u + 3 * 2 ^ s = 2 ^ v * (u + 3 * 2 ^ (s - v)) := by
    calc
      2 ^ v * u + 3 * 2 ^ s
          = 2 ^ v * u + 3 * (2 ^ v * 2 ^ (s - v)) := by rw [hpow]
      _ = 2 ^ v * u + 2 ^ v * (3 * 2 ^ (s - v)) := by
          rw [← Nat.mul_assoc 3, Nat.mul_comm 3 (2 ^ v), Nat.mul_assoc]
      _ = 2 ^ v * (u + 3 * 2 ^ (s - v)) := by rw [← Nat.mul_add]
  have hk : 1 ≤ s - v := Nat.sub_pos_of_lt hs
  have hodd : Odd (u + 3 * 2 ^ (s - v)) := by
    have : u + 3 * 2 ^ (s - v) = u + 2 ^ (s - v) * 3 := by rw [Nat.mul_comm]
    rw [this]
    exact odd_add_mul_pow_two u (s - v) 3 hu hk
  have hne : u + 3 * 2 ^ (s - v) ≠ 0 := by
    intro hz
    have : 0 < u := by change u % 2 = 1 at hu; omega
    omega
  rw [hfactor, v2_pow_mul_odd v _ hodd hne]

theorem vtt_low_add (v u s : Nat) (hu : Odd u) (_hup : u ≠ 0) (hs : s < v) :
    v2 (2 ^ v * u + 3 * 2 ^ s) = s := by
  have hpow : 2 ^ v = 2 ^ s * 2 ^ (v - s) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hs)]
  have hfactor : 2 ^ v * u + 3 * 2 ^ s = 2 ^ s * (u * 2 ^ (v - s) + 3) := by
    calc
      2 ^ v * u + 3 * 2 ^ s
          = (2 ^ s * 2 ^ (v - s)) * u + 3 * 2 ^ s := by rw [hpow]
      _ = 2 ^ s * (2 ^ (v - s) * u) + 2 ^ s * 3 := by
          rw [Nat.mul_assoc, Nat.mul_comm 3 (2 ^ s)]
      _ = 2 ^ s * (2 ^ (v - s) * u + 3) := by rw [← Nat.mul_add]
      _ = 2 ^ s * (u * 2 ^ (v - s) + 3) := by rw [Nat.mul_comm (2 ^ (v - s)) u]
  have hodd : Odd (u * 2 ^ (v - s) + 3) := by
    change u % 2 = 1 at hu
    change (u * 2 ^ (v - s) + 3) % 2 = 1
    have h2 : (2 ^ (v - s)) % 2 = 0 := by
      have hk : 1 ≤ v - s := Nat.sub_pos_of_lt hs
      match h : v - s with
      | 0 => omega
      | k + 1 => rw [Nat.pow_succ]; omega
    have heven : (u * 2 ^ (v - s)) % 2 = 0 := by rw [Nat.mul_mod, h2]; simp
    omega
  have hne : u * 2 ^ (v - s) + 3 ≠ 0 := by omega
  rw [hfactor, v2_pow_mul_odd s _ hodd hne]

theorem vtt_res_add (v u : Nat) (hu : Odd u) (_hup : u ≠ 0) :
    v + 1 ≤ v2 (2 ^ v * u + 3 * 2 ^ v) := by
  have hfactor : 2 ^ v * u + 3 * 2 ^ v = 2 ^ v * (u + 3) := by
    calc
      2 ^ v * u + 3 * 2 ^ v = 2 ^ v * u + 2 ^ v * 3 := by rw [Nat.mul_comm 3]
      _ = 2 ^ v * (u + 3) := by rw [← Nat.mul_add]
  have heven : (u + 3) % 2 = 0 := odd_add_three_even u hu
  obtain ⟨m, hm⟩ : ∃ m, u + 3 = 2 * m := ⟨(u + 3) / 2, by omega⟩
  have hmpos : m ≠ 0 := by
    have : 0 < u := by change u % 2 = 1 at hu; omega
    omega
  rw [hfactor, hm]
  have hrewrite : 2 ^ v * (2 * m) = 2 ^ (v + 1) * m := by
    calc
      2 ^ v * (2 * m) = (2 ^ v * 2) * m := by rw [Nat.mul_assoc]
      _ = 2 ^ (v + 1) * m := by rw [← Nat.pow_succ]
  rw [hrewrite]
  have two_pow_ne : ∀ k, 2 ^ k ≠ 0 := by
    intro k; induction k with
    | zero => decide
    | succ k ih => rw [Nat.pow_succ]; omega
  have hge : ∀ k, k ≤ v2 (2 ^ k * m) := by
    intro k; induction k with
    | zero => omega
    | succ k ih =>
      have hne : 2 ^ k * m ≠ 0 := by
        intro h
        rcases Nat.mul_eq_zero.mp h with hp | hm0
        · exact two_pow_ne k hp
        · exact hmpos hm0
      have : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
        calc
          2 ^ (k + 1) * m = (2 ^ k * 2) * m := by rw [Nat.pow_succ]
          _ = 2 * (2 ^ k * m) := by rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
      rw [this, v2_mul_two _ hne]; omega
  exact hge (v + 1)

/-! ### Subtractive factor cases -/

theorem vtt_high_sub (v u s : Nat) (hu : Odd u) (_hup : u ≠ 0) (hs : v < s)
    (hle : 3 * 2 ^ s ≤ 2 ^ v * u) :
    v2 (2 ^ v * u - 3 * 2 ^ s) = v := by
  have hpow : 2 ^ s = 2 ^ v * 2 ^ (s - v) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hs)]
  have h3 : 3 * 2 ^ s = 2 ^ v * (3 * 2 ^ (s - v)) := by
    rw [hpow, Nat.mul_left_comm 3]
  have hle_u : 3 * 2 ^ (s - v) ≤ u := by
    have hpos : 0 < 2 ^ v := Nat.two_pow_pos _
    have : 2 ^ v * (3 * 2 ^ (s - v)) ≤ 2 ^ v * u := by
      calc
        2 ^ v * (3 * 2 ^ (s - v)) = 3 * 2 ^ s := by rw [h3]
        _ ≤ 2 ^ v * u := hle
    exact Nat.le_of_mul_le_mul_left this hpos
  have hfactor : 2 ^ v * u - 3 * 2 ^ s = 2 ^ v * (u - 3 * 2 ^ (s - v)) := by
    rw [h3, ← Nat.mul_sub_left_distrib]
  have hk : 1 ≤ s - v := Nat.sub_pos_of_lt hs
  have hodd : Odd (u - 3 * 2 ^ (s - v)) := by
    change u % 2 = 1 at hu
    change (u - 3 * 2 ^ (s - v)) % 2 = 1
    have heven : (3 * 2 ^ (s - v)) % 2 = 0 := by
      have hk' : 1 ≤ s - v := hk
      have h2 : (2 ^ (s - v)) % 2 = 0 := by
        cases hkv : s - v with
        | zero => omega
        | succ k => rw [Nat.pow_succ]; omega
      rw [Nat.mul_mod, h2]
    omega
  have hne : u - 3 * 2 ^ (s - v) ≠ 0 := by
    intro hz
    have hodd' : (u - 3 * 2 ^ (s - v)) % 2 = 1 := hodd
    simp [hz] at hodd'
  rw [hfactor, v2_pow_mul_odd v _ hodd hne]

theorem vtt_low_sub (v u s : Nat) (hu : Odd u) (_hup : u ≠ 0) (hs : s < v)
    (hle : 3 * 2 ^ s ≤ 2 ^ v * u) :
    v2 (2 ^ v * u - 3 * 2 ^ s) = s := by
  have hpow : 2 ^ v = 2 ^ s * 2 ^ (v - s) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hs)]
  have hAu : 2 ^ v * u = 2 ^ s * (u * 2 ^ (v - s)) := by
    calc
      2 ^ v * u = 2 ^ s * 2 ^ (v - s) * u := by rw [hpow]
      _ = 2 ^ s * (2 ^ (v - s) * u) := by rw [Nat.mul_assoc]
      _ = 2 ^ s * (u * 2 ^ (v - s)) := by rw [Nat.mul_comm (2 ^ (v - s)) u]
  have hle' : 3 ≤ u * 2 ^ (v - s) := by
    have hpos : 0 < 2 ^ s := Nat.two_pow_pos _
    have : 2 ^ s * 3 ≤ 2 ^ s * (u * 2 ^ (v - s)) := by
      calc
        2 ^ s * 3 = 3 * 2 ^ s := by rw [Nat.mul_comm]
        _ ≤ 2 ^ v * u := hle
        _ = 2 ^ s * (u * 2 ^ (v - s)) := hAu
    exact Nat.le_of_mul_le_mul_left this hpos
  have hfactor : 2 ^ v * u - 3 * 2 ^ s = 2 ^ s * (u * 2 ^ (v - s) - 3) := by
    rw [hAu, show 3 * 2 ^ s = 2 ^ s * 3 from Nat.mul_comm _ _]
    exact (Nat.mul_sub_left_distrib (2 ^ s) (u * 2 ^ (v - s)) 3).symm
  have hodd : Odd (u * 2 ^ (v - s) - 3) := by
    change u % 2 = 1 at hu
    change (u * 2 ^ (v - s) - 3) % 2 = 1
    have heven : (u * 2 ^ (v - s)) % 2 = 0 := by
      have h2 : (2 ^ (v - s)) % 2 = 0 := by
        match h : v - s with
        | 0 => omega
        | k + 1 => rw [Nat.pow_succ]; omega
      rw [Nat.mul_mod, h2]; simp
    omega
  have hne : u * 2 ^ (v - s) - 3 ≠ 0 := by
    intro hz
    change (u * 2 ^ (v - s) - 3) % 2 = 1 at hodd
    simp [hz] at hodd
  rw [hfactor, v2_pow_mul_odd s _ hodd hne]

theorem vtt_res_sub (v u : Nat) (hu : Odd u) (_hup : u ≠ 0)
    (_hle_u : 3 ≤ u) (hgt : 3 < u) :
    v + 1 ≤ v2 (2 ^ v * u - 3 * 2 ^ v) := by
  have hfactor : 2 ^ v * u - 3 * 2 ^ v = 2 ^ v * (u - 3) := by
    rw [show 3 * 2 ^ v = 2 ^ v * 3 from Nat.mul_comm _ _, ← Nat.mul_sub_left_distrib]
  obtain ⟨m, hm⟩ : ∃ m, u - 3 = 2 * m := by
    have heven : (u - 3) % 2 = 0 := by change u % 2 = 1 at hu; omega
    exact ⟨(u - 3) / 2, by omega⟩
  have hmpos : m ≠ 0 := by intro hz; omega
  rw [hfactor, hm]
  have hrewrite : 2 ^ v * (2 * m) = 2 ^ (v + 1) * m := by
    calc
      2 ^ v * (2 * m) = (2 ^ v * 2) * m := by rw [Nat.mul_assoc]
      _ = 2 ^ (v + 1) * m := by rw [← Nat.pow_succ]
  rw [hrewrite]
  have two_pow_ne : ∀ k, 2 ^ k ≠ 0 := by
    intro k; induction k with
    | zero => decide
    | succ k ih => rw [Nat.pow_succ]; omega
  have hge : ∀ k, k ≤ v2 (2 ^ k * m) := by
    intro k; induction k with
    | zero => omega
    | succ k ih =>
      have hne : 2 ^ k * m ≠ 0 := by
        intro h
        rcases Nat.mul_eq_zero.mp h with hp | hm0
        · exact two_pow_ne k hp
        · exact hmpos hm0
      have : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
        calc
          2 ^ (k + 1) * m = (2 ^ k * 2) * m := by rw [Nat.pow_succ]
          _ = 2 * (2 ^ k * m) := by rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
      rw [this, v2_mul_two _ hne]; omega
  exact hge (v + 1)

/-! ### Main theorem -/

theorem valuation_transition (x s : Nat) (_hx : Odd x) (_hs : 0 < s) :
    (v2 (A x) < s → v2 (A (flipBit x s)) = v2 (A x)) ∧
    (s < v2 (A x) → v2 (A (flipBit x s)) = s) ∧
    (s = v2 (A x) → v2 (A x) + 1 ≤ v2 (A (flipBit x s))) := by
  -- Freeze valuation and odd part
  let v := v2 (A x)
  let u := A x / 2 ^ v
  have hv : v2 (A x) = v := rfl
  have hAne : A x ≠ 0 := Nat.pos_iff_ne_zero.mp (A_pos x)
  have hAu : A x = 2 ^ v * u := by
    simpa [v, u] using eq_v2_mul_div (A x) hAne
  have hu : Odd u := by
    simpa [v, u] using div_v2_odd (A x) hAne
  have hup : u ≠ 0 := by
    intro h0
    have : Odd u := hu
    simp [Odd, h0] at this
  -- Restate goals with v
  change
    (v < s → v2 (A (flipBit x s)) = v) ∧
    (s < v → v2 (A (flipBit x s)) = s) ∧
    (s = v → v + 1 ≤ v2 (A (flipBit x s)))
  refine ⟨?high, ?low, ?res⟩
  · intro hvs
    cases hbit : x.testBit s
    · have hA' := A_flipBit_of_bit_false x s hbit
      rw [hA', hAu]
      exact vtt_high_add v u s hu hup hvs
    · have hAeq := A_flipBit_of_bit_true x s hbit
      have hle : 3 * 2 ^ s ≤ A x := by omega
      have hA' : A (flipBit x s) = A x - 3 * 2 ^ s := by omega
      have hle' : 3 * 2 ^ s ≤ 2 ^ v * u := by rwa [← hAu]
      rw [hA', hAu]
      exact vtt_high_sub v u s hu hup hvs hle'
  · intro hsv
    cases hbit : x.testBit s
    · have hA' := A_flipBit_of_bit_false x s hbit
      rw [hA', hAu]
      exact vtt_low_add v u s hu hup hsv
    · have hAeq := A_flipBit_of_bit_true x s hbit
      have hle : 3 * 2 ^ s ≤ A x := by omega
      have hA' : A (flipBit x s) = A x - 3 * 2 ^ s := by omega
      have hle' : 3 * 2 ^ s ≤ 2 ^ v * u := by rwa [← hAu]
      rw [hA', hAu]
      exact vtt_low_sub v u s hu hup hsv hle'
  · intro hsv
    cases hbit : x.testBit s
    · have hA' := A_flipBit_of_bit_false x s hbit
      have h1 := vtt_res_add v u hu hup
      rw [hA', hAu, hsv]
      exact h1
    · have hAeq := A_flipBit_of_bit_true x s hbit
      have hle : 3 * 2 ^ s ≤ A x := by omega
      have hA' : A (flipBit x s) = A x - 3 * 2 ^ s := by omega
      have hA'pos : 0 < A (flipBit x s) := A_pos (flipBit x s)
      have hle_u : 3 ≤ u := by
        have hpos : 0 < 2 ^ v := Nat.two_pow_pos _
        have : 2 ^ v * 3 ≤ 2 ^ v * u := by
          calc
            2 ^ v * 3 = 3 * 2 ^ v := by rw [Nat.mul_comm]
            _ = 3 * 2 ^ s := by rw [hsv]
            _ ≤ A x := hle
            _ = 2 ^ v * u := hAu
        exact Nat.le_of_mul_le_mul_left this hpos
      have hgt : 3 < u := by
        have hfac : A (flipBit x s) = 2 ^ v * (u - 3) := by
          have : A (flipBit x s) = 2 ^ v * u - 3 * 2 ^ v := by
            rw [hA', hAu, hsv]
          rw [this, show 3 * 2 ^ v = 2 ^ v * 3 from Nat.mul_comm _ _]
          exact (Nat.mul_sub_left_distrib (2 ^ v) u 3).symm
        have : 0 < 2 ^ v * (u - 3) := by rwa [← hfac]
        have hpos : 0 < 2 ^ v := Nat.two_pow_pos _
        have hsub : u - 3 ≠ 0 := by
          intro h0
          simp [h0] at this
        omega
      have h1 := vtt_res_sub v u hu hup hle_u hgt
      rw [hA', hAu, hsv]
      exact h1

end BooleanCarry
