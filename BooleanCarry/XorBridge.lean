/-
  XOR bit-flip bridge: flipBit ↔ ± 2^s and A under flip.
-/

import BooleanCarry.Core

namespace BooleanCarry

/-! ### XOR bridge: flipBit ↔ ± 2^s (no sorry) -/

/-- AND with a pure power of two. -/
theorem and_two_pow (x s : Nat) :
    x &&& 2 ^ s = if x.testBit s then 2 ^ s else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  cases hbit : x.testBit s
  · show (x.testBit i && decide (s = i)) = (0 : Nat).testBit i
    by_cases hi : s = i
    · subst hi; simp [hbit]
    · simp [hi]
  · show (x.testBit i && decide (s = i)) = (2 ^ s).testBit i
    by_cases hi : s = i
    · subst hi; simp [hbit]
    · simp [hi]

/-- Disjoint bits ⇒ XOR equals OR. -/
theorem xor_eq_or_of_and_eq_zero (x y : Nat) (h : x &&& y = 0) :
    x ^^^ y = x ||| y := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hand : (x.testBit i && y.testBit i) = false := by
    have := congrArg (fun z => z.testBit i) h
    simpa [Nat.testBit_and] using this
  rw [Nat.testBit_xor, Nat.testBit_or]
  cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all

/-- Bit `s` clear ⇒ `x % 2^{s+1} = x % 2^s`. -/
theorem mod_two_pow_succ_eq_of_not_testBit (x s : Nat) (h : x.testBit s = false) :
    x % 2 ^ (s + 1) = x % 2 ^ s := by
  have he : x / 2 ^ s % 2 = 0 := by
    simpa [Nat.testBit_eq_decide_div_mod_eq] using h
  have heq : x / 2 ^ s = 2 * (x / 2 ^ s / 2) := by omega
  have hr : x % 2 ^ s < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hlt : x % 2 ^ s < 2 ^ (s + 1) :=
    Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : s ≤ s + 1))
  have hx : x % 2 ^ s + 2 ^ (s + 1) * (x / 2 ^ s / 2) = x := by
    have hpow : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [Nat.pow_succ]; ac_rfl
    have : 2 ^ (s + 1) * (x / 2 ^ s / 2) = 2 ^ s * (x / 2 ^ s) := by
      calc
        2 ^ (s + 1) * (x / 2 ^ s / 2) = (2 * 2 ^ s) * (x / 2 ^ s / 2) := by rw [hpow]
        _ = 2 ^ s * (2 * (x / 2 ^ s / 2)) := by
          rw [Nat.mul_comm 2 (2 ^ s), Nat.mul_assoc]
        _ = 2 ^ s * (x / 2 ^ s) := by rw [← heq]
    calc
      x % 2 ^ s + 2 ^ (s + 1) * (x / 2 ^ s / 2)
          = x % 2 ^ s + 2 ^ s * (x / 2 ^ s) := by rw [this]
      _ = 2 ^ s * (x / 2 ^ s) + x % 2 ^ s := by ac_rfl
      _ = x := Nat.div_add_mod x (2 ^ s)
  have huniq := (Nat.div_mod_unique (b := 2 ^ (s + 1)) (Nat.two_pow_pos (s + 1))).mpr
    ⟨hx, hlt⟩
  exact huniq.2

/-- When bit `s` is clear, `x ||| 2^s = x + 2^s`. -/
theorem or_two_pow_eq_add_of_not_testBit (x s : Nat) (h : x.testBit s = false) :
    x ||| 2 ^ s = x + 2 ^ s := by
  let q := x / 2 ^ (s + 1)
  let r := x % 2 ^ s
  have hr : r < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hx : x = 2 ^ (s + 1) * q + r := by
    have hmod := mod_two_pow_succ_eq_of_not_testBit x s h
    have hsplit := Nat.div_add_mod x (2 ^ (s + 1))
    calc
      x = 2 ^ (s + 1) * (x / 2 ^ (s + 1)) + x % 2 ^ (s + 1) := hsplit.symm
      _ = 2 ^ (s + 1) * q + r := by
          change 2 ^ (s + 1) * (x / 2 ^ (s + 1)) + x % 2 ^ (s + 1) =
            2 ^ (s + 1) * (x / 2 ^ (s + 1)) + x % 2 ^ s
          rw [hmod]
  have hr' : r + 2 ^ s < 2 ^ (s + 1) := by
    change x % 2 ^ s + 2 ^ s < 2 ^ (s + 1)
    have : x % 2 ^ s < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [Nat.pow_succ]; omega
  have hor : r ||| 2 ^ s = r + 2 ^ s := Nat.or_two_pow_eq_add_of_lt hr
  have hbig : 2 ^ (s + 1) * q ||| (r + 2 ^ s) = 2 ^ (s + 1) * q + (r + 2 ^ s) :=
    (Nat.two_pow_add_eq_or_of_lt (i := s + 1) hr' q).symm
  have hr2 : r < 2 ^ (s + 1) :=
    Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : s ≤ s + 1))
  have hx_or : x = 2 ^ (s + 1) * q ||| r := by
    rw [hx]
    exact Nat.two_pow_add_eq_or_of_lt (i := s + 1) hr2 q
  calc
    x ||| 2 ^ s = (2 ^ (s + 1) * q ||| r) ||| 2 ^ s := by rw [hx_or]
    _ = 2 ^ (s + 1) * q ||| (r ||| 2 ^ s) := by rw [Nat.or_assoc]
    _ = 2 ^ (s + 1) * q ||| (r + 2 ^ s) := by rw [hor]
    _ = 2 ^ (s + 1) * q + (r + 2 ^ s) := hbig
    _ = x + 2 ^ s := by rw [hx]; omega

/-- When bit `s` is clear, XOR with `2^s` equals add. -/
theorem flipBit_eq_add_of_not_testBit (x s : Nat) (h : x.testBit s = false) :
    flipBit x s = x + 2 ^ s := by
  have hflip : flipBit x s = x ^^^ 2 ^ s := by
    simp [flipBit, one_shiftLeft_eq_pow]
  rw [hflip]
  have hand : x &&& 2 ^ s = 0 := by
    rw [and_two_pow]; simp [h]
  rw [xor_eq_or_of_and_eq_zero x (2 ^ s) hand]
  exact or_two_pow_eq_add_of_not_testBit x s h

/-- When bit `s` is set, XOR with `2^s` equals subtract. -/
theorem flipBit_eq_sub_of_testBit (x s : Nat) (h : x.testBit s = true) :
    flipBit x s = x - 2 ^ s := by
  have hle : 2 ^ s ≤ x := Nat.ge_two_pow_of_testBit h
  have hy_bit : (x - 2 ^ s).testBit s = false := by
    have hadd : (x - 2 ^ s) + 2 ^ s = x := Nat.sub_add_cancel hle
    have htb := Nat.testBit_two_pow_add_eq (x - 2 ^ s) s
    rw [Nat.add_comm] at htb
    rw [hadd] at htb
    cases hy : (x - 2 ^ s).testBit s
    · rfl
    · simp [h, hy] at htb
  have hy_add : flipBit (x - 2 ^ s) s = x := by
    rw [flipBit_eq_add_of_not_testBit _ s hy_bit, Nat.sub_add_cancel hle]
  calc
    flipBit x s = flipBit (flipBit (x - 2 ^ s) s) s := by rw [hy_add]
    _ = x - 2 ^ s := by
      simp [flipBit, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- `A` after clearing-bit flip: add `3·2^s`. -/
theorem A_flipBit_of_bit_false (x s : Nat) (h : x.testBit s = false) :
    A (flipBit x s) = A x + 3 * 2 ^ s := by
  rw [flipBit_eq_add_of_not_testBit x s h]
  change 3 * (x + 2 ^ s) + 1 = 3 * x + 1 + 3 * 2 ^ s
  omega

/-- `A` after setting-bit flip: subtract `3·2^s`. -/
theorem A_flipBit_of_bit_true (x s : Nat) (h : x.testBit s = true) :
    A (flipBit x s) + 3 * 2 ^ s = A x := by
  have hle : 2 ^ s ≤ x := Nat.ge_two_pow_of_testBit h
  rw [flipBit_eq_sub_of_testBit x s h]
  change 3 * (x - 2 ^ s) + 1 + 3 * 2 ^ s = 3 * x + 1
  omega

end BooleanCarry
