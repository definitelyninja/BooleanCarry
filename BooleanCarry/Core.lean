/-
  Core definitions: A, Odd, flipBit.
-/

namespace BooleanCarry


/-- Affine map: A(x) = 3x + 1. -/
def A (x : Nat) : Nat := 3 * x + 1


/-- Flip bit `s` of `x` (XOR with `2^s`). -/
def flipBit (x s : Nat) : Nat := x ^^^ (1 <<< s)


/-- Odd natural numbers. -/
def Odd (x : Nat) : Prop := x % 2 = 1


@[simp] theorem A_def (x : Nat) : A x = 3 * x + 1 := rfl

theorem A_pos (x : Nat) : 0 < A x := by
  change 0 < 3 * x + 1
  omega


theorem A_even_of_odd (x : Nat) (hx : Odd x) : A x % 2 = 0 := by
  change (3 * x + 1) % 2 = 0
  change x % 2 = 1 at hx
  omega


/-- `1 <<< s = 2^s`. -/
theorem one_shiftLeft_eq_pow (s : Nat) : (1 : Nat) <<< s = 2 ^ s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    calc
      (1 : Nat) <<< (s + 1) = 2 * ((1 : Nat) <<< s) := Nat.shiftLeft_succ _ _
      _ = 2 * (2 ^ s) := by rw [ih]
      _ = 2 ^ s * 2 := by ac_rfl
      _ = 2 ^ (s + 1) := by rw [Nat.pow_succ]


/-- If `u` is odd and `k ≥ 1`, then `u + 2^k * t` is odd. -/
theorem odd_add_mul_pow_two (u k t : Nat) (hu : Odd u) (hk : 1 ≤ k) :
    Odd (u + 2 ^ k * t) := by
  change u % 2 = 1 at hu
  change (u + 2 ^ k * t) % 2 = 1
  have hpow : (2 ^ k) % 2 = 0 := by
    match k with
    | 0 => omega
    | k + 1 =>
      rw [Nat.pow_succ]
      omega
  have : (2 ^ k * t) % 2 = 0 := by
    rw [Nat.mul_mod, hpow]
    simp
  omega


/-- Odd `u` ⇒ `u + 3` even. -/
theorem odd_add_three_even (u : Nat) (hu : Odd u) : (u + 3) % 2 = 0 := by
  change u % 2 = 1 at hu
  omega


/-- Flipping bit `s ≥ 1` preserves oddness. -/
theorem flipBit_odd_of_odd (x s : Nat) (hx : Odd x) (hs : 0 < s) :
    Odd (flipBit x s) := by
  change x % 2 = 1 at hx
  change (x ^^^ (1 <<< s)) % 2 = 1
  have hs0 : s ≠ 0 := Nat.pos_iff_ne_zero.mp hs
  have hpow0 : ((1 : Nat) <<< s).testBit 0 = false := by
    rw [Nat.testBit_shiftLeft]
    have : ¬ (0 ≥ s) := by omega
    simp [this]
  have hx0 : x.testBit 0 = true := by
    simpa [Nat.testBit_zero] using hx
  have hxor0 : (x ^^^ (1 <<< s)).testBit 0 = true := by
    rw [Nat.testBit_xor, hx0, hpow0]
    decide
  simpa [Nat.testBit_zero] using hxor0



end BooleanCarry
