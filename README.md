# BooleanCarry

Lean 4 formalization of a valuation transition theorem for A(x) = 3x+1 under single bit flips.

## Theorem

`BooleanCarry.valuation_transition` in `BooleanCarry/VTT.lean`

For odd x and s >= 1, with A(x) = 3*x+1 and flipBit(x,s) = x XOR 2^s,
let v = v2(A(x)). Then:

- v < s  =>  v2(A(flipBit x s)) = v
- s < v  =>  v2(A(flipBit x s)) = s
- s = v  =>  v2(A(flipBit x s)) >= v + 1

## Build

```
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

Lean version: see lean-toolchain. No Mathlib.

## Layout

```
BooleanCarry/Core.lean       A, Odd, flipBit
BooleanCarry/Valuation.lean  v2 and factor lemmas
BooleanCarry/XorBridge.lean  flipBit = x +/- 2^s
BooleanCarry/VTT.lean        main theorem
```
