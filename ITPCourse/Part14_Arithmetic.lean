import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

section Arithmetic
/-
  We start with some basic arithmetic formulas manipulations.
-/

/-
  __Exercise__: Prove the following.
  You will likely only need basic tactics, and `simp` to simplify a few
  sums.
-/
theorem forall_x_y_h
  (P: Real → Real → Prop)
  : (∀ x y, P x y) ↔ (∀ x h, P x (x+h))
  := sorry

theorem forall_x_y_h_left
  (P: Real → Real → Prop)
  : (∀ x h, P x (x+h)) → (∀ x y, P x y)
  := (forall_x_y_h P).mpr

/-
  __Exercise__: Prove the following.
  You might want to use:
  - Tactics `linarith`, `let`, `unfold`, `constructor`
  - `lt_or_le`
-/
theorem forall_ε (a b: Real)
  : (a ≤ b) ↔ (∀ ε>0, a ≤ b + ε)
  := sorry

/-
  __Exercise__: Prove the following.
  Note how `n: Nat` is automatically converted to a `Real` below when we use
  `n * a`. This is done through the `NatCast` type class. If you see `↑n`
  printed instead of `n`, the `↑` is denoting the automatic coercion.
  You might want to use:
  - `⌈ … ⌉₊` aka `Nat.ceil`
  - `Nat.le_ceil`
  - `div_mul_cancel₀`
  - Tactic `push_cast` to turn `↑(a+b)` into `↑a + ↑b`
  - Tactics `ring`, `congr`, `gcongr`, `positivity`, `simp`, `calc`
-/
theorem archimedes (a b: Real)
  (h1: 0 < a)
  (h2: a ≤ b)
  : ∃ n: Nat, n * a > b
  := sorry

/-
  Real intervals in Lean are denoted as follows:
  - `Set.Ioo x y` open interval `(x,y)`
  - `Set.Icc x y` closed interval `[x,y]`
  - `Set.Ico x y` semi-open interval `[x,y)`
  - `Set.Ioc x y` semi-open interval `(x,y]`
  - `Set.Ioi x` open straight `(x,+∞)`
  - `Set.Iio x` open straight `(-∞,x)`
  - `Set.Ici x` closed straight `[x,+∞)`
  - `Set.Iic x` closed straight `(-∞,x]`
  - `Set.univ` the whole real line `(-∞,+∞)`
-/
example (x y: Real):
  Set.Ioi x ∩ Set.Iio y = Set.Ioo x y
  := rfl

/-
  __Exercise__: Prove the following.
-/
example (x y: Real) (h: x < y):
  Set.Ioi x ∩ Set.Ioi y = Set.Ioi y
  := sorry

end Arithmetic
