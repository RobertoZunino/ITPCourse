
import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Linarith

section Sets
/-
  Previously, we saw that we can represent the "subsets" of a type `τ` using
  a function `τ → Prop`.
-/
example: Nat → Prop
  := λ n => n < 20

/-
  This approach is embraced by the Lean libraries, that define `Set τ` in
  that way:
-/
#print Set

example: Set Nat
  := λ n => n < 20

/-
  The library also provides a more familiar notation, hiding the fact that
  sets are represented as function `… → Prop`
-/
def less20: Set Nat
  := { n: Nat | n < 20 }

example: 10 ∈ less20
  := by
  dsimp [less20] -- Expand the definitions
  decide         -- Compute using the `Decidable` type class

end Sets

section Set_operations

/-
  This is the notation for indexed intersections.
-/
theorem an_empty_intersection:
  ⋂ n: Nat, { m: Nat | m ≥ n } = ∅
  := by
  apply Set.ext
  intro x
  constructor
  case mp =>
    intro h
    have h1 : x ∈ { m | m ≥ x.succ }
      := h { m | m ≥ x.succ } (by exists x.succ)
    dsimp at h1
    have h2 : x > x := h1
    exact (lt_self_iff_false x).mp h1
  case mpr =>
    intro h
    contradiction

-- The same, but with more automation.
example:
  ⋂ n: Nat, { m: Nat | m ≥ n } = ∅
  := by
  ext
  next x =>
  constructor
  case mp =>
    intro h
    simp at h
    have h1 := h x.succ
    linarith
  case mpr =>
    intro h
    contradiction

/-
  Instead, this is the notation for intersecting a family of sets.
-/
example:
  ⋂₀ { { m: Nat | m ≥ n } | n: Nat } = ∅
  := an_empty_intersection

-- TODO explain the set-image syntax
def foo (n: Nat): Set Nat := { n+m | (m:Nat) (_ : m + 5 > 6) }

#print foo

-- TODO explain the family syntax

-- TODO more basic set theory using `Set τ`

end Set_operations

section Set_like_types
/-
  Note that if we have `s: Set τ` then `s` is not a type, and we can not use
  it as such. For instance, we can not write `List s`.

  If we need an actual type, we need to use a dependent sum of the form
    `(t: τ) × (property t)`
  Concretely, we have several options. One is to define a `structure`.
-/
structure less20_struct where
  n: Nat
  prop: n < 20

example: less20_struct := ⟨ 5 , by decide ⟩

example: Type := List less20_struct  -- This is OK.

/-
  The Lean libraries, however, allow a more familiar syntax for this kind of
  set-like dependent sums:
-/
def less20_τ: Type := { n: Nat // n < 20 }
                            -- ↑↑ Note the // instead of |

example: less20_τ := ⟨ 5 , by decide ⟩

example: Type := List less20_τ   -- This is OK.

/-
  To convert `x: less20_τ` into a `Nat` we can use `x.val` (or `x.1`).
  Instead, `x.mem` (or `x.2`) certifies that `x.val` belongs to the set.
-/
example: less20_τ → Nat
  := λ x => x.val

example (x: less20_τ): x.val < 20
  := x.mem

/-
  Note that, when using set-like types, we do not have a real way to write
  `… ∈ less20_τ` in the middle of a general formula, for the same reason we
  can not write `(x : τ) ∨ p`. Lean terms must be typed, so their syntax
  already mandates if they live inside a type or not.
-/

def less10_τ: Type := { n: Nat // n < 10 }

theorem pseudo_inclusion:
  ∀ x: less10_τ, ∃ y: less20_τ, x.val = y.val
  := by
  intro x
  have h : x.val < 20 := by calc
    _ < 10 := x.mem
    _ < 20 := by decide
  exists ⟨ x.val , h ⟩

/-
  Above, we had to prove `h` before we used it.
  Alternatively, we can postpone its proof using `?name`:
-/
theorem pseudo_inclusion₂:
  ∀ x: less10_τ, ∃ y: less20_τ, x.val = y.val
  := by
  intro x
  exists ⟨ x.val , ?h ⟩  -- Postponed!
  -- 2 goals remaining here
  case h =>
    calc
    _ < 10 := x.mem
    _ < 20 := by decide
  -- back to the main goal `x.val = y.val`
  rfl

end Set_like_types
