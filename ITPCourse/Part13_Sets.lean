
import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Linarith

section Set_notation
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

/-
  A plethora of variations on the syntax `{ … | … }` is available from the
  libraries. Here we only mention a few examples.
  Note that there is some special handling of relations like `<` and `⊆`.
-/
example: Set Nat := { n | n < 10 }
example: Set Nat := { n < 10 | n > 5 }
example: Set Nat := { n^2 + n + 2 | n > 5 }
example: Set Nat := { n^2 + n + 2 | (n: Nat) (prop: n > 5 ∧ n < 20) }
example: Set (Set Nat) := { s | ∀ n ∈ s, 1 ≤ n ∧ n ≤ 20 }
example: Set (Set Nat) := { {n, n+1} | n: Nat }
example: Set (Set Nat) := { {n, n+1} | (n: Nat) (prop: n > 20) }

example: Set Nat := { n | n > 5 ∧ n < 10 }

/-
  Not all "reasonable" notations are accepted: for instance, these are
  allowed
-/
example: Set Nat := { n | n > 5 ∧ n < 10 }
example: Set Nat := { n+1 | n > 5 }
/-
  but `{ n+1 | n > 5 ∧ n < 10 }` is not allowed. It can be defined in one of
  the following ways:
-/
example: Set Nat := { n+1 | (n: Nat) (prop: n > 5 ∧ n < 10) }
example: Set Nat := { n+1 | (n: Nat) (prop1: n > 5) (prop2: n < 10) }
example: Set Nat := { m | ∃ n: Nat, m = n+1 ∧ n > 5 ∧ n < 10 }

/-
  The scoping of variables can be tricky. Here `a` is the function argument,
  while `n` ranges over all naturals `> 10`.
-/
example: Nat → Set Nat := λ a => { n+a | n > 10 }
-- Alternatively:
example: Nat → Set Nat := λ a => { n+a | (n:Nat) (prop: n > 10) }

/-
  We can also write enumerated sets:
-/
example: {1,2} = { n: Nat | n=1 ∨ n=2 } := rfl

/-
  __Exercise__: Prove the following.
-/
example {τ: Type} {x y: τ}: {x , y} = ({y , x}: Set τ)
  := sorry

end Set_notation

section Set_operations
/-
  Intersecting an _indexed_ family of sets `Aᵢ` is done using the syntax
    `⋂ i: I, Aᵢ`
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
example
  : ⋂ n: Nat, { m: Nat | m ≥ n } = ∅
  := by
  ext
  case h x =>
  constructor
  case mp =>
    intro h
    simp at h
    have h1 := h x.succ
    linarith   -- `linarith` solves goals with linear arithmetics
  case mpr =>
    intro h
    contradiction

/-
  If the index ranges over a `Set` and not over all the values in a type, we
  can use `⋂ i ∈ I, Aᵢ` instead
-/
example
  : ⋂ n ∈ ({1 , 2} : Set Nat), {n} = ∅
  := by
  ext
  case h x =>
  constructor
  case mp =>
    intro h
    simp at h
    linarith
  case mpr =>
    intro h
    contradiction

/-
  If we want to intersect a (non-indexed) family of sets, i.e. a
  `F : Set (Set τ)` then we can use the notation `⋂₀ F`.

  Here's the previous example `an_empty_intersection` from above, but with
  a family of sets instead.
-/
example
  : ⋂₀ { { m: Nat | m ≥ n } | n: Nat } = ∅
  := an_empty_intersection

/-
  The empty set, as we have already seen, is `∅`.
-/
example {τ: Type}: ∅ = { _t: τ | False } := rfl
/-
  The "full" set, containing _all_ the values in a type, is `Set.univ`.
-/
example {τ: Type}: Set.univ = { _t: τ | True } := rfl

/-
  Consequently, the empty intersection is the "full" set.
-/
example {τ: Type}:
  ⋂₀ (∅ : Set (Set τ)) = Set.univ
  := by simp

/-
  Unions use similar notation:
    `⋃ i: I, Aᵢ`  indexed union
    `⋃₀ F`        union of a family
-/
example {τ: Type}:
  ⋃ t: τ, {t} = Set.univ
  := by
  ext
  case h x =>
  constructor
  case mp =>
    intro h
    trivial
  case mpr =>
    intro h
    exists {x}
    constructor
    case left =>
      exists x
    case right =>
      trivial

example {τ: Type}:
  ⋃₀ (∅ : Set (Set τ)) = ∅
  := by simp

/-
  The following examples illustrate the basic set operators
    `∩`, `∪`, `\`, `ᶜ`
-/
example {s₁ s₂: Set Nat}: s₁ ∩ s₂ = s₂ ∩ s₁ := by exact Set.inter_comm s₁ s₂
example {s₁ s₂: Set Nat}: s₁ ∪ s₂ = s₂ ∪ s₁ := by exact Set.union_comm s₁ s₂
example {s: Set Nat}: s \ s = ∅ := by simp
example {s: Set Nat}: sᶜ ∩ s = ∅ := by exact Set.compl_inter_self s

/-
  __Exercise__: Prove the following.
-/
example {τ: Type} {A: Set τ} {B: Nat → Set τ}:
  A ∩ ⋂ n: Nat, B n
  =
  ⋂ n: Nat, A ∩ B n
  := sorry

end Set_operations

section Sets_vs_types
/-
  Sets might superficially resemble types, but there are profound
  differences between these two concepts.

  A (correct) Lean term has an associated type, which is essentially unique.
  The term `true` is a `Bool`, and only a `Bool`. The type of a term is
  computed automatically by Lean.

  With sets, this does not hold. Any value `x` belongs to many sets:
    `{x}`, `{x,y}`, `{x,y,z}`, … , `{x} ∪ S`.

  The typing `x : σ` is _not_ a proposition, and can essentially only appear
  at the top-level of a Lean definition. There is no way to write something
  like `(x : σ) ∨ (x : τ)`.

  The membership `x ∈ S` is a proposition. We can write `x ∈ S ∨ x ∈ T`.

  In Lean, a set `S` must have a type, namely `Set α` for some `α: Type`.
  In a sense, Lean does not have real sets, but only subsets of some already
  constructed type.
-/
end Sets_vs_types

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

example: Type := List less20_struct  -- This is now OK.

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

section Images
/-
  The image of a set along a function is denoted with `f '' A`.
-/
example
  : (λ x => x+1) '' {1,2,3} = {2,3,4}
  := by
  ext x
  case h =>
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, Nat.reduceAdd, exists_eq_left]
  tauto

/-
  The domain of a function `f: α → β` is simply `Set.univ: Set α`.
  The domain is then `Set.univ: Set β`.
  The range of a function is instead `Set.range f`.
-/
example
  (α β: Type) (f: α → β)
  : Set.range f = f '' Set.univ
  := Set.image_univ.symm

/-
  The preimage of a set is instead denoted with `f ⁻¹' S`
-/
example
  : (λ x => x+1) ⁻¹' {2,3,4} = {1,2,3}
  := by
  ext x
  case h =>
  simp only [Set.mem_preimage, Set.mem_insert_iff, Nat.reduceEqDiff,
    Set.mem_singleton_iff]

example
  : (λ x: ℤ => x^2) ⁻¹' {4} = {-2,2}
  := by
  ext x
  case h =>
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Int.reduceNeg,
    Set.mem_insert_iff]
  constructor
  case mp =>
    intro h
    -- A convenient lemma from the libraries!
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h
  case mpr =>
    intro h
    cases h
    case inl h1 =>
      subst x
      dsimp
    case inr h2 =>
      subst x
      dsimp

end Images
