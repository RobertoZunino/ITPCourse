
section The_sum_type

/-
  A sum type, written `A ⊕ B`, intuitively represents the disjoint union
  of the types `A` and `B`.

  The values denoted by a sum type can (only) be of one of the following
  forms:
    `Sum.inl a` for some `a: A`
    or
    `Sum.inr b` for some `b: B`.

  These can often be abbreviated to `.inl a` and `.inr b`.

  The `.inl` and `.inr` functions are, effectively, two "inclusion"
  functions. Their name comes from "inclusion from the left" (`.inl`)
  and "inclusion from the right" (`.inr`).
    `.inl: A → A ⊕ B`
    `.inr: B → A ⊕ B`

  Note that `.inl a` and `.inr b` are postulated to be always _distinct_
  values, even when `A = B` and `a = b`. For instance, within the sum type
  `Nat ⊕ Nat` the values
    `.inl 42`
    `.inr 42`
  are different.
-/

/-
  Introduction in a sum type can be performed using the two inclusions:
-/

def something₁: String ⊕ Nat := .inl "hello"
def something₂: String ⊕ Nat := .inr 123456

/-
  Elimination can instead be performed through _pattern matching_.
  Here, we must take _both_ cases into account.
-/

def hello: String
  := match something₁ with
  | .inl s  => s
  | .inr _n => "a Nat is not a String"

/-
  __Exercise__: Try removing a case from the `match`.
-/

/-
  The computation/β rule for sum types involves two distinct reductions.

  β₁: The expression
    match .inl v with
    | .inl x₁ => e₁
    | .inr x₂ => e₂
  reduces to `e₁` where the occurrences of the variable `x₁` have been
  replaced by `v`.

  β₂: Similarly, the expression
    match .inr v with
    | .inl x₁ => e₁
    | .inr x₂ => e₂
  reduces to `e₂` where the occurrences of the variable `x₂` have been
  replaced by `v`.
-/

-- An example of β₁
example:
  (λ (x: String) (f: String → Bool) (g: Nat → Bool) =>
    match (.inl x : String ⊕ Nat) with
    | .inl s => f s
    | .inr n => g n)
  = (λ (x: String) f _g => f x)
  := rfl

-- An example of β₂
example:
  (λ (y: Nat) (f: String → Bool) (g: Nat → Bool) =>
    match (.inr y : String ⊕ Nat) with
    | .inl s => f s
    | .inr n => g n)
  = (λ (y: Nat) _f g => g y)
  := rfl

/-
  The uniqueness/η rule involves the following reduction.

  When `s` is a term having a sum type, then the expression
    match s with
    | .inl x₁ => .inl x₁
    | .inr x₂ => .inr x₂
  reduces to `s`.

  Note: this rule is not seen, in general, by Lean as a _definitional_
  equality. (It is still a theorem, though, even if `rfl` is not enough
  to prove it.)
-/

/-
  Terminology note: in the literature sum types can be found under a
  plethora of different names, depending on the actual programming language
  at hand. Here are some alternative names:
    - sum type
    - disjoint union
    - tagged union
    - variant type
-/

/-
  __Exercise__: Try experimenting with nested sums like
  `Nat ⊕ String ⊕ Bool`.
-/

end The_sum_type

section The_boolean_type
/-
  The boolean type `Bool` has only two values, `true` and `false`.

  The terms `true` and `false` therefore act as introduction forms.
-/

def aBoolean: Bool := true

/-
  Elimination is done using the conditional:
    `if b then … else …`
-/

def negation (b: Bool)
  := if b then false else true

/-
  __Exercise__: Try eliminating a boolean using pattern matching instead.
-/

/-
  __Exercise__: Recall the `Unit` type, admitting only a single value `()`.
  We can observe that the `Bool` type is isomorphic to `Unit ⊕ Unit`. Indeed
  such type only admits values `.inl ()` and `.inr ()`.
  Try defining an explicit type isomorphism.
-/

end The_boolean_type


section The_empty_sum
/-
  When dealing with products, we observed that the "product of zero types"
  `Unit` is a type which admits only one value, namely `()`.

  By contrast, the "sum of zero types" is a type named `Empty` which admits
  no values at all. It is similar to the empty set in this regard.

  `Empty` has no introduction form, consequently.

  `Empty` can be eliminated by pattern matching. Since it has no values,
  we have exactly "zero cases" to handle, and so the pattern matching is
  trivial. In Lean, this requires a special syntax: instead of using a
  `match … with` term with no cases, we must use its variant `nomatch …`.
-/

def fromEmpty (e: Empty): String
  := nomatch e

end The_empty_sum


section Type_isomorphisms
/-
  Sum types, when taken up to isomorphism, form an abelian monoid.
    `α ⊕ Empty ≅ α` (unit)
    `(α ⊕ β) ⊕ γ ≅ α ⊕ (β ⊕ γ)` (associativity)
    `α ⊕ β ≅ β ⊕ α` (commutativity)

  In this regard, sum types and product types are similar.
-/

/-
  We also have special isomorphisms that involve both sums and products.

  One of them is distributivity:
    `α × (β ⊕ γ) ≅ (α × β) ⊕ (α × γ)` (distributivity)

  The other is the absorption law:
    `α × Zero ≅ Zero`

  In general, `×, Unit, ⊕, Empty` types form an _abelian semiring_,
  when taken up to isomorphism.

  Types formed in this way are called _algebraic types_.

  Note in passing that algebraic types can always be written (up to
  isomorphism) in a simple canonic form, a sum-of-products, or in other
  words as _polynomials_. This is due to the abelian semiring properties.
  We will exploit this fact later on.

  __Exercise__: Try to define some of these isomorphisms, for some concrete
  types such as `α = String`, `β = Nat`, `γ = Bool`.
-/

/-
  Finally, sum and function types also satisfy a few "power laws":
    `A⁰ ≅ 1` i.e. `Zero → α ≅ Unit`
    `Cᴬ⁺ᴮ ≅ Cᴬ × Cᴮ` i.e. `(α ⊕ β) → γ ≅ (α → γ) × (β → γ)`

  Note that `0ᴬ ≅ 0` is __not__ true in general: a simple counterexample
  is `0⁰ ≅ 1`, which is implied by the laws above.

  __Exercise__: Try once again to define some of these isomorphisms,
  after having replaced `A,B,C` with some concrete types .
-/

end Type_isomorphisms
