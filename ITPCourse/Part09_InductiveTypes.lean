
section Inductive_types
/-
  An inductive type is a type whose values are only those that can be
  formed though a given set of operations, named _constructors_.

  Inductive types, as their name suggests, also allow for defining a type
  through _induction_. Still, to help understanding, we start our
  presentation from a few basic examples which do not exploit induction at
  all.
-/

section Not_really_inductive_inductive_types

section Enumerated_types

inductive Color where
| red: Color
| green: Color
| blue: Color
/-
  Here, `Color.red` is a constant of type `Color`, and is one of the
  introduction forms for that type. In many contexts, it can be shortened
  as `.red`.

  The other constructors `.green` and `.blue` provide other introduction
  forms. Each form is _distinct_ from the others.

  Elimination is done through pattern matching/case analysis.

  Effectively, the `Color` type is isomorphic to a sum type.
    `Color ≅ Unit ⊕ Unit ⊕ Unit`
-/
def Color.permute₁ (c: Color): Color
  := match c with
  | .red   => .green
  | .green => .blue
  | .blue  => .red

-- Equivalent to the above
def Color.permute₂: Color → Color
  | .red   => .green
  | .green => .blue
  | .blue  => .red

end Enumerated_types

section Algebraic_types
/-
  In `inductive` types, constructors are allowed to be functions:
-/
def Point: Type := Nat × Nat -- `Nat` coordinates

inductive Shape where
  -- A segment given by its endpoints
| segment: Point → Point → Shape
  -- A triangle given by its vertices
| triangle: Point → Point → Point → Shape
  -- A circle given by its center and radius
| circle: Point → Nat → Shape
/-
  Each constructor type must end with `… → Shape`.

  Each constructor has a disjoint image from any other constructor. Further,
  it acts injectively on its arguments, as if it were building a tuple.

  Effectively, the `Shape` type above is isomorphic to:
    `Shape ≅ (Point × Point) ⊕ (Point × Point × Point) ⊕ (Point × Nat)`

  Introduction and elimination work as shown below.
-/
example: Shape
  := .circle (3,4) 42

def Shape.translate_x (δx: Nat): Shape → Shape
  | .segment (x₁, y₁) (x₂, y₂)
    => .segment (x₁ + δx, y₁) (x₂ + δx, y₂)
  | .triangle (x₁, y₁) (x₂, y₂) (x₃, y₃)
    => .triangle (x₁ + δx, y₁) (x₂ + δx, y₂) (x₃ + δx, y₃)
  | .circle (x, y) r
    => .circle (x + δx, y) r

/-
  Effectively, any _algebraic_ type formed through the operations
    `Empty, ⊕, Unit, ×`
  can be represented, up to type isomorphism, as an `inductive` type.
  Indeed, as we previously mentioned, by exploiting the abelian semiring
  laws, any such type can be written in polynomial form (a sum-of-products)
    `… × (… × … × …) ⊕ (… × …) ⊕ ⋯`
  This can then be turned into an `inductive` type: we can declare a
  constructor `c` for each product in the sum, and make `c` take as many
  arguments as the factors in the product it corresponds to.

  __Exercise__: Try turning
    `Nat ⊕ (String × Bool) ⊕ Unit`
  into an `inductive` type.
-/
end Algebraic_types

end Not_really_inductive_inductive_types

section Actually_inductive_inductive_types
/-
  Constructors are allowed to use in their arguments the type we are
  defining right now.

  That is, the type of a constructor `c: … → … → … → T` can mention `T` in
  the `…` parts. This makes the type actually _inductive_.

  [ Actually, there are a few restrictions on how `T` can be used there, but
    we will not discuss them. ]

  The most famous example inductive type is, of course, `ℕ`:
-/
inductive ℕ where
| zero: ℕ
| succ: ℕ → ℕ

/-
  Introduction is done in the obvious way:
-/
example: ℕ := .zero
example: ℕ := .succ .zero
example: ℕ := .succ (.succ .zero)
example: ℕ := .succ (.succ (.succ .zero))

-- Alternative syntax
example: ℕ := ℕ.zero
example: ℕ := ℕ.zero.succ
example: ℕ := ℕ.zero.succ.succ
example: ℕ := ℕ.zero.succ.succ.succ

/-
  Elimination is done with pattern matching, as usual, but the functions
  we define can now be _recursive_.
-/
def ℕ.double₁: ℕ → ℕ
| .zero   => .zero
| .succ n => .succ (.succ (ℕ.double₁ n))

-- Alternative syntax
def ℕ.double₂: ℕ → ℕ
| .zero   => .zero
| .succ n => n.double₂.succ.succ
/-
  Recursive functions definitions must make their recursive calls with
  "structurally smaller" arguments, to ensure the recursion eventually
  terminates.

  For instance, these are disallowed:
    `def f (n: ℕ): ℕ  := f n`
    `def f (n: ℕ): ℕ  := f (n.succ)`
-/

/-
  Note that the standard `Nat` type was defined just like our `ℕ` above:
-/
#print Nat

section The_recursor

/-
  Each time an inductive type `τ` is defined, Lean implicitly creates a
  special function `τ.rec` called _recursor_. The recursor has many purposes:

    - `τ.rec` acts as a general elimination rule for `τ`.

    - `τ.rec` is implicitly used to implement recursive functions (such as
      `ℕ.double` above).

    - `τ.rec` provides an _induction principle_ that can be exploited to
      prove theorems.

  Let us read the type for `ℕ.rec`, which is quite complex:
-/
#print ℕ.rec
/-
  This is a universe-polymorphic function. Let us discuss the case where
  `Sort u = Prop`. The recursor type then states:

    - Given any `motive: ℕ → Prop` (a property on `ℕ`)
    - Given the base case `motive ℕ.zero`
    - Given the induction case `∀ (a: ℕ), motive a → motive a.succ`
    - Then, we have `∀ (t: ℕ), motive t`

  So, this is the standard induction principle on natural numbers. The
  property is called a `motive`, the `∀`s are dependent product types,
  but everything else is very familiar.

  Note that the case `Sort u = Type` (or `= Type v`) is relatively similar:

    - Given any `motive: ℕ → Type` (a type family indexed by naturals)
    - Given a value in the first type in the family `motive ℕ.zero`
    - Given a way to construct values in the next type from the previous one
      `(a: ℕ) → motive a → motive a.succ`
    - Then, we have a value on all types in the family, i.e., we have a
      dependent function `(t: ℕ) → motive t`

  It might be helpful to consider the simpler case where `motive t` is a
  constant `α`, so the resulting function is simply of type `ℕ → α`. The
  recursor then simply takes `x: α`, `f: α → α` and `n: ℕ`, and repeatedly
  applies `n` times the function `f` to `x` so to obtain `⋯ f (f (f x))` of
  type `α`.
-/

section A_theoretical_remark
/-
  Note that, even in the case of actually inductive types like `ℕ` we still
  have an isomorphism like those we observed for algebraic types. Applying
  the same technique we get:
    `ℕ ≅ Unit ⊕ ℕ`

  Indeed, one can argue that `ℕ` is the "smallest" solution to this
  "recursive type equation". (In category theory, this is referred to as an
  "initial F-algebra".)

  In a sense, the recursor makes `ℕ` to be the "smallest", the "least" type
  which admits introductions `.zero` and `.succ`. Indeed, any other type `α`
  admitting those would satisfy the base case and induction case above, so
  we get an inclusion function `ℕ → α` trough `ℕ.rec`.
-/
end A_theoretical_remark

end The_recursor

end Actually_inductive_inductive_types

-- TODO more examples: lists, trees, expressions

end Inductive_types
