
section The_product_type

/-
  The product type `A × B` is the type of pairs carrying a component of
  type `A` and another of type `B`.

  Here is how to construct a value in a product type (introduction).
-/

def myPair: String × Bool := ("hello", true)

/-
  Here is how to exploit a (previously-constructed) pair to extract its
  components.
-/

def first_component: String := myPair.fst
def second_component: Bool  := myPair.snd

-- Alternatively,

def first_component₂: String := myPair.1
def second_component₂: Bool  := myPair.2

-- We can verify their values as follows:

#eval first_component      -- `"hello"`
#eval second_component     -- `true`


section A_more_complex_example

def pairFun: Nat → Nat × Nat
  := λ n => (n+1, n+2)

#eval (pairFun 10).fst   -- `11`
#eval (pairFun 30).snd   -- `32`

end A_more_complex_example

/-
  The computation / β rule for the product type states that

    `(x, y).fst` reduces to `x`
    `(x, y).snd` reduces to `y`

  The uniqueness / η rule instead states that

    `(p.fst, p.snd)` reduces to `p`

  when `p` is an expression having a product type.
-/

section Pattern_matching

/-
  There is another very important elimination form that can be used on
  pairs: _pattern matching_.

  The `match … with …` expression allows one to obtain both components of a
  pair.
-/

def sum_of_components: Nat
  := match pairFun 10 with
  | (a, b) => a + b

/-
  Above, the pair resulting from `pairFun 10` is dissected into its
  components, which are bound to variables `a` and `b`. The expression
  after the `=>` can use these variables to compute the final result of the
  `match`.

  We can use pattern matching even on nested pairs, like pairs-of-pairs:
-/

def pat_example₁ (x: (Nat × String) × Nat): Nat
  := match x with
  | ((a, _b), c) => a + c

/-
  Above, Lean warns that `b` is not used after the `=>`. Naming that
  component `_b` avoids the warning. We can even use `_`.
-/

def pat_example₂ (x: (Nat × String) × Nat): Nat
  := match x with
  | ((a, _), c) => a + c

/-
  When pattern matching, we can not repeat the same variable twice or more.

  For instance, `| ((a,_),a) => …` is an error.

  __Exercise__: Try it.

  By contrast, `_` can appear multiple times to discard multiple unneeded
  values.
-/

def pat_example₃ (x: (Nat × String) × Nat): Nat
  := match x with
  | ((a, _), _) => a

/-
  The following shorthand notation implicitly performs a `match`.
  Note how it avoids naming the argument `x`.
-/

def pat_example₄: (Nat × String) × Nat → Nat
  | ((a, _), c) => a + c

example: pat_example₄ = pat_example₁
  := rfl

/-
  __Exercise__: Define `swap₁` and `swap₂` to swap the pairs components.
-/
def swap₁: Nat × String → String × Nat
  := sorry
def swap₂: String × Nat → Nat × String
  := sorry
/-
  Prove that their composition (in either direction) is the identity on pairs.
-/
example: sorry = (λ x: Nat × String => x)
  := sorry
example: sorry = (λ x: String × Nat => x)
  := sorry

end Pattern_matching

section Tuples

/-
  Tuples in Lean are modelled as nested pairs.

    `A × B × C × D` means `A × (B × (C × D))`

    `(a,b,c,d)` means `(a,(b,(c,d)))`
-/

#eval (1,(2,3))   -- Printed as `(1,2,3)`

/-
  __Exercise__: Implement left/right rotations on 4-tuples.
  Then, test `identityᵢ` on a few cases.
  Finally, prove they are indeed the identity.
-/

def left_rot: Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat
  := sorry

def right_rot: Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat
  := sorry

def identity₁ (x: Nat × Nat × Nat × Nat): Nat × Nat × Nat × Nat
  := right_rot (left_rot x)

def identity₂ (x: Nat × Nat × Nat × Nat): Nat × Nat × Nat × Nat
  := left_rot (right_rot x)

end Tuples

end The_product_type

section The_empty_product

/-
  The product of zero types is called `Unit` and allows only one value:
  the "zero-tuple" `()`.
-/

def uninteresting: Unit := ()

/-
  __Exercise__: Define how to convert `Nat × Unit` to `Nat` and back with no
  loss of information.
  Prove that their compositions (in either direction) is the identity.
-/
def there: Nat × Unit → Nat
  := sorry
def back_again: Nat → Nat × Unit
  := sorry

end The_empty_product

section Type_isomorphisms
/-
  Two types `α`  and `β` are said to be isomorphic (`α ≅ β`) when there are
  two functions
    `f: α → β`
    `g: β → α`
  such that their compositions `f ∘ g` and `g ∘ f` are the respective
  identity functions, i.e.
    `(λ a:α => g (f a)) = (λ a:α => a)`
    `(λ b:β => f (g b)) = (λ b:β => b)`
-/

/-
  In particular, product types satisfy the following isomorphisms:
    `α × Unit ≅ α` (unit)
    `(α × β) × γ ≅ α × (β × γ)` (associativity)
    `α × β ≅ β × α` (commutativity)
  Hence, if we consider types up to isomorphism, they can be seen as an
  _abelian monoid_.
-/
end Type_isomorphisms

section Currying

/-
  We saw that multiple-argument functions in Lean are usually represented
  with a type such as `A₁ → A₂→ ⋯ → Aₙ → B`.

  Of course, we can also use tuples and use instead the alternative type
  `(A₁ × A₂ × ⋯ × Aₙ) → B`.

  A function with the former type is named "curried", after Haskell Curry
  who introduced such idea. A function with the latter type, involving
  tuples, is called "uncurried".

  __Exercise__: Convert functions between the two forms, completing the
  following definitions.
-/

def curry:
  (Bool × String → Nat)
  →
  (Bool → String → Nat)
  := sorry

def uncurry:
  (Bool → String → Nat)
  →
  (Bool × String → Nat)
  := sorry

/-
  __Exercise__: Define a few functions and convert them to their
  curried/uncurried variants. Test them.
-/

/-
  __Exercise__: Prove that `curry` and `uncurry`, composed in either
  direction, are the identity on the appropriate function type.
-/

/-
  Currying can be seen as a type isomorphism:
    `α × β → γ ≅ α → β → γ`

  When writing the type of functions `A → B` using the exponential
  notation `Bᴬ` or `B^A`, then the above isomorphism reads as
    `Cᴬˣᴮ ≅ (Cᴮ)ᴬ`
  which is a very easy law to remember.

  Indeed, the following "power laws" hold on functions types and products:
    `A¹ ≅ A` i.e. `Unit → α ≅ α`
    `1ᴬ ≅ 1` i.e. `α → Unit ≅ Unit`
    `(B×C)ᴬ ≅ Bᴬ × Cᴬ` i.e. `α → β × γ ≅ (α → β) × (α → γ)`
    `Cᴬˣᴮ ≅ (Cᴮ)ᴬ` i.e. `α × β → γ ≅ α → β → γ` (currying)

  __Exercise__: Define an instance of these isomorphisms on some concrete
  case such as `α = String`, `β = Nat`, `γ = Bool`.
  Find which compositions can be proved equal to the identity using `rfl`,
  and which ones instead would require a more complex proof.
-/

end Currying
