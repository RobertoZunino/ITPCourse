
section Type_classes
/-
  Sometimes we want to add additional information on top of existing types.

  As an example, suppose we want to order a type:
-/
structure OrderOn (τ: Type) where
  -- The ≤ relation
  leq: τ → τ → Prop
  -- Preorder laws
  leq_refl: ∀ x, leq x x
  leq_trans: ∀ {x y z}, leq x y → leq y z → leq x z

def orderNat: OrderOn Nat where
  leq := Nat.le
  leq_refl := Nat.le_refl
  leq_trans := Nat.le_trans

/-
  We might then want to define ways to define an order on, say, types such
  as `τ × σ`, `τ ⊕ σ`, `τ → σ`, … given orders for `τ` and `σ`.
-/
def orderProduct {τ σ: Type} (oτ: OrderOn τ) (oσ: OrderOn σ)
  : OrderOn (τ × σ)
  where
  leq := λ (t₁,s₁) (t₂,s₂) => oτ.leq t₁ t₂ ∧ oσ.leq s₁ s₂
  leq_refl := sorry
  leq_trans := sorry
/-
  … and so on for other types.

  Using this approach can be cumbersome, though, since we have to manually
  construct the order associated to a type every single time.
  Below, we check if a `List` (a type from the library) is ordered.
-/
def orderedList {τ: Type} (oτ: OrderOn τ): List τ → Prop
| []   => True
| [_]  => True
| (x₁ :: x₂ :: rest)
  => oτ.leq x₁ x₂ ∧ orderedList oτ (x₂ :: rest)

def a_list: List (Nat × Nat) := [(0,10), (4,17), (5,22)]

example:
  orderedList (orderProduct orderNat orderNat) a_list
  := by
  simp [ a_list, orderedList , orderNat , orderProduct ]

/-
  Type classes provide an automated way to construct the additional
  information associated to a type, such as the order as done above.

  A `class` is similar to a `structure` with (at least) one parameter.
-/
class Order (τ: Type) where
  -- The ≤ relation
  leq: τ → τ → Prop
  -- Preorder laws
  leq_refl: ∀ x, leq x x
  leq_trans: ∀ {x y z}, leq x y → leq y z → leq x z

/-
  Class instances provide a way to connect any type `τ` to their order.
-/
instance instOrderNat: Order Nat where
  leq := Nat.le
  leq_refl := Nat.le_refl
  leq_trans := Nat.le_trans

/-
  An argument in brackets `[o: Order …]` makes Lean automatically search
  for other instances. This is called a _class constraint_.
-/
instance instOrderProduct {τ σ: Type} [oτ: Order τ] [oσ: Order σ]
  : Order (τ × σ)
  where
  leq := λ (t₁,s₁) (t₂,s₂) => oτ.leq t₁ t₂ ∧ oσ.leq s₁ s₂
  leq_refl := sorry
  leq_trans := sorry

def orderedList₂ {τ: Type} [oτ: Order τ]: List τ → Prop
| []   => True
| [_]  => True
| (x₁ :: x₂ :: rest)
  => oτ.leq x₁ x₂ ∧ orderedList₂ (x₂ :: rest)
                            --  ↑  No additional argument here

def ord_example
  : orderedList₂ a_list
             -- ↑  No additional argument here
  := by
  simp [ a_list, orderedList₂ , Order.leq ]
/-
  Note how Lean automatically inferred the instance, providing the right
  order relation to the called function. Effectively, Lean operates in
  the following way:
  - `a_list` is a `List (Nat × Nat)`, so `τ` is inferred to be `Nat × Nat`
  - `orderList'` requires `Order (Nat × Nat)`, we search for instances
  - `instOrderProduct` can provide that, but requires `Order Nat` (twice)
  - `instOrderNat` provides `Order Nat`
  Lean then automatically solves the constraint at hand while generating the
  missing arguments for us.

  We can show the inferred instances as follows:
-/
section
set_option pp.all true
#check orderedList₂ a_list
end

/-
  Also note that sometimes we can also completely avoid naming instances.
-/
def orderedList₃ {τ: Type} [Order τ]: List τ → Prop
                        -- ↑ No given name
| []   => True
| [_]  => True
| (x₁ :: x₂ :: rest)
  => Order.leq x₁ x₂ ∧ orderedList₃ (x₂ :: rest)
  -- ↑ No reference to any particular instance

/-
  Type classes are heavily exploited in the Lean standard libraries to keep
  the notational noise down. Instead of using
    `Nat.le x y`
    `Int.le x y`
    `Rat.le x y`
    `Real.le x y`
    …
  we can simply write the much more readable
    `x ≤ y`
  and Lean will pick up the "right" relation for the types at hand.
-/
#print LE
#check instLENat
/-
  The same happens for addition, multiplication, and many other common
  mathematical operators.

  Even number literals like `42` implicitly use type classes so that they
  can be used as `Nat`, `Int`, … or whatever type is needed. This is also
  why, when the context does not demand a precise type, we explicitly have
  to use something like `(42: Nat)` to prod Lean into selecting the right
  instance.
-/
#print OfNat

/-
  Finally note that is is possible that a class constraint like `[Order τ]`
  can be solved in multiple different ways, if there are multiple instances
  that can do that.
-/
instance instOrderString₁: Order String where
  leq := λ x y => x ≤ y   -- standard alphabetic/lexicographic order
  leq_refl := sorry
  leq_trans := sorry
instance instOrderString₂: Order String where
  leq := λ x y => y ≤ x   -- opposite order
  leq_refl := sorry
  leq_trans := sorry
/-
  The automatic constraint solver will pick one of these when dealing with
  `[Order String]`. There are ways to change the priority between
  conflicting instances, but we will not see them. Refer to the Lean
  documentation if you really need this. When possible, avoiding conflicting
  instances is the best solution.
-/
end Type_classes

section Decidable_properties
-- TODO
end Decidable_properties
