
namespace DependentSums

section Dependent_sums
/-
  We have seen dependent products
    `(a: α) → β a`
  as the type of functions whose result lives in a type that depends on the
  actual argument value. This generalizes the notion of function type.

  A dependent sum
    `(a: α) × β a`
  is the type of pairs `⟨ a, b ⟩` whose second component `b` lives in a type
  that depends on the value of the first component `a`. This generalizes the
  notion of product type.
-/
example: (τ: Type) × τ := ⟨Bool  , true   ⟩
example: (τ: Type) × τ := ⟨Nat   , 42     ⟩
example: (τ: Type) × τ := ⟨String, "hello"⟩

def dep_sum₁: Type
  := (b: Bool) × (if b then String else Bool)
example: dep_sum₁ := ⟨ true  , "hello" ⟩
example: dep_sum₁ := ⟨ false , true    ⟩

/-
  Note that `β a` can be an empty type for some values of `a`. Consequently,
  the dependent sum `(a: α) × β a` could prevent certain values of `a` to
  occur in pairs.
-/
def dep_sum₂: Type
  := (x: Nat × Nat) × (if x.1 = x.2 then Unit else Empty)
example: dep_sum₂ := ⟨ (0,0) , () ⟩
example: dep_sum₂ := ⟨ (1,1) , () ⟩
example: dep_sum₂ := ⟨ (2,2) , () ⟩
example: dep_sum₂ := ⟨ (3,3) , () ⟩
-- We can not choose `x = (2,3)`, for instance.

section Structures
/-
  `structure`s can also form dependent sums types. Unlike with the `×`
  notation, a `structure` can also involve fields whose type is in `Prop`.
-/
structure dep_sum₃: Type where
  a: Nat
  b: Nat
  equal: a = b  -- A proposition

example: dep_sum₃ :=
  { a := 3
  , b := 3
  , equal := rfl
  }

example: dep_sum₃ where -- `where` is a shortcut for `:= { … }`
  a := 4
  b := 4
  equal := rfl

/-
  This is extremely useful when formalizing mathematical objects.

  Here are a few examples:
-/
structure Bijection (α β: Type): Type where
  fw: α → β
  bk: β → α
  fw_bk: ∀ a, bk (fw a) = a
  bk_fw: ∀ b, fw (bk b) = b

def Bijection.inverse (α β: Type) (bij: Bijection α β)
  : Bijection β α where
  fw := bij.bk
  bk := bij.fw
  fw_bk := bij.bk_fw
  bk_fw := bij.fw_bk

structure Monoid where  -- Note: this lives in `Type 1`!
  τ: Type
  op: τ → τ → τ
  assoc: ∀ x y z, op (op x y) z = op x (op y z)
  id: τ
  id_op: ∀ x, op id x = x
  op_id: ∀ x, op x id = x

def Monoid.opposite (m: Monoid): Monoid where
  τ := m.τ
  op := λ x y => m.op y x
  assoc := by
    intro x y z
    symm   -- Apply symmetry to the goal equation
    exact m.assoc z y x
  id := m.id
  id_op := m.op_id
  op_id := m.id_op

/-
  We can _inherit_ all the declared fields af a `structure` into a new one.
-/
structure AbelianMonoid extends Monoid where
  comm: ∀ x y, op x y = op y x
/-
  Note how `op` correctly refers to the inherited field.

  Indeed, all the inherited fields are just there:
-/
def nat_additive_monoid: AbelianMonoid where
  τ := Nat
  op := Nat.add
  assoc := Nat.add_assoc  -- Theorems from the library
  id := 0
  id_op := Nat.zero_add
  op_id := Nat.add_zero
  comm := Nat.add_comm

def underlying_type: Type
  := nat_additive_monoid.τ  -- Field access

def underlying_identity: Nat
  := nat_additive_monoid.id

/-
  Inheritance also automatically provides a type conversion function.
  Effectively, this "forgets" the additional fields.
-/
#check AbelianMonoid.toMonoid

/-
  __Exercise__: Define the type of monoid homomorphisms.
-/
structure MonoidHom (m₁ m₂: Monoid) where
  some_fields: sorry

end Structures

end Dependent_sums

section Extensionality
/-
  When defining a structure, we can request the generation of an
  "extensionality" theorem, stating that two values having the structure
  type are equal if and only if they have the same fields.

  This is also convenient in the non-dependent case as well.
-/
@[ext] -- Request extensionality
structure Point where
  x: Nat
  y: Nat

#check Point.ext      -- Same coordinates → same point
#check Point.ext_iff  -- Same coordinates ↔ same point

/-
  The `ext` tactic can also be used in proofs to invoke `Point.ext`.
-/
example (p q: Point)
  (hx: p.x = q.x)
  (hy: p.y = q.y)
  : p = q
  := by
  ext -- applies Point.ext
  case x =>
    exact hx
  case y =>
    exact hy

end Extensionality

section Existential_quantification
/-
  The Curry-Howard correspondent of a dependent sum is an existentially
  quantified proposition
    `(a: α) × β a` ↔ `∃ a: α, β a`
-/
example (τ: Type): ∀ x: τ, ∃ y: τ, y = x
  := λ x => ⟨ x, rfl ⟩

/-
  A more complex example: if `R` is a symmetric and transitive relation
  such that `∀ x, ∃ y, R x y`, then it is also reflexive.
-/
def Reflexive {τ: Type} (R: τ → τ → Prop)
  := ∀ x, R x x
def Symmetric {τ: Type} (R: τ → τ → Prop)
  := ∀ {x y}, R x y → R y x
def Transitive {τ: Type} (R: τ → τ → Prop)
  := ∀ {x y z}, R x y → R y z → R x z

example (τ: Type) (R: τ → τ → Prop)
  (symm: Symmetric R)
  (tran: Transitive R)
  (conn: ∀ x, ∃ y, R x y)
  : Reflexive R
  := by
  unfold Reflexive -- Not needed, but expends the definition for clarity
  intro x
  have h4: ∃ y, R x y := conn x
  have ⟨ y , h5 ⟩ := h4  -- Eliminating the `∃`
  have h6: R y x := symm h5
  exact tran h5 h6

/-
  Note the "smart" use of `{ … }` above.

  __Exercise__: Replace all the braces with `( … )` and fix the proof.
  You can first add a few `_` for the additional arguments you need to
  pass. Replace those with the actual values. Note how the proof is now
  much worse to read.
-/

/-
  __Exercise__: Define primality on natural numbers.
  Exploit multiplication and quantifiers.
-/
def divides (n m: Nat): Prop
  := sorry

def prime (n: Nat): Prop
  := n > 1 ∧ sorry

section On_impredicativity
/-
  Consider a proof of an existential property:
-/
theorem solution_exists: ∃ n, n = 5 ∨ n = 7 := ⟨ 5 , .inl rfl ⟩
/-
  Recall that it is impossible to eliminate a proof of a proposition
  (in `Prop`) to construct a non-proof, a value of a type (in `Type`).

  In other words, this is not allowed:
    ```
    def solution: Nat := solution_exists.1
    ```
  Even if `solution_exists` is a pair, we can not project its first
  component and build a `Nat` value. This is because
  `solution_exists : ∃ n, … : Prop`, so it is a proof of a proposition, but
  the result type is `Nat : Type` which is not a proposition.

  We will be able to partially circumvent this using the axiom of choice
  `Classical.choose`:
-/
noncomputable def solution: Nat := Classical.choose solution_exists
/-
  Note that `solution` is an unknown value which depends on an axiom, and
  as such it can not be evaluated (e.g., using `#eval`). That's why we had
  to mark the `def` as `noncomputable`.

  It is _not_ defined as `5`, even if `h` uses `5`.

  Indeed, since impredicativity causes _proof irrelevance_, the choice axiom
  not convey any more information about the solution it picks, since it must
  pick the same solution when used on _any_ proof, as shown below:
-/
-- An apparently different proof.
theorem solution_exists₂: ∃ n, n = 5 ∨ n = 7 := ⟨ 7 , .inr rfl ⟩
-- By proof irrelevance, it is actually definitionally equal.
theorem same_proof: solution_exists = solution_exists₂ := rfl
-- Hence, the axiom of choice must pick the same solution in both cases.
theorem same_choice:
  Classical.choose solution_exists = Classical.choose solution_exists₂
  := rfl

/-
  We will return on the axiom of choice in the future.
-/
end On_impredicativity

end Existential_quantification

section Recap_exercises
/-
  __Exercise__: Define a function for the direct product of two monoids.
  To prove the involved properties, you can use
    `by simp [ prop1, prop2, … ]`
  asking Lean to try solving them automatically by exploiting the mentioned
  properties.
-/
def Monoid.prod (m₁ m₂: Monoid): Monoid  -- You can also use `where` here.
  := sorry

/-
  __Exercise__: Define a `Group` type.
-/

/-
  __Exercise__: Define a `Ring` type.
  It might be convenient to first define a `GroupOn (τ: Type)`, a group type
  that is parametrized by the underlying type `τ`.
-/

/-
  __Exercise__: Observe how the type of rational numbers `Rat` is defined in
  the libraries.
-/
#print Rat

/-
  __Exercise__:  Prove the following statements.
-/
example (τ σ: Type) (P: τ → σ → Prop)
  : (∃ x y, P x y) → ∃ y x, P x y
  := sorry

example (τ: Type) (P: τ → Prop) (q: Prop)
  : (∃ x, P x ∧ q) ↔ (∃ x, P x) ∧ q
  := sorry

example (τ: Type) (P: τ → Prop) (q: Prop)
  (t: τ) -- You will need this additional non-emptiness assumption.
  : (∃ x, P x ∨ q) ↔ (∃ x, P x) ∨ q
  := sorry

example (τ: Type) (P: τ → Prop) (q: Prop)
  : (∀ x, P x → q) ↔ ((∃ x, P x) → q)
  := sorry

/-
  __Exercise__: Formalize and prove the following statement, known as the
  "driker's lemma". The proof requires the use of `Classical.em`.

  In any non-empty bar, there is at least a person `p` such that, if `p`
  drinks, then _every person_ in the bar drinks.
-/

/-
  __Exercise__: Prove Cantor's theorem.
  There is no surjective function from `τ` to `τ → Prop`.
  This is the most famous proof "by diagonalization".
-/
theorem Cantor {τ: Type}
  (g: τ → (τ → Prop))
  : ¬ g.Surjective
  := by
  intro g_surj
  let diag: τ → Prop := sorry
  sorry

/-
  __Exercise__: Prove Lawvere's fixed point theorem.
  If there is a surjective function from `τ` to `τ → σ`, then any function
  `σ → σ` admits a fixed point.
  The proof is similar to the one for Cantor's theorem.

  Bonus: if you make this universe-polymorphic, you can derive Cantor's
  theorem as a corollary, by choosing `f = λ p => ¬ p`.
-/
theorem Lawvere {τ σ: Type}
  (g: τ → (τ → σ))
  (g_surj: g.Surjective)
  (f: σ → σ)
  : ∃s, f s = s
  := by
  let diag: τ → σ := sorry
  sorry

end Recap_exercises

end DependentSums
