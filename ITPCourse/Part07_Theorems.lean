/-
  We now discuss how to prove logical statements in Lean beyond basic
  equalities.
-/

section The_Curry_Howard_isomorphism
/-
  So far we focused on how to define mathematical objects in Lean.

  It turns out that the _same_ techniques can be applied to prove theorems
  as well. This is because there is a strong correspondence between
  propositions as types, known as the _Curry-Howard_ isomorphism.

  In brief, we have the following correspondences:

    Propositions            ↔ Types
    `True`                  ↔ `Unit`
    `False`                 ↔ `Empty`
    `p ∧ q` (conjunction)   ↔ `p × q` (product type)
    `p ∨ q` (disjunction)   ↔ `p ⊕ q` (sum types)
    `p → q` (implication)   ↔ `p → q` (function type)
    `∀ a:A, P a` (for all)  ↔ `(a:A) → P a` (dependent product type)

  The underlying idea is to regard a proposition as a _type_ denoting all
  the possible proofs for that proposition. Under this idea:

  - `True` has one proof, like `Unit` has one value.
  - `False` has no proofs, like `Empty` has no values.
  - A proof for `p ∧ q` is a pair `(proof_of_p, proof_of_q)`, like with
    product types.
  - A proof for `p ∨ q` is either `Or.inl proof_of_p` or `Or.inr proof_of_q`
    like with sum types.
  - A proof for `p → q` is a function that maps proofs of `p` into proofs of
    `q`, like with function types.
  - A proof for `∀ a:A, P x` is a function that maps any value `a:A` into a
    proof of `P a`.

  Propositions are therefore types, and they live in the `Prop` universe.
-/

/-
  Let's see a few examples. We recommend to move your cursor to the proofs
  blow and observe what type of variables are in scope at each point. These
  are effectively the hypotheses available at that point in the proof.

  Proving that `p → p` for any `p` essentially amounts to define the
  polymorphic identity
-/
theorem simple_implication: ∀ p: Prop, p → p
  := λ _p h => h   -- `h` is essentially an "hypothesis", here

/-
  Transitivity of `→` is proved by composing functions:
-/
theorem implication_trans: ∀ p q r: Prop, (p → q) → (q → r) → (p → r)
  := λ _p _q _r h1 h2 pr_p => h2 (h1 pr_p)

/-
  Commutativity of the `∧` corresponds to swapping pair components:
-/
theorem and_commut₁ (p q: Prop) (h: p ∧ q): q ∧ p
  := ⟨ h.2, h.1 ⟩

theorem and_commut₂ (p q: Prop) (h: p ∧ q): q ∧ p
  := match h with
  | ⟨ pr_p, pr_q ⟩ => ⟨ pr_q, pr_p ⟩

/-
  Idempotency of the `∨` is easily established:
-/
theorem or_idempot (p: Prop) (h: p ∨ p): p
  := match h with
  | .inl pr_p => pr_p  -- `Or.inl` can be shortened to `.inl`
  | .inr pr_p => pr_p  -- `Or.inr` can be shortened to `.inr`

/-
  `True` introduction is proved by `True.intro`.
-/
theorem triviality: True := True.intro

/-
  `False` elimination is done by `False.elim`
-/
theorem false_identity_for_or (p: Prop) (h: False ∨ p): p
  := match h with
  | .inl pr_false => pr_false.elim   -- This contradiciton proves anything!
  | .inr pr_p     => pr_p

/-
  A theorem involving a `∀` quantifier.
  Note that here `P: Nat → Prop` makes `P` a property on naturals.
-/
theorem all_or (P: Nat → Prop) (h: ∀ a b, P a ∨ P b): ∀ n, P n
  := λ n => or_idempot (P n) (h n n)   -- `P n` could also be `_`
/-
  Carefully inspect the types above.
  `h n n` has type `P n ∨ P n`, so `or_idempot` ends the proof.

  Note in passing that it would make sense to make the first argument of
  `or_idempot` to be implicit, so that we can hide that noise in the proof.
-/
end The_Curry_Howard_isomorphism

section Exercises
/-
  __Exercise__: Here is a list of propositions you can prove.
-/
example (p: Prop): p → (p ∧ True)
  := sorry

example (p: Prop): p → (p ∧ p)
  := sorry

example (p q r: Prop): (p → q → r) → (p ∧ q → r)
  := sorry

example (p q r: Prop): (p ∧ q → r) → (p → q → r)
  := sorry

example
  (f: Nat → Nat)
  (P Q: Nat → Prop)
  (h1: ∀ x, P x → Q (f x))
  (h2: ∀ y, P y)
  : ∀ n, Q (f n)
  := sorry

example  -- More challenging
  (f: Nat → Nat)
  (P: Nat → Prop)
  (h: ∀ x, P x → P (f x))
  : ∀ n, P n → P (f (f n))
  := sorry

example (p q: Prop): p → (q → p)
  := sorry

example (p q r: Prop): (p → q) → (p → q → r) → (p → r)
  := sorry

example (p q r: Prop): ((p → q) → p) → ((q → p) → q) → p ∧ q
  := sorry

example (p p' q q': Prop):
  (p → p') → (q → q') → (p ∧ q → p' ∧ q')
  := sorry

example (p p' q q': Prop):
  (p → p') → (q → q') → (p ∨ q → p' ∨ q')
  := sorry

example (p p' q q': Prop):
  (p' → p) → (q → q') → ((p → q) → (p' → q'))
  := sorry

end Exercises

section More_connectives
/-
  Negation `¬ p` stands for `p → False`.
-/
example (p: Prop): ¬(p ∧ ¬ p)
  := sorry

example (p q: Prop): ¬ q → (p ∨ q) → p
  := sorry

/-
  If-and-only-if `p ↔ q` is similar to `(p → q) ∧ (q → q)`.

  Check out `Iff.intro` and `Iff.elim` to understand how to use it.
  Alternatively, use the notation `⟨ … , … ⟩`, which works on all
  product-like types.
-/
theorem iff_example₁ (p: Prop): p ↔ (p ∨ p)
  := Iff.intro (.inl) (or_idempot p)
theorem iff_example₂ (p: Prop): p ↔ (p ∨ p)
  := ⟨ .inl , or_idempot p ⟩

example (p: Prop): p → p ∨ p
  := (iff_example₁ p).1
example (p: Prop): p → p ∨ p
  := (iff_example₁ p).mp
example (p: Prop): p → p ∨ p
  := match iff_example₁ p with
  | ⟨ pr , _ ⟩ => pr

/-
  __Exercise__: Prove the following.
-/
theorem yoneda (p: Prop)
  : p ↔ (∀ q: Prop, (p → q) → q)
  := sorry

example: False ↔ (∀ q: Prop, q)
  := sorry
example: True ↔ (∀ q: Prop, q)
  := sorry
example (p q: Prop)
  : p ∧ q ↔ (∀ r: Prop, p → q → r)
  := sorry
example (p q: Prop)
  : p ∨ q ↔ (∀ r: Prop, (p → r) → (q → r) → r)
  := sorry

end More_connectives

section Classical_logic
/-
  The logical system seen so far is powerful and can prove many theorems we
  can find in everyday mathematics. However, it can not prove them all.

  The logic seen so far is called _intuitionistic_, or _constructive_ logic,
  and is weaker than _classical_ logic, which lies at the foundation of
  modern mathematics. The most famous example of a classical theorem that is
  not intuitionistic is the law of excluded middle:
-/
def excluded_middle: Prop := ∀ p: Prop, p ∨ ¬ p
/-
  We will not show that `excluded_middle` is not provable with what we saw
  so far, but as an informal argument we might observe that a proof of this
  law (made under no assumptions) should intuitively reduce to one of these
  forms:
    `λ p => .inl proof_of_p`
    `λ p => .inr proof_of_¬p`
  However, if any one of these existed we could craft one of the following:
    `λ p => proof_of_p`  of type `∀ p: Prop, p`
    `λ p => proof_of_¬p` of type `∀ p: Prop, ¬p`
  and neither can exist without breaking the logic!

  However, even if it's not _provable_, we can still take it as an
  _assumption_.
-/
theorem em_example₁ (em: excluded_middle) (p q: Prop)
  : p ∨ (p → q)
  := match em p with
  | .inl pr_p  => .inl pr_p
  | .inr pr_np => .inr (λ pr_p => (pr_np pr_p).elim)

/-
  We can do even better. In Lean the law of excluded middle is already
  present in the standard library as a theorem which is proved from a few
  lower-level `axiom`s. We can use it through the name `Classical.em`. On
  use, the `axiom`s are silently added as implicit "invisible" assumptions,
  in the same spirit as much in the spirit of the previous example.
-/
theorem em_example₂ (p q: Prop)
  : p ∨ (p → q)
  := match Classical.em p with
  | .inl pr_p  => .inl pr_p
  | .inr pr_np => .inr (λ pr_p => (pr_np pr_p).elim)

#check em_example₂         -- No `em` assumption shown
#print axioms em_example₂  -- Three axioms implicitly used!

#check em_example₁         -- Explicit `em` assumption shown
#print axioms em_example₁  -- No axioms

/-
  Finally, note that adding `excluded_middle` to intuitionistic logic is
  enough to make it as powerful as classical logic.

  We can now make "proofs by cases" such as the following:
-/
example (p q r: Prop)
  (h1: p  → q)
  (h2: ¬p → r)
  : q ∨ r
  := match Classical.em p with
  | .inl pr_p  => .inl (h1 pr_p)
  | .inr pr_np => .inr (h2 pr_np)

/-
  __Exercise__: Prove the De Morgan's laws.
-/
example (p q: Prop)
  : ¬(p ∧ q) ↔ ¬ p ∨ ¬ q
  := sorry

example (p q: Prop)
  : ¬(p ∨ q) ↔ ¬ p ∧ ¬ q
  := sorry

/-
  __Exercise__: Prove the following.
-/
theorem peirce's_law (p q: Prop)
  : ((p → q) → p) → p
  := sorry

theorem double_negation (p: Prop)
  : ¬ ¬ p → p
  := sorry

theorem contrapositive (p q: Prop)
  : (p → q) ↔ (¬q → ¬p)
  := sorry

end Classical_logic

section Impredicativity
/-
  As a technical note, we remark that the type of propositions `Prop` is
  rather special, in that it is an _impredicative_ universe.

  Concretely, "for all" propositions, which are dependent product types,
  follow the following type formation rule:

    if  `x: τ` where `τ` is any type living in any universe
    and `P: τ → Prop`
    then `(x: τ) → P t` (which is the same as `∀ x: τ, P t`) is a type
         living in universe `Prop`.

  Note that `τ` can live in any universe (e.g. `Type 100`), yet the
  resulting "for all" proposition is fixed to be `Prop`. With predicative
  universes, `τ: Type u` would force the dependent product to live in
  `Type (max u …)`. Having a codomain in `Prop` keeps the universe level
  down.
-/

section Why_impredicativity?
/-
  Why is impredicativity important?

  Well, without it we could not easily write properties which quantify over
  "all the propositions".
-/
def Leibniz_equality (τ: Type) (a b: τ): Prop
  := ∀ P: τ → Prop, P a → P b
/-
  If we only use predicative universes, we must use a higher universe, and
  that can cause issues later on.
-/
def Leibniz_equality_in_type (τ: Type) (a b: τ): Type 1
  := ∀ P: τ → Type, P a → P b
/-
  __Exercise__: (challenging)
  Try proving reflexivity and symmetry of these relations.
  Note that the impredicative relation can be exploited when choosing `P`,
  so symmetry can be proved by claiming that since `a` has the property of
  being equal to `a`, then `b` must satisfy the same property.
  The predicative relation prevents the same proof to be used.
  (It can still be proved symmetric, but we might not have seen enough Lean
  to handle that at this time.)
-/
end Why_impredicativity?

section Why_predicativity?
/-
  Counterpoint: if impredicativity is good to have, why don't we make `Type`
  impredicative like `Prop`?

  The issue is that impredicativity comes at a cost: in the presence of a
  few axioms like excluded middle and choice, it causes _proof irrelevance_:
  any two proofs `pr₁ pr₂: p` of the same theorem `p: Prop` are necessarily
  equal: `pr₁ = pr₂`. This is known as the Barbanera-Berardi paradox.

  This is not a significant issue in `Prop`, since when dealing with
  propositions we care only about whether a proof exists or not -- whether
  we have more than one proof, or whether two proofs are equal are legit
  questions but they are not nearly as interesting.

  Lean completely embraces proof irrelevance in `Prop`, making any two
  proofs of the same theorem to always by considered _definitionally_ equal:
-/
theorem true_or_true₁: True ∨ True := .inl True.intro
theorem true_or_true₂: True ∨ True := .inr True.intro
example: true_or_true₁ = true_or_true₂ := rfl
/-
  Proof irrelevance is fine in `Prop`, but we can not accept it in `Type`.
  If `Type` were impredicative, consequently causing proof irrelevance, we
  would have `true = false` in `Bool`, and `0 = 1` in `Nat`, since they
  would be proofs/terms of the same proposition/type.

  For these reasons, the best choice is to have an impredicative universe
  for propositions (`Prop`) and use predicative universes for everything
  else (`Type u`).
-/
end Why_predicativity?

section The_general_dependent_product_type_formation_rule
/-
  If you are curious, the full general rule for dependent products, working
  in all universes is:

    if  `x: τ` where `τ: Sort u`
    and `f: τ → Sort v`
    then `(x: τ) → P t` is a type living in universe `Sort (imax u v)`
    where `imax u v` is `0` if `v = 0` and `max u v` otherwise.

  You can then obtain the predicative and impredicative type formation rules
  from the above and by recalling `Prop = Sort 0` and `Type u = Sort (u+1)`.
-/
end The_general_dependent_product_type_formation_rule

end Impredicativity

-- TODO first tactics

-- propext, funxext
