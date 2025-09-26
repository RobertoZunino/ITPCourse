
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic


section The_free_monoid
/-
  The free monoid over a type `α` is formed by the finite sequences of
  values in `α`, i.e., by the _lists_ of `α`.
-/
structure FreeMon (α: Type) where
  list: List α

/-
  We can make this into a monoid using the standard `Monoid` type class.
-/
instance instFreeMonoid (α: Type)
  : Monoid (FreeMon α) where
  one := {list := []}
  mul a b := {list := a.list ++ b.list}
  mul_assoc := by simp [HMul.hMul]
  mul_one := by simp [HMul.hMul, OfNat.ofNat]
  one_mul := by simp [HMul.hMul, OfNat.ofNat]

/-
  A value `a: α` can be converted to elements of `FreeMon α` by taking the
  singleton list `[a]`.
  Hence, we have an inclusion ("`of`") from `α` to `FreeMon α`.
-/
def FreeMon.of {α} (a: α): FreeMon α
  := { list := [a] }

/-
  A fundamental property of the free monoid is a bijection between:
  - functions from _type_ `α` to (the underlying type of) a _monoid_ `β`
  - monoid homomorphisms from `FreeMon α` to monoid `β`.

  The type of plain functions is written as `α → β`.
  The type of homomorphisms is written as `FreeMon α →* β`.
  The type of bijections is therefore `(α → β) ≃ (FreeMon α →* β)`.
-/
def FreeMon.hom_equiv
  {α β: Type} [Monoid β]
  : (α → β) ≃ (FreeMon α →* β)
  := by
  constructor
  case toFun =>
    intro f
    exact
      { toFun := λ x => (x.list.map f).prod
      , map_one' := by simp [OfNat.ofNat, One.one]
      , map_mul' := by simp [HMul.hMul, Mul.mul]
      }
  case invFun =>
    intro h
    exact λ a => h (of a)
  case left_inv =>
    intro f
    simp [of]
  case right_inv =>
    intro h
    simp
    congr
    funext y
    cases y
    case mk ys =>
    simp
    induction ys
    case nil =>
      change _ = h 1
      rw [h.map_one]
      simp [OfNat.ofNat]
    case cons z zs ih =>
      simp
      rw [ih]
      rw [←h.map_mul]
      congr

/-
  Free monoids enjoy a _universal property_: any function from type `α` to
  monoid `β` factors through `FreeMon.of` in a unique way.
-/
theorem FreeMon.universal_property
  (α β: Type) [Monoid β]
  (f: α → β)
  : ∃! m: (FreeMon α →* β), f = m ∘ of
  := by
  exists hom_equiv f
  constructor
  case left =>
    -- We prove that `hom_equiv f` is indeed a factor of `f`.
    funext a
    simp [of, hom_equiv]
  case right =>
    -- We prove that the factor is unique.
    intro m h_m
    subst f
    symm
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    funext a
    simp [hom_equiv]

end The_free_monoid

section Recap_exercises
/-
  __Exercise__: Prove a few simple monoid (or group) isomorphisms such as:
    `Trivial × α ≅ α`
    `α × β ≅ β × α`
  Search the libraries for definitions, or provide your own.
-/

/-
  __Exercise__: (challenging) Define the free group over type `α`.

  The free group is given by those sequences in `List (Bool × α)` which are
  "reduced", i.e., no element `(b,a)` is adjacent to its inverse `(¬b,a)`.
  Formalize this property, define `FreeGrp α`, and prove it indeed forms a
  group.
-/

/-
  __Exercise__: (challenging) Extend the previous exercise and prove the
  universal property for free groups, following what we did for `FreeMon α`.
-/
end Recap_exercises
