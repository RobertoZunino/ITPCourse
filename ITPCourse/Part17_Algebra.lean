
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory


section The_free_monoid
/-
  We start by studying a simple algebraic structure: the free monoid.

  The free monoid over a type `α` is formed by the finite sequences of
  values in `α`, i.e., by the _lists_ of `α`.
-/
structure FreeMon (α: Type) where
  list: List α

/-
  We can associate a monoid structure to our `FreeMon α` type by providing
  a suitable instance for the standard library `Monoid` type class.
-/
instance instFreeMonoid {α: Type}
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

section On_library_conventions
/-
  Representing monoids, groups, and other algebraic structures is done
  in several different variants in the libraries. Below, we only discuss
  monoids for the sake of simplicity, but the same variants also apply to
  other algebraic structures.
-/

section Type_classes_vs_objects_in_a_category
/-
  Sometimes, a monoid is simply expressed by augmenting a base type `α` with
  an associated `Monoid` instance, as we did above.

  Other times, a monoid is instead represented as `A: MonCat`, an object in
  the category of monoids. The `MonCat` type is actually a structure (a
  dependent sum type) with fields
    `carrier: Type` and
    `str: Monoid carrier`
  effectively pairing the base type and the type class instance.
  The `MonCat.of` function pairs the carrier with the appropriate instance.
-/
example: MonCat := MonCat.of (FreeMon ℕ)

end Type_classes_vs_objects_in_a_category

section Multiplicative_vs_additive
/-
  By default, monoids are multiplicative. Given `x y: α` and `Monoid α`, the
  monoid operation is denoted as `x * y`, ad `1` is the neutral element.

  A separate type class `AddMonoid`, can be used instead if we want to adopt
  an additive notation, e.g., `x + y` and `0`.
-/
example {α} [Monoid α] (x y: α): α := x * y * 1
example {α} [AddMonoid α] (x y: α): α := x + y + 0
/-
  The `Multiplicative` and `Additive` functions can switch between
  notations.
-/
def onetwo: Additive (FreeMon ℕ) := FreeMon.mk [1,2]
def onetwoonetwo: Additive (FreeMon ℕ) := FreeMon.mk [1,2,1,2]
example: onetwo + onetwo + 0 = onetwoonetwo := by rfl

end Multiplicative_vs_additive

section Homomorphisms_and_isomorphisms
/-
  Given
    `α β: Type`
    `Monoid α`    (resp. `AddMonoid α`)
    `Monoid β`    (resp. `AddMonoid β`)
  an homomorphism is denoted as
    `f: α →* β`   (resp. ``f: α →+ β`)

  Isomorphisms can instead be expressed as
    `f: α ≃* β`   (resp. ``f: α ≃+ β`)

  When using categories, we instead have
    `α β: MonCat`
    `α ⟶ β` as generic category morphism
    `α ≅ β` as generic category isomorphism

  Il the library, there are suitable "bridge" results between the variants.
-/
example (α β: Type) [Monoid α] [Monoid β] (iso: α ≃* β)
  : MonCat.of α ≅ MonCat.of β
  := iso.toMonCatIso

example (α β: MonCat) (iso: α ≅ β)
  : α.carrier ≃* β.carrier
  := iso.monCatIsoToMulEquiv

/-
  The types for homomorphisms and isomorphisms are structures, whose fields
  contain the obvious function and properties. Given `f: α →* β` we have:
    `f.toFun: α → β` the plain function
    `f.map_one` the property `f 1 = 1`
    `f.map_mul` the property `f (x * y) = f x * f y`
  (The additive analogous are similar.)

  Homomorphisms and isomorphisms are automatically converted to the related
  function upon application.
-/
example (f: ℤ →+ ℤ): ℤ := f.toFun 42  -- Explicit hom-to-fun conversion
example (f: ℤ →+ ℤ): ℤ := f 42        -- Implicit conversion

example (f: AddMonCat.of ℤ ⟶ AddMonCat.of ℤ): ℤ
  := f.hom.toFun 42 -- Explicit conversion morphism-to-hom-to-fun
example (f: AddMonCat.of ℤ ⟶ AddMonCat.of ℤ): ℤ
  := f 42           -- Implicit conversion

end Homomorphisms_and_isomorphisms

end On_library_conventions

section Basic_examples_on_cyclic_groups
/-
  Integers modulo `n: ℕ` (ℤ/nℤ, or ℤₙ) are written in Lean as `ZMod n`. The
  libraries provide the well-known `AddGroup (ZMod n)` additive cyclic group
  structure.
-/
#check ZMod 4  -- ℤ₄
#check inferInstanceAs (AddGroup (ZMod 4))

example: ZMod 4 := 0   -- Constants are converted seamlessly
example: ZMod 4 := 1
example: ZMod 4 := 2
example: ZMod 4 := 3

example: 2 + 3 = (1: ZMod 4) := rfl

/-
  If `α β: Type` each form an `AddGroup`, then the product type `α × β` also
  has an associated group structure, given by their _direct product_.
-/
#check inferInstanceAs (AddGroup (ZMod 2 × ZMod 2))  -- ℤ₂ × ℤ₂

example: ZMod 2 × ZMod 2 := (0, 0)
example: ZMod 2 × ZMod 2 := (0, 1)
example: ZMod 2 × ZMod 2 := (1, 0)
example: ZMod 2 × ZMod 2 := (1, 1)

example: (0,1) + (1,1) = ((1,0): ZMod 2 × ZMod 2) := rfl
example: (0,1) + 0     = ((0,1): ZMod 2 × ZMod 2) := rfl

/-
  In group ℤ₂ × ℤ₂ adding any element to itself yields the neutral element.

  Proof by brutal case exhaustion.
-/
theorem ℤ₂_ℤ₂_plus_self
  (x: ZMod 2 × ZMod 2)
  : x + x = 0  -- This zero is the neutral element `(0, 0)`
  := by
  match x with
  | (0, 0) => rfl  -- A basic computation suffices to prove any equation.
  | (1, 0) => rfl
  | (0, 1) => rfl
  | (1, 1) => rfl

/-
  Exploiting the above result, we prove that the additive cyclic groups
    `ZMod 4` and `ZMod 2 × ZMod 2`
  are _not_ isomorphic.
-/
example
  (iso: ZMod 4 ≃+ ZMod 2 × ZMod 2)
  : False
  := by
  let osi := iso.symm  -- A name for the inverse
  suffices 0 ≠ (0: ZMod 4) by contradiction
  calc (0: ZMod 4)  -- A short computation in ℤ₄
    _ = osi 0               := by rw [map_zero]
    _ = osi (iso 1 + iso 1) := by rw [ℤ₂_ℤ₂_plus_self]
    _ = osi (iso (1 + 1))   := by rw [←map_add]
    _ = 1 + 1               := by rw [iso.symm_apply_apply]
    _ = 2                   := by rfl
    _ ≠ 0                   := by intro h ; cases h

/-
  The same result above, but using category-theoretic notation.

  Below, `iso ≫ osi` is `osi ∘ iso`.
-/
example
  (isom: AddGrp.of (ZMod 4) ≅ AddGrp.of (ZMod 2 × ZMod 2))
  : False
  := by
  let iso := isom.hom  -- A name for the forward morphism
  let osi := isom.inv  -- A name for the inverse morphism
  suffices 0 ≠ (0: ZMod 4) by contradiction
  calc (0: ZMod 4)  -- A short computation in ℤ₄
    _ = osi 0                := by rw [map_zero]
    _ = osi (iso 1 + iso 1)  := by rw [ℤ₂_ℤ₂_plus_self]
    _ = osi (iso (1 + 1))    := by rw [←map_add]
    _ = (iso ≫ osi) (1 + 1) := by simp
    _ = 1 + 1                := by rw [isom.hom_inv_id] ; simp
    _ = 2                    := by rfl
    _ ≠ 0                    := by intro h ; cases h

end Basic_examples_on_cyclic_groups

section Recap_exercises
/-
  __Exercise__: Prove a few simple monoid (or group) isomorphisms such as:
    `Unit × α ≃* α`
    `α × β ≃* β × α`
  Also try searching the libraries for help.
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
