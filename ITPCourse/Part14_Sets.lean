
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

section Set_notation
/-
  Previously, we saw that we can represent the "subsets" of a type `τ` using
  a function `τ → Prop`.
-/
example: ℕ → Prop
  := λ n => n < 20

/-
  This approach is embraced by the Lean libraries, that define `Set τ` in
  that way:
-/
#print Set

example: Set ℕ
  := λ n => n < 20

/-
  The library also provides a more familiar notation, hiding the fact that
  sets are represented as function `… → Prop`
-/
def less20: Set ℕ
  := { n: ℕ | n < 20 }

example: 10 ∈ less20
  := by
  dsimp [less20] -- Expand the definitions
  decide         -- Compute using the `Decidable` type class

/-
  A plethora of variations on the syntax `{ … | … }` is available from the
  libraries. Here we only mention a few examples.
  Note that there is some special handling of relations like `<` and `⊆`.
-/
example: Set ℕ := { n | n < 10 }
example: Set ℕ := { n < 10 | n > 5 }
example: Set ℕ := { n^2 + n + 2 | n > 5 }
example: Set ℕ := { n^2 + n + 2 | (n: ℕ) (prop: n > 5 ∧ n < 20) }
example: Set (Set ℕ) := { s | ∀ n ∈ s, 1 ≤ n ∧ n ≤ 20 }
example: Set (Set ℕ) := { {n, n+1} | n: ℕ }
example: Set (Set ℕ) := { {n, n+1} | (n: ℕ) (prop: n > 20) }

example: Set ℕ := { n | n > 5 ∧ n < 10 }

/-
  Not all "reasonable" notations are accepted: for instance, these are
  allowed
-/
example: Set ℕ := { n | n > 5 ∧ n < 10 }
example: Set ℕ := { n+1 | n > 5 }
/-
  but `{ n+1 | n > 5 ∧ n < 10 }` is not allowed. It can be defined in one of
  the following ways:
-/
example: Set ℕ := { n+1 | (n: ℕ) (prop: n > 5 ∧ n < 10) }
example: Set ℕ := { n+1 | (n: ℕ) (prop1: n > 5) (prop2: n < 10) }
example: Set ℕ := { m | ∃ n: ℕ, m = n+1 ∧ n > 5 ∧ n < 10 }

/-
  The scoping of variables can be tricky. Here `a` is the function argument,
  while `n` ranges over all naturals `> 10`.
-/
example: ℕ → Set ℕ := λ a => { n+a | n > 10 }
-- Alternatively:
example: ℕ → Set ℕ := λ a => { n+a | (n:ℕ) (prop: n > 10) }

/-
  We can also write enumerated sets:
-/
example: {1,2} = { n: ℕ | n=1 ∨ n=2 } := rfl

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
  ⋂ n: ℕ, { m: ℕ | m ≥ n } = ∅
  := by
  apply Set.ext -- The extensionality principle
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
  : ⋂ n: ℕ, { m: ℕ | m ≥ n } = ∅
  := by
  ext x  -- Similar to `apply Set.ext ; intro x`
  case h =>
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
  : ⋂ n ∈ ({1 , 2} : Set ℕ), {n} = ∅
  := by
  ext x
  case h =>
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
  : ⋂₀ { { m: ℕ | m ≥ n } | n: ℕ } = ∅
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
  ext x
  case h =>
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
example {s₁ s₂: Set ℕ}: s₁ ∩ s₂ = s₂ ∩ s₁ := by exact Set.inter_comm s₁ s₂
example {s₁ s₂: Set ℕ}: s₁ ∪ s₂ = s₂ ∪ s₁ := by exact Set.union_comm s₁ s₂
example {s: Set ℕ}: s \ s = ∅ := by simp
example {s: Set ℕ}: sᶜ ∩ s = ∅ := by exact Set.compl_inter_self s

/-
  __Exercise__: Prove the following.
-/
example {τ: Type} {A: Set τ} {B: ℕ → Set τ}:
  A ∩ ⋂ n: ℕ, B n
  =
  ⋂ n: ℕ, A ∩ B n
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
  n: ℕ
  prop: n < 20

example: less20_struct := ⟨ 5 , by decide ⟩

example: Type := List less20_struct  -- This is now OK.

/-
  The Lean libraries, however, allow a more familiar syntax for this kind of
  set-like dependent sums:
-/
def less20_τ: Type := { n: ℕ // n < 20 }
                            -- ↑↑ Note the // instead of |

example: less20_τ := ⟨ 5 , by decide ⟩

example: Type := List less20_τ   -- This is OK.

/-
  To convert `x: less20_τ` into a `ℕ` we can use `x.val` (or `x.1`).
  Instead, `x.mem` (or `x.2`) certifies that `x.val` belongs to the set.
-/
example: less20_τ → ℕ
  := λ x => x.val

example (x: less20_τ): x.val < 20
  := x.mem

/-
  Note that, when using set-like types, we do not have a real way to write
  `… ∈ less20_τ` in the middle of a general formula, for the same reason we
  can not write `(x : τ) ∨ p`. Lean terms must be typed, so their syntax
  already mandates if they live inside a type or not.
-/

def less10_τ: Type := { n: ℕ // n < 10 }

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

section Finite_sets
/-
  The finiteness of a set `S` can be defined in several equivalent ways.

  One is to require an enumeration of `S`.
-/
def Finite₁ {α: Type} (S: Set α)
  := ∃ n: ℕ,
    -- f: {0 .. n-1} → α
    ∃ f: (x: ℕ) → x < n → α,
    -- f surjective on S
    ∀ s ∈ S, ∃ x h, f x h = s

/-
  Another way instead uses inductively defined predicates.
-/
inductive Finite₂ {α: Type}: Set α → Prop
| empty: Finite₂ ∅
| insert: ∀ s S, Finite₂ S → Finite₂ (S ∪ {s})

/-
  We now prove they are equivalent.

  Here is the first implication: if `S` is finitely enumerable then it is
  finite in the inductive sense.
-/
theorem Finite₁_to_Finite₂ {α: Type} (S: Set α)
  : Finite₁ S → Finite₂ S
  := by
  intro S_fin
  have ⟨ n , f , f_surj ⟩ := S_fin
  clear S_fin
  revert S f
  induction n

  case zero =>
    intro S f f_surj
    have S_empty: S = ∅
      := by
      ext s
      simp only [Set.mem_empty_iff_false, iff_false]
      intro s_in_S
      have ⟨ k , k_neg , h ⟩  := f_surj s s_in_S
      contradiction -- `k: ℕ` can not be negative
    subst S
    exact Finite₂.empty

  case succ n ih =>
    intro S f f_surj
    let f' (x : ℕ) (h: x < n): α
      := f x (by linarith)
    let fn: α := f n (by linarith)

    let S' := { f x (by linarith)
      | (x: ℕ) (h: x < n) (in_S: f x (by linarith) ∈ S) }

    have S'_sub_S: S' ⊆ S
      := by
      unfold S'
      intro s
      simp only [Set.mem_setOf_eq, forall_exists_index]
      intro x x_lt_n f_in_S f_s
      subst s
      exact f_in_S

    have S_sub_S': S ⊆ S' ∪ {fn}
      := by
      unfold S'
      intro s
      simp only [Int.reduceNeg, Int.reduceMul, Int.rawCast.eq_1,
        Int.cast_eq, Nat.rawCast.eq_1, Nat.cast_id, Int.cast_ofNat_Int,
        Nat.cast_ofNat, Int.reduceAdd, Int.ofNat_eq_coe, eq_mp_eq_cast,
        id_eq, Int.natCast_add, exists_prop, Set.union_singleton,
        Set.mem_insert_iff, Set.mem_setOf_eq]
      intro s_in_S
      have ⟨ x , x_lt , f_s ⟩ := f_surj s s_in_S
      have h1: x ≤ n := by linarith
      replace h1: x = n ∨ x < n := Nat.eq_or_lt_of_le h1
      cases h1
      case inl x_eq =>
        left
        subst x
        subst s
        rfl
      case inr x_lt2  =>
        right
        case h =>
        exists x
        exists x_lt2
        constructor
        case left =>
          rw [f_s]
          exact s_in_S
        case right =>
          rw [f_s]

    cases (Classical.em (S = S'))

    case inl S_eq_S' =>
      rw [S_eq_S']
      refine ih S' f' ?f'_surj
      case f'_surj =>
        intro s s_in_S'
        unfold S' at s_in_S'
        have ⟨ x , x_lt , in_S , eq_s ⟩  := s_in_S'
        exists x
        exists x_lt

    case inr S_neq_S' =>
      have fn_in_S: fn ∈ S
        := by
        by_contra fn_notin_S -- by contradiction
        apply S_neq_S'
        apply subset_antisymm
        case a =>
          intro s s_S
          cases S_sub_S' s_S
          case inl h =>
            exact h
          case inr h =>
            simp_all only [Set.union_singleton, Set.mem_singleton_iff]
        case a =>
          exact S'_sub_S

      have S_eq_S'fn: S = S' ∪ {fn}
        := by
        apply subset_antisymm
        case a =>
          exact S_sub_S'
        case a =>
          apply Set.union_subset_iff.mpr
          constructor
          case left =>
            exact S'_sub_S
          case right =>
            exact Set.singleton_subset_iff.mpr fn_in_S

      rw [S_eq_S'fn]
      apply Finite₂.insert fn
      case a =>
        apply ih S' f' ?f'_surj
        case f'_surj =>
          intro s s_in_S'
          unfold S' at s_in_S'
          have ⟨ x , x_lt , in_S , eq_s ⟩ := s_in_S'
          exists x
          exists x_lt

/-
  Here is the second implication: if `S` is finite in the inductive sense
  then it is finitely enumerable.
-/
theorem Finite₂_to_Finite₁ {α: Type} (S: Set α)
  : Finite₂ S → Finite₁ S
  := by
  intro h
  induction h

  case empty =>
    let f (x: ℕ) (n_lt: x<0): α
      := by contradiction -- the domain is empty
    exists 0
    exists f
    intro x x_lt
    contradiction

  case insert s' S' ih2 ih =>
    have ⟨ n , f , h_f ⟩ := ih
    let f' (x: ℕ) (x_lt: x<n+1): α
      := if x_lt2: x<n
      then f x (by linarith)
      else s'
    exists n+1
    exists f'
    intro s s_in_S's
    cases s_in_S's
    case inl s_in_S' =>
      have ⟨ x , x_lt , f_eq ⟩ := h_f s s_in_S'
      exists x
      exists (by linarith)
      unfold f'
      simp only [x_lt, ↓reduceDIte]
      exact f_eq
    case inr s_eq_s' =>
      simp at s_eq_s'
      subst s
      exists n
      exists (by linarith)
      unfold f'
      simp only [lt_self_iff_false, ↓reduceDIte]

-- The equivalence.
theorem Finite₂_iff_Finite₁ {α: Type} (S: Set α)
  : Finite₁ S ↔ Finite₂ S
  := ⟨ Finite₁_to_Finite₂ S , Finite₂_to_Finite₁ S ⟩

/-
  __Exercise__: Observe how the libraries define the finiteness of a set,
  by checking out how `Set.Finite` is defined.
  For a challenge, prove the next statement.
-/
#check Set.Finite

example {α: Type} (S: Set α)
  : Finite₁ S ↔ Set.Finite S
  := sorry

/-
  In the library there is a special type for finite sets, `Finset`:
-/
example: Finset ℕ := {2,3,7}

/-
  Converting a `Set` to a `Finset` and back is possible, under the obvious
  assumptions.
-/
noncomputable
def Set_to_Finset {τ: Type}: (S: Set τ) → S.Finite → Finset τ :=
  by
  intro S h
  exact Set.Finite.toFinset h

def Finset_to_Set {τ: Type}: Finset τ → Set τ := Finset.toSet

/-
  __Exercise__: Prove these conversions are inverses, completing the proofs
  below.
  Use `unfold` and `simp` to get some help from the library.
-/
example {τ: Type} (F: Finset τ)
  : Set_to_Finset (Finset_to_Set F) (Finset.finite_toSet F) = F
  := by
  apply Finset.ext _
  intro x
  sorry

example {τ: Type} (S: Set τ) (S_fin: S.Finite)
  : Finset_to_Set (Set_to_Finset S S_fin) = S
  := by
  apply Set.ext _
  intro x
  sorry

end Finite_sets

section Finite_sums
/-
  In the library, finite sums `∑ i ∈ S, f i` are defined in terms of
  `Finset`.
-/
example: (∑ i ∈ {1,2,3}, i^2) = 1 + 4 + 9
  := rfl

/-
  The finite set of naturals `{0,1,…,n-1}` is `Finset.range n`.
-/
example: (∑ i ∈ Finset.range 11, i) = 55
  := rfl

/-
  Interval notation like `Set.Iio n` can also be used.
-/
example: (∑ i ∈ Set.Iio 11, i) = 55
  := rfl

/-
  A convenient shortcut:
-/
example: (∑ i < 11, i) = 55
  := rfl

/-
  The library allows to manipulate finite sums in several ways.
  Below, we show how `Finset.sum_range_succ` can be used to isolate a term
  in the sum.
-/
example (k: Nat) (f: Nat → Nat)
  : (∑ n < k+1 , f n)
  = (∑ n < k , f n) + f k
  := by
  rw [Nat.Iio_eq_range]
  apply Finset.sum_range_succ

/-
  Here is the classic inductive proof of the formula for 1+2+…+n.

  Note that we cast numbers to `Rat`, so that `/ 2` is the actual division
  and not the quotient. In this way we can use `ring` to close some subgoals
  more easily.
-/
example (n: Nat)
  : (∑ i ≤ n, i: Rat) = n * (n+1) / 2
  := by
  rw [←Finset.Iio_succ_eq_Iic]
  rw [Nat.Iio_eq_range]
  simp only [Nat.succ_eq_succ, Nat.succ_eq_add_one, mul_one]
  induction n
  case zero =>
    dsimp
    rw [Finset.sum_singleton]
    ring
  case succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    push_cast
    ring

end Finite_sums

section Recap_exercises
/-
  __Exercise__: Prove the following.
-/
example
  (α β γ: Type)
  (f: α → β) (g: β → γ)
  (s: Set α)
  : (g ∘ f) '' s = g '' (f '' s)
  := sorry

/-
  __Exercise__: Find which inclusions hold between
    `f ⁻¹' (f '' S)   ⊆?⊇   S`
    `f '' (f ⁻¹' T)   ⊆?⊇   T`
  and prove them.
-/

/-
  __Exercise__: Find how images and preimages behave when dealing with
  unions and intersections.
    `f '' (S ∪ T)   ⊆?⊇   (f '' S) ∪ (f '' T)`
    `f '' (S ∩ T)   ⊆?⊇   (f '' S) ∩ (f '' T)`
    `f ⁻¹' (S ∪ T)   ⊆?⊇   (f ⁻¹' S) ∪ (f ⁻¹' T)`
    `f ⁻¹' (S ∩ T)   ⊆?⊇   (f ⁻¹' S) ∩ (f ⁻¹' T)`
-/
end Recap_exercises
