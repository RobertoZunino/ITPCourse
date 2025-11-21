
import Mathlib.Data.Real.Basic
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Compactness.Compact


section Basic_linear_algebra
/-
  `Fin n` is a finite type with `n` values.

  Roughly, we can think of it as the type of the naturals `< n`.
-/
example (n: ℕ)
  : FinEnum.card (Fin n) = n
  := FinEnum.card_fin

/-
  Consequently, `Fin n → ℝ` is a way to express the linear space `ℝⁿ`.

  Vectors in such linear space can be written as `![x₁, x₂, …]`.
-/
example: Fin 3 → ℝ := ![0, -4, 5.67]

/-
  Matrices can be similarly expressed as `Fin n → Fin m → ℝ`.
  Alternatively, `Matrix (Fin n) (Fin m) ℝ` denotes the same type.
-/
example: Matrix (Fin 3) (Fin 3) ℝ
  := -- A 3×3 matrix
  ![ ![ 1, 2, 3]
   , ![ 4, 5, 6]
   , ![ 7, 8, 9]
  ]

/-
  We now prove that four 3-dimensional vectors can not be linearly
  independent.

  Below, note that `![v₁, v₂, v₃, v₄]` is essentially a 4×3 matrix.
-/
example
  (v₁ v₂ v₃ v₄: Fin 3 → ℝ)  -- Vectors in ℝ³
  : ¬ LinearIndependent ℝ ![v₁, v₂, v₃, v₄]
  := by
  intro ind
  have h := LinearIndependent.fintype_card_le_finrank ind
  dsimp at h
  simp at h

/-
  Linear spaces in Lean are modelled as _modules_ over a _field_.
  This uses a few type classes.
-/
example
  (K V: Type)
  [Field K]         -- Needed to make the module into a linear space
  [AddCommGroup V]  -- Also required to make a linear space
  [Module K V]
  : V
  := 0 -- The null vector of `V`

/-
  The product of two linear spaces.

  The required `Module` instance is already defined in the libraries.
-/
example
  (K U V: Type)
  [Field K]
  [AddCommGroup U] [AddCommGroup V]
  [Module K U] [Module K V]
  : Module K (U × V)
  := inferInstance

/-
  Linear maps are denoted with `V →ₗ[K] U` (a suitable structure).
  We can define the diagonal map `x ↦ (x,x)` as follows:
-/
example
  (K V: Type)
  [Field K]
  [AddCommGroup V]
  [Module K V]
  : V →ₗ[K] V × V
  := by
  -- We provide the map …
  apply IsLinearMap.mk' (λ x: V => (x,x))
  -- … and prove its linearity exploiting automation.
  constructor <;> simp_all

/-
  A linear map is injective when it has null kernel.
-/
example
  (K U V: Type)
  [Field K]
  [AddCommGroup U] [AddCommGroup V]
  [Module K U] [Module K V]
  (f: V →ₗ[K] U)
  (f_null_ker: LinearMap.ker f = ⊥)
  : (⇑f).Injective
  := by
  intro v₁ v₂ eq
  have diff_in_ker: (v₁ - v₂) ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker]
    calc f (v₁ - v₂)
    _ = f v₁ - f v₂ := by simp
    _ = f v₁ - f v₁ := by rw [eq]
    _ = 0           := by simp
  rw [f_null_ker, Submodule.mem_bot, sub_eq_zero] at diff_in_ker
  exact diff_in_ker

/-
  The same exercise, but exploiting the libraries.
-/
example
  (K U V: Type)
  [Field K]
  [AddCommGroup U] [AddCommGroup V]
  [Module K U] [Module K V]
  (f: V →ₗ[K] U)
  (f_null_ker: LinearMap.ker f = ⊥)
  : (⇑f).Injective
  := LinearMap.ker_eq_bot.mp f_null_ker

/-
  If `U` and `V` are linear subspaces of `W`, then `U ∩ V` is still a linear
  subspace.
-/
def linear_spaces_intersection₁
  {K W: Type}
  [Field K]
  [AddCommGroup W]
  [Module K W]
  (U: Submodule K W)
  (V: Submodule K W)
  : Submodule K W
  where
  carrier := U.carrier ∩ V.carrier
  add_mem' := by
    -- Note: `simp_all [Submodule.add_mem]` would suffice.
    -- We provide a more detailed proof anyway.
    intro x y hx hy
    have ⟨ hxu , hxv ⟩ := hx
    have ⟨ hyu , hyv ⟩ := hy
    constructor
    . exact U.add_mem' hxu hyu
    . exact V.add_mem' hxv hyv
  zero_mem' := by
    -- Note: `simp_all` would suffice.
    constructor
    . exact U.zero_mem'
    . exact V.zero_mem'
  smul_mem' := by
    -- Note: `simp_all [Submodule.smul_mem]` would suffice.
    intro c x hx
    have ⟨ hxu , hxv ⟩ := hx
    constructor
    . exact U.smul_mem' c hxu
    . exact V.smul_mem' c hxv

/-
  The intersection of two subspaces is, of course, already defined in the
  libraries. Subspaces are ordered by inclusion, so their "infimum" `U ⊓ V`
  already denotes the intersection.
-/
def linear_spaces_intersection₂
  {K W: Type}
  [Field K]
  [AddCommGroup W]
  [Module K W]
  (U: Submodule K W)
  (V: Submodule K W)
  : Submodule K W
  := U ⊓ V  -- The infimum

/-
  We now prove that there are no injective linear functions `U →ₗ V` between
  when `U` has a higher dimension than `V`.
-/
example
  (K U V: Type)
  [Field K]
  [AddCommGroup U] [AddCommGroup V]
  [Module K U] [Module K V]
  (f: U →ₗ[K] V)
  (U_higher_dim_V: Module.rank K U > Module.rank K V)
  : ¬ (⇑f).Injective
  := by
  intro f_inj
  -- Let's take a basis of `U`
  have ⟨ ix_U , ⟨ basis_U ⟩ ⟩ := Module.Basis.exists_basis K U
  -- The cardinality of the basis is the dimension
  have rank_U: Cardinal.mk ix_U = Module.rank K U
    := Module.Basis.mk_eq_rank'' basis_U
  -- We define a family of vectors of `V`
  let fam_V (i: ix_U): V := f (basis_U i)
  -- We prove the family having independent vectors
  have fam_indip: LinearIndependent K fam_V
    := by
    intro v₁ v₂ h
    apply basis_U.linearIndependent
    apply f_inj
    simp [Finsupp.linearCombination, fam_V] at h ⊢
    simp [map_finsuppSum, map_smul, h]
  -- Therefore, the dimension of `V` is at least the cardinality of the
  -- family.
  have rank_V: Cardinal.mk ix_U ≤ Module.rank K V
    := LinearIndependent.cardinal_le_rank fam_indip
  -- We conclude by contradiction.
  have contra: Module.rank K V < Module.rank K V
    := by
    calc Module.rank K V
    _ < Module.rank K U := U_higher_dim_V
    _ = Cardinal.mk ix_U := rank_U.symm
    _ ≤ Module.rank K V := rank_V
  exact contra.false

/-
  The same exercise, but using a related theorem form the libraries.
-/
example
  (K U V: Type)
  [Field K]
  [AddCommGroup U] [AddCommGroup V]
  [Module K U] [Module K V]
  (f: U →ₗ[K] V)
  -- `U` has a larger dimension than `V`
  (U_higher_dim_V: Module.rank K U > Module.rank K V)
  : ¬ (⇑f).Injective
  := by
  have := LinearMap.rank_le_of_injective f
  grind

/-
  __Exercise__: Read about these results from the libraries.
-/
-- Rank-nullity theorem
#check LinearMap.finrank_range_add_finrank_ker
-- Linear maps correspond to matrices, in finite dimension.
#check Matrix.toLin'
-- A matrix has null determinant iff its kernel is nontrivial.
#check Matrix.exists_mulVec_eq_zero_iff

/-
  We now prove that a specific non-singular matrix induces an injective
  linear map.
-/
example
  (A: Matrix (Fin 3) (Fin 3) ℝ)
  (A_def: A =
    ![ ![1, 2, 3]
     , ![2, 1, 3]
     , ![1, 2, 5]
     ])
  : (⇑(Matrix.toLin' A)).Injective
  := by
  suffices A_det_inv: Invertible A.det by
    have A_inv: Invertible A := Matrix.invertibleOfDetInvertible A
    exact Matrix.mulVec_injective_of_invertible A

  apply invertibleOfNonzero
  subst A
  simp [Matrix.det_fin_three]
  linarith

end Basic_linear_algebra

section Basic_topology
/-
  We prove a classic result: a closed set contained in a compact is
  compact.
-/
example
  {α: Type} [TopologicalSpace α]
  {K X: Set α} (X_sub_K: X ⊆ K)
  (X_closed: IsClosed X)
  (K_compact: IsCompact K)
  : IsCompact X
  := by
  rw [isCompact_iff_finite_subcover] at K_compact ⊢
  intro ι F F_are_open F_coversX
  -- Add Xᶜ to the covering
  let F': ι ⊕ Unit → Set α
    | .inl i  => F i
    | .inr () => Xᶜ
  -- F' is still a family of open sets
  have F'_are_open:  ∀ j, IsOpen (F' j)
    := by
    intro j
    unfold F'
    cases j
    case inl i =>
      dsimp
      exact F_are_open i
    case inr _u =>
      dsimp
      exact IsClosed.isOpen_compl
  -- F' is a covering of K
  have F'_coversK:  K ⊆ ⋃ j, F' j
    := by
    intro x x_K
    by_cases x_X: x ∈ X
    case pos =>
      simp
      left
      have ⟨ Y , ⟨ i , Y_def ⟩ , x_Y ⟩ := F_coversX x_X
      exists i
      dsimp [F']
      dsimp at Y_def
      rw [Y_def]
      exact x_Y
    case neg =>
      simp
      right
      exists ()
  -- Extract a finite covering of K from F'
  -- Here, t' is a finite set of indices for F'
  have ⟨ t' , t'_covers ⟩ := K_compact F' F'_are_open F'_coversK
  -- Discard from t' the Unit values, hence obtaining a finite set of ι
  let t: Finset ι := t'.toLeft
  exists t
  intro x x_X
  -- Since t' covers K, it also covers X, so we have x ∈ Y for some Y = F' j
  have ⟨ Y , ⟨ j , Y_def ⟩ , x_Y⟩ := t'_covers (X_sub_K x_X)
  dsimp at Y_def
  subst Y
  simp at x_Y
  have ⟨ y_t' , x_F'j ⟩ := x_Y
  cases j
  case inl i =>
    simp [F'] at x_F'j
    simp
    exists i
    simp [x_F'j]
    simp [t]
    exact y_t'
  case inr =>
    simp [F'] at x_F'j
    contradiction

end Basic_topology

section Recap_exercises
/-
  __Exercise__: _Bilinear_ maps can be equivalently expressed in Lean either
  by using the tensor product `A ⊗[K] B →ₗ …` or by chaining linear maps as
  `A →ₗ (B →ₗ …)`.
  Check out the following equivalence result.
-/
open TensorProduct
#check TensorProduct.lift.equiv

/-
  __Exercise__: Prove that a function `f: A × B → C` which is linear in each
  argument induces a bilinear map `A ⊗[K] B →ₗ[K] C`.
-/
example
  (K A B C: Type)
  [Field K]
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]
  [Module K A] [Module K B] [Module K C]
  (f: A × B → C)
  (f_linA: ∀ b, IsLinearMap K (fun a => f (a, b)))
  (f_linB: ∀ a, IsLinearMap K (fun b => f (a, b)))
  : A ⊗[K] B →ₗ[K] C
  := by
  apply TensorProduct.lift
  -- The bilinear map can now be expressed as `A →ₗ[K] (B →ₗ[K] C)`.
  case f' =>
  sorry

end Recap_exercises
