
import Mathlib.Data.Real.Basic
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Compactness.Compact


section Basic_linear_algebra
/-
  `Fin n` is a finite type with `n` values.
-/
example (n : ℕ)
  : FinEnum.card (Fin n) = n
  := FinEnum.card_fin

/-
  `Fin n → ℝ` is therefore a way to express `ℝⁿ`.
  Such vectors can be written as `![x₁, x₂, …]`.
-/
example: Fin 3 → ℝ := ![0, -4, 5.67]

/-
  Four 3-dimensional vectors can not be linearly independent.

  Note that `![v₁, v₂, v₃, v₄]` below is essentially a 4×3 matrix.
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
  __Exercise__: Read about these results from the libraries.
-/
-- Rank-nullity theorem
#check LinearMap.finrank_range_add_finrank_ker
-- Linear maps correspond to matrices, in finite dimension.
#check Matrix.toLin
-- A matrix has null determinant iff its kernel is nontrivial.
#check Matrix.exists_mulVec_eq_zero_iff

end Basic_linear_algebra

section Basic_topology
/-
  We now prove a classic result: a closed set contained in a compact is
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
