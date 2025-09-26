
import Mathlib.Data.Real.Basic
import Mathlib.Data.FinEnum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv


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
