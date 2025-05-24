
import Mathlib.Data.Set.Basic

section Sets
-- TODO some basic set theory using `Set τ`

-- This is a `Type`, denoting pairs `⟨ n , some_proof ⟩`.
example: Type := { n: Nat // n < 20 }

example: { n: Nat // n < 20 }
  := by
  exists 10

-- This is a `Nat → Prop` function.
example: Set Nat := { n: Nat | n < 20 }

example: 10 ∈ { n: Nat | n < 20 }
  := by
  dsimp   -- Expand the definitions
  decide  -- Compute using the `Decidable` type class

end Sets
