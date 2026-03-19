import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Data.Nat.Prime.Basic

namespace BurnsidePrimeDegreeTheorem

open MulAction

/--
**Burnside's theorem on transitive permutation groups of prime degree (statement)**.

A transitive permutation group of prime degree is either 2-transitive or has a normal regular
subgroup.
-/
theorem MainTheorem
    {α : Type*} [Fintype α]
    {G : Subgroup (Equiv.Perm α)}
    (htrans : IsPretransitive G α)
    (hp : (Fintype.card α).Prime) :
    IsMultiplyPretransitive G α 2 ∨
      ∃ N : Subgroup G, N.Normal ∧ IsPretransitive N α ∧
        ∀ a : α, MulAction.stabilizer N a = ⊥ := by
  sorry

end BurnsidePrimeDegreeTheorem
