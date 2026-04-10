import Mathlib.Tactic.DeriveFintype

/-!
# Spin type

Two-state spin values for the Ising model.
-/

namespace IsingModel

/-- A single-site spin in the Ising model: either `up` (+1) or `down` (-1). -/
inductive Spin
  | up
  | down
  deriving DecidableEq, Fintype, Inhabited, Repr

namespace Spin

/-- Map a spin to its physical sign value: `up ↦ 1`, `down ↦ -1`. -/
def toSign : Spin → Int
  | up   =>  1
  | down => -1

end Spin

end IsingModel
