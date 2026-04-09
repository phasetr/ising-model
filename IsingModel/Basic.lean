import Mathlib.Data.Fintype.Basic

/-!
# Spin type

Two-state spin values for the Ising model.
See `.self-local/tex/0001-spin-type.tex` for the mathematical description.
-/

set_option linter.hashCommand false

namespace IsingModel

/-- A single-site spin in the Ising model: either `up` (+1) or `down` (-1). -/
inductive Spin
  | up
  | down
  deriving DecidableEq, Inhabited, Repr

namespace Spin

instance : Fintype Spin where
  elems := {Spin.up, Spin.down}
  complete := by intro s; cases s <;> decide

/-- Map a spin to its physical sign value: `up ↦ 1`, `down ↦ -1`. -/
def toSign : Spin → Int
  | up   =>  1
  | down => -1

#guard Spin.up.toSign = 1
#guard Spin.down.toSign = -1

end Spin

end IsingModel
