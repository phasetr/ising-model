import Mathlib.Tactic.DeriveFintype
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Ising model: basic definitions

Spin type, configuration space, and Ising parameters.
-/

namespace IsingModel

/-! ## Spin -/

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

/-! ## Configuration space -/

/-- A spin configuration on sites of type `ι`. -/
abbrev Config (ι : Type*) := ι → Spin

/-! ## Ising parameters -/

/-- Parameters for the Ising model over an ordered field `K`. -/
structure IsingParams (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- Coupling constant. -/
  J : K
  /-- External magnetic field. -/
  h : K
  /-- Inverse temperature. -/
  β : K

end IsingModel
