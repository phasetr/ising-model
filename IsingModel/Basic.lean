import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Ising model: basic definitions

Spin type, spin operations, configuration space, and Ising parameters.
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

/-- Flip a spin: `up ↔ down`. -/
def flip : Spin → Spin
  | .up   => .down
  | .down => .up

/-- The spin sign cast into a commutative ring `K`. -/
def sign (K : Type*) [CommRing K] (s : Spin) : K := ↑s.toSign

/-- The square of any spin sign is `1`: `(±1)² = 1`. -/
@[simp]
theorem toSign_sq (s : Spin) : s.toSign ^ 2 = 1 := by
  cases s <;> simp [toSign]

/-- The square of the spin sign in `K` is `1`: `(sign K s)² = 1`. -/
@[simp]
theorem sign_sq {K : Type*} [CommRing K] (s : Spin) :
    Spin.sign K s ^ 2 = 1 := by
  cases s
  · simp [sign, toSign]
  · simp [sign, toSign, sq, neg_neg]

/-- Flipping a spin negates its sign: `toSign(flip s) = -toSign(s)`. -/
@[simp]
theorem toSign_flip (s : Spin) : s.flip.toSign = -s.toSign := by
  cases s <;> simp [flip, toSign]

/-- Flipping a spin negates its sign in `K`: `sign K (flip s) = -sign K s`. -/
@[simp]
theorem sign_flip {K : Type*} [CommRing K] (s : Spin) :
    Spin.sign K s.flip = -Spin.sign K s := by
  cases s <;> simp [sign, flip, toSign]

/-- Flipping twice is the identity. -/
@[simp]
theorem flip_flip (s : Spin) : s.flip.flip = s := by
  cases s <;> rfl

/-- A flipped spin is different from the original. -/
theorem flip_ne (s : Spin) : s.flip ≠ s := by
  cases s <;> simp [flip]

/-- Spin multiplication: `up` acts as identity, `down` acts as flip. -/
def mul : Spin → Spin → Spin
  | .up, s => s
  | .down, s => s.flip

/-- `toSign(mul a b) = toSign(a) * toSign(b)`. -/
@[simp]
theorem toSign_mul (a b : Spin) : (a.mul b).toSign = a.toSign * b.toSign := by
  cases a <;> cases b <;> simp [mul, flip, toSign]

/-- `mul a` is an involution (hence a bijection). -/
@[simp]
theorem mul_mul_cancel (a b : Spin) : a.mul (a.mul b) = b := by
  cases a <;> simp [mul, flip_flip]

end Spin

/-! ## Configuration space -/

/-- A spin configuration on sites of type `ι`. -/
abbrev Config (ι : Type*) := ι → Spin

namespace Config

/-- Flip all spins in a configuration. -/
def flip {ι : Type*} (σ : Config ι) : Config ι := fun i => (σ i).flip

/-- Flipping all spins twice recovers the original configuration. -/
@[simp]
theorem flip_flip {ι : Type*} (σ : Config ι) : σ.flip.flip = σ := by
  ext i; exact Spin.flip_flip (σ i)

/-- Flip a configuration at a single site `j`. -/
def flipAt {ι : Type*} [DecidableEq ι] (j : ι) (σ : Config ι) : Config ι :=
  Function.update σ j (σ j).flip

/-- `flipAt j` is an involution. -/
@[simp]
theorem flipAt_flipAt {ι : Type*} [DecidableEq ι] (j : ι) (σ : Config ι) :
    (σ.flipAt j).flipAt j = σ := by
  ext i
  simp [flipAt, Function.update]
  split <;> simp_all

/-- Flipping at any site produces a different configuration. -/
theorem flipAt_ne {ι : Type*} [DecidableEq ι] (j : ι) (σ : Config ι) :
    σ.flipAt j ≠ σ := by
  intro h
  have h1 := congr_fun h j
  simp only [flipAt, Function.update_self] at h1
  exact absurd h1 (Spin.flip_ne (σ j))

end Config

/-! ## Ising parameters -/

/-- Parameters for the Ising model over an ordered field `K`. -/
structure IsingParams (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- Coupling constant. -/
  J : K
  /-- External magnetic field. -/
  h : K
  /-- Inverse temperature. -/
  β : K

/-! ## Ferromagnetic condition -/

/-- The ferromagnetic condition: non-negative coupling, non-negative field, positive temperature. -/
structure Ferromagnetic {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : IsingParams K) : Prop where
  /-- Non-negative coupling constant. -/
  hJ : 0 ≤ p.J
  /-- Non-negative external field. -/
  hh : 0 ≤ p.h
  /-- Positive inverse temperature. -/
  hβ : 0 < p.β

end IsingModel
