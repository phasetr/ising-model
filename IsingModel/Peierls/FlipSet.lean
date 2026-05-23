import IsingModel.Peierls.PhaseBoundary

/-!
# Peierls argument — spin flip on a subset

This module is part of the split `IsingModel.Peierls` development. It
defines `Config.flipSet`, the cut-edge set `cutEdges G S`, and computes
the effect of `flipSet` on the phase boundary and zero-field Hamiltonian.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Spin flip on a subset

Flipping all spins in a subset S is the key operation in the Peierls argument.
It is an involution on configurations. -/

/-- Flip all spins at sites in S, leaving others unchanged. -/
def Config.flipSet (S : Finset ι) (σ : Config ι) : Config ι :=
  fun i => if i ∈ S then (σ i).flip else σ i

omit [Fintype ι] in
/-- Flipping on S twice is the identity. -/
@[simp]
theorem Config.flipSet_flipSet (S : Finset ι) (σ : Config ι) :
    Config.flipSet S (Config.flipSet S σ) = σ := by
  ext i; simp [Config.flipSet]; split <;> simp

omit [Fintype ι] in
/-- `flipSet S` is injective (since it is an involution). -/
theorem Config.flipSet_injective (S : Finset ι) :
    Function.Injective (Config.flipSet S (ι := ι)) := by
  intro σ τ h
  have : Config.flipSet S (Config.flipSet S σ) =
      Config.flipSet S (Config.flipSet S τ) := congr_arg (Config.flipSet S) h
  simp only [Config.flipSet_flipSet] at this; exact this

/-! ## Cut edges

The edge cut of a set S is the set of graph edges with exactly one
endpoint in S. This corresponds to the boundary of the "droplet" S. -/

/-- Whether an edge has exactly one endpoint in S (crosses the boundary of S). -/
def edgeCrosses (S : Finset ι) (e : Sym2 ι) : Bool :=
  Sym2.lift ⟨fun i j => xor (decide (i ∈ S)) (decide (j ∈ S)),
    fun i j => by simp [Bool.xor_comm]⟩ e

/-- The set of graph edges with exactly one endpoint in S. -/
def cutEdges (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (S : Finset ι) : Finset (Sym2 ι) :=
  G.edgeFinset.filter (fun e => edgeCrosses S e)

/-! ## Phase boundary under flip: symmetric difference

The key combinatorial fact: flipping spins on S transforms the phase boundary
by symmetric difference with the cut edges of S.

For each edge {i,j}:
- If exactly one endpoint is in S: disagreement flips (agree ↔ disagree)
- If both or neither are in S: disagreement is preserved -/

omit [Fintype ι] in
/-- Edge disagreement under `flipSet S` equals XOR of original disagreement
and crossing. This is the fundamental identity for the Peierls argument. -/
private theorem edgeDisagrees_flipSet_eq (S : Finset ι) (σ : Config ι)
    (e : Sym2 ι) :
    edgeDisagrees (Config.flipSet S σ) e =
      xor (edgeDisagrees σ e) (edgeCrosses S e) := by
  refine Sym2.ind (fun i j => ?_) e
  simp only [edgeDisagrees, edgeCrosses, Config.flipSet, Sym2.lift_mk]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj] <;>
    cases σ i <;> cases σ j <;> simp [Spin.flip]

omit [Fintype ι] in
/-- When `cutEdges G S ⊆ phaseBoundary G σ`, flipping on S removes those edges:
`phaseBoundary G (flipSet S σ) = phaseBoundary G σ \ cutEdges G S`. -/
theorem phaseBoundary_flipSet_of_subset (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (S : Finset ι) (σ : Config ι)
    (hsub : cutEdges G S ⊆ phaseBoundary G σ) :
    phaseBoundary G (Config.flipSet S σ) = phaseBoundary G σ \ cutEdges G S := by
  ext e
  simp only [phaseBoundary, cutEdges, Finset.mem_filter, Finset.mem_sdiff,
    edgeDisagrees_flipSet_eq]
  constructor
  · intro ⟨he, hxor⟩
    -- If crosses = true: since cut ⊆ boundary, disagrees = true,
    -- so xor true true = false, contradicting hxor
    have hcf : edgeCrosses S e = false := by
      cases hc : edgeCrosses S e with
      | false => rfl
      | true =>
        exfalso
        have hmem := hsub (Finset.mem_filter.mpr ⟨he, hc⟩)
        simp only [phaseBoundary, Finset.mem_filter] at hmem
        simp [hmem.2, hc] at hxor
    simp only [hcf, Bool.xor_false] at hxor
    exact ⟨⟨he, hxor⟩, fun ⟨_, hc⟩ => by rw [hcf] at hc; exact absurd hc Bool.false_ne_true⟩
  · intro ⟨⟨he, hd⟩, hncut⟩
    refine ⟨he, ?_⟩
    have hcf : edgeCrosses S e = false := by
      rw [Bool.eq_false_iff]; intro hc; exact hncut ⟨he, hc⟩
    simp [hd, hcf]

omit [Fintype ι] in
/-- When `cutEdges G S ⊆ phaseBoundary G σ`, the boundary size decreases. -/
theorem phaseBoundarySize_flipSet_of_subset (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (S : Finset ι) (σ : Config ι)
    (hsub : cutEdges G S ⊆ phaseBoundary G σ) :
    phaseBoundarySize G (Config.flipSet S σ) =
      phaseBoundarySize G σ - (cutEdges G S).card := by
  simp only [phaseBoundarySize, phaseBoundary_flipSet_of_subset G S σ hsub,
    Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]

/-! ## Energy difference under flip

When `cut(S) ⊆ ∂σ`, the energy decreases by `2J|cut(S)|`. -/

/-- Energy difference under flip when cut edges are contained in the boundary.
`H(σ) - H(σ^S) = 2J|cut(S)|`, i.e., the flipped configuration has lower energy. -/
theorem hamiltonian_flipSet_diff (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (S : Finset ι) (σ : Config ι)
    (hsub : cutEdges G S ⊆ phaseBoundary G σ) :
    hamiltonian G ⟨J, 0, β⟩ σ - hamiltonian G ⟨J, 0, β⟩ (Config.flipSet S σ) =
      2 * J * ↑(cutEdges G S).card := by
  rw [hamiltonian_boundary G J β σ, hamiltonian_boundary G J β (Config.flipSet S σ)]
  rw [phaseBoundarySize_flipSet_of_subset G S σ hsub]
  have hle : (cutEdges G S).card ≤ phaseBoundarySize G σ :=
    Finset.card_le_card hsub
  push_cast [Nat.cast_sub hle]
  ring


end IsingModel
