import IsingModel.Hamiltonian

/-!
# Lattice-system bridge: `couplingOf` style coupling for Ising Hamiltonian

This file establishes the **compatibility layer** between the present `ising-model`
project and the planned merger into [`lattice-system`](https://github.com/phasetr/lattice-system).
It mirrors the lattice-system convention `couplingOf G J : Λ → Λ → ℂ` (`Lattice/Graph.lean`)
on the real-valued side, and proves that the Ising interaction energy
`-J·∑_{e ∈ edges} σ_{e₁}·σ_{e₂}` equals the half-trace
`-(1/2)·∑_{x, y} couplingOf G J x y · σ_x · σ_y` of the symmetric coupling matrix.

This bridge is *purely additive* — no existing definition is changed and no existing
proof is touched. It provides:

* `IsingModel.LatticeSystemBridge.couplingOf` — the canonical real-valued coupling
  associated with a `SimpleGraph G` and a uniform edge weight `J : K`; returns `J`
  on edges of `G`, and `0` elsewhere. Real-valued analog of
  `LatticeSystem.Lattice.couplingOf` (which is `ℂ`-valued).
* `IsingModel.LatticeSystemBridge.couplingOf_self` — the diagonal of `couplingOf` is `0`
  (no self-loops in a `SimpleGraph`).
* `IsingModel.LatticeSystemBridge.couplingOf_symm` — symmetry of `couplingOf`.
* `IsingModel.LatticeSystemBridge.interactionEnergy_eq_half_trace_couplingOf` — the
  bridge identity expressing the Ising interaction energy in the `couplingOf`-trace form
  used in lattice-system's Heisenberg framework. Each unordered edge `{u, v}` contributes
  twice to the trace sum (as `(u, v)` and `(v, u)`), giving a factor 2 absorbed by `(1/2)`.

The convention follows the standard mathematical-physics literature on many-body systems
on graphs (Lieb 1989, Marshall–Lieb–Mattis, Miyao 2021); see
`lattice-system/LatticeSystem/Lattice/Graph.lean` for the `ℂ`-valued original.

References:

* `LatticeSystem.Lattice.couplingOf` (lattice-system, `Lattice/Graph.lean`).
* Miyao, *An algebraic approach to revealing magnetic structures of ground states in
  many-electron systems*, §3 p. 9.
-/

namespace IsingModel
namespace LatticeSystemBridge

open Finset SimpleGraph

variable {ι K : Type*} [Field K]

/-- **Real-valued analog of `LatticeSystem.Lattice.couplingOf`**: the canonical pairwise
coupling associated with a `SimpleGraph G` on the vertex type `ι` and a uniform field-valued
edge weight `J : K`; returns `J` on adjacent pairs and `0` on non-adjacent pairs (including
the diagonal, since a `SimpleGraph` has no self-loops). -/
def couplingOf (G : SimpleGraph ι) [DecidableRel G.Adj] (J : K) :
    ι → ι → K :=
  fun x y => if G.Adj x y then J else 0

/-- **Diagonal vanishes**: `couplingOf G J x x = 0`. -/
@[simp]
theorem couplingOf_self (G : SimpleGraph ι) [DecidableRel G.Adj] (J : K) (x : ι) :
    couplingOf G J x x = 0 := by
  unfold couplingOf
  rw [if_neg G.irrefl]

/-- **Symmetry**: `couplingOf G J x y = couplingOf G J y x`. -/
theorem couplingOf_symm (G : SimpleGraph ι) [DecidableRel G.Adj] (J : K) (x y : ι) :
    couplingOf G J x y = couplingOf G J y x := by
  unfold couplingOf
  by_cases h : G.Adj x y
  · rw [if_pos h, if_pos (G.symm h)]
  · rw [if_neg h, if_neg (fun h' => h (G.symm h'))]

/-- **Per-pair spin product via couplingOf**: rewrites the contribution of a single
adjacent pair `(x, y)` to the trace-style sum using `couplingOf`. For non-adjacent pairs the
coupling is `0` so the contribution vanishes. -/
theorem couplingOf_mul_spinPair (G : SimpleGraph ι) [DecidableRel G.Adj]
    (J : K) (σ : Config ι) (x y : ι) :
    couplingOf G J x y * (Spin.sign K (σ x) * Spin.sign K (σ y))
      = if G.Adj x y then J * (Spin.sign K (σ x) * Spin.sign K (σ y)) else 0 := by
  unfold couplingOf
  split_ifs with h <;> simp

end LatticeSystemBridge
end IsingModel
