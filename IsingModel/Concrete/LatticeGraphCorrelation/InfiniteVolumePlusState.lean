import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxScreeningLimit
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Infinite-volume `+` expectation of a single spin on ℤ^d (Issue #3565)

The culmination of the cubic-box `+`-state programme: the **infinite-volume `+`
boundary expectation of a single spin exists** as the monotone (decreasing) limit
of the finite-volume `+` box spins along the cubic exhaustion.  (This constructs
the limiting expectation of `σ_x`; extending it to all local observables — and
verifying the linearity / positivity / normalisation of a genuine Gibbs state — is
follow-up.)

For a fixed site `x ∈ cubicBox d N`, the screened single-site `+` box spins
`k ↦ plusBoxSpin d (N+k) (N+k+1) … x` (free inner box `cubicBox d (N+k)`, immediate
`+` boundary layer) form an **antitone** sequence — growing the free region pushes
the `+` boundary further away, decreasing the expectation of the monotone single
spin (FV Lemma 3.22, `plusBoxSpin_antitone_interior`, combined with the ambient
screening `plusBoxSpin_screening_succ`) — and is **bounded** in `[-1, 1]`
(`plusBoxSpin_mem_Icc`).  Hence it **converges** (`tendsto_atTop_ciInf`) to its
infimum, the infinite-volume `+` expectation of `σ_x`.

* `plusBoxSpin_infiniteVolume_antitone` — the antitone screened sequence.
* `tendsto_plusBoxSpin_infiniteVolume` — the monotone-convergence existence of the
  infinite-volume `+` state expectation of `σ_x`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Lemma 3.22, §6 (the `+` extremal state and the thermodynamic limit).
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

/-- **The screened single-site `+` box spin sequence is antitone**: for a fixed
site `x ∈ cubicBox d N`, `k ↦ plusBoxSpin d (N+k) (N+k+1) … x` decreases — growing
the free inner box pushes the `+` boundary further away (FV Lemma 3.22,
`plusBoxSpin_antitone_interior`), and the ambient box can be matched by the
screening `plusBoxSpin_screening_succ`. -/
theorem plusBoxSpin_infiniteVolume_antitone {d N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (x : Fin d → ℤ) (hx : x ∈ cubicBox d N) :
    Antitone (fun k => plusBoxSpin d (N + k) (N + k + 1) J h β x
      (cubicBox_mono d (by omega) hx)) := by
  apply antitone_nat_of_succ_le
  intro k
  exact le_trans
    (plusBoxSpin_antitone_interior d (show N + k ≤ N + k + 1 by omega) hβ hJ x
      (cubicBox_mono d (show N ≤ N + k + 2 by omega) hx))
    (le_of_eq (plusBoxSpin_screening_succ (show N + k + 1 ≤ N + k + 1 by omega)
      (cubicBox_mono d (show N + k + 1 ≤ N + k + 1 + 1 by omega)) x
      (cubicBox_mono d (show N ≤ N + k + 1 by omega) hx)))

/-- **The infinite-volume `+` expectation of a single spin exists** (the
thermodynamic limit of the cubic-box `+` state, Issue #3565): for a fixed site
`x ∈ cubicBox d N`, the screened single-site `+` box spins converge (decreasingly)
to their infimum,

`plusBoxSpin d (N+k) (N+k+1) … x  →  ⨅ k, plusBoxSpin d (N+k) (N+k+1) … x`   as `k → ∞`.

The sequence is antitone (`plusBoxSpin_infiniteVolume_antitone`) and bounded below
(by `-1`, from `plusBoxSpin_mem_Icc`), so `tendsto_atTop_ciInf` applies. -/
theorem tendsto_plusBoxSpin_infiniteVolume {d N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (x : Fin d → ℤ) (hx : x ∈ cubicBox d N) :
    Tendsto (fun k => plusBoxSpin d (N + k) (N + k + 1) J h β x (cubicBox_mono d (by omega) hx))
      atTop
      (nhds (⨅ k, plusBoxSpin d (N + k) (N + k + 1) J h β x (cubicBox_mono d (by omega) hx))) := by
  refine tendsto_atTop_ciInf (plusBoxSpin_infiniteVolume_antitone hβ hJ x hx) ⟨-1, ?_⟩
  rintro y ⟨k, rfl⟩
  exact (plusBoxSpin_mem_Icc d (N + k) (N + k + 1) J h β x _).1

end Ambient

end IsingModel
