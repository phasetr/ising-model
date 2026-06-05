import IsingModel.Conditioning.PlusOnePointConnectedBound
import IsingModel.Conditioning.CubicBoxComponentSize
import IsingModel.Conditioning.EdgeWalkCounting
import IsingModel.Conditioning.CountGeometricCapstone
import IsingModel.Conditioning.EdgeSetDistance

/-!
# High-temperature decay of the finite-box `+` magnetization (FV §3.7.3 capstone)

The FV §3.7.3 exponential bound `⟨σ₀⟩⁺_{B(n)} ≤ (4d²·tanh βJ)^n/(1-4d²·tanh βJ)` in the cubic
box `B(m)` with `+` boundary on the inner box `B(n)`, for `4d²·tanh βJ < 1`. Composes the
component bound (3.48), the component-size lower bound `|C|≥n` (3.49), the counting bound
`#{C:|C|=ℓ}≤(2d)^{2ℓ}` (the FV-Lemma-3.38 walk injection), and the geometric capstone.
Towards the high-temperature `m*(β)=0` (Issue #3613).

* `gibbsExpectationBC_box_singleSpin_le` — the box magnetization decay bound.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eq. (3.49), p. 118.
-/

namespace IsingModel

open Finset Ambient

/-- **High-temperature box magnetization decay** (FV (3.49)): in the cubic box `B(m)` with
`+` boundary on the inner box `B(n)`, the `+` expectation of the origin spin is bounded by
the geometric tail `(4d²·tanh βJ)^n/(1-4d²·tanh βJ)`, provided `0 < d`, `0 < tanh βJ`, and
`4d²·tanh βJ < 1`. -/
theorem gibbsExpectationBC_box_singleSpin_le {d n m : ℕ} (hd : 0 < d) (J β : ℝ)
    {z : ↑(cubicBox d m)} (hz0 : (z : Fin d → ℤ) = 0) (hzΛ : z ∈ plusBoxInterior d n m)
    (htanh_pos : 0 < Real.tanh (β * J))
    (htanh1 : 4 * (d : ℝ) ^ 2 * Real.tanh (β * J) < 1) :
    gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d m)) β (fun _ => J) 0
        (plusBoxInterior d n m) (plusConfig _) (spinProduct {z})
      ≤ (4 * (d : ℝ) ^ 2 * Real.tanh (β * J)) ^ n
        / (1 - 4 * (d : ℝ) ^ 2 * Real.tanh (β * J)) := by
  classical
  set G := inducedGraph (latticeGraph d) (cubicBox d m) with hGdef
  refine (gibbsExpectationBC_plus_singleSpin_h_zero_le_connected G J β
    (plusBoxInterior d n m) hzΛ htanh_pos.le).trans ?_
  set Snum := G.edgeFinset.powerset.filter
    (fun X => ∀ v ∈ plusBoxInterior d n m,
      Even ((if v = z then 1 else 0) + (X.filter (v ∈ ·)).card)) with hSnum
  set Comp0s := Snum.image (fun X => componentOfZero X z) with hComp0s
  -- every `X ∈ Snum` has a `z`-edge (odd degree at the origin)
  have hzedge : ∀ X ∈ Snum, ∃ e₀ ∈ X, z ∈ e₀ := by
    intro X hX
    have hX' := Finset.mem_filter.mp hX
    have hodd : Odd ((X.filter (z ∈ ·)).card) := by
      have hev := hX'.2 z hzΛ
      rw [if_pos rfl] at hev
      rcases Nat.even_or_odd ((X.filter (z ∈ ·)).card) with h | h
      · exact absurd hev (by rw [add_comm]; simpa [Nat.even_add_one] using h)
      · exact h
    obtain ⟨e₀, he₀⟩ := Finset.card_pos.mp hodd.pos
    rw [Finset.mem_filter] at he₀
    exact ⟨e₀, he₀.1, he₀.2⟩
  rw [show (4 * (d : ℝ) ^ 2 * Real.tanh (β * J))
      = ((4 * d ^ 2 : ℕ) : ℝ) * Real.tanh (β * J) from by push_cast; ring]
  refine sum_pow_le_geometric_tail_of_count Comp0s Finset.card htanh_pos.le
    (M := 4 * d ^ 2) n ?_ ?_ ?_ ?_
  · -- `n ≤ |C|` for each component
    intro C hC
    rw [hComp0s, Finset.mem_image] at hC
    obtain ⟨X, hXSnum, rfl⟩ := hC
    have hX' := Finset.mem_filter.mp hXSnum
    have hXG : X ⊆ G.edgeFinset := Finset.mem_powerset.mp hX'.1
    obtain ⟨e₀, he₀X, hze₀⟩ := hzedge X hXSnum
    exact card_componentOfZero_ge_of_E0 X hXG hz0 he₀X hze₀ hX'.2
  · -- counting bound `#{C : |C|=ℓ} ≤ (4d²)^ℓ`
    intro ℓ
    have hbound := card_connected_edge_sets_inducedLatticeGraph_le (cubicBox d m) z ℓ
      (Comp0s.filter (fun C => C.card = ℓ)) (by
        intro C hC
        rw [Finset.mem_filter, hComp0s, Finset.mem_image] at hC
        obtain ⟨⟨X, hXSnum, rfl⟩, hcardℓ⟩ := hC
        have hX' := Finset.mem_filter.mp hXSnum
        have hXG : X ⊆ G.edgeFinset := Finset.mem_powerset.mp hX'.1
        obtain ⟨e₀, he₀X, hze₀⟩ := hzedge X hXSnum
        exact ⟨(componentOfZero_subset X z).trans hXG,
          isEdgeConnected_componentOfZero he₀X hze₀, hcardℓ,
          e₀, mem_componentOfZero_of_incident he₀X hze₀, hze₀⟩)
    calc ((Comp0s.filter (fun C => C.card = ℓ)).card : ℝ)
        ≤ (((2 * d) ^ (2 * ℓ) : ℕ) : ℝ) := by exact_mod_cast hbound
      _ = ((4 * d ^ 2 : ℕ) : ℝ) ^ ℓ := by push_cast; rw [pow_mul]; ring
  · -- `0 < 4d²·tanh`
    have hdpos : (0 : ℝ) < 4 * (d : ℝ) ^ 2 := by positivity
    calc (0 : ℝ) < 4 * (d : ℝ) ^ 2 * Real.tanh (β * J) := by positivity
      _ = ((4 * d ^ 2 : ℕ) : ℝ) * Real.tanh (β * J) := by push_cast; ring
  · -- `4d²·tanh < 1`
    calc ((4 * d ^ 2 : ℕ) : ℝ) * Real.tanh (β * J)
        = 4 * (d : ℝ) ^ 2 * Real.tanh (β * J) := by push_cast; ring
      _ < 1 := htanh1

end IsingModel
