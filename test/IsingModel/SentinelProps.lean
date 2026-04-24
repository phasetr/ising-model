import IsingModel.TestGenerators

set_option linter.style.nativeDecide false

/-!
# Refactor-sentinel property suite (Issue #888 Step P2)

Pinned property tests for the Ising model definitions that CI can use to
detect regressions during refactoring.

## Design

- All ℤ/ℚ computations — no `Real.exp`.
- **Formal weight K**: instead of `exp(βJ)`, use a formal parameter `K : ℚ`.
  Set K = 2 for concrete pinned tests (exact ℚ arithmetic).
- **Independent expected values**: each concrete value is derived from hand
  calculation or an existing formal theorem, never from the current `#eval`.
- `native_decide` is used throughout; no `decide` (too slow for ℚ).

## Expected values (hand-calculated, K = 2)

### chainGraph2 (1 edge {0,1}, 4 configs)

| σ      | aligned? | boltzmannWeightFormal |
|--------|----------|-----------------------|
| up,up  | yes      | K¹ = 2                |
| up,dn  | no       | K⁻¹ = 1/2            |
| dn,up  | no       | K⁻¹ = 1/2            |
| dn,dn  | yes      | K¹ = 2                |
Z = 2 + 1/2 + 1/2 + 2 = 5
⟨σ₀⟩ = 0 (by Z₂ symmetry)
⟨σ₀σ₁⟩ = (2 - 1/2 - 1/2 + 2)/5 = 3/5

### chainGraph3 (2 edges {0,1},{1,2}, 8 configs)

| σ       | edgeSum | B   |
|---------|---------|-----|
| +++ | 2  | K²=4       |
| ++-  | 0  | K⁰=1       |
| +-+  | -2 | K⁻²=1/4   |
| +-- | 0  | K⁰=1       |
| -++ | 0  | K⁰=1       |
| -+-  | -2 | K⁻²=1/4   |
| --+  | 0  | K⁰=1       |
| ---  | 2  | K²=4       |
Z = 4 + 1 + 1/4 + 1 + 1 + 1/4 + 1 + 4 = 12.5 = 25/2

### triangleGraph (3 edges, 8 configs)

| σ   | edgeSum | B        |
|-----|---------|----------|
| +++ | 3       | K³=8     |
| ++- | -1      | K⁻¹=1/2  |
| +-+ | -1      | K⁻¹=1/2  |
| +-- | -1      | K⁻¹=1/2  |
| -++ | -1      | K⁻¹=1/2  |
| +-+ × | wait — redo:

Trianglegraph: edges {0,1},{0,2},{1,2}. For σ = (s₀,s₁,s₂):
edgeSum = s₀s₁ + s₀s₂ + s₁s₂.

| σ          | edgeSum      | B at K=2         |
|------------|--------------|------------------|
| +++        | 1+1+1=3      | 2³=8             |
| ++-        | 1-1-1=-1     | 2⁻¹=1/2          |
| +-+        | -1+1-1=-1    | 1/2              |
| +--        | -1-1+1=-1    | 1/2              |
| -++        | -1-1+1=-1    | 1/2              |
| -+-        | -1+1-1=-1    | 1/2              |
| --+        | 1-1-1=-1     | 1/2              |
| ---        | 1+1+1=3      | 8                |
Z = 8 + 6*(1/2) + 8 = 16 + 3 = 19

Wait, let me recount. Mixed configs: there are 6 of them (2 choices for minority spin):
- 3 configs with 2 up, 1 down: (++-), (+-+), (-++), each has edgeSum = 1+(-1)+(-1) = -1
- 3 configs with 1 up, 2 down: (+--), (-+-), (--+), each has edgeSum = (-1)+(-1)+1 = -1
Total: all 6 mixed have edgeSum = -1.
Z = 8 + 8 + 6*(1/2) = 16 + 3 = 19.

So triangleGraph at K=2: Z = 19.
-/

namespace IsingModel.Test.SentinelProps

open IsingModel.TestGenerators

/-! ## Formal Boltzmann weight and partition function (ℚ) -/

/-- **Formal Boltzmann weight** for a spin configuration `σ` on graph `G`,
using formal parameter `K : ℚ` in place of `Real.exp (β * J)`.

`boltzmannWeightFormal G K σ := K ^ (∑_e σ_i · σ_j)`

where the exponent is the signed edge coupling sum (∈ ℤ, hence `zpow`).
For K > 0 with K = exp(βJ), this equals the true Boltzmann weight
exp(βJ · ∑_e σ_i σ_j). -/
def boltzmannWeightFormal {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [Fintype G.edgeSet]
    (K : ℚ) (σ : Fin n → Spin) : ℚ :=
  K ^ edgeCouplingSum G σ

/-- **Formal partition function** over ℚ: Z(G, K) = ∑_σ K^(coupling sum).
For K = exp(βJ) > 0, this equals the physical Z at h = 0. -/
def partitionFnFormal {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [Fintype G.edgeSet]
    (K : ℚ) : ℚ :=
  ∑ σ : Fin n → Spin, boltzmannWeightFormal G K σ

/-- **Formal correlation** ⟨σ_A⟩ = (∑_σ σ^A · B(σ)) / Z. -/
def correlationFormal {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [Fintype G.edgeSet]
    (K : ℚ) (A : Finset (Fin n)) : ℚ :=
  (∑ σ : Fin n → Spin,
    boltzmannWeightFormal G K σ * (spinProductZ A σ : ℚ)) /
  partitionFnFormal G K

/-! ## Pinned partition function values (K = 2, hand-calculated) -/

/-- chainGraph2 partition function at K = 2 equals 5.
Hand calc: 2 + 1/2 + 1/2 + 2 = 5. -/
example : partitionFnFormal chainGraph2 2 = 5 := by native_decide

/-- chainGraph3 partition function at K = 2 equals 25/2.
Hand calc: 4 + 1 + 1/4 + 1 + 1 + 1/4 + 1 + 4 = 25/2. -/
example : partitionFnFormal chainGraph3 2 = 25 / 2 := by native_decide

/-- triangleGraph partition function at K = 2 equals 19.
Hand calc: 2 all-aligned configs (B=8) + 6 frustrated configs (B=1/2) = 16+3=19. -/
example : partitionFnFormal triangleGraph 2 = 19 := by native_decide

/-- partitionFnFormal is positive for K = 2 (all Boltzmann weights > 0). -/
example : 0 < partitionFnFormal chainGraph2 2 := by native_decide

example : 0 < partitionFnFormal triangleGraph 2 := by native_decide

/-! ## Z₂ symmetry: ⟨σ_i⟩ = 0 at h = 0 (formal weight, any K) -/

/-- ⟨σ_0⟩ = 0 for chainGraph2 at K = 2 (Z₂ symmetry). -/
example : correlationFormal chainGraph2 2 {0} = 0 := by native_decide

/-- ⟨σ_0⟩ = 0 for triangleGraph at K = 2. -/
example : correlationFormal triangleGraph 2 {0} = 0 := by native_decide

/-! ## Two-point correlation values -/

/-- ⟨σ₀σ₁⟩ = 3/5 for chainGraph2 at K = 2.
Hand calc: (2 - 1/2 - 1/2 + 2)/5 = 3/5.
Physics check: tanh(βJ) at K = exp(βJ) = 2 gives (K-1/K)/(K+1/K) = (3/2)/(5/2) = 3/5. ✓ -/
example : correlationFormal chainGraph2 2 {0, 1} = 3 / 5 := by native_decide

/-! ## GKS-I: correlations are nonneg (ℚ formal, K = 2) -/

/-- ⟨σ_A⟩ ≥ 0 for A = {0} on chainGraph2 (trivially 0). -/
example : 0 ≤ correlationFormal chainGraph2 2 {0} := by native_decide

/-- ⟨σ₀σ₁⟩ ≥ 0 for chainGraph2 at K = 2 (ferromagnetic). -/
example : 0 ≤ correlationFormal chainGraph2 2 {0, 1} := by native_decide

/-- ⟨σ₀σ₁⟩ ≥ 0 for triangleGraph at K = 2 (ferromagnetic even on K₃). -/
example : 0 ≤ correlationFormal triangleGraph 2 {0, 1} := by native_decide

/-! ## GKS-II: ⟨σ_A σ_B⟩ ≥ ⟨σ_A⟩⟨σ_B⟩ (ℚ formal) -/

/-- GKS-II for chainGraph2, A = {0}, B = {1}: ⟨σ₀σ₁⟩ ≥ ⟨σ₀⟩⟨σ₁⟩ = 0.
Equivalent to nonnegativity of the correlation at h=0. -/
example : correlationFormal chainGraph2 2 {0} * correlationFormal chainGraph2 2 {1}
    ≤ correlationFormal chainGraph2 2 {0, 1} := by native_decide

/-- GKS-II for triangleGraph, A = {0}, B = {1}. -/
example : correlationFormal triangleGraph 2 {0} * correlationFormal triangleGraph 2 {1}
    ≤ correlationFormal triangleGraph 2 {0, 1} := by native_decide

/-! ## Edge coupling sum properties -/

/-- edgeCouplingSum for chainGraph2 (all-up) = 1. -/
example : edgeCouplingSum chainGraph2 (fun _ => Spin.up) = 1 := by native_decide

/-- edgeCouplingSum for chainGraph2 (mixed up,down) = -1. -/
example : edgeCouplingSum chainGraph2 (fun i : Fin 2 => [Spin.up, Spin.down].getD i.val Spin.up) = -1 := by native_decide

/-- edgeCouplingSum for chainGraph3 (all-up) = 2. -/
example : edgeCouplingSum chainGraph3 (fun _ => Spin.up) = 2 := by native_decide

/-- spinProductZ: product over {0,1} of all-up config = 1. -/
example : spinProductZ (n := 2) {0, 1} (fun _ => Spin.up) = 1 := by native_decide

/-- spinProductZ: product over {0} of mixed (up,down) = 1. -/
example : spinProductZ (n := 2) {0} (fun i => [Spin.up, Spin.down].getD i.val Spin.up) = 1 := by native_decide

/-- spinProductZ: product over {1} of mixed (up,down) = -1. -/
example : spinProductZ (n := 2) {1} (fun i => [Spin.up, Spin.down].getD i.val Spin.up) = -1 := by native_decide

end IsingModel.Test.SentinelProps
