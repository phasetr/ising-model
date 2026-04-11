import IsingModel.GibbsMeasure
import IsingModel.Hamiltonian
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-!
# FKG inequality for the Ising model

The Fortuin-Kasteleyn-Ginibre inequality states that monotone nondecreasing
functions are positively correlated under the ferromagnetic Ising measure.

We apply Mathlib's `fkg` from `Combinatorics.SetFamily.FourFunctions` to
the Ising Boltzmann weight, after verifying log-supermodularity.

Reference: Friedli–Velenik, Theorem 3.21 (p. 98), Theorem 3.50 (pp. 128–130).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Lattice structure on Config ι -/

-- Config ι = ι → Spin has DistribLattice from Pi instance + Spin LinearOrder.
-- Sup/inf are pointwise: (σ ⊔ σ')_i = max(σ_i, σ'_i), (σ ⊓ σ')_i = min(σ_i, σ'_i).

example : DistribLattice (Config ι) := inferInstance

/-! ## Log-supermodularity of the Boltzmann weight -/

/-- The key lattice inequality for ±1 spins:
`σ_i σ_j + σ'_i σ'_j ≤ (σ_i ⊔ σ'_i)(σ_j ⊔ σ'_j) + (σ_i ⊓ σ'_i)(σ_j ⊓ σ'_j)`.
Reference: Friedli–Velenik, p. 129. -/
private theorem spin_edge_supermodular (a b c d : Spin) :
    Spin.sign ℝ a * Spin.sign ℝ b + Spin.sign ℝ c * Spin.sign ℝ d ≤
    Spin.sign ℝ (a ⊔ c) * Spin.sign ℝ (b ⊔ d) +
    Spin.sign ℝ (a ⊓ c) * Spin.sign ℝ (b ⊓ d) := by
  -- All 16 cases for (a,b,c,d) ∈ {up,down}⁴. Discharge by decide or norm_num.
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [Spin.sign, Spin.toSign]

/-- The Boltzmann weight is log-supermodular:
`w(σ) * w(σ') ≤ w(σ ⊔ σ') * w(σ ⊓ σ')`.
This follows from supermodularity of each edge term in the Hamiltonian. -/
theorem boltzmannWeight_log_supermodular (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (σ σ' : Config ι) :
    boltzmannWeight G p σ * boltzmannWeight G p σ' ≤
    boltzmannWeight G p (σ ⊔ σ') * boltzmannWeight G p (σ ⊓ σ') := by
  -- w(σ)w(σ') = exp(-βH(σ)-βH(σ')) and w(σ⊔σ')w(σ⊓σ') = exp(-βH(σ⊔σ')-βH(σ⊓σ'))
  -- So need: -βH(σ)-βH(σ') ≤ -βH(σ⊔σ')-βH(σ⊓σ')
  -- i.e. H(σ⊔σ')+H(σ⊓σ') ≤ H(σ)+H(σ')
  -- This follows from edge supermodularity: σᵢσⱼ+σ'ᵢσ'ⱼ ≤ (σᵢ⊔σ'ᵢ)(σⱼ⊔σ'ⱼ)+(σᵢ⊓σ'ᵢ)(σⱼ⊓σ'ⱼ)
  sorry

/-! ## FKG inequality -/

/-- **FKG inequality for the Ising model**: For a ferromagnetic Ising model,
monotone nondecreasing nonneg functions `f, g` satisfy `⟨fg⟩ ≥ ⟨f⟩⟨g⟩`.

Reference: Friedli–Velenik, Theorem 3.21, p. 98. -/
theorem fkg_ising (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (f g : Config ι → ℝ)
    (hf_nn : 0 ≤ f) (hg_nn : 0 ≤ g)
    (hf_mono : Monotone f) (hg_mono : Monotone g) :
    gibbsExpectation G p f * gibbsExpectation G p g ≤
    gibbsExpectation G p (f * g) := by
  -- Apply Mathlib's fkg with μ = boltzmannWeight
  unfold gibbsExpectation
  have hZ := partitionFunction_pos G p
  have hZne := partitionFunction_ne_zero G p
  have hw_nn : 0 ≤ boltzmannWeight G p := fun σ => le_of_lt (boltzmannWeight_pos G p σ)
  have hw_sm : ∀ a b : Config ι,
      boltzmannWeight G p a * boltzmannWeight G p b ≤
      boltzmannWeight G p (a ⊓ b) * boltzmannWeight G p (a ⊔ b) := by
    intro a b
    have h := boltzmannWeight_log_supermodular G p hf a b
    linarith [mul_comm (boltzmannWeight G p (a ⊔ b)) (boltzmannWeight G p (a ⊓ b))]
  -- Mathlib fkg: (Σ μ*f)(Σ μ*g) ≤ (Σ μ)(Σ μ*f*g)
  -- with μ = boltzmannWeight, args: hμ₀ hf₀ hg₀ hf_mono hg_mono hμ_sm
  have hfkg := fkg (μ := boltzmannWeight G p) (f := f) (g := g)
    hw_nn hf_nn hg_nn hf_mono hg_mono hw_sm
  -- Mathlib fkg gives: (Σ w*f)(Σ w*g) ≤ (Σ w)(Σ w*fg)
  -- We need: (Z⁻¹ Σ f*w)(Z⁻¹ Σ g*w) ≤ Z⁻¹ Σ fg*w
  -- i.e. Z⁻² (Σ f*w)(Σ g*w) ≤ Z⁻¹ Σ fg*w
  -- From fkg: (Σ w*f)(Σ w*g) ≤ Z (Σ w*fg)
  sorry

end IsingModel
