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

omit [DecidableEq ι] in
/-- The Boltzmann weight is log-supermodular:
`w(σ) * w(σ') ≤ w(σ ⊔ σ') * w(σ ⊓ σ')`.
This follows from supermodularity of each edge term in the Hamiltonian. -/
theorem boltzmannWeight_log_supermodular (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (σ σ' : Config ι) :
    boltzmannWeight G p σ * boltzmannWeight G p σ' ≤
    boltzmannWeight G p (σ ⊔ σ') * boltzmannWeight G p (σ ⊓ σ') := by
  -- w(σ)w(σ') = exp(-βH(σ)) * exp(-βH(σ')) = exp(-βH(σ)-βH(σ'))
  -- Need: exp(-βH(σ)-βH(σ')) ≤ exp(-βH(σ⊔σ')-βH(σ⊓σ'))
  -- By exp monotonicity, suffices: -βH(σ)-βH(σ') ≤ -βH(σ⊔σ')-βH(σ⊓σ')
  -- i.e. H(σ⊔σ')+H(σ⊓σ') ≤ H(σ)+H(σ')
  unfold boltzmannWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp_of_le
  -- Goal: -β*H(σ) + -β*H(σ') ≤ -β*H(σ⊔σ') + -β*H(σ⊓σ')
  -- Unfold H and show edge/site supermodularity
  unfold hamiltonian interactionEnergy externalFieldEnergy
  -- Site terms: sign(σ_i) + sign(σ'_i) = sign(σ_i⊔σ'_i) + sign(σ_i⊓σ'_i)
  have hsite : ∀ i, Spin.sign ℝ (σ i) + Spin.sign ℝ (σ' i) =
      Spin.sign ℝ ((σ ⊔ σ') i) + Spin.sign ℝ ((σ ⊓ σ') i) := by
    intro i; simp only [Pi.sup_apply, Pi.inf_apply]
    cases σ i <;> cases σ' i <;> simp [Spin.sign, Spin.toSign]
  -- Edge terms: supermodularity
  have hedge : ∀ e ∈ G.edgeFinset,
      edgeSpin (K := ℝ) σ e + edgeSpin (K := ℝ) σ' e ≤
      edgeSpin (K := ℝ) (σ ⊔ σ') e + edgeSpin (K := ℝ) (σ ⊓ σ') e := by
    intro e _
    refine Sym2.ind (fun i j => ?_) e
    simp only [edgeSpin, Sym2.lift_mk, Spin.sign]
    exact spin_edge_supermodular (σ i) (σ j) (σ' i) (σ' j)
  -- Combine: sum of edge and site supermodularity
  have hedge_sum : ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e +
      ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ' e ≤
      ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) (σ ⊔ σ') e +
      ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) (σ ⊓ σ') e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun e he => hedge e he
  have hsite_sum : ∑ i : ι, Spin.sign ℝ (σ i) + ∑ i, Spin.sign ℝ (σ' i) =
      ∑ i, Spin.sign ℝ ((σ ⊔ σ') i) + ∑ i, Spin.sign ℝ ((σ ⊓ σ') i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hsite i
  -- -β(-J Σ edge - h Σ site) for σ and σ', vs σ⊔σ' and σ⊓σ'
  -- The goal has -β * (-J * Σ edge + -(h) * Σ site) form.
  -- Expand and use hedge_sum, hsite_sum with β ≥ 0, J ≥ 0, h ≥ 0.
  have hβ := hf.hβ.le
  have hJ := hf.hJ
  have hh := hf.hh
  -- Need: -β(-J·Σe_σ - h·Σs_σ) + -β(-J·Σe_σ' - h·Σs_σ')
  --     ≤ -β(-J·Σe_sup - h·Σs_sup) + -β(-J·Σe_inf - h·Σs_inf)
  -- i.e. β·J·(Σe_σ+Σe_σ') + β·h·(Σs_σ+Σs_σ')
  --    ≤ β·J·(Σe_sup+Σe_inf) + β·h·(Σs_sup+Σs_inf)
  -- From hedge_sum and hsite_sum (equality for sites, ≤ for edges):
  -- β*J*(Σ_edge + Σ_edge') ≤ β*J*(Σ_edge_sup + Σ_edge_inf)
  have h1 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hedge_sum hJ) hβ
  -- β*h*(Σ_site + Σ_site') = β*h*(Σ_site_sup + Σ_site_inf)
  -- Combine: the full inequality
  linarith [h1, congrArg (p.β * p.h * ·) hsite_sum]

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
  have hfkg := fkg (μ := boltzmannWeight G p) (f := f) (g := g)
    hw_nn hf_nn hg_nn hf_mono hg_mono hw_sm
  -- hfkg: (Σ w*f)(Σ w*g) ≤ (Σ w)(Σ w*(f*g))
  -- gibbsExpectation G p f = Z⁻¹ Σ f*w, where Z = Σ w = partitionFunction
  -- Goal: (Z⁻¹ Σ f*w)(Z⁻¹ Σ g*w) ≤ Z⁻¹ Σ (f*g)*w
  set_option linter.unusedSimpArgs false in
  simp only [gibbsExpectation, partitionFunction]
  have hZinv := inv_pos.mpr hZ
  -- Rewrite Σ f σ * w σ = Σ w σ * f σ
  simp_rw [show ∀ σ : Config ι, f σ * boltzmannWeight G p σ =
    boltzmannWeight G p σ * f σ from fun σ => mul_comm _ _,
    show ∀ σ : Config ι, g σ * boltzmannWeight G p σ =
    boltzmannWeight G p σ * g σ from fun σ => mul_comm _ _,
    show ∀ σ : Config ι, (f * g) σ * boltzmannWeight G p σ =
    boltzmannWeight G p σ * (f σ * g σ) from fun σ => by simp [Pi.mul_apply]; ring]
  -- Now: (Z⁻¹ Σ w*f)(Z⁻¹ Σ w*g) ≤ Z⁻¹ Σ w*(f*g)
  -- i.e. Z⁻² (Σ w*f)(Σ w*g) ≤ Z⁻¹ Σ w*(f*g)
  -- From hfkg: (Σ w*f)(Σ w*g) ≤ Z * Σ w*(f*g)
  -- Divide by Z²: Z⁻² (Σ w*f)(Σ w*g) ≤ Z⁻¹ Σ w*(f*g)
  rw [show (∑ σ, boltzmannWeight G p σ)⁻¹ * ∑ σ, boltzmannWeight G p σ * (f σ * g σ) =
    (∑ σ, boltzmannWeight G p σ)⁻¹ * ∑ σ, boltzmannWeight G p σ * (f σ * g σ) from rfl]
  have hZ' := hZ
  rw [show partitionFunction G p = ∑ σ, boltzmannWeight G p σ from rfl] at hZ'
  -- hfkg: (Σ w*f)(Σ w*g) ≤ Z * Σ w*(f*g) where Z = Σ w
  -- Goal: Z⁻¹ * Σ w*f * (Z⁻¹ * Σ w*g) ≤ Z⁻¹ * Σ w*(f*g)
  -- i.e. Z⁻² * (Σ w*f)(Σ w*g) ≤ Z⁻¹ * Σ w*(f*g)
  -- From hfkg, dividing by Z² (Z > 0):
  set Z := ∑ σ : Config ι, boltzmannWeight G p σ
  have hZne := ne_of_gt hZ'
  -- hfkg: (Σ w*f)(Σ w*g) ≤ Z * Σ w*(f*g)
  -- Goal: (Z⁻¹ Σ w*f)(Z⁻¹ Σ w*g) ≤ Z⁻¹ Σ w*(f*g)
  -- = Z⁻² (Σ w*f)(Σ w*g) ≤ Z⁻¹ Σ w*(f*g)
  -- Multiply both sides by Z² > 0:
  -- (Σ w*f)(Σ w*g) ≤ Z * Σ w*(f*g) = hfkg ✓
  rw [show ((Z⁻¹ * ∑ x, boltzmannWeight G p x * f x) *
      (Z⁻¹ * ∑ x, boltzmannWeight G p x * g x)) =
    Z⁻¹ * Z⁻¹ * ((∑ x, boltzmannWeight G p x * f x) *
      (∑ x, boltzmannWeight G p x * g x)) from by ring]
  rw [show Z⁻¹ * Z⁻¹ = (Z * Z)⁻¹ from by rw [mul_inv_rev]]
  rw [show Z⁻¹ * ∑ σ, boltzmannWeight G p σ * (f σ * g σ) =
    (Z * Z)⁻¹ * (Z * ∑ σ, boltzmannWeight G p σ * (f σ * g σ)) from by
      field_simp]
  exact mul_le_mul_of_nonneg_left hfkg (by positivity)

end IsingModel
