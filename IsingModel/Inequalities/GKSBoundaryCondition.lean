import IsingModel.Inequalities.GKS
import IsingModel.Inequalities.FKGBoundaryCondition
import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxScreening

/-!
# GKS-I for the `+` boundary-condition state (FV §3.6 / Theorem 3.49, Issue #3605)

The first Griffiths inequality (GKS-I) extended from the free Gibbs state to the `+`
boundary-condition state.  The key observation is that the `+` boundary Boltzmann
weight is the free weight multiplied by a product of *pinning factors*,

`w^+_Λ(σ) = w(σ) · ∏_{i ∉ Λ} (½ + ½·s(σ_i))`,

each of the form `(a + b·σ^C)` with `a, b ≥ 0`, so `hasNonnegCorrelations_mul_prod`
shows the `+` boundary weight has non-negative correlations.  Hence
`⟨σ^A⟩^+_Λ ≥ 0` (GKS-I).  This is the foundation for GKS-II and the
`β`/`J`-monotonicity of the `+` magnetization.

* `boltzmannWeightBC_plus_eq_prod` — the pinning-factor product representation.
* `boltzmannWeightBC_plus_hasNonnegCorrelations` — the `+` weight has HNC.
* `gibbsExpectationBC_plus_spinProduct_nonneg` — GKS-I: `⟨σ^A⟩^+_Λ ≥ 0`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.6, Theorem 3.49 (GKS-I, pp. 127–128).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Pinning-factor product representation of the `+` boundary Boltzmann weight**: for
a uniform coupling, `w^+_Λ(σ) = w(σ) · ∏_{i ∈ Λᶜ} (½ + ½·σ_i)`.  Each factor is `1`
when `σ_i = +1` and `0` when `σ_i = −1`, so the product realises the boundary
indicator `[σ agrees with + off Λ]`. -/
theorem boltzmannWeightBC_plus_eq_prod (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) (Λ : Finset ι) (σ : Config ι) :
    boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ
      = boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ *
          ∏ i ∈ Finset.univ \ Λ, (1 / 2 + 1 / 2 * spinProduct {i} σ) := by
  unfold boltzmannWeightBC
  by_cases hag : agreesOff Λ (plusConfig ι) σ
  · rw [Set.indicator_of_mem hag, boltzmannWeightJ_uniform_eq]
    rw [Finset.prod_eq_one, mul_one]
    intro i hi
    have hiΛ : i ∉ Λ := (Finset.mem_sdiff.mp hi).2
    have hup : σ i = Spin.up := hag i hiΛ
    rw [spinProduct_singleton, hup]
    norm_num [Spin.toSign]
  · rw [Set.indicator_of_notMem hag]
    symm
    rw [mul_eq_zero]
    right
    simp only [agreesOff, not_forall] at hag
    obtain ⟨i, hiΛ, hne⟩ := hag
    refine Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiΛ⟩) ?_
    have hne' : σ i ≠ Spin.up := hne
    have hdown : σ i = Spin.down := by
      rcases hd : σ i with _ | _
      · exact absurd hd hne'
      · rfl
    rw [spinProduct_singleton, hdown]
    norm_num [Spin.toSign]

/-- **The `+` boundary Boltzmann weight has non-negative correlations**: by the
pinning-factor product representation and `hasNonnegCorrelations_mul_prod` (each factor
`½ + ½·σ_i` has `a, b ≥ 0`). -/
theorem boltzmannWeightBC_plus_hasNonnegCorrelations (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h : ℝ} (hβ : 0 < β) (hJ : 0 ≤ J) (hh : 0 ≤ h) (Λ : Finset ι) :
    HasNonnegCorrelations (boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι)) := by
  have heq : boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι)
      = fun σ => boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ *
          ∏ i ∈ Finset.univ \ Λ, (1 / 2 + 1 / 2 * spinProduct {i} σ) :=
    funext (boltzmannWeightBC_plus_eq_prod G β J h Λ)
  rw [heq]
  exact hasNonnegCorrelations_mul_prod (Finset.univ \ Λ)
    (boltzmannWeight_hasNonnegCorrelations G (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩)
    _ (fun i _ => ⟨1 / 2, 1 / 2, {i}, by norm_num, by norm_num, fun σ => rfl⟩)

/-- **First Griffiths inequality (GKS-I) for the `+` boundary state**: for a
ferromagnetic Ising model with the `+` boundary condition, every spin correlation is
non-negative, `⟨σ^A⟩^+_Λ ≥ 0`. -/
theorem gibbsExpectationBC_plus_spinProduct_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h : ℝ} (hβ : 0 < β) (hJ : 0 ≤ J) (hh : 0 ≤ h) (Λ : Finset ι) (A : Finset ι) :
    0 ≤ gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι) (spinProduct A) := by
  unfold gibbsExpectationBC
  refine mul_nonneg (inv_nonneg.mpr (partitionFunctionBC_pos G β (fun _ => J) h Λ _).le) ?_
  exact boltzmannWeightBC_plus_hasNonnegCorrelations G hβ hJ hh Λ A

end IsingModel
