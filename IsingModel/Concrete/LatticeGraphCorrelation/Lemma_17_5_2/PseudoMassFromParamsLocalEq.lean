import IsingModel.PseudoMass.FromParamsBasic

/-!
# Local pseudo-mass defining equations for concrete beta profiles

This module packages the neighborhood-local defining equation for the concrete
`pseudoMassFromParamsAtPair` beta profile.  It supplies the shape required by
the localized Lemma 17.5.2 pseudo-mass Lipschitz APIs.
-/

namespace IsingModel

open Filter Set

namespace Ambient

/-- **Concrete beta-profile local pseudo-mass equation from a local active range**:
if the infinite correlation profile stays in `Ioo 0 2` near `β`, then the
corresponding `pseudoMassFromParamsAtPair` profile satisfies the pseudo-mass
defining equation near `β`. -/
theorem pseudoMassFromParamsAtPair_beta_pseudoMassG_eventuallyEq_of_corr_eventually_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β : ℝ}
    (hcorr : ∀ᶠ β' in nhds β,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2) :
    (fun β' =>
      pseudoMassG α r
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) x z)) =ᶠ[nhds β]
      (fun β' =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) := by
  simpa [pseudoMassFromParamsAtPair] using
    (pseudoMassG_pseudoMassExt_eventuallyEq_of_eventually_mem
      hα hr (c := fun β' =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) hcorr)

/-- **Concrete beta-profile local pseudo-mass equation from continuity**:
pointwise active-range membership of the infinite correlation upgrades by
continuity to the neighborhood-local defining equation required by the
pseudo-mass derivative APIs. -/
theorem pseudoMassFromParamsAtPair_beta_pseudoMassG_eventuallyEq_of_corr_continuousAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β : ℝ}
    (hc_cont :
      ContinuousAt
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2) :
    (fun β' =>
      pseudoMassG α r
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) x z)) =ᶠ[nhds β]
      (fun β' =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) := by
  have hc_nhds :
      Set.Ioo (0 : ℝ) 2 ∈
        nhds (Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :=
    IsOpen.mem_nhds isOpen_Ioo hcorr
  have hcorr_eventually :
      ∀ᶠ β' in nhds β,
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 :=
    hc_cont.tendsto hc_nhds
  exact
    pseudoMassFromParamsAtPair_beta_pseudoMassG_eventuallyEq_of_corr_eventually_mem
      hα hr Λ J x z hcorr_eventually

/-- **Closed-interval high-temperature local equation package**: if the whole
closed beta interval has continuity and the infinite correlation is in the
active range at every interval point, then the concrete
`pseudoMassFromParamsAtPair` profile supplies the local defining equation at
every interval point. -/
theorem pseudoMassFromParamsAtPair_beta_pseudoMassG_eventuallyEq_on_Icc_of_corr_continuousAt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) {β₁ β₂ : ℝ}
    (hc_cont : ∀ β ∈ Set.Icc β₁ β₂,
      ContinuousAt
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2) :
    ∀ β ∈ Set.Icc β₁ β₂,
      (fun β' =>
        pseudoMassG α r
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) x z)) =ᶠ[nhds β]
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) := by
  intro β hβ
  exact pseudoMassFromParamsAtPair_beta_pseudoMassG_eventuallyEq_of_corr_continuousAt
    hα hr Λ J x z (hc_cont β hβ) (hcorr β hβ)

end Ambient

end IsingModel
