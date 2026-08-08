import IsingModel.AmbientLatticeSumFInfHSymMono
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyInfinite monotonicity wrappers

Instantiates monotonicity of the infinite-volume free energy in `J`, in the external field,
in `β` and in `|h|` at `IsingModel.latticeGraph d`. Each is a pass-through of the ambient
`freeEnergyInfinite_monotone_*` lemma.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d J-monotonicity of `freeEnergyInfinite`** (any-Exhaustion with
caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_J
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun J : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyInfinite_monotone_J (IsingModel.latticeGraph d) Λ hh hβ hc

/-- **ℤ^d h-monotonicity of `freeEnergyInfinite`** (any-Exhaustion with
caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun h : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyInfinite_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ hc

/-- **ℤ^d β-monotonicity of `freeEnergyInfinite`** (any-Exhaustion with
caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_beta
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun β : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) :=
  freeEnergyInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh hc

/-- **ℤ^d `|h|`-monotonicity of `freeEnergyInfinite`** (any-Exhaustion
with caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_abs_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _))
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_monotone_abs_h (IsingModel.latticeGraph d) Λ hJ hβ hc hh

end Ambient

end IsingModel
