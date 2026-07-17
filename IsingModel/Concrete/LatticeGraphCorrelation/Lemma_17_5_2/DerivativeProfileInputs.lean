import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# GJ §17.5 Lemma 17.5.2 capstone — derivative-profile inputs

This module names shared finite-volume beta-derivative profile inputs used by
the Cauchy and Dini provider routes.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 derivative-profile metric Cauchy input**:
on every closed beta interval contained in the open high-temperature region,
the finite-volume beta-derivative profiles are eventually Cauchy uniformly in
the metric epsilon--`N` sense. -/
def Lemma_17_5_2_DerivativeProfileMetricCauchyOnIcc
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) : Prop :=
  ∀ β₁ β₂ : ℝ,
    Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
      ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
        ∀ β ∈ Set.Icc β₁ β₂,
          dist
            (deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} m) β)
            (deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) < ε

/-- **GJ §17.5 Lemma 17.5.2 derivative-profile pointwise limit input**:
the finite-volume beta-derivative profiles converge pointwise on the open
high-temperature interval to the candidate limiting derivative profile `g'`. -/
def Lemma_17_5_2_DerivativeProfilePointwiseLimit
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ) : Prop :=
  ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
    Filter.Tendsto
      (fun n =>
        deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
      Filter.atTop (nhds (g' β))

end Ambient
end IsingModel
