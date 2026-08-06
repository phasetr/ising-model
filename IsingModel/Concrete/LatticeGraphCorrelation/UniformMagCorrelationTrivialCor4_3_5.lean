import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Cor 4.3.5 ∞-volume correlation wrappers

Narrow child module for two ℤ^d
`correlationInfinite_latticeGraph_*_cor_4_3_5_h0` wrappers extracted
from `UniformMagCorrelationTrivial.lean`:

* `correlationInfinite_latticeGraph_cor_4_3_5_h0`,
* `correlationInfinite_latticeGraph_cubicExhaustion_cor_4_3_5_h0`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Cor 4.3.5 at ∞-volume** (GJ §4.3 Cor 4.3.5 p. 62, any-Exhaustion):
inductive (n+2)-point bound at `h = 0`. -/
theorem correlationInfinite_latticeGraph_cor_4_3_5_h0
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (S : Finset (Fin d → ℤ)) {j k : Fin d → ℤ}
    (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ (insert j (insert k S))
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ S *
          correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ {j, k} +
        ∑ T ∈ S.powerset,
          correlationInfinite (IsingModel.latticeGraph d) Λ
              ⟨J, 0, β⟩ (insert j T) *
            correlationInfinite (IsingModel.latticeGraph d) Λ
              ⟨J, 0, β⟩ (insert k (S \ T)) :=
  correlationInfinite_cor_4_3_5_h0
    (IsingModel.latticeGraph d) Λ J β hf S hj hk hjk

/-- **ℤ^d Cor 4.3.5 at ∞-volume** (Glimm–Jaffe §4.3 Cor 4.3.5 p. 62):
inductive (n+2)-point bound at `h = 0` on ℤ^d. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_cor_4_3_5_h0
    (d : ℕ) (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (S : Finset (Fin d → ℤ)) {j k : Fin d → ℤ}
    (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ (insert j (insert k S))
      ≤ correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ S *
          correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ {j, k} +
        ∑ T ∈ S.powerset,
          correlationInfinite (IsingModel.latticeGraph d)
              (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ (insert j T) *
            correlationInfinite (IsingModel.latticeGraph d)
              (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ (insert k (S \ T)) :=
  correlationInfinite_cor_4_3_5_h0 (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hf S hj hk hjk


end Ambient
end IsingModel
