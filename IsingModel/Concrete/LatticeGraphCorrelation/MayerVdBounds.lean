import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerVdBounds

/-!
# Concrete Mayer vd bound wrappers

Narrow child module for concrete `ℤ^d` `vdPolymerFamilies_sum` bound
wrappers. This keeps callers that only need these forwarders out of the
monolithic lattice-correlation legacy module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 vdPolymerFamilies_sum bound family ℤ^d wraps -/

/-- **ℤ^d Λ: vdSum_tanh ≤ 2^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_le_two_pow
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_le_two_pow
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: vdSum_tanh ≤ (1+tanh)^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_le_one_plus_tanh_pow
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_le_one_plus_tanh_pow
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: 1 ≤ vdSum_tanh** under `0 ≤ β·J`. -/
theorem one_le_vdPolymerFamilies_sum_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  Ambient.one_le_vdPolymerFamilies_sum_Λ
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d along-ex: vdSum_tanh ≤ 2^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_le_two_pow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_le_two_pow
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: vdSum_tanh ≤ (1+tanh)^|E|** under `0 ≤ β·J`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_le_one_plus_tanh_pow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_le_one_plus_tanh_pow
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: 1 ≤ vdSum_tanh** under `0 ≤ β·J`. -/
theorem one_le_vdPolymerFamilies_sumAlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  Ambient.one_le_vdPolymerFamilies_sumAlongExhaustion
    (IsingModel.latticeGraph d) Λ hβJ n

/-! ### §18.5 vdPolymerFamilies_sum generic-t bounds ℤ^d wraps -/

/-- **ℤ^d Λ: 1 ≤ vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_ge_one_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_ge_one_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: vdSum ≤ (1+t)^|E|** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_le_one_plus_pow_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card)
      ≤ (1 + t) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_le_one_plus_pow_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: 0 < vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_pos_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_pos_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: vdSum = 1 + ε(t)** decomposition. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_eq_one_add
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) =
      1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_eq_one_add
    (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d along-ex: 1 ≤ vdSum** under `0 ≤ t`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_ge_one_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_ge_one_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: vdSum ≤ (1+t)^|E|** under `0 ≤ t`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_le_one_plus_pow_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card)
      ≤ (1 + t) ^
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_le_one_plus_pow_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: 0 < vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_pos_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_pos_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: vdSum = 1 + ε(t)** decomposition. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_eq_one_add
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) =
      1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_eq_one_add
    (IsingModel.latticeGraph d) Λ t n

end Ambient
end IsingModel
