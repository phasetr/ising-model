import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d per-stage lower bounds on the partition function, cubic exhaustion

Instantiates at `IsingModel.latticeGraph d`, along `Ambient.cubicExhaustion d` and at a fixed
stage `n`, the ferromagnetic lower bounds `2 ^ |Λ_n|` and `(2 * cosh (β * h)) ^ |Λ_n|` on the
partition function, together with their logarithmic forms `|Λ_n| * log 2` and
`|Λ_n| * log (2 * cosh (β * h))`. Every statement assumes the ferromagnetic hypothesis on the
parameter record, and none assumes the stage volume nonempty.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 2^|Λ_n|** (ferromagnetic). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_two_pow_card
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_ge_two_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ (2 cosh βh)^|Λ_n|** (ferromagnetic). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_two_cosh_pow_card
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (2 * Real.cosh (p.β * p.h)) ^ ((Ambient.cubicExhaustion d).volume n).card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_ge_two_cosh_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d log Z bound**: `|Λ_n|·log 2 ≤ log Z_n`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_ge_card_mul_log_two
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n) :=
  log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d sharp log Z bound**: `|Λ_n|·log(2 cosh βh) ≤ log Z_n`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_ge_card_mul_log_two_cosh
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (((Ambient.cubicExhaustion d).volume n).card : ℝ)
        * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n) :=
  log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_cosh_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

end Ambient
end IsingModel
