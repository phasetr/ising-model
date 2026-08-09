import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d per-stage lower bounds on the free-energy density

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and along `Ambient.cubicExhaustion d`, the per-stage lower bounds `log 2` and
`log (2 * cosh (β * h))` on the free-energy density, which at stage `n` is the logarithm of
the partition function divided by the stage volume. Every statement assumes the ferromagnetic
signs `0 ≤ J`, `0 ≤ h` and `0 < β` on the parameter record `⟨J, h, β⟩`, and every statement
assumes the stage volume nonempty.
-/

namespace IsingModel
namespace Ambient

/-- **Per-stage lower bound on ℤ^d**: `log 2 ≤ freeEnergyAlongExhaustion` for
ferromagnetic + nonempty stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_ge_log_two
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    Real.log 2 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_log_two (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n hne

/-- **Sharp per-stage lower bound on ℤ^d**:
`log(2 cosh(βh)) ≤ freeEnergyAlongExhaustion`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_ge_log_two_cosh
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_log_two_cosh (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n hne

/-- **ℤ^d per-stage `log 2 ≤ f_n`** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_log_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log 2 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_ge_log_two (IsingModel.latticeGraph d) Λ
    hJ hh hβ n hne

/-- **ℤ^d per-stage `log(2 cosh(βh)) ≤ f_n`** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_log_two_cosh
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_ge_log_two_cosh (IsingModel.latticeGraph d) Λ
    hJ hh hβ n hne

end Ambient
end IsingModel
