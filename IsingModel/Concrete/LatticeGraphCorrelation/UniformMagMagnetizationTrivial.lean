import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPoint
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMag

/-!
# ℤ^d magnetizationΛ + magnetizationAlongExhaustion monotone + trivial-slice wrappers

Narrow child module for 15 ℤ^d wrappers covering
`magnetizationΛ_latticeGraph_*` and
`magnetizationAlongExhaustion_latticeGraph_*` J / h / β monotonicity
on `[0, ∞)` / `(0, ∞)` and trivial slices `h_zero`, `beta_zero`,
`zero_params`, `J_zero` / `J_zero_of_mem` / `J_zero_eventually_eq`.
Theorem names are unchanged from the former `UniformMag`
declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetizationΛ h-monotonicity**: `MonotoneOn` in `h` on `Ici 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : ↑Λ) :
    MonotoneOn
      (fun h : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici 0) :=
  magnetizationΛ_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d magnetizationΛ β-monotonicity**: `MonotoneOn` in `β` on `Ioi 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (i : ↑Λ) :
    MonotoneOn
      (fun β : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi 0) :=
  magnetizationΛ_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh i

/-- **ℤ^d magnetizationΛ J-monotonicity**: `MonotoneOn` in `J` on `Ici 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (i : ↑Λ) :
    MonotoneOn
      (fun J : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici 0) :=
  magnetizationΛ_monotone_J (IsingModel.latticeGraph d) Λ hh hβ i

/-- **ℤ^d magnetizationAlongExhaustion h-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (i : Fin d → ℤ) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ
    hJ hβ i hh₁ hh₁₂ n

/-- **ℤ^d magnetizationAlongExhaustion β-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (i : Fin d → ℤ) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ
    hJ hh i hβ₁ hβ₁₂ n

/-- **ℤ^d magnetizationAlongExhaustion J-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (i : Fin d → ℤ) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ
    hh hβ i hJ₁ hJ₁₂ n

/-- **ℤ^d magnetizationΛ at h = 0 vanishes (Z₂)**. -/
theorem magnetizationΛ_latticeGraph_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_h_zero (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d magnetizationAlongExhaustion at h = 0 vanishes (Z₂)** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_h_zero (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d magnetizationΛ vanishes at β=0**. -/
theorem magnetizationΛ_latticeGraph_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_beta_zero (IsingModel.latticeGraph d) Λ J h i

/-- **ℤ^d magnetizationAlongExhaustion vanishes at β=0** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_beta_zero (IsingModel.latticeGraph d) Λ J h i n

/-- **ℤ^d magnetizationΛ vanishes at J=h=0**. -/
theorem magnetizationΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_zero_params (IsingModel.latticeGraph d) Λ β i

/-- **ℤ^d magnetizationAlongExhaustion vanishes at J=h=0** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_zero_params (IsingModel.latticeGraph d) Λ β i n

/-- **ℤ^d magnetizationΛ at J=0 closed form**: `= tanh(β·h)`. -/
theorem magnetizationΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) :=
  magnetizationΛ_J_zero (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d magnetizationAlongExhaustion at J=0** per stage (on-stage):
`i ∈ Λ.volume n ⇒ = tanh(β·h)`. -/
theorem magnetizationAlongExhaustion_latticeGraph_J_zero_of_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    {i : Fin d → ℤ} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i n = Real.tanh (β * h) :=
  magnetizationAlongExhaustion_J_zero_of_mem (IsingModel.latticeGraph d) Λ h β hi

/-- **ℤ^d magnetizationAlongExhaustion at J=0 is eventually `tanh(β·h)`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_J_zero_eventually_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (i : Fin d → ℤ) :
    ∀ᶠ n in Filter.atTop,
      magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) i n = Real.tanh (β * h) :=
  magnetizationAlongExhaustion_J_zero_eventually_eq
    (IsingModel.latticeGraph d) Λ h β i


end Ambient

end IsingModel
