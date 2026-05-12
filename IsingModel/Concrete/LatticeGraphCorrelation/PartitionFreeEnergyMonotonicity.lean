import IsingModel.Concrete.LatticeGraphBED

/-!
# Concrete partition/free-energy parameter monotonicity wrappers

Thin `ℤ^d` specializations of finite-volume and along-exhaustion partition /
free-energy monotonicity statements.  These wrappers keep downstream users from
importing the legacy concrete correlation module when they only need parameter
monotonicity or zero-parameter comparison facts.
-/

namespace IsingModel

namespace Ambient

/-! ## Along-exhaustion free-energy bounds and monotonicity -/

/-- **ℤ^d per-stage explicit upper bound on freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_upper_bound
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n ≤ Real.log 2 +
      |p.β| * (|p.J| * (Ambient.inducedGraph (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume n)).edgeFinset.card
          + |p.h| * Fintype.card
            (↑((Ambient.cubicExhaustion d).volume n) : Type _))
        / Fintype.card (↑((Ambient.cubicExhaustion d).volume n) : Type _) :=
  freeEnergyAlongExhaustion_upper_bound (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n hne

/-- **ℤ^d `freeEnergyAlongExhaustion` per-stage upper bound** (any-Exhaustion):
`≤ log 2 + |β|·(|J|·|E_n|+|h|·|V_n|)/|V_n|`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_upper_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      ≤ Real.log 2 + |p.β| *
          (|p.J| * (Ambient.inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n)).edgeFinset.card
            + |p.h| * Fintype.card (↑(Λ.volume n) : Type _))
        / Fintype.card (↑(Λ.volume n) : Type _) :=
  freeEnergyAlongExhaustion_upper_bound
    (IsingModel.latticeGraph d) Λ p n hne

/-- **ℤ^d per-stage J-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun J : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ n

/-- **ℤ^d per-stage h-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun h : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ n

/-- **ℤ^d per-stage β-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    MonotoneOn
      (fun β : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ioi 0) :=
  freeEnergyAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh n

/-- **ℤ^d per-stage J-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun J : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ hh hβ n

/-- **ℤ^d per-stage h-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun h : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ n

/-- **ℤ^d per-stage β-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    MonotoneOn
      (fun β : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ioi 0) :=
  freeEnergyAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh n

/-! ## Along-exhaustion partition-function monotonicity -/

/-- **ℤ^d log_partitionFunctionAlongExhaustion J-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_J
    (IsingModel.latticeGraph d) Λ h β hh hβ hJ₁ hJ n

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_h
    (IsingModel.latticeGraph d) Λ J β hJ hβ hh₁ hh n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_beta
    (IsingModel.latticeGraph d) Λ J h hJ hh hβ₁ hβ n

/-- **ℤ^d freeEnergyAlongExhaustion ≥ zero_params**: `f(0,0,β) ≤ f(J,h,β)`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_zero_params
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨0, 0, β⟩ n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ zero_params** analog. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_zero_params
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨0, 0, β⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  partitionFunctionAlongExhaustion_ge_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n

/-! ## Lambda-layer partition-function monotonicity -/

/-! ## Moved: Λ-layer partitionFunctionΛ / log_partitionFunctionΛ monotonicity wrappers

The six wrappers `partitionFunctionΛ_latticeGraph_monotone_{J,h,beta}`
and `log_partitionFunctionΛ_latticeGraph_monotone_{J,h,beta}` now live in
`PartitionFreeEnergyMonotonicityLambda.lean`. -/


/-- **ℤ^d log_partitionFunctionAlongExhaustion J-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J₁, h, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J₂, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β hh hβ hJ₁ hJ n

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh₁ hh n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β₁⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β₂⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h hJ hh hβ₁ hβ n

end Ambient

end IsingModel
