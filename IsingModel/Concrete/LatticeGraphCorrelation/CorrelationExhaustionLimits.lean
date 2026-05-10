import IsingModel.Concrete.LatticeGraphCorrelation.LambdaCorrelationMonotonicity
import IsingModel.AmbientLattice.CorrelationInfinite
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Concrete along-exhaustion correlation limit wrappers

Narrow child module for concrete `latticeGraph` along-exhaustion correlation
monotonicity, boundedness, eventuality, and infinite-volume limit wrappers. The
theorem names are the same as the former legacy declarations, but callers can
now avoid importing the monolithic concrete legacy module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-exhaustion correlation limit wrappers -/

/-- **ℤ^d per-stage h-monotonicity of correlationAlongExhaustion**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h₁, β⟩ A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h₂, β⟩ A n :=
  correlationAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ A hh₁ hh₁₂ n

/-- **ℤ^d per-stage β-monotonicity of correlationAlongExhaustion**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset (Fin d → ℤ)) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β₁⟩ A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h, β₂⟩ A n :=
  correlationAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh A hβ₁ hβ₁₂ n

/-- **ℤ^d per-stage J-monotonicity of correlationAlongExhaustion**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J₁, h, β⟩ A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J₂, h, β⟩ A n :=
  correlationAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ A hJ₁ hJ₁₂ n

/-- **ℤ^d correlationAlongExhaustion range is bddAbove**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_bddAbove
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    BddAbove (Set.range (correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A)) :=
  correlationAlongExhaustion_bddAbove (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A

/-- **ℤ^d `|correlationAlongExhaustion| ≤ 1` eventually**. -/
theorem abs_correlationAlongExhaustion_latticeGraph_eventually_le_one
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    ∀ᶠ n in Filter.atTop,
      |correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n| ≤ 1 :=
  abs_correlationAlongExhaustion_eventually_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A

/-- **ℤ^d `correlationAlongExhaustion` eventually equals the lifted `correlationΛ`**
(any-Exhaustion): for any finite `A`, eventually `A ⊆ Λ.volume n` and
`correlationAlongExhaustion = correlationΛ` on the lifted set. -/
theorem correlationAlongExhaustion_latticeGraph_eventually
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ hA : A ⊆ Λ.volume n,
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n =
        correlationΛ (IsingModel.latticeGraph d) (Λ.volume n) p
          (Ambient.liftFinset A hA) :=
  correlationAlongExhaustion_eventually (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `|correlationAlongExhaustion| ≤ 1` eventually** (any-Exhaustion). -/
theorem abs_correlationAlongExhaustion_latticeGraph_eventually_le_one_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    ∀ᶠ n in Filter.atTop,
      |correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n| ≤ 1 :=
  abs_correlationAlongExhaustion_eventually_le_one
    (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d correlationAlongExhaustion ≤ 1** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_le_one
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n ≤ 1 :=
  correlationAlongExhaustion_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A n

/-- **ℤ^d correlationAlongExhaustion ≥ 0** per stage (ferromagnetic). -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A n :=
  correlationAlongExhaustion_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A n

/-- **ℤ^d shifted correlationΛ sequence is monotone and bounded by 1**
(any-Exhaustion, ferromagnetic). -/
theorem correlationΛ_shifted_monotone_bounded_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Monotone (fun n : ℕ =>
      correlationΛ (IsingModel.latticeGraph d) (Λ.volume (n + N)) p
        (Ambient.liftFinset A (hN (n + N) (Nat.le_add_left N n))))
    ∧ ∀ n : ℕ,
      correlationΛ (IsingModel.latticeGraph d) (Λ.volume (n + N)) p
        (Ambient.liftFinset A (hN (n + N) (Nat.le_add_left N n))) ≤ 1 :=
  correlationΛ_shifted_monotone_bounded (IsingModel.latticeGraph d) Λ p hf hN

/-- **ℤ^d shifted correlationΛ sequence converges** (any-Exhaustion, ferromagnetic). -/
theorem correlationΛ_shifted_tendsto_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    ∃ L : ℝ, Filter.Tendsto
      (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
        (Λ.volume (m + N)) p
        (Ambient.liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds L) :=
  correlationΛ_shifted_tendsto (IsingModel.latticeGraph d) Λ p hf hN

/-- **ℤ^d correlationΛ → correlationInfinite under an explicit subset hypothesis**
(any-Exhaustion). -/
theorem tendsto_correlationΛ_correlationInfinite_of_subset_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Filter.Tendsto
      (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
        (Λ.volume (m + N)) p
        (Ambient.liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds (correlationInfinite (IsingModel.latticeGraph d) Λ p A)) :=
  tendsto_correlationΛ_correlationInfinite_of_subset
    (IsingModel.latticeGraph d) Λ p hf hN

/-- **ℤ^d physical identification: correlationΛ → correlationInfinite**
(any-Exhaustion). -/
theorem tendsto_correlationΛ_correlationInfinite_latticeGraph_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    ∃ N : ℕ, ∃ hN : ∀ n ≥ N, A ⊆ Λ.volume n,
      Filter.Tendsto
        (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
          (Λ.volume (m + N)) p
          (Ambient.liftFinset A (hN (m + N) (Nat.le_add_left N m))))
        Filter.atTop (nhds (correlationInfinite (IsingModel.latticeGraph d)
          Λ p A)) :=
  tendsto_correlationΛ_correlationInfinite (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d physical identification: correlationΛ → correlationInfinite**. -/
theorem tendsto_correlationΛ_correlationInfinite_latticeGraph
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    ∃ N : ℕ, ∃ hN : ∀ n ≥ N, A ⊆ (Ambient.cubicExhaustion d).volume n,
      Filter.Tendsto
        (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume (m + N)) p
          (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
        Filter.atTop (nhds (correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p A)) :=
  tendsto_correlationΛ_correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A

/-- **ℤ^d correlationAlongExhaustion → ciSup** (any Exhaustion). -/
theorem correlationAlongExhaustion_latticeGraph_tendsto_ciSup_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)
      Filter.atTop
      (nhds (⨆ n, correlationAlongExhaustion (IsingModel.latticeGraph d)
        Λ p A n)) :=
  correlationAlongExhaustion_tendsto_ciSup (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d correlationAlongExhaustion → ciSup**. -/
theorem correlationAlongExhaustion_latticeGraph_tendsto_ciSup
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A)
      Filter.atTop
      (nhds (⨆ n, correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n)) :=
  correlationAlongExhaustion_tendsto_ciSup (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A

/-- **ℤ^d correlationAlongExhaustion → correlationInfinite**. -/
theorem tendsto_correlationAlongExhaustion_correlationInfinite_latticeGraph
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A)
      Filter.atTop
      (nhds (correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A)) :=
  tendsto_correlationAlongExhaustion_correlationInfinite
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf A

/-- **ℤ^d correlationAlongExhaustion → correlationInfinite** (any Exhaustion). -/
theorem tendsto_correlationAlongExhaustion_correlationInfinite_latticeGraph_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)
      Filter.atTop
      (nhds (correlationInfinite (IsingModel.latticeGraph d) Λ p A)) :=
  tendsto_correlationAlongExhaustion_correlationInfinite
    (IsingModel.latticeGraph d) Λ p hf A

end Ambient
end IsingModel
