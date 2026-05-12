import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG

/-!
# Base finite-volume and ∞-volume correlation wrappers at ℤ^d

Concrete wrappers for the finite-volume (`correlationΛ`, `partitionFunctionΛ`,
`freeEnergyΛ`) and ∞-volume (`correlationInfinite`, `magnetizationInfinite`,
`spontaneousCorrelation`) functionals on the ℤ^d Ising model.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationΛ volume-monotonicity**:
`A ⊆ Λ₁ ⊆ Λ₂ ⇒ ⟨σ^A⟩_{Λ₁} ≤ ⟨σ^A⟩_{Λ₂}` for ferromagnetic `p`. -/
theorem correlationΛ_latticeGraph_monotone_volume
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (h12 : Λ₁ ⊆ Λ₂)
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} (hA : A ⊆ Λ₁) :
    correlationΛ (IsingModel.latticeGraph d) Λ₁ p (liftFinset A hA)
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ₂ p
          (liftFinset A (hA.trans h12)) :=
  correlationΛ_monotone_volume (IsingModel.latticeGraph d) h12 p hf hA

/-- **ℤ^d partitionFunctionΛ positivity** per finite volume. -/
theorem partitionFunctionΛ_latticeGraph_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    0 < partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_pos (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `|correlationΛ| ≤ 1`** per finite volume. -/
theorem abs_correlationΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    |correlationΛ (IsingModel.latticeGraph d) Λ p A| ≤ 1 :=
  abs_correlationΛ_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d correlationΛ ≤ 1** per finite volume. -/
theorem correlationΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ p A ≤ 1 :=
  correlationΛ_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d correlationΛ ≥ 0** per finite volume (ferromagnetic). -/
theorem correlationΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (A : Finset (↑Λ : Type _)) :
    0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  correlationΛ_nonneg (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d freeEnergyAlongExhaustion_apply unfolding**. -/
@[simp]
theorem freeEnergyAlongExhaustion_latticeGraph_apply
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      = freeEnergyΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) p :=
  freeEnergyAlongExhaustion_apply (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d partitionFunctionAlongExhaustion_apply unfolding**. -/
@[simp]
theorem partitionFunctionAlongExhaustion_latticeGraph_apply
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      = partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) p :=
  partitionFunctionAlongExhaustion_apply (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d freeEnergyAlongExhaustion = log Z / |Λ|** (log-bridge). -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_eq_log_div_card
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      = (Fintype.card (↑((Ambient.cubicExhaustion d).volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p n) :=
  freeEnergyAlongExhaustion_eq_log_div_card (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d `correlationAlongExhaustion` is ≤ 1** per stage (unconditional).
Concrete specialization of `correlationAlongExhaustion_le_one`. -/
theorem correlationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n ≤ 1 :=
  correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d cross-exhaustion sandwich** (ferromagnetic): for any two ℤ^d
exhaustions `Λ, Λ'`, per stage `correlationAlongExhaustion Λ'` is ≤
the `correlationInfinite` computed via `Λ`. -/
theorem correlationAlongExhaustion_latticeGraph_le_correlationInfinite_of_other
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ' p A n
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  correlationAlongExhaustion_le_correlationInfinite_of_other
    (IsingModel.latticeGraph d) Λ Λ' p hf A n

/-- **ℤ^d `correlationAlongExhaustion ≤ correlationInfinite`** per stage
(ferromagnetic): stage-wise upper bound by the limsup value. -/
theorem correlationAlongExhaustion_latticeGraph_le_correlationInfinite
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  correlationAlongExhaustion_le_correlationInfinite
    (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `correlationAlongExhaustion` is ≥ 0** per stage (ferromagnetic).
Concrete specialization of `correlationAlongExhaustion_nonneg`. -/
theorem correlationAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  correlationAlongExhaustion_nonneg (IsingModel.latticeGraph d) Λ p hf A n

/-- **ℤ^d `correlationInfinite` on the empty site set = 1** (any Exhaustion). -/
@[simp]
theorem correlationInfinite_latticeGraph_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p ∅ = 1 :=
  correlationInfinite_empty (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `correlationΛ` vanishes at `β = 0`** for nonempty `A : Finset ↑Λ`. -/
theorem correlationΛ_latticeGraph_beta_zero_vanish_of_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ)
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 :=
  correlationΛ_beta_zero_vanish_of_nonempty (IsingModel.latticeGraph d) Λ J h A hA

/-- **ℤ^d `correlationΛ` vanishes at `J = h = 0`** for nonempty `A`. -/
theorem correlationΛ_latticeGraph_zero_params_vanish_of_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 :=
  correlationΛ_zero_params_vanish_of_nonempty (IsingModel.latticeGraph d) Λ β A hA

/-- **ℤ^d `correlationAlongExhaustion` vanishes at `β = 0`** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_beta_zero_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) A n = 0 :=
  correlationAlongExhaustion_beta_zero_vanish (IsingModel.latticeGraph d)
    Λ J h A hA n

/-- **ℤ^d `correlationAlongExhaustion` vanishes at `J = h = 0`** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_zero_params_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (β : ℝ) (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) A n = 0 :=
  correlationAlongExhaustion_zero_params_vanish (IsingModel.latticeGraph d)
    Λ β A hA n

/-- **ℤ^d `partitionFunctionΛ_apply`** unfolding. -/
theorem partitionFunctionΛ_latticeGraph_apply
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  partitionFunctionΛ_apply (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `correlationΛ_apply`** unfolding. -/
theorem correlationΛ_latticeGraph_apply
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ p A
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A :=
  correlationΛ_apply (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `freeEnergyΛ_apply`** unfolding. -/
theorem freeEnergyΛ_latticeGraph_apply
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  freeEnergyΛ_apply (IsingModel.latticeGraph d) Λ p

/-! ## Moved: magnetization* / spontaneousCorrelation monotone_ambient_subgraph wrappers

The 4 ℤ^d
`magnetization{Λ,AlongExhaustion,Infinite}_latticeGraph_monotone_ambient_subgraph`
and `spontaneousCorrelation_latticeGraph_monotone_ambient_subgraph`
wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.BaseMonotoneAmbientSubgraph`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: spontaneousCorrelation / spontaneousMagnetization_monotone_ambient_subgraph wrappers

The 9 ℤ^d `spontaneousCorrelation_latticeGraph_*` wrappers
(`neg_one_le`, `nonneg`, `le_one`, `monotone_J`, `monotone_beta`,
`singleton_eq_spontaneousMagnetization`, `abs_le_one`, `sq_le_one`)
plus the `spontaneousMagnetization_latticeGraph_monotone_ambient_subgraph`
companion now live in
`IsingModel.Concrete.LatticeGraphCorrelation.BaseSpontaneousCorrelation`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: magnetization sq_le_one + correlation J=0 / ge_tanh wrappers

The 8 ℤ^d wrappers
`magnetization{Λ,AlongExhaustion,Infinite}_latticeGraph_sq_le_one`,
`correlationΛ_latticeGraph_J_zero`,
`correlation{Λ,Infinite}_latticeGraph_ge_tanh_pow_card`, and
`magnetization{Λ,Infinite}_latticeGraph_ge_tanh` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.BaseBoundsTanh`.
The legacy import path is preserved by re-importing the new child.
-/


/-- **ℤ^d `correlationAlongExhaustion` at `J = 0`** per stage (on-stage):
`A ⊆ Λ.volume n ⇒ = tanh(β·h)^|A|`. -/
theorem correlationAlongExhaustion_latticeGraph_J_zero_of_subset
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) {A : Finset (Fin d → ℤ)} {n : ℕ} (hAn : A ⊆ Λ.volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) A n
      = Real.tanh (β * h) ^ A.card :=
  correlationAlongExhaustion_J_zero_of_subset (IsingModel.latticeGraph d) Λ h β hAn

/-- **ℤ^d `correlationAlongExhaustion` at `J = 0` is eventually constant
at `tanh(β·h)^|A|`**. -/
theorem correlationAlongExhaustion_latticeGraph_J_zero_eventually_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (A : Finset (Fin d → ℤ)) :
    ∀ᶠ n in Filter.atTop,
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) A n
        = Real.tanh (β * h) ^ A.card :=
  correlationAlongExhaustion_J_zero_eventually_eq
    (IsingModel.latticeGraph d) Λ h β A


/-- **ℤ^d correlationΛ_empty = 1** per finite volume. -/
@[simp]
theorem correlationΛ_latticeGraph_empty
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    correlationΛ (IsingModel.latticeGraph d) Λ p ∅ = 1 :=
  correlationΛ_empty (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d correlationAlongExhaustion_empty = 1** per stage. -/
@[simp]
theorem correlationAlongExhaustion_latticeGraph_empty
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p ∅ n = 1 :=
  correlationAlongExhaustion_empty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d correlationAlongExhaustion of_subset unfolding**. -/
theorem correlationAlongExhaustion_latticeGraph_of_subset
    (d : ℕ) (p : IsingParams ℝ)
    {A : Finset (Fin d → ℤ)} {n : ℕ}
    (hA : A ⊆ (Ambient.cubicExhaustion d).volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n
      = correlationΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) p (liftFinset A hA) :=
  correlationAlongExhaustion_of_subset (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hA

/-- **ℤ^d correlationAlongExhaustion of_not_subset unfolding**. -/
theorem correlationAlongExhaustion_latticeGraph_of_not_subset
    (d : ℕ) (p : IsingParams ℝ)
    {A : Finset (Fin d → ℤ)} {n : ℕ}
    (hA : ¬ A ⊆ (Ambient.cubicExhaustion d).volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n = 0 :=
  correlationAlongExhaustion_of_not_subset (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hA

/-- **ℤ^d correlationAlongExhaustion stage-index Monotone**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    Monotone (correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A) :=
  correlationAlongExhaustion_monotone (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A

/-- **ℤ^d correlationΛ_gks_second** (GKS-II at finite volume). -/
theorem correlationΛ_latticeGraph_gks_second
    (d : ℕ) {Λ : Finset (Fin d → ℤ)}
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A B : Finset (Fin d → ℤ)} (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    ∃ hAB : A ∆ B ⊆ Λ,
      correlationΛ (IsingModel.latticeGraph d) Λ p (liftFinset A hA)
        * correlationΛ (IsingModel.latticeGraph d) Λ p (liftFinset B hB)
        ≤ correlationΛ (IsingModel.latticeGraph d) Λ p (liftFinset (A ∆ B) hAB) := by
  have hAB : A ∆ B ⊆ Λ := by
    intro x hx
    rw [Finset.mem_symmDiff] at hx
    rcases hx with ⟨hxA, _⟩ | ⟨hxB, _⟩
    · exact hA hxA
    · exact hB hxB
  refine ⟨hAB, ?_⟩
  exact correlationΛ_gks_second (IsingModel.latticeGraph d) p hf hA hB

end Ambient
end IsingModel
