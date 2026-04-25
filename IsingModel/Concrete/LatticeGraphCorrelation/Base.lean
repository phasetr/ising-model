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

/-- **ℤ^d `magnetizationΛ_monotone_ambient_subgraph`**:
`G₁ ≤ G₂ ⇒ M_{Λ,G₁}(i) ≤ M_{Λ,G₂}(i)` (ferromagnetic). -/
theorem magnetizationΛ_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph G₁ Λ).edgeSet]
    [Fintype (Ambient.inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ↑Λ) :
    magnetizationΛ G₁ Λ p i ≤ magnetizationΛ G₂ Λ p i :=
  magnetizationΛ_monotone_ambient_subgraph h Λ p hf i

/-- **ℤ^d `magnetizationAlongExhaustion_monotone_ambient_subgraph`**
per stage (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion G₁ Λ p i n
      ≤ magnetizationAlongExhaustion G₂ Λ p i n :=
  magnetizationAlongExhaustion_monotone_ambient_subgraph h Λ p hf i n

/-- **ℤ^d `magnetizationInfinite_monotone_ambient_subgraph`**
(ferromagnetic). -/
theorem magnetizationInfinite_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    magnetizationInfinite G₁ Λ p i ≤ magnetizationInfinite G₂ Λ p i :=
  magnetizationInfinite_monotone_ambient_subgraph h Λ p hf i

/-- **ℤ^d `spontaneousCorrelation_monotone_ambient_subgraph`**
(ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation G₁ Λ J β A
      ≤ spontaneousCorrelation G₂ Λ J β A :=
  spontaneousCorrelation_monotone_ambient_subgraph hG Λ hJ hβ A

/-- **ℤ^d `-1 ≤ spontaneousCorrelation`** (ferromagnetic). -/
theorem neg_one_le_spontaneousCorrelation_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    -1 ≤ spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A :=
  neg_one_le_spontaneousCorrelation (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d spontaneousCorrelation ≥ 0** (ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    0 ≤ spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A :=
  spontaneousCorrelation_nonneg (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d spontaneousCorrelation ≤ 1** (ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A ≤ 1 :=
  spontaneousCorrelation_le_one (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d J-direction monotonicity of `spontaneousCorrelation`**
(ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun J : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A)
      (Set.Ici 0) :=
  spontaneousCorrelation_monotone_J (IsingModel.latticeGraph d) Λ hβ A

/-- **ℤ^d β-direction monotonicity of `spontaneousCorrelation`**
(ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun β : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A)
      (Set.Ioi 0) :=
  spontaneousCorrelation_monotone_beta (IsingModel.latticeGraph d) Λ hJ A

/-- **ℤ^d `spontaneousCorrelation ... {i} = spontaneousMagnetization ... i`**
(any-Exhaustion): singleton-set spontaneous correlation equals
spontaneous magnetization. -/
theorem spontaneousCorrelation_latticeGraph_singleton_eq_spontaneousMagnetization
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (i : Fin d → ℤ) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β {i}
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i :=
  spontaneousCorrelation_singleton_eq_spontaneousMagnetization
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d `|spontaneousCorrelation| ≤ 1`** (ferromagnetic). -/
theorem abs_spontaneousCorrelation_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    |spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A| ≤ 1 :=
  abs_spontaneousCorrelation_le_one (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d `spontaneousCorrelation² ≤ 1`** (ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A ^ 2 ≤ 1 :=
  spontaneousCorrelation_sq_le_one (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d `spontaneousMagnetization_monotone_ambient_subgraph`**
(ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization G₁ Λ J β i
      ≤ spontaneousMagnetization G₂ Λ J β i :=
  spontaneousMagnetization_monotone_ambient_subgraph hG Λ hJ hβ i

/-- **ℤ^d `magnetizationΛ² ≤ 1`**. -/
theorem magnetizationΛ_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ p i ^ 2 ≤ 1 :=
  magnetizationΛ_sq_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `magnetizationAlongExhaustion² ≤ 1`** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n ^ 2 ≤ 1 := by
  have h := abs_magnetizationAlongExhaustion_le_one
    (IsingModel.latticeGraph d) Λ p i n
  have : |magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n| ^ 2
      ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **ℤ^d `magnetizationInfinite² ≤ 1`** (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i ^ 2 ≤ 1 :=
  magnetizationInfinite_sq_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `correlationΛ` at `J = 0` closed form**:
`correlationΛ ⟨0, h, β⟩ A = tanh(β·h)^|A|`. -/
theorem correlationΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card :=
  correlationΛ_J_zero (IsingModel.latticeGraph d) Λ h β A

/-- **ℤ^d `correlationΛ ≥ tanh(β·h)^|A|`** (ferromagnetic). -/
theorem correlationΛ_latticeGraph_ge_tanh_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  correlationΛ_ge_tanh_pow_card (IsingModel.latticeGraph d) Λ hJ hh hβ A

/-- **ℤ^d `correlationInfinite ≥ tanh(β·h)^|A|`** (ferromagnetic). -/
theorem correlationInfinite_latticeGraph_ge_tanh_pow_card
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  correlationInfinite_ge_tanh_pow_card (IsingModel.latticeGraph d) Λ hJ hh hβ A


/-- **ℤ^d `magnetizationΛ ≥ tanh(β·h)`** (ferromagnetic). -/
theorem magnetizationΛ_latticeGraph_ge_tanh
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : ↑Λ) :
    Real.tanh (β * h)
      ≤ magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  magnetizationΛ_ge_tanh (IsingModel.latticeGraph d) Λ hJ hh hβ i

/-- **ℤ^d `magnetizationInfinite ≥ tanh(β·h)`** (ferromagnetic, any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_ge_tanh
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : Fin d → ℤ) :
    Real.tanh (β * h)
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  magnetizationInfinite_ge_tanh (IsingModel.latticeGraph d) Λ hJ hh hβ i


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
