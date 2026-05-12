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
# ℤ^d magnetizationAlongExhaustion + correlationAlongExhaustion bounds + convergence wrappers

Narrow child module for 17 ℤ^d wrappers covering
`magnetizationAlongExhaustion_latticeGraph_*` and
`correlationAlongExhaustion_latticeGraph_*` bound / monotone /
convergent / bddAbove / bddBelow / `_le_*Infinite` / `_tendsto_ciSup`
/ `_eq_ciSup` and `tendsto_magnetizationAlongExhaustion_*Infinite`
wrappers on `latticeGraph d`. Theorem names are unchanged from the
former `UniformMag` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d magnetizationAlongExhaustion ≤ 1** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n ≤ 1 :=
  magnetizationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationAlongExhaustion ≥ 0** per stage (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) (n : ℕ) :
    0 ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  magnetizationAlongExhaustion_nonneg (IsingModel.latticeGraph d) Λ p hf i n

/-- **ℤ^d `magnetizationAlongExhaustion ≤ magnetizationInfinite`** per stage
(ferromagnetic): stage-wise upper bound by the limsup value. -/
theorem magnetizationAlongExhaustion_latticeGraph_le_magnetizationInfinite
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationAlongExhaustion_le_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationAlongExhaustion → magnetizationInfinite** (ferromagnetic):
Concrete specialization of `tendsto_magnetizationAlongExhaustion_magnetizationInfinite`. -/
theorem tendsto_magnetizationAlongExhaustion_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop
      (nhds (magnetizationInfinite (IsingModel.latticeGraph d) Λ p i)) :=
  tendsto_magnetizationAlongExhaustion_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d existential convergence of `magnetizationAlongExhaustion`**
(ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_convergent
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    ∃ L : ℝ, Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop (nhds L) :=
  magnetizationAlongExhaustion_convergent (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d stage-index monotonicity of `magnetizationAlongExhaustion`**
(ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Monotone (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i) :=
  magnetizationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d `magnetizationAlongExhaustion` bounded above** (unconditional). -/
theorem magnetizationAlongExhaustion_latticeGraph_bddAbove
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    BddAbove (Set.range
      (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)) :=
  magnetizationAlongExhaustion_bddAbove (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `correlationAlongExhaustion` bounded below** (unconditional). -/
theorem correlationAlongExhaustion_latticeGraph_bddBelow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    BddBelow (Set.range
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)) :=
  correlationAlongExhaustion_bddBelow (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion` bounded above** (unconditional). -/
theorem correlationAlongExhaustion_latticeGraph_bddAbove
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    BddAbove (Set.range
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)) :=
  correlationAlongExhaustion_bddAbove (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion` monotone** (ferromagnetic):
volume-increasing ⇒ correlation nondecreasing. -/
theorem correlationAlongExhaustion_latticeGraph_monotone
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Monotone (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A) :=
  correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d `correlationAlongExhaustion` existential convergence**
(ferromagnetic). -/
theorem correlationAlongExhaustion_latticeGraph_convergent
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    ∃ L : ℝ, Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)
      Filter.atTop (nhds L) :=
  correlationAlongExhaustion_convergent (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d `magnetizationAlongExhaustion` bounded below** (unconditional). -/
theorem magnetizationAlongExhaustion_latticeGraph_bddBelow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    BddBelow (Set.range
      (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)) :=
  magnetizationAlongExhaustion_bddBelow (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationAlongExhaustion → ⨆ n ...** (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_tendsto_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop
      (nhds (⨆ n, magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ p i n)) :=
  magnetizationAlongExhaustion_tendsto_ciSup (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d `magnetizationInfinite` as `ciSup`**:
`magnetizationInfinite = ⨆ n, magnetizationAlongExhaustion`. -/
theorem magnetizationInfinite_latticeGraph_eq_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i
      = ⨆ n, magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  magnetizationInfinite_eq_ciSup (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `correlationInfinite` as `ciSup`**. -/
theorem correlationInfinite_latticeGraph_eq_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A
      = ⨆ n, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  correlationInfinite_eq_ciSup (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion ≤ correlationInfinite`** pointwise. -/
theorem correlationAlongExhaustion_le_correlationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  correlationAlongExhaustion_le_correlationInfinite (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `magnetizationAlongExhaustion ≤ magnetizationInfinite`** pointwise. -/
theorem magnetizationAlongExhaustion_le_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationAlongExhaustion_le_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p i n

end Ambient

end IsingModel
