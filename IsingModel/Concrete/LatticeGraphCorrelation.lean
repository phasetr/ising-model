import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Complex
import IsingModel.Concrete.LatticeGraphCorrelation.PerStage
import IsingModel.Concrete.LatticeGraphCorrelation.Magnetization
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.Concrete.LatticeGraphCorrelation.Inequalities
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMag
import IsingModel.Concrete.LatticeGraphCorrelation.Base
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.ComplexAnalyticity
import IsingModel.PeierlsInfinite
import IsingModel.AmbientComplexAnalyticity
import IsingModel.AmbientFKG

/-!
# Concrete translation invariance for the ℤ^d Ising correlation

Apply the abstract `correlationInfinite_vaddFinset_of_translationInvariant`
theorem (`TranslationInvariance.lean`, PR #251) to the physical
`d`-dimensional Ising setup
`(IsingModel.latticeGraph d, Ambient.cubicExhaustion d)`:

* `isTranslationInvariant_latticeGraph` (PR #244) supplies the
  `IsTranslationInvariant (Fin d → ℤ) (latticeGraph d)` instance.
* `cubicExhaustion d` (PR #245) supplies the ambient exhaustion.
* The `Fintype (inducedGraph (latticeGraph d) Λ).edgeSet` instance
  (PR #246) supplies the Fintype hypothesis for arbitrary `Λ`.

## Main theorems

* `correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset`:
  `correlationInfinite (latticeGraph d) (cubicExhaustion d) p
  (vaddFinset t A) = correlationInfinite ... p A` (ferromagnetic).
* `magnetizationInfinite_latticeGraph_cubicExhaustion_translation`:
  single-site specialization.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6, p. 68.
-/

open scoped symmDiff

namespace IsingModel

namespace Ambient

/-! #### GJ §5.4 Prop 5.4.2 along-exhaustion wrappers (Peierls)

Direct ℤ^d forwarders for `prop_5_4_2_along_exhaustion` and
`prop_5_4_2_limsup_le` from `IsingModel/PeierlsInfinite.lean`, at the
ambient `latticeGraph d` on an arbitrary `Ambient.Exhaustion (Fin d → ℤ)`.
The caller supplies stage-wise `Preconnected` + `Fintype G_n.edgeSet`
instances and the geometric choice of `B n`, `i n`, and the exponential
bound hypothesis; the `DecidableRel (inducedGraph …).Adj` instance
required by the abstract theorems is supplied via `classical` in the
proof body (so it does not appear in the wrapper signatures). -/

/-- **ℤ^d GJ §5.4 Prop 5.4.2 per-stage along-exhaustion**
(Λ-induced): pointwise Peierls bound at every stage of the exhaustion.
Thin pass-through of `IsingModel.prop_5_4_2_along_exhaustion`; the
proof uses `classical` to supply the stage-wise
`DecidableRel (inducedGraph …).Adj` instance without exposing it in
the type. -/
theorem prop_5_4_2_along_exhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (hconn : ∀ n, (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).Preconnected)
    (J β c : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : ∀ n, Finset (↑(Λ.volume n) : Type _))
    (hB : ∀ n, (B n).Nonempty)
    (i : ∀ n, (↑(Λ.volume n) : Type _))
    (hexp : ∀ n,
      2 * ((2 : ℝ) ^ Fintype.card (↑(Λ.volume n) : Type _)) *
          Real.exp (-2 * β * J) ≤
        Real.exp (-c * β)) :
    ∀ n,
      0 ≤ 1 - IsingModel.plusGibbsExpectation
              (Ambient.inducedGraph
                (IsingModel.latticeGraph d) (Λ.volume n))
              ⟨J, 0, β⟩ (B n) (fun σ => IsingModel.Spin.sign ℝ (σ (i n))) ∧
      1 - IsingModel.plusGibbsExpectation
            (Ambient.inducedGraph
              (IsingModel.latticeGraph d) (Λ.volume n))
            ⟨J, 0, β⟩ (B n) (fun σ => IsingModel.Spin.sign ℝ (σ (i n))) ≤
        Real.exp (-c * β) := by
  classical
  exact IsingModel.prop_5_4_2_along_exhaustion
    (IsingModel.latticeGraph d) Λ hconn J β c hβ hJ B hB i hexp

/-- **ℤ^d GJ §5.4 Prop 5.4.2 limsup bound** (Λ-induced): the
`Filter.limsup` at `atTop` of the `n ↦ 1 − plusGibbsExpectation`
sequence is bounded above by `exp(-c·β)`. Thin pass-through of
`IsingModel.prop_5_4_2_limsup_le`; proof uses `classical` to supply
the stage-wise `DecidableRel` instance without exposing it in the
type. -/
theorem prop_5_4_2_limsup_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (hconn : ∀ n, (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).Preconnected)
    (J β c : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : ∀ n, Finset (↑(Λ.volume n) : Type _))
    (hB : ∀ n, (B n).Nonempty)
    (i : ∀ n, (↑(Λ.volume n) : Type _))
    (hexp : ∀ n,
      2 * ((2 : ℝ) ^ Fintype.card (↑(Λ.volume n) : Type _)) *
          Real.exp (-2 * β * J) ≤
        Real.exp (-c * β)) :
    Filter.limsup
      (fun n : ℕ =>
        1 - IsingModel.plusGibbsExpectation
              (Ambient.inducedGraph
                (IsingModel.latticeGraph d) (Λ.volume n))
              ⟨J, 0, β⟩ (B n) (fun σ => IsingModel.Spin.sign ℝ (σ (i n))))
      Filter.atTop ≤ Real.exp (-c * β) := by
  classical
  exact IsingModel.prop_5_4_2_limsup_le
    (IsingModel.latticeGraph d) Λ hconn J β c hβ hJ B hB i hexp

/-- **ℤ^d `freeEnergyInfinite_beta_zero`** (any-Exhaustion, ∀ n nonempty):
`freeEnergyInfinite ⟨J, h, 0⟩ = log 2`. -/
theorem freeEnergyInfinite_latticeGraph_beta_zero_forall_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero (IsingModel.latticeGraph d) Λ J h hne

/-- **ℤ^d `freeEnergyInfinite_zero_params`** (any-Exhaustion, ∀ n nonempty):
`freeEnergyInfinite ⟨0, 0, β⟩ = log 2`. -/
theorem freeEnergyInfinite_latticeGraph_zero_params_forall_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params (IsingModel.latticeGraph d) Λ β hne

/-- **ℤ^d `freeEnergyInfinite_eq_bot_at_J_zero`** (any-Exhaustion):
at `J = 0` the ∞-vol free energy equals the `⊥`-graph value. -/
theorem freeEnergyInfinite_latticeGraph_eq_bot_at_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
      (⊥ : SimpleGraph (Fin d → ℤ)) (Λ.volume n)).edgeSet]
    (h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (⊥ : SimpleGraph (Fin d → ℤ)) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_eq_bot_at_J_zero (IsingModel.latticeGraph d) Λ h β

/-- **ℤ^d `freeEnergyAlongExhaustion_eq_bot_at_J_zero`** (any-Exhaustion):
at `J = 0` the per-stage free energy equals the `⊥`-graph value. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_bot_at_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
      (⊥ : SimpleGraph (Fin d → ℤ)) (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (⊥ : SimpleGraph (Fin d → ℤ)) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_eq_bot_at_J_zero
    (IsingModel.latticeGraph d) Λ h β n

/-- **ℤ^d inducedGraph_mono**: `G₁ ≤ G₂` lifts to `inducedGraph G₁ Λ ≤ inducedGraph G₂ Λ`. -/
theorem inducedGraph_mono_latticeGraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ)) :
    Ambient.inducedGraph G₁ Λ ≤ Ambient.inducedGraph G₂ Λ :=
  Ambient.inducedGraph_mono h Λ

/-- **ℤ^d freeEnergy_monotone_h direct** (Λ-induced, ferromagnetic). -/
theorem freeEnergy_monotone_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    MonotoneOn (IsingModel.freeEnergyH
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β) (Set.Ici 0) :=
  IsingModel.freeEnergy_monotone_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ

/-- **ℤ^d freeEnergy_monotone_J direct** (Λ-induced, ferromagnetic). -/
theorem freeEnergy_monotone_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) :
    MonotoneOn (IsingModel.freeEnergyJ
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β) (Set.Ici 0) :=
  IsingModel.freeEnergy_monotone_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hh hβ

/-- **ℤ^d freeEnergy_monotone_beta direct** (Λ-induced, ferromagnetic). -/
theorem freeEnergy_monotone_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, h, β⟩)
      (Set.Ioi 0) :=
  IsingModel.freeEnergy_monotone_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh

/-- **ℤ^d freeEnergy_zero_params at Λ-induced**:
`freeEnergy ⟨0, 0, β⟩ = log 2` for nonempty Λ. -/
theorem freeEnergy_zero_params_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 :=
  IsingModel.freeEnergy_zero_params
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β hne

/-- **ℤ^d freeEnergy_beta_zero at Λ-induced**:
`freeEnergy ⟨J, h, 0⟩ = log 2` for nonempty Λ. -/
theorem freeEnergy_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  IsingModel.freeEnergy_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h hne

/-- **ℤ^d freeEnergy_J_zero at Λ-induced**:
`freeEnergy ⟨0, h, β⟩ = log(2·cosh(β·h))` for nonempty Λ. -/
theorem freeEnergy_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  IsingModel.freeEnergy_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hne

/-- **ℤ^d freeEnergy_neg_h at Λ-induced**. -/
theorem freeEnergy_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ)
      = IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-- **ℤ^d freeEnergy_eq_abs_h at Λ-induced**. -/
theorem freeEnergy_eq_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β⟩ : IsingParams ℝ)
      = IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_eq_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-- **ℤ^d freeEnergy_monotone_abs_h at Λ-induced** (ferromagnetic). -/
theorem freeEnergy_monotone_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_monotone_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ hh

/-- **ℤ^d freeEnergy_eq_bot_at_J_zero at Λ-induced**. -/
theorem freeEnergy_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ)
      = IsingModel.freeEnergy (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d freeEnergy_ge_log_two_cosh at Λ-induced** (ferromagnetic). -/
theorem freeEnergy_ge_log_two_cosh_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    Real.log (2 * Real.cosh (β * h))
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_ge_log_two_cosh
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hJ hh hβ hne

/-- **ℤ^d freeEnergy_bot_h_zero at Λ-induced**:
`freeEnergy (⊥ : SimpleGraph ↑Λ) ⟨J, 0, β⟩ = log 2`. -/
theorem freeEnergy_bot_h_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy (⊥ : SimpleGraph (↑Λ : Type _))
        (⟨J, 0, β⟩ : IsingParams ℝ) = Real.log 2 :=
  IsingModel.freeEnergy_bot_h_zero J β hne

/-- **ℤ^d card_mul_freeEnergy_eq_log_partitionFunction direct** (Λ-induced):
`|ι|·f = log Z` for nonempty Λ. -/
theorem card_mul_freeEnergy_eq_log_partitionFunction_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    (Fintype.card (↑Λ : Type _) : ℝ)
      * IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
      = Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.card_mul_freeEnergy_eq_log_partitionFunction
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hne

/-- **ℤ^d freeEnergy_ge_log_two_of_ferromagnetic at Λ-induced**:
`log 2 ≤ freeEnergy Λ p` for ferromagnetic `p` and nonempty Λ. -/
theorem freeEnergy_ge_log_two_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    Real.log 2
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.freeEnergy_ge_log_two_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf hne

/-- **ℤ^d freeEnergy_nonneg_of_ferromagnetic at Λ-induced**:
`0 ≤ freeEnergy G Λ p` for ferromagnetic `p` and nonempty Λ. -/
theorem freeEnergy_nonneg_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    0 ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.freeEnergy_nonneg_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf hne

/-- **ℤ^d freeEnergy_bot at Λ-induced type**: `freeEnergy ⊥ = log(2 cosh(βh))`. -/
theorem freeEnergy_bot_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy (⊥ : SimpleGraph (↑Λ : Type _)) p
      = Real.log (2 * Real.cosh (p.β * p.h)) :=
  IsingModel.freeEnergy_bot p hne

/-- **ℤ^d `partitionFunction` of `⊥` at Λ**: closed form
`Z_⊥ = (2 cosh(βh))^|Λ|`. -/
theorem partitionFunction_bot_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _)) p
      = (2 * Real.cosh (p.β * p.h)) ^ Fintype.card (↑Λ : Type _) :=
  IsingModel.partitionFunction_bot (ι := (↑Λ : Type _)) p

/-- **ℤ^d `partitionFunction (⊥) ≥ 1`** at Λ-induced subgraph. -/
theorem partitionFunction_bot_latticeGraph_ge_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (1 : ℝ) ≤ IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _)) p :=
  IsingModel.partitionFunction_bot_ge_one (ι := (↑Λ : Type _)) p

/-- **ℤ^d `partitionFunction (⊥) ≥ 2^|Λ|`** at Λ-induced subgraph. -/
theorem partitionFunction_bot_latticeGraph_ge_two_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (2 : ℝ) ^ Fintype.card (↑Λ : Type _)
      ≤ IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _)) p :=
  IsingModel.partitionFunction_bot_ge_two_pow_card (ι := (↑Λ : Type _)) p

/-- **ℤ^d `partitionFunction_eq_bot_at_J_zero`** at Λ-induced: at `J = 0`
the partition function is graph-independent (equals the `⊥`-graph value). -/
theorem partitionFunctionΛ_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d `correlation_eq_bot_at_J_zero`** at Λ-induced: at `J = 0`
the correlation is graph-independent. -/
theorem correlationΛ_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = IsingModel.correlation (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β A

/-- **ℤ^d `correlation_bot_closed`** at Λ-induced:
`⟨σ^A⟩_⊥ = tanh(β·h)^|A|`. -/
theorem correlation_bot_closed_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation (⊥ : SimpleGraph (↑Λ : Type _)) p A
      = Real.tanh (p.β * p.h) ^ A.card :=
  IsingModel.correlation_bot_closed p A

/-- **ℤ^d sum_config_spinProduct_eq_zero at Λ-induced**:
for nonempty `A`, `Σ_σ σ^A = 0`. -/
theorem sum_config_spinProduct_eq_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    ∑ σ : IsingModel.Config (↑Λ : Type _), IsingModel.spinProduct A σ = 0 :=
  IsingModel.sum_config_spinProduct_eq_zero A hA

/-- **ℤ^d sum_config_spinProduct_empty at Λ-induced**:
`Σ_σ σ^∅ = |Config ↑Λ|`. -/
theorem sum_config_spinProduct_empty_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    ∑ σ : IsingModel.Config (↑Λ : Type _), IsingModel.spinProduct ∅ σ
      = (Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ) :=
  IsingModel.sum_config_spinProduct_empty

/-- **ℤ^d spinProduct_mul at Λ-induced**:
`σ^A · σ^C = σ^{A Δ C}`. -/
theorem spinProduct_mul_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A C : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct A σ * IsingModel.spinProduct C σ
      = IsingModel.spinProduct (symmDiff A C) σ :=
  IsingModel.spinProduct_mul A C σ

/-- **ℤ^d edgeSpin_sq at Λ-induced**: `edgeSpin σ e ^ 2 = 1`. -/
theorem edgeSpin_sq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (σ : IsingModel.Config (↑Λ : Type _)) (e : Sym2 (↑Λ : Type _)) :
    IsingModel.edgeSpin (K := ℝ) σ e ^ 2 = 1 :=
  IsingModel.edgeSpin_sq σ e

/-- **ℤ^d one_sub_spinProduct_nonneg at Λ-induced**: `0 ≤ 1 - σ^B`. -/
theorem one_sub_spinProduct_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (B : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    0 ≤ 1 - IsingModel.spinProduct B σ :=
  IsingModel.one_sub_spinProduct_nonneg B σ

/-- **ℤ^d abs_spinProduct_eq_one at Λ-induced**: `|σ^A| = 1`. -/
theorem abs_spinProduct_eq_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    |IsingModel.spinProduct A σ| = 1 :=
  IsingModel.abs_spinProduct_eq_one A σ

/-- **ℤ^d abs_spinProduct_le_one at Λ-induced**: `|σ^A| ≤ 1`. -/
theorem abs_spinProduct_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    |IsingModel.spinProduct A σ| ≤ 1 :=
  IsingModel.abs_spinProduct_le_one A σ

/-- **ℤ^d Walsh orthogonality at Λ-induced**. -/
theorem walsh_orthogonality_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (S T : Finset (↑Λ : Type _)) (hST : S ≠ T) :
    ∑ σ : IsingModel.Config (↑Λ : Type _),
      IsingModel.spinProduct S σ * IsingModel.spinProduct T σ = 0 :=
  IsingModel.walsh_orthogonality S T hST

/-- **ℤ^d Walsh completeness at Λ-induced**:
`Σ_S σ^S(σ) σ^S(τ) = card · [σ = τ]`. -/
theorem walsh_completeness_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (σ τ : IsingModel.Config (↑Λ : Type _)) :
    ∑ S : Finset (↑Λ : Type _),
        IsingModel.spinProduct S σ * IsingModel.spinProduct S τ
      = if σ = τ then (Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ) else 0 :=
  IsingModel.walsh_completeness σ τ

/-- **ℤ^d Walsh Fourier inversion at Λ-induced**:
`f(σ) = Σ_S ĉ_S σ^S` where `ĉ_S = card⁻¹ Σ_τ σ^S(τ) f(τ)`. -/
theorem walsh_fourier_inversion_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (f : IsingModel.Config (↑Λ : Type _) → ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    f σ = ∑ S : Finset (↑Λ : Type _),
      ((Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ)⁻¹
        * ∑ τ : IsingModel.Config (↑Λ : Type _),
            IsingModel.spinProduct S τ * f τ)
      * IsingModel.spinProduct S σ :=
  IsingModel.walsh_fourier_inversion f σ

/-- **ℤ^d Walsh normalization at Λ-induced**. -/
theorem walsh_normalization_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (S : Finset (↑Λ : Type _)) :
    ∑ σ : IsingModel.Config (↑Λ : Type _),
        IsingModel.spinProduct S σ * IsingModel.spinProduct S σ
      = Fintype.card (IsingModel.Config (↑Λ : Type _)) :=
  IsingModel.walsh_normalization S

/-- **ℤ^d `card_config_eq_two_pow` at Λ**:
`|Config ↑Λ| = 2^|Λ|`. -/
theorem card_config_eq_two_pow_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Fintype.card (IsingModel.Config (↑Λ : Type _))
      = 2 ^ Fintype.card (↑Λ : Type _) :=
  IsingModel.card_config_eq_two_pow

/-- **ℤ^d edgeSpin_flip at Λ-induced**:
`edgeSpin(σ.flip, e) = edgeSpin(σ, e)`. -/
theorem edgeSpin_flip_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (σ : IsingModel.Config (↑Λ : Type _)) (e : Sym2 (↑Λ : Type _)) :
    IsingModel.edgeSpin (K := ℝ) σ.flip e = IsingModel.edgeSpin σ e :=
  IsingModel.edgeSpin_flip σ e

/-- **ℤ^d interactionEnergy_flip at Λ-induced**:
`interactionEnergy_Λ(J, σ.flip) = interactionEnergy_Λ(J, σ)`. -/
theorem interactionEnergy_flip_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.interactionEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J σ.flip
      = IsingModel.interactionEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J σ :=
  IsingModel.interactionEnergy_flip
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J σ

/-- **ℤ^d hamiltonian_flip_eq at Λ-induced**: at `h = 0` the Hamiltonian
is invariant under spin flip. -/
theorem hamiltonianΛ_flip_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hp : p.h = 0)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ.flip
      = IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ :=
  IsingModel.hamiltonian_flip_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hp σ

/-- **ℤ^d hamiltonian_neg_h at Λ-induced**:
`H_Λ(σ; -h) = H_Λ(σ.flip; h)`. -/
theorem hamiltonianΛ_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) σ
      = IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) σ.flip :=
  IsingModel.hamiltonian_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β σ

/-- **ℤ^d hamiltonian_bot at Λ**: `H_⊥(σ) = -h · Σ sign σ`. -/
theorem hamiltonian_bot_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian (⊥ : SimpleGraph (↑Λ : Type _)) p σ
      = -p.h * ∑ i : (↑Λ : Type _), IsingModel.Spin.sign ℝ (σ i) :=
  IsingModel.hamiltonian_bot p σ

/-- **ℤ^d partitionFunction_monotone_h direct** at Λ-induced (ferromagnetic). -/
theorem partitionFunction_monotone_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (h₁ h₂ : ℝ) (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ h₁ h₂ hh₁ hh

/-- **ℤ^d partitionFunction_monotone_J direct** at Λ-induced (ferromagnetic). -/
theorem partitionFunction_monotone_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β)
    (J₁ J₂ : ℝ) (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J₁, h, β⟩ : IsingParams ℝ)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J₂, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hh hβ J₁ J₂ hJ₁ hJ

/-- **ℤ^d partitionFunction_monotone_beta direct** at Λ-induced (ferromagnetic). -/
theorem partitionFunction_monotone_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h)
    (β₁ β₂ : ℝ) (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β₁⟩ : IsingParams ℝ)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β₂⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h hJ hh β₁ β₂ hβ₁ hβ

/-- **ℤ^d partitionFunction_J_zero direct** at Λ-induced:
`Z_Λ at ⟨0, h, β⟩ = (2·cosh(β·h))^|Λ|`. -/
theorem partitionFunction_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ)
      = (2 * Real.cosh (β * h)) ^ Fintype.card (↑Λ : Type _) :=
  IsingModel.partitionFunction_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d partitionFunction_beta_zero direct** at Λ-induced:
`Z_Λ at ⟨J, h, 0⟩ = |Config Λ| = 2^|Λ|`. -/
theorem partitionFunction_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = (Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ) :=
  IsingModel.partitionFunction_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h

/-- **ℤ^d partitionFunction_zero_params direct** at Λ-induced:
`Z_Λ at ⟨0, 0, β⟩ = |Config Λ|`. -/
theorem partitionFunction_zero_params_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = (Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ) :=
  IsingModel.partitionFunction_zero_params
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β

/-- **ℤ^d partitionFunction_neg_h direct** at Λ-induced:
`Z_Λ at ⟨J, -h, β⟩ = Z_Λ at ⟨J, h, β⟩`. -/
theorem partitionFunction_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ)
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-- **ℤ^d correlation_neg_h direct** at Λ-induced: Z₂ odd-symmetry
under `h → -h`. `correlation ⟨J,-h,β⟩ A = (-1)^|A| · correlation ⟨J,h,β⟩ A`.
Concrete wrapper for `IsingModel.correlation_neg_h` (#754). -/
theorem correlation_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) A
      = (-1) ^ A.card * IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β A

/-- **ℤ^d magnetization_neg_h direct** at Λ-induced.
Concrete wrapper for `IsingModel.magnetization_neg_h` (#755). -/
theorem magnetization_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i
      = -IsingModel.magnetization
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  IsingModel.magnetization_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β i

/-- **ℤ^d truncated2_neg_h direct** at Λ-induced (i ≠ j).
Concrete wrapper for `IsingModel.truncated2_neg_h` (#756). -/
theorem truncated2_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    {i j : (↑Λ : Type _)} (hij : i ≠ j) :
    IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i j
      = IsingModel.truncated2
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j :=
  IsingModel.truncated2_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β hij

/-- **ℤ^d truncated3_neg_h direct** at Λ-induced (pairwise distinct):
antisymmetric, `U_3(-h) = -U_3(h)`. Concrete wrapper for
`IsingModel.truncated3_neg_h` (#758). -/
theorem truncated3_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    {i j k : (↑Λ : Type _)} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsingModel.truncated3
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i j k
      = -IsingModel.truncated3
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j k :=
  IsingModel.truncated3_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β hij hjk hik

/-- **ℤ^d truncated4_neg_h direct** at Λ-induced (pairwise distinct):
invariant under `h → -h`. Concrete wrapper for
`IsingModel.truncated4_neg_h` (#757). -/
theorem truncated4_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    {i j k l : (↑Λ : Type _)}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    IsingModel.truncated4
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i j k l
      = IsingModel.truncated4
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j k l :=
  IsingModel.truncated4_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β hij hik hil hjk hjl hkl

/-- **ℤ^d correlation_eq_abs_h_of_even_card direct** at Λ-induced:
for `|A|` even, `correlation ⟨J, h, β⟩ A = correlation ⟨J, |h|, β⟩ A`.
Concrete wrapper for `IsingModel.correlation_eq_abs_h_of_even_card`
(#760). -/
theorem correlation_eq_abs_h_of_even_card_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    (A : Finset (↑Λ : Type _)) (heven : Even A.card) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β⟩ : IsingParams ℝ) A
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, |h|, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_eq_abs_h_of_even_card
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β A heven

/-- **ℤ^d correlationInfinite invariance under `h → -h`** (even `|A|`):
`correlationInfinite ⟨J,-h,β⟩ A = correlationInfinite ⟨J,h,β⟩ A`.
Concrete wrapper for `correlationInfinite_neg_h_of_even_card` (#765). -/
theorem correlationInfinite_neg_h_of_even_card_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (heven : Even A.card) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) A
      = correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  correlationInfinite_neg_h_of_even_card (IsingModel.latticeGraph d) Λ J h β A heven

/-- **ℤ^d correlationInfinite equals value at `|h|`** (even `|A|`):
concrete wrapper for `correlationInfinite_eq_abs_h_of_even_card` (#765). -/
theorem correlationInfinite_eq_abs_h_of_even_card_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (heven : Even A.card) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) A
      = correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) A :=
  correlationInfinite_eq_abs_h_of_even_card (IsingModel.latticeGraph d) Λ J h β A heven

/-- **ℤ^d partitionFunction_eq_abs_h direct** at Λ-induced. -/
theorem partitionFunction_eq_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β⟩ : IsingParams ℝ)
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_eq_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-- **ℤ^d partitionFunction_monotone_abs_h direct** at Λ-induced
(ferromagnetic). -/
theorem partitionFunction_monotone_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ hh

/-- **ℤ^d partitionFunction_ge_one_of_ferromagnetic direct** (Λ-induced). -/
theorem partitionFunction_ge_one_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (1 : ℝ) ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_ge_one_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d log_partitionFunction_nonneg_of_ferromagnetic direct** (Λ-induced). -/
theorem log_partitionFunction_nonneg_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.log_partitionFunction_nonneg_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d partitionFunction_ge_two_pow_card_of_ferromagnetic direct** (Λ-induced). -/
theorem partitionFunction_ge_two_pow_card_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Fintype.card (↑Λ : Type _)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_ge_two_pow_card_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic direct**
(Λ-induced). -/
theorem partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 * Real.cosh (p.β * p.h)) ^ Fintype.card (↑Λ : Type _)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic direct**
(Λ-induced). -/
theorem log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Fintype.card (↑Λ : Type _) : ℝ) * Real.log 2
      ≤ Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic direct**
(Λ-induced). -/
theorem log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Fintype.card (↑Λ : Type _) : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d partitionFunction_pos direct** at Λ-induced: `0 < Z_Λ`. -/
theorem partitionFunction_pos_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    0 < IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d partitionFunction_ne_zero direct** at Λ-induced. -/
theorem partitionFunction_ne_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p ≠ 0 :=
  IsingModel.partitionFunction_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d cov_hnc_boltzmann_nonneg direct** (Λ-induced, ferromagnetic):
covariance bound for HNC `f` with Boltzmann weight. -/
theorem cov_hnc_boltzmann_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hferm : Ferromagnetic p)
    (f : IsingModel.Config (↑Λ : Type _) → ℝ)
    (hf : IsingModel.HasNonnegCorrelations f) (B : Finset (↑Λ : Type _)) :
    0 ≤ (∑ σ, IsingModel.spinProduct B σ * f σ
            * IsingModel.boltzmannWeight
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) *
        (∑ σ, IsingModel.boltzmannWeight
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) -
      (∑ σ, IsingModel.spinProduct B σ *
          IsingModel.boltzmannWeight
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) *
        (∑ σ, f σ * IsingModel.boltzmannWeight
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) :=
  IsingModel.cov_hnc_boltzmann_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hferm f hf B

/-- **ℤ^d boltzmannWeight_subgraph_factor direct** (Λ-induced):
`w_{G₂} = (∏_e exp(...)) · w_{G₁}` for `G₁ ≤ G₂` on `↑Λ`. -/
theorem boltzmannWeight_subgraph_factor_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {G₁ G₂ : SimpleGraph (↑Λ : Type _)}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.boltzmannWeight G₂ p σ
      = (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
          Real.exp (p.β * p.J * IsingModel.edgeSpin (K := ℝ) σ e))
        * IsingModel.boltzmannWeight G₁ p σ :=
  IsingModel.boltzmannWeight_subgraph_factor h₁₂ p σ

/-- **ℤ^d boltzmannWeight positivity** at Λ-induced subgraph:
`0 < exp(-β H_Λ(σ))`. -/
theorem boltzmannWeightΛ_latticeGraph_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    0 < IsingModel.boltzmannWeight
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ :=
  IsingModel.boltzmannWeight_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ

/-- **ℤ^d partitionFunctionΛ ≠ 0** at Λ-induced subgraph. -/
theorem partitionFunctionΛ_latticeGraph_ne_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p ≠ 0 :=
  IsingModel.partitionFunction_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d hamiltonianΛ at `J = 0`** (Λ-induced subgraph): the Hamiltonian
reduces to `-h · Σ sign σ`. -/
theorem hamiltonianΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = -h * ∑ i : (↑Λ : Type _), IsingModel.Spin.sign ℝ (σ i) :=
  IsingModel.hamiltonian_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

/-- **ℤ^d hamiltonianΛ at zero parameters** (Λ-induced subgraph):
`H_Λ ⟨0, 0, β⟩ σ = 0`. -/
theorem hamiltonianΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ) σ = 0 :=
  IsingModel.hamiltonian_zero_params
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β σ

/-- **ℤ^d hamiltonianΛ equals `⊥`-hamiltonian at `J = 0`** (Λ-induced subgraph):
at `J = 0` the Hamiltonian is graph-independent. -/
theorem hamiltonianΛ_latticeGraph_eq_bot_at_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = IsingModel.hamiltonian (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) σ :=
  IsingModel.hamiltonian_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

/-- **ℤ^d `hamiltonian` absolute value bound** at Λ-induced subgraph:
`|H_Λ(σ)| ≤ |J|·|E| + |h|·|Λ|`. -/
theorem hamiltonianΛ_latticeGraph_abs_le
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    |IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ|
      ≤ |p.J|
          * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        + |p.h| * Fintype.card (↑Λ : Type _) :=
  IsingModel.hamiltonian_abs_le
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ

/-- **ℤ^d `freeEnergyΛ` upper bound** at nonempty Λ-induced subgraph:
`f_Λ ≤ log 2 + |β|·(|J|·|E| + |h|·|Λ|) / |Λ|`. -/
theorem freeEnergyΛ_latticeGraph_upper_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      ≤ Real.log 2 + |p.β| * (|p.J|
          * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          + |p.h| * Fintype.card (↑Λ : Type _))
        / Fintype.card (↑Λ : Type _) :=
  IsingModel.freeEnergy_upper_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hne

/-- **ℤ^d `partitionFunctionΛ` upper bound** at Λ-induced subgraph:
`Z ≤ |Config| · exp(|β|·(|J|·|E| + |h|·|Λ|))`. -/
theorem partitionFunctionΛ_latticeGraph_upper
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p
      ≤ Fintype.card (IsingModel.Config (↑Λ : Type _))
        * Real.exp (|p.β| * (|p.J|
            * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          + |p.h| * Fintype.card (↑Λ : Type _))) :=
  IsingModel.partitionFunction_upper
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `partitionFunctionΛ` lower bound** at Λ-induced subgraph:
`exp(-|β|·(|J|·|E| + |h|·|Λ|)) ≤ Z`. -/
theorem partitionFunctionΛ_latticeGraph_lower
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    Real.exp (-(|p.β| * (|p.J|
          * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        + |p.h| * Fintype.card (↑Λ : Type _))))
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  IsingModel.partitionFunction_lower
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d gibbsExpectation as ratio** at Λ-induced:
`⟨F⟩ = Z⁻¹ · numerator(F)`. -/
theorem gibbsExpectation_eq_div_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (F : IsingModel.Config (↑Λ : Type _) → ℝ) :
    IsingModel.gibbsExpectation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F
      = (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p)⁻¹
          * IsingModel.numerator
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F :=
  IsingModel.gibbsExpectation_eq_div
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F

/-- **ℤ^d gibbsExpectation nonneg from numerator nonneg** at Λ-induced. -/
theorem gibbsExpectation_nonneg_of_numerator_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (F : IsingModel.Config (↑Λ : Type _) → ℝ)
    (hnum : 0 ≤ IsingModel.numerator
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F) :
    0 ≤ IsingModel.gibbsExpectation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F :=
  IsingModel.gibbsExpectation_nonneg_of_numerator_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F hnum

/-- **ℤ^d correlation_monotone_J direct** (Λ-induced, ferromagnetic). -/
theorem correlation_monotone_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (B : Finset (↑Λ : Type _)) :
    MonotoneOn (IsingModel.correlationJ
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B) (Set.Ici 0) :=
  IsingModel.correlation_monotone_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ B

/-- **ℤ^d correlation_monotone_h direct** (Λ-induced, ferromagnetic). -/
theorem correlation_monotone_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (B : Finset (↑Λ : Type _)) :
    MonotoneOn (IsingModel.correlationH
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β B) (Set.Ici 0) :=
  IsingModel.correlation_monotone_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ B

/-- **ℤ^d correlation_monotone_beta direct** (Λ-induced, ferromagnetic). -/
theorem correlation_monotone_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun β : ℝ => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  IsingModel.correlation_monotone_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh A

/-- **ℤ^d correlationJ_nonneg direct** (Λ-induced, ferromagnetic): for
`h ≥ 0`, `β > 0`, and `J ≥ 0`, `0 ≤ correlationJ (inducedGraph … Λ) h β B J`.
Thin pass-through of `IsingModel.correlationJ_nonneg`; GJ §4.2 Prop 4.2.1
slice at `correlationJ` (GKS-I). -/
theorem correlationJ_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (B : Finset (↑Λ : Type _)) (J : ℝ) (hJ : 0 ≤ J) :
    0 ≤ IsingModel.correlationJ
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J :=
  IsingModel.correlationJ_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ B J hJ

/-- **ℤ^d correlationJ_le_one direct** (Λ-induced): for every `J`,
`correlationJ (inducedGraph … Λ) h β B J ≤ 1`. Thin pass-through of
`IsingModel.correlationJ_le_one` (unconditional upper bound). -/
theorem correlationJ_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (B : Finset (↑Λ : Type _)) (J : ℝ) :
    IsingModel.correlationJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J ≤ 1 :=
  IsingModel.correlationJ_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J

/-- **ℤ^d correlation_convergent direct** (Λ-induced, ferromagnetic):
for `h ≥ 0`, `β > 0`, the sequence `n ↦ ⟨σ^B⟩_{(J=n, h, β)}` converges as
`n → ∞`. Thin pass-through of `IsingModel.correlation_convergent`;
GJ §4.2 Thm 4.2.3 (J → ∞ along ℕ). -/
theorem correlation_convergent_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (B : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlationJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B n)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ B

/-- **ℤ^d correlation_convergent_h direct** (Λ-induced, ferromagnetic):
for `J ≥ 0`, `β > 0`, the sequence `n ↦ ⟨σ^A⟩_{(J, n, β)}` converges as
`n → ∞`. Thin pass-through of `IsingModel.correlation_convergent_h`. -/
theorem correlation_convergent_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, (n : ℝ), β⟩ A)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ A

/-- **ℤ^d correlation_convergent_beta direct** (Λ-induced, ferromagnetic):
for `J ≥ 0`, `h ≥ 0`, the sequence `n ↦ ⟨σ^A⟩_{(J, h, n+1)}` converges as
`n → ∞`. Thin pass-through of `IsingModel.correlation_convergent_beta`. -/
theorem correlation_convergent_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (A : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, h, (n + 1 : ℝ)⟩ A)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh A

/-! ### Hamiltonian / Z bound / `J = 0` closed-form wrappers

Direct ℤ^d forwarders for a mixed batch from
`IsingModel/Conditioning.lean` and `IsingModel/GibbsMeasure.lean`:
Boltzmann positivity (`boltzmannWeight_pos`), the GJ §10.3
finite-volume energy / Z / free-energy bounds
(`hamiltonian_abs_le`, `partitionFunction_{upper,lower}`,
`freeEnergy_upper_bound`, Cor 10.3.2), and the `J = 0` Hamiltonian
closed form (`hamiltonian_J_zero`). The `boltzmannWeight_pos` and
`hamiltonian_J_zero` items are basic infrastructure, not §10.3 proper. -/

/-- **ℤ^d boltzmannWeight_pos direct** (Λ-induced): `0 < w(σ)` pointwise.
Thin pass-through of `IsingModel.boltzmannWeight_pos`. -/
theorem boltzmannWeight_pos_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    0 < IsingModel.boltzmannWeight
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ :=
  IsingModel.boltzmannWeight_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ

/-- **ℤ^d hamiltonian_abs_le direct** (Λ-induced):
`|H(σ)| ≤ |J| · |E(latticeGraph d)|_Λ + |h| · |Λ|`. Thin pass-through of
`IsingModel.hamiltonian_abs_le`. Finite-volume energy bound (GJ §10.3). -/
theorem hamiltonian_abs_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    |IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ|
      ≤ |p.J| *
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        + |p.h| * Fintype.card (↑Λ : Type _) :=
  IsingModel.hamiltonian_abs_le
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ

/-- **ℤ^d partitionFunction_upper direct** (Λ-induced):
`Z ≤ 2^|Λ| · exp(|β|·(|J|·|E|_Λ + |h|·|Λ|))` (GJ §10.3, Cor 10.3.2).
Thin pass-through of `IsingModel.partitionFunction_upper`. -/
theorem partitionFunction_upper_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
      ≤ Fintype.card (IsingModel.Config (↑Λ : Type _)) *
          Real.exp (|p.β| *
            (|p.J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + |p.h| * Fintype.card (↑Λ : Type _))) :=
  IsingModel.partitionFunction_upper
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d partitionFunction_lower direct** (Λ-induced):
`exp(-|β|·(|J|·|E|_Λ + |h|·|Λ|)) ≤ Z`. Thin pass-through of
`IsingModel.partitionFunction_lower`. -/
theorem partitionFunction_lower_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    Real.exp (-(|p.β| *
        (|p.J| *
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          + |p.h| * Fintype.card (↑Λ : Type _))))
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_lower
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d freeEnergy_upper_bound direct** (Λ-induced, nonempty `Λ`):
`f ≤ log 2 + |β|·(|J|·|E|_Λ + |h|·|Λ|) / |Λ|` (GJ §10.3). Thin
pass-through of `IsingModel.freeEnergy_upper_bound`. -/
theorem freeEnergy_upper_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
      ≤ Real.log 2 +
          |p.β| *
            (|p.J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + |p.h| * Fintype.card (↑Λ : Type _))
          / Fintype.card (↑Λ : Type _) :=
  IsingModel.freeEnergy_upper_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hne

/-- **ℤ^d hamiltonian_J_zero direct** (Λ-induced): at `J = 0`,
`H = -h · ∑ sign(σ_i)`. Thin pass-through of
`IsingModel.hamiltonian_J_zero`. -/
theorem hamiltonian_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = -h * ∑ i : (↑Λ : Type _), IsingModel.Spin.sign ℝ (σ i) :=
  IsingModel.hamiltonian_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

/-! ### Hamiltonian spin-flip + J=0 graph-independence + spinProduct helpers
(base `IsingModel.*` layer)

Direct ℤ^d forwarders for a coherent mixed batch from
`IsingModel/GibbsMeasure.lean` and `IsingModel/Hamiltonian.lean`:
spin-flip / h-reflection identities
(`hamiltonian_flip_eq`, `hamiltonian_neg_h`),
the `J = 0` graph-independence chain
(`hamiltonian_zero_params`, `hamiltonian_eq_bot_at_J_zero`,
`partitionFunction_eq_bot_at_J_zero`, `correlation_eq_bot_at_J_zero`),
and three basic `spinProduct` helpers
(`spinProduct_singleton`, `spinProduct_union`, `spinProduct_sq`).

These operate on the base `IsingModel.hamiltonian` /
`IsingModel.partitionFunction` / `IsingModel.correlation` /
`IsingModel.spinProduct` API at the Λ-induced subgraph of
`latticeGraph d` (`ι := ↑Λ`, `G := Ambient.inducedGraph (latticeGraph d) Λ`).
They parallel — but do not duplicate — the existing `Ambient.*Λ`-layer
wrappers (`hamiltonianΛ_*_latticeGraph` at line 1287+,
`partitionFunctionΛ_eq_bot_at_J_zero_latticeGraph` at line 1134, etc.)
which target `Ambient.hamiltonianΛ` / `Ambient.partitionFunctionΛ` /
`Ambient.correlationΛ`, a different API surface. The `spinProduct_*`
wrappers are genuinely new; the `Ambient.*Λ`-layer has no spinProduct
parallel. -/

/-- **ℤ^d hamiltonian_flip_eq direct** (Λ-induced, `h = 0`): at `h = 0`
the Hamiltonian is invariant under global spin flip. Thin pass-through
of `IsingModel.hamiltonian_flip_eq`. -/
theorem hamiltonian_flip_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hp : p.h = 0)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ.flip
      = IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ :=
  IsingModel.hamiltonian_flip_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hp σ

/-- **ℤ^d hamiltonian_neg_h direct** (Λ-induced): the `h → -h` reflection
corresponds to the global spin flip:
`H(σ; J, -h, β) = H(σ.flip; J, h, β)`. Thin pass-through of
`IsingModel.hamiltonian_neg_h`. -/
theorem hamiltonian_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) σ
      = IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) σ.flip :=
  IsingModel.hamiltonian_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β σ

/-- **ℤ^d hamiltonian_zero_params direct** (Λ-induced): at `J = h = 0`,
`H = 0`. Thin pass-through of `IsingModel.hamiltonian_zero_params`. -/
theorem hamiltonian_zero_params_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ) σ = 0 :=
  IsingModel.hamiltonian_zero_params
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β σ

/-- **ℤ^d hamiltonian_eq_bot_at_J_zero direct** (Λ-induced):
at `J = 0` the Hamiltonian coincides with the one on the edgeless graph
`⊥`. Thin pass-through of `IsingModel.hamiltonian_eq_bot_at_J_zero`. -/
theorem hamiltonian_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = IsingModel.hamiltonian
          (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) σ :=
  IsingModel.hamiltonian_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

/-- **ℤ^d partitionFunction_eq_bot_at_J_zero direct** (Λ-induced):
`Z_G ⟨0, h, β⟩ = Z_⊥ ⟨0, h, β⟩`. Thin pass-through of
`IsingModel.partitionFunction_eq_bot_at_J_zero`. -/
theorem partitionFunction_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ)
      = IsingModel.partitionFunction
          (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d correlation_eq_bot_at_J_zero direct** (Λ-induced):
`⟨σ^A⟩_G = ⟨σ^A⟩_⊥` at `J = 0`. Thin pass-through of
`IsingModel.correlation_eq_bot_at_J_zero`. -/
theorem correlation_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = IsingModel.correlation
          (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β A

/-- **ℤ^d spinProduct_singleton direct** (Λ-induced):
`spinProduct {i} σ = sign(σ_i)`. Thin pass-through of
`IsingModel.spinProduct_singleton`. -/
theorem spinProduct_singleton_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (i : (↑Λ : Type _))
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct ({i} : Finset (↑Λ : Type _)) σ
      = ((σ i).toSign : ℝ) :=
  IsingModel.spinProduct_singleton i σ

/-- **ℤ^d spinProduct_union direct** (Λ-induced): for disjoint
`A, B : Finset (↑Λ)`, `spinProduct (A ∪ B) = spinProduct A · spinProduct B`.
Thin pass-through of `IsingModel.spinProduct_union`. -/
theorem spinProduct_union_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {A B : Finset (↑Λ : Type _)} (hAB : Disjoint A B)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct (A ∪ B) σ
      = IsingModel.spinProduct A σ * IsingModel.spinProduct B σ :=
  IsingModel.spinProduct_union hAB σ

/-- **ℤ^d spinProduct_sq direct** (Λ-induced):
`(spinProduct A σ)^2 = 1` since each factor is `±1`. Thin pass-through
of `IsingModel.spinProduct_sq`. -/
theorem spinProduct_sq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (A : Finset (↑Λ : Type _))
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct A σ ^ 2 = 1 :=
  IsingModel.spinProduct_sq A σ

/-- **ℤ^d Cor 4.3.5 at `h = 0`, Λ-induced subgraph** (GJ §4.3 Cor 4.3.5):
inductive `(n+2)`-point bound at finite volume. -/
theorem cor_4_3_5_h0_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (S : Finset (↑Λ)) (j k : ↑Λ) (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    IsingModel.correlation (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) (insert j (insert k S))
      ≤ IsingModel.correlation
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (⟨J, 0, β⟩ : IsingParams ℝ) S
          * IsingModel.correlation
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) {j, k}
        + ∑ T ∈ S.powerset,
            IsingModel.correlation
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (⟨J, 0, β⟩ : IsingParams ℝ) (insert j T)
              * IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) (insert k (S \ T)) :=
  IsingModel.cor_4_3_5_h0
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hf S j k hj hk hjk

/-- **ℤ^d correlation_odd_vanish** at Λ-induced: at `h = 0`, the
correlation `⟨σ^A⟩ = 0` for any odd-cardinality `A`. -/
theorem correlation_odd_vanish_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset (↑Λ : Type _)) (hodd : Odd A.card) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) A = 0 :=
  IsingModel.correlation_odd_vanish
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β A hodd

/-- **ℤ^d truncated2 J=0 vanish for i ≠ j** at Λ-induced. -/
theorem truncated2_J_zero_of_ne_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    {i j : ↑Λ} (hij : i ≠ j) :
    IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) i j = 0 :=
  IsingModel.truncated2_J_zero_of_ne
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hij

/-- **ℤ^d truncated2 β=0 vanish** at Λ-induced. -/
theorem truncated2_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i j : ↑Λ) :
    IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) i j = 0 :=
  IsingModel.truncated2_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h i j

/-- **ℤ^d truncated3 J=0 vanish for pairwise distinct** at Λ-induced. -/
theorem truncated3_J_zero_of_pairwise_distinct_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    {i j k : ↑Λ} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsingModel.truncated3
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) i j k = 0 :=
  IsingModel.truncated3_J_zero_of_pairwise_distinct
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hij hjk hik

/-- **ℤ^d truncated3 β=0 vanish** at Λ-induced. -/
theorem truncated3_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i j k : ↑Λ) :
    IsingModel.truncated3
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) i j k = 0 :=
  IsingModel.truncated3_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h i j k

/-- **ℤ^d truncated2 nonneg** at Λ-induced (ferromagnetic). -/
theorem truncated2_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j : ↑Λ) :
    0 ≤ IsingModel.truncated2
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i j :=
  IsingModel.truncated2_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf i j

/-- **ℤ^d GHS inequality at Λ-induced subgraph** (Glimm–Jaffe §4.3 Cor 4.3.4):
`U_3(i, j, k) ≤ 0` for ferromagnetic `p` and distinct sites. -/
theorem ghs_inequality_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j k : ↑Λ) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsingModel.truncated3
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i j k ≤ 0 :=
  IsingModel.ghs_inequality
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf i j k hij hjk hik

/-- **ℤ^d truncated4 β=0 vanish** at Λ-induced. -/
theorem truncated4_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i j k l : ↑Λ) :
    IsingModel.truncated4
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) i j k l = 0 :=
  IsingModel.truncated4_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h i j k l

/-- **ℤ^d truncated4 J=0 closed form** at Λ-induced (pairwise distinct):
`truncated4 = -2 · tanh(β·h)^4`. -/
theorem truncated4_J_zero_of_pairwise_distinct_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    {i j k l : ↑Λ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    IsingModel.truncated4
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) i j k l
      = -2 * Real.tanh (β * h) ^ 4 :=
  IsingModel.truncated4_J_zero_of_pairwise_distinct
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β
    hij hik hil hjk hjl hkl

/-- **ℤ^d Cor 4.3.3 at Λ-induced subgraph** (Glimm–Jaffe §4.3):
`U_4(i, j, k, l) ≤ 0` at `h = 0` for ferromagnetic and distinct sites. -/
theorem cor_4_3_3_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (i j k l : ↑Λ) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    IsingModel.truncated4 (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j k l ≤ 0 :=
  IsingModel.cor_4_3_3 (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
    J β hf i j k l hij hik hil hjk hjl hkl

/-- **ℤ^d magnetizationΛ J → ∞ convergence**: specialisation of
`correlation_convergent` at `B = {i}`. -/
theorem magnetizationΛ_latticeGraph_convergent_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlationJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β {i} n)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ {i}

/-- **ℤ^d magnetizationΛ h → ∞ convergence**: specialisation of
`correlation_convergent_h` at `A = {i}`. -/
theorem magnetizationΛ_latticeGraph_convergent_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, (n : ℝ), β⟩ : IsingParams ℝ) {i})
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ {i}

/-- **ℤ^d magnetizationΛ β → ∞ convergence**: specialisation of
`correlation_convergent_beta` at `A = {i}`. -/
theorem magnetizationΛ_latticeGraph_convergent_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, (n + 1 : ℝ)⟩ : IsingParams ℝ) {i})
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh {i}

/-- **ℤ^d correlationJΛ nonneg** at Λ-induced (ferromagnetic):
`0 ≤ correlationJ Λ h β B J` for `h, J ≥ 0, β > 0`. -/
theorem correlationJΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (B : Finset (↑Λ : Type _))
    (J : ℝ) (hJ : 0 ≤ J) :
    0 ≤ IsingModel.correlationJ
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J :=
  IsingModel.correlationJ_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ B J hJ

/-- **ℤ^d correlationJΛ ≤ 1** at Λ-induced. -/
theorem correlationJΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (h β : ℝ) (B : Finset (↑Λ : Type _)) (J : ℝ) :
    IsingModel.correlationJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J ≤ 1 :=
  IsingModel.correlationJ_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J

/-- **ℤ^d correlationΛ J → ∞ convergence**: for `0 ≤ h`, `0 < β`. -/
theorem correlationΛ_latticeGraph_convergent
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (B : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlationJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B n)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ B

/-- **ℤ^d correlationΛ β → ∞ convergence**: for `0 ≤ J`, `0 ≤ h`, the sequence
`n ↦ ⟨σ^A⟩_Λ(J, h, n+1)` converges. -/
theorem correlationΛ_latticeGraph_convergent_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (A : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, (n + 1 : ℝ)⟩ : IsingParams ℝ) A)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh A

/-- **ℤ^d correlationΛ h → ∞ convergence**: for `0 ≤ J`, `0 < β`, the sequence
`n ↦ ⟨σ^A⟩_Λ(J, n, β)` converges. -/
theorem correlationΛ_latticeGraph_convergent_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, (n : ℝ), β⟩ : IsingParams ℝ) A)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ A

/-- **ℤ^d per-Λ h-monotonicity of `correlationΛ`**. -/
theorem correlationΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) {J : ℝ} (hJ : 0 ≤ J)
    {β : ℝ} (hβ : 0 < β) (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun h : ℝ => correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationΛ_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d per-Λ β-monotonicity of `correlationΛ`**. -/
theorem correlationΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) {J : ℝ} (hJ : 0 ≤ J)
    {h : ℝ} (hh : 0 ≤ h) (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun β : ℝ => correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  correlationΛ_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh A

/-- **ℤ^d per-Λ J-monotonicity of `correlationΛ`**. -/
theorem correlationΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) {h : ℝ} (hh : 0 ≤ h)
    {β : ℝ} (hβ : 0 < β) (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun J : ℝ => correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationΛ_monotone_J (IsingModel.latticeGraph d) Λ hh hβ A

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

/-- **ℤ^d `Z` is super-multiplicative on disjoint Finset unions**
(ferromagnetic). Direct wrapper of `partitionFunctionΛ_disjUnion_super_multiplicative`. -/
theorem partitionFunctionΛ_latticeGraph_disjUnion_super_multiplicative
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ₁ p
      * partitionFunctionΛ (IsingModel.latticeGraph d) Λ₂ p
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p :=
  partitionFunctionΛ_disjUnion_super_multiplicative
    (IsingModel.latticeGraph d) hd p hf

/-- **ℤ^d `log Z` is super-additive on disjoint Finset unions**
(ferromagnetic). Direct wrapper of `log_partitionFunctionΛ_disjUnion_super_additive`. -/
theorem log_partitionFunctionΛ_latticeGraph_disjUnion_super_additive
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ₁ p)
      + Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ₂ p)
    ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p) :=
  log_partitionFunctionΛ_disjUnion_super_additive
    (IsingModel.latticeGraph d) hd p hf

/-- **ℤ^d `|Λ| · freeEnergyΛ = log Z_Λ`** for nonempty `Λ`. -/
theorem card_mul_freeEnergyΛ_latticeGraph_eq_log_partitionFunctionΛ_of_nonempty
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    (p : IsingParams ℝ) :
    (Λ.card : ℝ) * freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty
    (IsingModel.latticeGraph d) hne p

/-- **ℤ^d weighted monotonicity of `freeEnergyΛ` on disjoint unions**
(ferromagnetic): `|Λ₁|·f_{Λ₁} ≤ |Λ₁ ∪ Λ₂|·f_{Λ₁ ∪ Λ₂}`. -/
theorem card_mul_freeEnergyΛ_latticeGraph_le_of_disjoint_union
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)}
    (hne₁ : Λ₁.Nonempty) (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ₁.card : ℝ) * freeEnergyΛ (IsingModel.latticeGraph d) Λ₁ p
      ≤ ((Λ₁ ∪ Λ₂).card : ℝ)
          * freeEnergyΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p := by
  classical
  exact card_mul_freeEnergyΛ_le_of_disjoint_union
    (IsingModel.latticeGraph d) hne₁ hd p hf

/-- **ℤ^d weighted super-additivity of `freeEnergyΛ` on disjoint unions**
(ferromagnetic). -/
theorem freeEnergyΛ_latticeGraph_weighted_super_additive_of_nonempty
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)}
    (hne₁ : Λ₁.Nonempty) (hne₂ : Λ₂.Nonempty) (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ₁.card : ℝ) * freeEnergyΛ (IsingModel.latticeGraph d) Λ₁ p
      + (Λ₂.card : ℝ) * freeEnergyΛ (IsingModel.latticeGraph d) Λ₂ p
    ≤ ((Λ₁ ∪ Λ₂).card : ℝ)
        * freeEnergyΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p :=
  freeEnergyΛ_weighted_super_additive_of_nonempty
    (IsingModel.latticeGraph d) hne₁ hne₂ hd p hf

/-- **ℤ^d `partitionFunctionΛ` respects Finset equality**. -/
theorem partitionFunctionΛ_latticeGraph_congr_finset
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (h : Λ₁ = Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ₁ p
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ₂ p :=
  partitionFunctionΛ_congr_finset (IsingModel.latticeGraph d) h p

/-- **ℤ^d `log Z_{Λ₁} ≤ log Z_{Λ₁ ∪ Λ₂}`** on disjoint unions (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_le_of_disjoint_union
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ₁ p)
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p) := by
  classical
  exact log_partitionFunctionΛ_le_of_disjoint_union
    (IsingModel.latticeGraph d) hd p hf

/-- **ℤ^d `Z_{Λ₁} ≤ Z_{Λ₁ ∪ Λ₂}`** on disjoint unions (ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_le_of_disjoint_union
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ₁ p
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p := by
  classical
  exact partitionFunctionΛ_le_of_disjoint_union
    (IsingModel.latticeGraph d) hd p hf

/-- **ℤ^d log partitionFunctionAlongExhaustion volume-monotonicity**
(ferromagnetic, any-Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_volume
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ p n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          Λ p (n + 1)) :=
  log_partitionFunctionAlongExhaustion_monotone_volume
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion volume-monotonicity**
(ferromagnetic, any-Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_volume
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          Λ p (n + 1) :=
  partitionFunctionAlongExhaustion_monotone_volume
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d log partitionFunctionAlongExhaustion volume-monotonicity** (ferromagnetic). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p (n + 1)) :=
  log_partitionFunctionAlongExhaustion_monotone_volume
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion volume-monotonicity** (ferromagnetic):
`partitionFunctionAlongExhaustion` at stage `n+1` is ≥ stage `n`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p (n + 1) :=
  partitionFunctionAlongExhaustion_monotone_volume (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion positivity**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_pos
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    0 < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_pos (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d partitionFunctionAlongExhaustion positivity** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    0 < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  partitionFunctionAlongExhaustion_pos (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d freeEnergyInfinite is strictly positive** (ferromagnetic). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_pos
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 < freeEnergyInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p := by
  refine freeEnergyInfinite_pos (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d freeEnergyInfinite is nonnegative** (ferromagnetic). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_nonneg
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p :=
  (freeEnergyInfinite_latticeGraph_cubicExhaustion_pos d p hf).le

/-- **ℤ^d freeEnergyInfinite strictly positive** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_pos
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 < freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_pos (IsingModel.latticeGraph d) Λ p hf (c := c) hc

/-- **ℤ^d freeEnergyInfinite nonnegative** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_nonneg
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  (freeEnergyInfinite_latticeGraph_pos d Λ p hf hc).le

/-- **log Z → ∞ along any-Exhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop_general
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ p n))
      Filter.atTop Filter.atTop :=
  log_partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) Λ p hf

/-- **log Z → ∞ along cubicExhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p n))
      Filter.atTop Filter.atTop :=
  log_partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf

/-- **Z → ∞ along any-Exhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop_general
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ p n)
      Filter.atTop Filter.atTop :=
  partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) Λ p hf

/-- **Z → ∞ along cubicExhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n)
      Filter.atTop Filter.atTop :=
  partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf

/-- **ℤ^d per-stage J-monotonicity of partitionFunctionAlongExhaustion**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J₁, h, β⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J₂, h, β⟩ n :=
  partitionFunctionAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β hh hβ hJ₁ hJ n

/-- **ℤ^d per-stage h-monotonicity of partitionFunctionAlongExhaustion**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h₁, β⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h₂, β⟩ n :=
  partitionFunctionAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh₁ hh n

/-- **ℤ^d per-stage β-monotonicity of partitionFunctionAlongExhaustion**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β₁⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h, β₂⟩ n :=
  partitionFunctionAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h hJ hh hβ₁ hβ n

/-- **ℤ^d per-stage J-monotonicity of partitionFunctionAlongExhaustion** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ
    h β hh hβ hJ₁ hJ n

/-- **ℤ^d per-stage h-monotonicity of partitionFunctionAlongExhaustion** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ
    J β hJ hβ hh₁ hh n

/-- **ℤ^d per-stage β-monotonicity of partitionFunctionAlongExhaustion** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ
    J h hJ hh hβ₁ hβ n

/-- **ℤ^d correlationInfinite translation invariance** (any-Exhaustion):
`correlationInfinite p (vaddFinset t A) = correlationInfinite p A`. -/
theorem correlationInfinite_latticeGraph_vaddFinset_of_translationInvariant
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p (vaddFinset t A)
      = correlationInfinite (IsingModel.latticeGraph d) Λ p A := by
  classical
  exact correlationInfinite_vaddFinset_of_translationInvariant
    (IsingModel.latticeGraph d) Λ t p hf A

/-- **ℤ^d spontaneousCorrelation translation invariance** (any-Exhaustion):
for ferromagnetic `(J ≥ 0, β > 0)`,
`spontaneousCorrelation J β (vaddFinset t A) = spontaneousCorrelation J β A`. -/
theorem spontaneousCorrelation_latticeGraph_translation
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β (vaddFinset t A)
      = spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A := by
  classical
  exact spontaneousCorrelation_translation
    (IsingModel.latticeGraph d) Λ t hJ hβ A

/-- **ℤ^d spontaneousMagnetization translation invariance** (any-Exhaustion):
for ferromagnetic `(J ≥ 0, β > 0)`,
`spontaneousMagnetization J β (t +ᵥ i) = spontaneousMagnetization J β i`. -/
theorem spontaneousMagnetization_latticeGraph_translation
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β (t +ᵥ i)
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i := by
  classical
  exact spontaneousMagnetization_translation
    (IsingModel.latticeGraph d) Λ t hJ hβ i

/-- **ℤ^d truncated2Infinite translation invariance** (any-Exhaustion):
`U_2(t+i, t+j) = U_2(i, j)`. -/
theorem truncated2Infinite_latticeGraph_translation
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p (t +ᵥ i) (t +ᵥ j)
      = truncated2Infinite (IsingModel.latticeGraph d) Λ p i j := by
  classical
  exact truncated2Infinite_translation (IsingModel.latticeGraph d) Λ t p hf i j

/-- **ℤ^d truncated3Infinite translation invariance** (any-Exhaustion):
`U_3(t+i, t+j, t+k) = U_3(i, j, k)`. -/
theorem truncated3Infinite_latticeGraph_translation
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p
        (t +ᵥ i) (t +ᵥ j) (t +ᵥ k)
      = truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k := by
  classical
  exact truncated3Infinite_translation (IsingModel.latticeGraph d) Λ t p hf i j k

/-- **ℤ^d truncated4Infinite translation invariance** (any-Exhaustion):
`U_4(t+i, t+j, t+k, t+l) = U_4(i, j, k, l)`. -/
theorem truncated4Infinite_latticeGraph_translation
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p
        (t +ᵥ i) (t +ᵥ j) (t +ᵥ k) (t +ᵥ l)
      = truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l := by
  classical
  exact truncated4Infinite_translation
    (IsingModel.latticeGraph d) Λ t p hf i j k l

/-- **ℤ^d freeEnergyAlongExhaustion shift translation invariance**:
`freeEnergyAlongExhaustion (Λ.shift t) n = freeEnergyAlongExhaustion Λ n`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_shift_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) (Λ.shift t) p n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_shift_eq (IsingModel.latticeGraph d) Λ t p n

/-- **ℤ^d freeEnergyInfinite shift translation invariance**:
`freeEnergyInfinite (Λ.shift t) = freeEnergyInfinite Λ`. -/
theorem freeEnergyInfinite_latticeGraph_shift_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) (Λ.shift t) p
      = freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_shift_eq (IsingModel.latticeGraph d) Λ t p

/-- **ℤ^d correlationAlongExhaustion shift translation invariance**:
`correlationAlongExhaustion (Λ.shift t) (vaddFinset t A) n = correlationAlongExhaustion Λ A n`. -/
theorem correlationAlongExhaustion_latticeGraph_shift_vaddFinset_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) (Λ.shift t) p
        (vaddFinset t A) n
      = correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  correlationAlongExhaustion_shift_vaddFinset_eq
    (IsingModel.latticeGraph d) Λ t p A n

/-- **ℤ^d extendGraphFromΛ₁_le_induce**:
`extendGraphFromΛ₁ (latticeGraph d) Λ₁ Λ₂ ≤ inducedGraph (latticeGraph d) Λ₂`. -/
theorem extendGraphFromΛ₁_le_induce_latticeGraph
    (d : ℕ) (Λ₁ Λ₂ : Finset (Fin d → ℤ)) :
    Ambient.extendGraphFromΛ₁ (IsingModel.latticeGraph d) Λ₁ Λ₂
      ≤ Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂ :=
  Ambient.extendGraphFromΛ₁_le_induce (IsingModel.latticeGraph d) Λ₁ Λ₂

/-- **ℤ^d correlationΛ_extendGraph_eq**: correlation equality between
the extended graph and the induced Λ₁ subgraph. -/
theorem correlationΛ_latticeGraph_extendGraph_eq
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.extendGraphFromΛ₁
      (IsingModel.latticeGraph d) Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ)
    {A : Finset (Fin d → ℤ)} (hA : A ⊆ Λ₁) :
    IsingModel.correlation
        (Ambient.extendGraphFromΛ₁ (IsingModel.latticeGraph d) Λ₁ Λ₂) p
        (Ambient.liftFinset A (hA.trans h12))
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁) p
          (Ambient.liftFinset A hA) :=
  Ambient.correlationΛ_extendGraph_eq (IsingModel.latticeGraph d) h12 p hA

/-- **ℤ^d correlationΛ translation invariance**:
`⟨σ^{vadd A}⟩_{t +ᵥ Λ}(p) = ⟨σ^A⟩_Λ(p)` on ℤ^d. -/
theorem correlationΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
        (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
      = correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  correlationΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p A

/-- **ℤ^d partitionFunctionΛ translation invariance**:
`Z_{t +ᵥ Λ}(p) = Z_Λ(p)` on ℤ^d. -/
theorem partitionFunctionΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p

/-- **ℤ^d freeEnergyΛ translation invariance**:
`f_{t +ᵥ Λ}(p) = f_Λ(p)` on ℤ^d. -/
theorem freeEnergyΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
      = freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p

/-- **ℤ^d log_partitionFunctionΛ translation invariance**:
`log Z_{t +ᵥ Λ}(p) = log Z_Λ(p)` on ℤ^d. -/
theorem log_partitionFunctionΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        (vaddFinset t Λ) p)
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) := by
  rw [partitionFunctionΛ_latticeGraph_vaddFinset_eq d t Λ p]

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0`** (any Finset):
`Z_Λ(⟨0, h, β⟩) = (2·cosh(β·h))^|Λ|`. -/
theorem partitionFunctionΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = (2 * Real.cosh (β * h)) ^ Λ.card :=
  partitionFunctionΛ_J_zero (IsingModel.latticeGraph d) Λ h β

/-- **ℤ^d partitionFunctionΛ closed form at `β = 0`** (any Finset):
`Z_Λ(⟨J, h, 0⟩) = 2^|Λ|`. -/
theorem partitionFunctionΛ_latticeGraph_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_beta_zero (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0, h = 0`** (any Finset):
`Z_Λ(⟨0, 0, β⟩) = 2^|Λ|`. -/
theorem partitionFunctionΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_zero_params (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d high-temperature partition function closed form (FV §3.7.3 eq. (3.45))**:
on the ℤ^d induced subgraph at zero external field,
`Z_Λ(⟨J, 0, β⟩) = 2^|Λ| · (cosh(β J))^|E_Λ| · ∑_{X ⊆ E_Λ, even-degree} tanh(β J)^|X|`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion_h_zero_closed`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        ∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d high-temperature correlation closed form (FV §3.7.3 eq. (3.46))**:
on the ℤ^d induced subgraph at zero external field,
`⟨σ_A⟩^Λ_{β,0} = (∑_{X : ∂X=A} tanh^|X|) / (∑_{X : ∂X=∅} tanh^|X|)`.
ℤ^d wrapper of `correlationΛ_high_temp_expansion_h_zero_closed`. -/
theorem correlationΛ_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A
      = (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) /
        (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) :=
  correlationΛ_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β A

/-- **ℤ^d high-temperature partition function lower bound (GJ §18.3 / FV (3.45))**:
under `0 ≤ β * J`,
`Z_Λ(⟨J, 0, β⟩) ≥ 2^|Λ| · (cosh(βJ))^|E_Λ|`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_lower_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d log partitionFunctionΛ closed form at `J = 0`** (any Finset):
`log Z_Λ(⟨0, h, β⟩) = |Λ| · log(2·cosh(β·h))`. -/
theorem log_partitionFunctionΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log (2 * Real.cosh (β * h)) :=
  log_partitionFunctionΛ_J_zero (IsingModel.latticeGraph d) Λ h β

/-- **ℤ^d log partitionFunctionΛ closed form at `β = 0`** (any Finset):
`log Z_Λ(⟨J, h, 0⟩) = |Λ| · log 2`. -/
theorem log_partitionFunctionΛ_latticeGraph_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_beta_zero (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d log partitionFunctionΛ closed form at `J = 0, h = 0`** (any Finset):
`log Z_Λ(⟨0, 0, β⟩) = |Λ| · log 2`. -/
theorem log_partitionFunctionΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_zero_params (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d partitionFunctionΛ h-evenness** (any Finset):
`Z_Λ(J, -h, β) = Z_Λ(J, h, β)`. -/
theorem partitionFunctionΛ_latticeGraph_neg_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d partitionFunctionΛ h-evenness**:
`Z_{Λ_n}(J, -h, β) = Z_{Λ_n}(J, h, β)` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_neg_h`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨J, -h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume n) (⟨J, h, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_neg_h (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) J h β

/-- **ℤ^d partitionFunctionAlongExhaustion h-evenness** per stage:
`Z(Λ_n; J, -h, β) = Z(Λ_n; J, h, β)`. Concrete specialization of
`partitionFunctionAlongExhaustion_neg_h`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d partitionFunctionAlongExhaustion h-evenness** per stage (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_neg_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d partitionFunctionAlongExhaustion `|h|`-rewrite** per stage (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d partitionFunctionAlongExhaustion ferromagnetic `|h|`-monotonicity**
per stage (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d) Λ
    J β hJ hβ hh n

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0`**:
`Z_{Λ_n}(⟨0, h, β⟩) = (2·cosh(β·h))^|Λ_n|` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_J_zero`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, h, β⟩ : IsingParams ℝ)
      = (2 * Real.cosh (β * h)) ^
          ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionΛ_J_zero (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) h β

/-- **ℤ^d partitionFunctionΛ closed form at `β = 0`**:
`Z_{Λ_n}(⟨J, h, 0⟩) = 2^|Λ_n|` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_beta_zero`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨J, h, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionΛ_beta_zero (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) J h

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0, h = 0`**:
`Z_{Λ_n}(⟨0, 0, β⟩) = 2^|Λ_n|` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_zero_params`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionΛ_zero_params (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) β

/-- **ℤ^d log_partitionFunctionΛ closed form at `J = 0`**:
`log Z_{Λ_n}(⟨0, h, β⟩) = |Λ_n| · log(2·cosh(β·h))` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_J_zero`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, h, β⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ)
          * Real.log (2 * Real.cosh (β * h)) :=
  log_partitionFunctionΛ_J_zero (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) h β

/-- **ℤ^d log_partitionFunctionΛ closed form at `β = 0`**:
`log Z_{Λ_n}(⟨J, h, 0⟩) = |Λ_n| · log 2` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_beta_zero`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨J, h, 0⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_beta_zero (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) J h

/-- **ℤ^d log_partitionFunctionΛ closed form at `J = 0, h = 0`**:
`log Z_{Λ_n}(⟨0, 0, β⟩) = |Λ_n| · log 2` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_zero_params`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, 0, β⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_zero_params (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) β

/-- **ℤ^d freeEnergyAlongExhaustion h-evenness** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d freeEnergyAlongExhaustion |h|-form** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d freeEnergyAlongExhaustion |h|-monotonicity** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh n

/-- **ℤ^d freeEnergyAlongExhaustion h-evenness** per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_neg_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d freeEnergyAlongExhaustion `|h|`-rewrite** per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d freeEnergyAlongExhaustion ferromagnetic `|h|`-monotonicity**
per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d) Λ
    J β hJ hβ hh n

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

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-evenness** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_neg_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-rewrite** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_eq_abs_h
    (IsingModel.latticeGraph d) Λ J h β n

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

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_abs_h
    (IsingModel.latticeGraph d) Λ J β hJ hβ hh n

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

/-- **ℤ^d freeEnergyΛ ≥ log(2 cosh βh)** (ferromagnetic, nonempty Λ). -/
theorem freeEnergyΛ_latticeGraph_ge_log_two_cosh
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_ge_log_two_cosh (IsingModel.latticeGraph d) hne hJ hh hβ

/-- **ℤ^d freeEnergyΛ ≥ log 2** (ferromagnetic, nonempty Λ). -/
theorem freeEnergyΛ_latticeGraph_ge_log_two
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_ge_log_two (IsingModel.latticeGraph d) hne hJ hh hβ

/-- **ℤ^d freeEnergyΛ ≥ 0** (ferromagnetic, nonempty Λ). -/
theorem freeEnergyΛ_latticeGraph_nonneg
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_nonneg_of_ferromagnetic (IsingModel.latticeGraph d) hne p hf

/-- **ℤ^d freeEnergyΛ closed form at `J = 0`**:
for nonempty `Λ` and any `h, β`,
`freeEnergyΛ ⟨0, h, β⟩ = log(2·cosh(β·h))`. Concrete specialization of
`freeEnergyΛ_J_zero`. -/
theorem freeEnergyΛ_latticeGraph_J_zero
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty) (h β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyΛ_J_zero (IsingModel.latticeGraph d) hne h β

/-- **ℤ^d freeEnergyΛ closed form at `β = 0`**:
for nonempty `Λ` and any `J, h`,
`freeEnergyΛ ⟨J, h, 0⟩ = log 2`. Concrete specialization of
`freeEnergyΛ_beta_zero`. -/
theorem freeEnergyΛ_latticeGraph_beta_zero
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty) (J h : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyΛ_beta_zero (IsingModel.latticeGraph d) hne J h

/-- **ℤ^d freeEnergyΛ closed form at `J = 0, h = 0`**:
for nonempty `Λ` and any `β`,
`freeEnergyΛ ⟨0, 0, β⟩ = log 2`. Concrete specialization of
`freeEnergyΛ_zero_params`. -/
theorem freeEnergyΛ_latticeGraph_zero_params
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty) (β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyΛ_zero_params (IsingModel.latticeGraph d) hne β

/-- **ℤ^d freeEnergyΛ h-evenness**:
`freeEnergyΛ ⟨J,-h,β⟩ = freeEnergyΛ ⟨J,h,β⟩` on any ℤ^d-vertex Finset.
Concrete specialization of `freeEnergyΛ_neg_h`. -/
theorem freeEnergyΛ_latticeGraph_neg_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d freeEnergyΛ `|h|`-rewrite**:
`freeEnergyΛ ⟨J,h,β⟩ = freeEnergyΛ ⟨J,|h|,β⟩`. Concrete specialization of
`freeEnergyΛ_eq_abs_h`. -/
theorem freeEnergyΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d freeEnergyΛ ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0` and `|h₁| ≤ |h₂|`,
`freeEnergyΛ ⟨J, h₁, β⟩ ≤ freeEnergyΛ ⟨J, h₂, β⟩`. Concrete specialization
of `freeEnergyΛ_monotone_abs_h`. -/
theorem freeEnergyΛ_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_monotone_abs_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh

/-- **ℤ^d freeEnergyΛ J-monotonicity**: for fixed `h ≥ 0`, `β > 0`,
`freeEnergyΛ` is monotone in `J` on `[0, ∞)`. Concrete specialization
of `freeEnergyΛ_monotone_J`. -/
theorem freeEnergyΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyΛ_monotone_J (IsingModel.latticeGraph d) Λ hh hβ

/-- **ℤ^d freeEnergyΛ h-monotonicity**: for fixed `J ≥ 0`, `β > 0`,
`freeEnergyΛ` is monotone in `h` on `[0, ∞)`. Concrete specialization
of `freeEnergyΛ_monotone_h`. -/
theorem freeEnergyΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyΛ_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ

/-- **ℤ^d freeEnergyΛ β-monotonicity**: for fixed `J ≥ 0`, `h ≥ 0`,
`freeEnergyΛ` is monotone in `β` on `(0, ∞)`. Concrete specialization
of `freeEnergyΛ_monotone_beta`. -/
theorem freeEnergyΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) :=
  freeEnergyΛ_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh

/-- **ℤ^d partitionFunctionΛ J-monotonicity** (pointwise). Concrete
specialization of `partitionFunctionΛ_monotone_J`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_J (IsingModel.latticeGraph d) Λ h β hh hβ hJ₁ hJ

/-- **ℤ^d partitionFunctionΛ h-monotonicity** (pointwise). Concrete
specialization of `partitionFunctionΛ_monotone_h`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh₁ hh

/-- **ℤ^d partitionFunctionΛ β-monotonicity** (pointwise). Concrete
specialization of `partitionFunctionΛ_monotone_beta`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_beta (IsingModel.latticeGraph d) Λ J h hJ hh hβ₁ hβ

/-- **ℤ^d partitionFunctionΛ `|h|`-rewrite**:
`Z_Λ(J,h,β) = Z_Λ(J,|h|,β)`. Concrete specialization of
`partitionFunctionΛ_eq_abs_h`. -/
theorem partitionFunctionΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d partitionFunctionΛ ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`Z_Λ(J,h₁,β) ≤ Z_Λ(J,h₂,β)`. Concrete specialization of
`partitionFunctionΛ_monotone_abs_h`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_abs_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh

/-- **ℤ^d log_partitionFunctionΛ h-evenness**: `log Z_Λ(J,-h,β) = log Z_Λ(J,h,β)`. -/
theorem log_partitionFunctionΛ_latticeGraph_neg_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ))
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d log_partitionFunctionΛ `|h|`-rewrite**: `log Z_Λ(J,h,β) = log Z_Λ(J,|h|,β)`. -/
theorem log_partitionFunctionΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d log_partitionFunctionΛ J-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_J (IsingModel.latticeGraph d) Λ h β hh hβ hJ₁ hJ

/-- **ℤ^d log_partitionFunctionΛ h-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh₁ hh

/-- **ℤ^d log_partitionFunctionΛ β-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_beta (IsingModel.latticeGraph d) Λ J h hJ hh hβ₁ hβ

/-- **ℤ^d log_partitionFunctionΛ `|h|`-monotonicity** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_abs_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-evenness** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-rewrite** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

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

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh n

/-- **ℤ^d partitionFunctionAlongExhaustion `|h|`-rewrite** per stage:
`Z(Λ_n; J, h, β) = Z(Λ_n; J, |h|, β)`. Concrete specialization of
`partitionFunctionAlongExhaustion_eq_abs_h`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d partitionFunctionAlongExhaustion ferromagnetic `|h|`-monotonicity**
per stage: for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`Z(Λ_n; J, h₁, β) ≤ Z(Λ_n; J, h₂, β)`. Concrete specialization of
`partitionFunctionAlongExhaustion_monotone_abs_h`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh n

/-- **ℤ^d partitionFunctionΛ ≥ 1** (ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_ge_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    1 ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_one_of_ferromagnetic (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d partitionFunctionΛ ≥ 2^|Λ|** (ferromagnetic, per-Λ). -/
theorem partitionFunctionΛ_latticeGraph_ge_two_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Λ.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_two_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d log partitionFunctionΛ ≥ |Λ|·log 2** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log 2
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d `log Z_Λ ≥ 0`** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    0 ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d `freeEnergyΛ = |↑Λ|⁻¹ · log Z_Λ`**. -/
theorem freeEnergyΛ_latticeGraph_eq_inv_card_mul_log
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = (Fintype.card (↑Λ : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  freeEnergyΛ_eq_inv_card_mul_log (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `freeEnergyΛ = (Λ.card)⁻¹ · log Z_Λ`** (Finset-card form). -/
theorem freeEnergyΛ_latticeGraph_eq_inv_Λcard_mul_log
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = (Λ.card : ℝ)⁻¹
        * Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  freeEnergyΛ_eq_inv_Λcard_mul_log (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `freeEnergyAlongExhaustion = |↑(Λ_n)|⁻¹ · log Z_n`** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_inv_card_mul_log
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_inv_card_mul_log (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d `freeEnergyAlongExhaustion = ((Λ.volume n).card)⁻¹ · log Z_n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_inv_Λcard_mul_log
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = ((Λ.volume n).card : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_inv_Λcard_mul_log
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d `freeEnergyΛ ≥ 0`** (ferromagnetic, nonempty `Λ`). -/
theorem freeEnergyΛ_latticeGraph_nonneg_of_ferromagnetic
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_nonneg_of_ferromagnetic (IsingModel.latticeGraph d) hne p hf

/-- **ℤ^d `freeEnergyAlongExhaustion ≥ 0`** per stage (ferromagnetic,
nonempty stage, any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_nonneg_of_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {n : ℕ}
    (hne : (Λ.volume n).Nonempty) :
    0 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf hne

/-- **ℤ^d `freeEnergyAlongExhaustion` as `log Z / card`** (any-Exhaustion):
alternate form of `freeEnergyAlongExhaustion_eq_inv_card_mul_log` using the
Fintype-card expression. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_log_div_card
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_log_div_card
    (IsingModel.latticeGraph d) Λ p n

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

/-- **ℤ^d partitionFunctionΛ ≥ (2 cosh βh)^|Λ|** (sharp, ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_ge_two_cosh_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (2 * Real.cosh (p.β * p.h)) ^ Λ.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_two_cosh_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 1** (ferromagnetic). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 1** (ferromagnetic, any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_one_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d log Z_n ≥ 0** (ferromagnetic, any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_nonneg_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ p n) :=
  log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d log partitionFunctionAlongExhaustion ≥ 0** (ferromagnetic). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n) :=
  log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

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

/-- **ℤ^d sharp log Z_Λ bound**: `|Λ|·log(2 cosh βh) ≤ log Z_Λ` (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two_cosh
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_cosh_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d partitionFunctionAlongExhaustion β=0 per-stage** (any-Exhaustion):
`= 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_beta_zero
    (IsingModel.latticeGraph d) Λ J h n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β=0** (any-Exhaustion):
`= |Λ_n|·log 2`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_beta_zero
    (IsingModel.latticeGraph d) Λ J h n

/-- **ℤ^d partitionFunctionAlongExhaustion J=h=0 per-stage** (any-Exhaustion):
`= 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_zero_params
    (IsingModel.latticeGraph d) Λ β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=h=0** (any-Exhaustion):
`= |Λ_n|·log 2`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_zero_params
    (IsingModel.latticeGraph d) Λ β n

/-- **ℤ^d partitionFunctionAlongExhaustion J=0 per-stage** (any-Exhaustion):
`= (2·cosh(β·h))^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_J_zero
    (IsingModel.latticeGraph d) Λ h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=0** (any-Exhaustion):
`= |Λ_n|·log(2·cosh(β·h))`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log (2 * Real.cosh (β * h)) :=
  log_partitionFunctionAlongExhaustion_J_zero
    (IsingModel.latticeGraph d) Λ h β n

/-- **ℤ^d partitionFunctionAlongExhaustion β=0 per-stage**: `= 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionAlongExhaustion_beta_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β=0**: `= |Λ_n|·log 2`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ) n)
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_beta_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h n

/-- **ℤ^d partitionFunctionAlongExhaustion J=h=0 per-stage**: `= 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionAlongExhaustion_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=h=0**: `= |Λ_n|·log 2`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ) n)
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β n

/-- **ℤ^d partitionFunctionAlongExhaustion J=0 per-stage**:
`= (2·cosh(β·h))^|Λ_n|`. Concrete specialization of
`partitionFunctionAlongExhaustion_J_zero`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^
          ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionAlongExhaustion_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=0**:
`= |Λ_n|·log(2·cosh(β·h))`. Concrete specialization of
`log_partitionFunctionAlongExhaustion_J_zero`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ) n)
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ)
          * Real.log (2 * Real.cosh (β * h)) :=
  log_partitionFunctionAlongExhaustion_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β n

/-- **ℤ^d freeEnergyAlongExhaustion β=0 per-stage** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_beta_zero (IsingModel.latticeGraph d) Λ J h n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=h=0 per-stage** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_zero_params (IsingModel.latticeGraph d) Λ β n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=0 per-stage** (any-Exhaustion):
`= log(2·cosh(β·h))`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyAlongExhaustion_J_zero (IsingModel.latticeGraph d) Λ h β n hne

/-- **ℤ^d freeEnergyAlongExhaustion β=0 per-stage**: `= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_beta_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=h=0 per-stage**: `= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=0 per-stage**: `= log(2·cosh(β·h))`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyAlongExhaustion_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β n hne

/-- **ℤ^d freeEnergyInfinite from convergence** (any-Exhaustion): if
`freeEnergyAlongExhaustion` tendsto `L`, then `freeEnergyInfinite = L`. -/
theorem freeEnergyInfinite_latticeGraph_eq_of_tendsto
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {L : ℝ}
    (h : Filter.Tendsto (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      Λ p) Filter.atTop (nhds L)) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p = L :=
  freeEnergyInfinite_eq_of_tendsto (IsingModel.latticeGraph d) Λ p h

/-- **ℤ^d freeEnergyInfinite of eventually constant sequence** (any-Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_of_eventually_const
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion
      (IsingModel.latticeGraph d) Λ p n = c) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p = c :=
  freeEnergyInfinite_of_eventually_const (IsingModel.latticeGraph d) Λ p h

/-- **ℤ^d freeEnergyInfinite from convergence**: if
`freeEnergyAlongExhaustion` tendsto `L`, then `freeEnergyInfinite = L`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_of_tendsto
    (d : ℕ) (p : IsingParams ℝ) {L : ℝ}
    (h : Filter.Tendsto (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p) Filter.atTop (nhds L)) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p = L :=
  freeEnergyInfinite_eq_of_tendsto (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p h

/-- **ℤ^d freeEnergyInfinite of eventually constant sequence**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_of_eventually_const
    (d : ℕ) (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion
      (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p n = c) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p = c :=
  freeEnergyInfinite_of_eventually_const (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p h

/-- **ℤ^d freeEnergyInfinite uniform upper bound via caller-supplied BED**
(any-Exhaustion): `freeEnergyInfinite ≤ log 2 + |β|·(|J|·c + |h|)`. -/
theorem freeEnergyInfinite_latticeGraph_le_uniform_upper_bound
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p
      ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) :=
  freeEnergyInfinite_le_uniform_upper_bound
    (IsingModel.latticeGraph d) Λ p hf hc

/-- **ℤ^d freeEnergyInfinite uniform upper bound via BED**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_le_uniform_upper_bound
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p
      ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  refine freeEnergyInfinite_le_uniform_upper_bound (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d BddAbove range of `freeEnergyAlongExhaustion`** (any-Exhaustion,
caller-supplied BED). -/
theorem BddAbove_freeEnergyAlongExhaustion_latticeGraph_range
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      Λ p)) :=
  BddAbove_freeEnergyAlongExhaustion_range (IsingModel.latticeGraph d) Λ p hBED

/-- **ℤ^d BddAbove range of `freeEnergyAlongExhaustion`**: via BED c=d. -/
theorem BddAbove_freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion
    (d : ℕ) (p : IsingParams ℝ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p)) :=
  BddAbove_freeEnergyAlongExhaustion_range (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p
    (boundedEdgeDensity_latticeGraph_cubicExhaustion d)

/-- **ℤ^d per-stage freeEnergyAlongExhaustion upper bound** using BED c = d. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_le_uniform_upper_bound
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  refine freeEnergyAlongExhaustion_le_uniform_upper_bound
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p
    (c := (d : ℝ)) ?_ n hne
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

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

/-- **ℤ^d per-stage `0 ≤ f_n`** (ferromagnetic, nonempty stage, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {n : ℕ}
    (hne : (Λ.volume n).Nonempty) :
    0 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf hne

/-- **ℤ^d free-energy shift invariance**:
`freeEnergyInfinite (latticeGraph d) ((cubicExhaustion d).shift t) p
  = freeEnergyInfinite (latticeGraph d) (cubicExhaustion d) p`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_shift
    (d : ℕ) (t : Fin d → ℤ) (p : IsingParams ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).shift t) p
      = freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p :=
  freeEnergyInfinite_shift_eq (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) t p

end Ambient

end IsingModel
