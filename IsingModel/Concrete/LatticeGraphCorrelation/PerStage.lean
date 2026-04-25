import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.ComplexAnalyticity
import IsingModel.PeierlsInfinite
import IsingModel.AmbientComplexAnalyticity
import IsingModel.AmbientFKG

/-!
# Per-stage complex analyticity, convergence, and critical-exponent bounds at ℤ^d

ℤ^d forwarders for:

1. **Complex Z / free energy along an exhaustion** — unfolding and real-complex
   compatibility identities from `AmbientComplexAnalyticity.lean`.
2. **Per-stage analyticity / continuity / norm-bound** — entire in `h`, `J`, `β`;
   `AnalyticOnNhd` on the Lee–Yang subdomain; per-stage Montel norm bound;
   `Z_ℂ ≠ 0` on `leeYangDomain`. Foundation for the GJ §4.6 Vitali extraction.
3. **Per-stage Gibbs expectation + FKG** — along-exhaustion Gibbs unfolding and
   the GJ §4.4 FKG inequality per stage; GJ §5.4 Prop 5.4.2 `+`-BC bound.
4. **GJ §17.7 critical-exponent bounds** — `η ≥ 0` and `ζ ≥ 0` at finite and
   ∞ volume; absence of even bound states.
5. **Subgraph monotonicity and convergence** — `partitionFunction`, `correlation`,
   `freeEnergy` monotone in subgraph; convergence of monotone subgraph sequences.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.4, §4.6, §5.4, §17.7.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! #### Complex partition function / free energy along an exhaustion
(ℤ^d wrappers)

ℤ^d forwarders for the complex along-exhaustion definitions and their
real-complex compatibility identities from
`IsingModel/AmbientComplexAnalyticity.lean`. Foundation for the GJ §4.6
Thm 4.6.2 ∞-vol Vitali completion at ℤ^d. -/

/-- **ℤ^d `partitionFunctionComplexAlongExhaustion` unfolding**:
equal to `partitionFunctionComplex` on the `n`-th volume of the
exhaustion. -/
theorem partitionFunctionComplexAlongExhaustion_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J h β : ℂ) (n : ℕ) :
    Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n
      = IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph
            (IsingModel.latticeGraph d) (Λ.volume n)) J h β :=
  Ambient.partitionFunctionComplexAlongExhaustion_apply
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d `freeEnergyComplexAlongExhaustion` unfolding**:
equal to `freeEnergyComplex` on the `n`-th volume of the exhaustion. -/
theorem freeEnergyComplexAlongExhaustion_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J h β : ℂ) (n : ℕ) :
    Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n
      = IsingModel.freeEnergyComplex
          (Ambient.inducedGraph
            (IsingModel.latticeGraph d) (Λ.volume n)) J h β :=
  Ambient.freeEnergyComplexAlongExhaustion_apply
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d real-complex compatibility for `partitionFunction_along_exhaustion`**:
`Z_ℂ_{Λ_n}(↑p.J, ↑p.h, ↑p.β) = ↑(Z_ℝ_{Λ_n}(p))`. Foundational identity for
the Vitali completion's real-axis limit identification. -/
theorem partitionFunctionComplexAlongExhaustion_at_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n
      = ((Ambient.partitionFunctionAlongExhaustion
          (IsingModel.latticeGraph d) Λ p n : ℝ) : ℂ) :=
  Ambient.partitionFunctionComplexAlongExhaustion_at_real_eq_ofReal
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d real-complex compatibility for `freeEnergy_along_exhaustion`**:
`f_ℂ_{Λ_n}(↑p.J, ↑p.h, ↑p.β) = ↑(f_ℝ_{Λ_n}(p))`. Foundational identity
for the Vitali completion's real-axis Fekete identification. -/
theorem freeEnergyComplexAlongExhaustion_at_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n
      = ((Ambient.freeEnergyAlongExhaustion
          (IsingModel.latticeGraph d) Λ p n : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_at_real_eq_ofReal
    (IsingModel.latticeGraph d) Λ p n

/-! #### Per-stage analyticity / continuity / norm-bound for the complex
along-exhaustion sequence (ℤ^d wrappers)

ℤ^d forwarders for the per-stage properties in
`IsingModel/AmbientComplexAnalyticity.lean`. Foundation for the Montel /
Vitali extraction. -/

/-- **ℤ^d per-stage entire in `h`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_h_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) (h₀ : ℂ) :
    AnalyticAt ℂ
      (fun h => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) h₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_h_stage
    (IsingModel.latticeGraph d) Λ J β n h₀

/-- **ℤ^d per-stage entire in `J`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_J_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (h β : ℂ) (n : ℕ) (J₀ : ℂ) :
    AnalyticAt ℂ
      (fun J => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) J₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_J_stage
    (IsingModel.latticeGraph d) Λ h β n J₀

/-- **ℤ^d per-stage entire in `β`** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_beta_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J h : ℂ) (n : ℕ) (β₀ : ℂ) :
    AnalyticAt ℂ
      (fun β => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) β₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_beta_stage
    (IsingModel.latticeGraph d) Λ J h n β₀

/-- **ℤ^d per-stage joint entire** for `partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_analyticAt_joint_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (n : ℕ) (z₀ : ℂ × ℂ × ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ z.1 z.2.1 z.2.2 n) z₀ :=
  Ambient.partitionFunctionComplexAlongExhaustion_analyticAt_joint_stage
    (IsingModel.latticeGraph d) Λ n z₀

/-- **ℤ^d per-stage `Continuous` in `h`** for
`partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_continuous_h_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) :
    Continuous
      (fun h => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) :=
  Ambient.partitionFunctionComplexAlongExhaustion_continuous_h_stage
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d per-stage `AnalyticAt h₀` for `freeEnergyComplexAlongExhaustion`
under `Z_{stage} ∈ slitPlane`**. -/
theorem freeEnergyComplexAlongExhaustion_analyticAt_h_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) (h₀ : ℂ)
    (hZ : Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h₀ β n ∈ Complex.slitPlane) :
    AnalyticAt ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) h₀ :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticAt_h_stage
    (IsingModel.latticeGraph d) Λ J β n h₀ hZ

/-- **ℤ^d per-stage `AnalyticOnNhd` on Lee-Yang subdomain** for
`freeEnergyComplexAlongExhaustion` (ferromagnetic). -/
theorem freeEnergyComplexAlongExhaustion_analyticOnNhd_leeYangSubdomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n)
      (IsingModel.leeYangSubdomain β
        (Fintype.card (↑(Λ.volume n) : Type _))) :=
  Ambient.freeEnergyComplexAlongExhaustion_analyticOnNhd_leeYangSubdomain_stage
    (IsingModel.latticeGraph d) Λ hβ J n

/-- **ℤ^d per-stage `DifferentiableOn` on Lee-Yang subdomain** for
`freeEnergyComplexAlongExhaustion`. -/
theorem freeEnergyComplexAlongExhaustion_differentiableOn_leeYangSubdomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) (n : ℕ) :
    DifferentiableOn ℂ
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n)
      (IsingModel.leeYangSubdomain β
        (Fintype.card (↑(Λ.volume n) : Type _))) :=
  Ambient.freeEnergyComplexAlongExhaustion_differentiableOn_leeYangSubdomain_stage
    (IsingModel.latticeGraph d) Λ hβ J n

/-- **ℤ^d per-stage `ContinuousOn` on Lee-Yang subdomain** for
`freeEnergyComplexAlongExhaustion`. -/
theorem freeEnergyComplexAlongExhaustion_continuousOn_leeYangSubdomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) (n : ℕ) :
    ContinuousOn
      (fun h => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n)
      (IsingModel.leeYangSubdomain β
        (Fintype.card (↑(Λ.volume n) : Type _))) :=
  Ambient.freeEnergyComplexAlongExhaustion_continuousOn_leeYangSubdomain_stage
    (IsingModel.latticeGraph d) Λ hβ J n

/-- **ℤ^d per-stage locally-uniform norm bound** for
`partitionFunctionComplexAlongExhaustion`: `‖Z_ℂ_{Λ_n}‖ ≤ 2^|Λ_n| · exp(...)`
under `|Re h| ≤ R`. Montel input for the Vitali extraction. -/
theorem norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) {R : ℝ} {h : ℂ} (hh : |h.re| ≤ R) :
    ‖Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
      ≤ Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) *
          Real.exp (|β| *
            (|J| * (Ambient.inducedGraph
                (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
              + R * Fintype.card (↑(Λ.volume n) : Type _))) :=
  Ambient.norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage
    (IsingModel.latticeGraph d) Λ β J n hh

/-- **ℤ^d per-stage `Z_ℂ ≠ 0 on leeYangDomain`** for
`partitionFunctionComplexAlongExhaustion` (ferromagnetic). -/
theorem partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangDomain) :
    Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n ≠ 0 :=
  Ambient.partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage
    (IsingModel.latticeGraph d) Λ hβ hJ n hh

/-- **ℤ^d real-axis convergence of `freeEnergyComplexAlongExhaustion`**
(under `DisjointTowerHypotheses` + `BoundedEdgeDensity`): at real
parameters, the complex along-exhaustion sequence converges (in `ℂ`) to
`↑(freeEnergyInfinite G Λ p)`. Pass-through of the abstract lemma. -/
theorem freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p) :
    Filter.Tendsto
      (fun n => Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
      Filter.atTop
      (nhds ((Ambient.freeEnergyInfinite
        (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ)) :=
  Ambient.freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
    (IsingModel.latticeGraph d) Λ p hBED hd

/-! #### Per-stage Gibbs expectation along an exhaustion + FKG (ℤ^d) -/

/-- **ℤ^d `gibbsExpectationAlongExhaustion` unfolding**: equal to
`gibbsExpectation` on the `n`-th volume with the `n`-th family
member. -/
theorem gibbsExpectationAlongExhaustion_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (F : (n : ℕ) → IsingModel.Config (↑(Λ.volume n) : Type _) → ℝ) (n : ℕ) :
    Ambient.gibbsExpectationAlongExhaustion
        (IsingModel.latticeGraph d) Λ p F n
      = IsingModel.gibbsExpectation
          (Ambient.inducedGraph
            (IsingModel.latticeGraph d) (Λ.volume n)) p (F n) :=
  Ambient.gibbsExpectationAlongExhaustion_apply
    (IsingModel.latticeGraph d) Λ p F n

/-- **ℤ^d per-stage FKG along an exhaustion** (GJ §4.4):
for ferromagnetic `p` and per-stage nonneg monotone families
`F n, G_fn n : Config (↑(Λ.volume n)) → ℝ`, the FKG inequality holds at
every stage `n`. Pass-through of `fkg_ising_along_exhaustion`. -/
theorem fkg_ising_along_exhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (F G_fn : (n : ℕ) → IsingModel.Config (↑(Λ.volume n) : Type _) → ℝ)
    (hF_nn : ∀ n, 0 ≤ F n) (hG_nn : ∀ n, 0 ≤ G_fn n)
    (hF_mono : ∀ n, Monotone (F n)) (hG_mono : ∀ n, Monotone (G_fn n))
    (n : ℕ) :
    Ambient.gibbsExpectationAlongExhaustion
        (IsingModel.latticeGraph d) Λ p F n
      * Ambient.gibbsExpectationAlongExhaustion
          (IsingModel.latticeGraph d) Λ p G_fn n
      ≤ Ambient.gibbsExpectationAlongExhaustion
          (IsingModel.latticeGraph d) Λ p (fun k => F k * G_fn k) n :=
  Ambient.fkg_ising_along_exhaustion
    (IsingModel.latticeGraph d) Λ p hf F G_fn
    hF_nn hG_nn hF_mono hG_mono n

/-- **ℤ^d GJ §5.4 Prop 5.4.2 genuine ∞-vol `+`-BC bound** (Λ-induced,
`liminf` form): for any exhaustion `Λ : Ambient.Exhaustion (Fin d → ℤ)`
with per-stage `Preconnected` + `Fintype G_n.edgeSet` instances and the
Peierls exponential bound `hexp`, the `liminf`-based canonical ∞-vol
`+`-expectation of `σ ↦ Spin.sign ℝ (σ (i n))` satisfies
`1 − plusGibbsExpectationLiminf ≤ exp(-c·β)`. Pass-through of
`IsingModel.prop_5_4_2_plusGibbsExpectationLiminf_bound`, with
`DecidableRel` supplied via `classical`. -/
theorem prop_5_4_2_plusGibbsExpectationLiminf_bound_latticeGraph
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
    1 - IsingModel.plusGibbsExpectationLiminf
          (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) B
          (fun n σ => IsingModel.Spin.sign ℝ (σ (i n)))
      ≤ Real.exp (-c * β) := by
  classical
  exact IsingModel.prop_5_4_2_plusGibbsExpectationLiminf_bound
    (IsingModel.latticeGraph d) Λ hconn J β c hβ hJ B hB i hexp

/-! #### §17.7 critical-exponent bounds at ℤ^d

Direct ℤ^d wrappers for the `η ≥ 0` and `ζ ≥ 0` critical-exponent
bounds at ℤ^d, for both finite-volume and ∞-volume. Pass-throughs of
`IsingModel.{eta,zeta}_nonneg_{finite,infinite}_vol`. -/

/-- **ℤ^d `ζ ≥ 0` finite-volume** (Λ-induced, GJ §17.7 Thm 17.7.1,
ferromagnetic at `h = 0`). Pass-through of
`IsingModel.zeta_nonneg_finite_vol`. -/
theorem zeta_nonneg_finite_vol_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (i j k l : (↑Λ : Type _))
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    IsingModel.truncated4
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, 0, β⟩ i j k l ≤ 0 :=
  IsingModel.zeta_nonneg_finite_vol
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hf
    i j k l hij hik hil hjk hjl hkl

/-- **ℤ^d `η ≥ 0` ∞-volume** (GJ §17.7 Thm 17.7.1, ferromagnetic).
Pass-through of `IsingModel.Ambient.eta_nonneg_infinite_vol`. -/
theorem eta_nonneg_infinite_vol_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    0 ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ p i j :=
  Ambient.eta_nonneg_infinite_vol (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `ζ ≥ 0` ∞-volume** (GJ §17.7 Thm 17.7.1, ferromagnetic at
`h = 0`). Pass-through of `IsingModel.Ambient.zeta_nonneg_infinite_vol`. -/
theorem zeta_nonneg_infinite_vol_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    {i j k l : Fin d → ℤ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    Ambient.truncated4Infinite (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ i j k l ≤ 0 :=
  Ambient.zeta_nonneg_infinite_vol (IsingModel.latticeGraph d) Λ J β hf
    hij hik hil hjk hjl hkl

/-- **ℤ^d absence of even bound states, finite-volume** (GJ §17.2
Λ-induced, ferromagnetic at `h = 0`). Pass-through of
`IsingModel.absence_of_even_bound_states_finite_vol`. -/
theorem absence_of_even_bound_states_finite_vol_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (i j k l : (↑Λ : Type _))
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    IsingModel.truncated4
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, 0, β⟩ i j k l ≤ 0 :=
  IsingModel.absence_of_even_bound_states_finite_vol
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hf
    i j k l hij hik hil hjk hjl hkl

/-- **ℤ^d absence of even bound states, ∞-volume** (GJ §17.2,
ferromagnetic at `h = 0`). Pass-through of
`IsingModel.Ambient.absence_of_even_bound_states_infinite_vol`. -/
theorem absence_of_even_bound_states_infinite_vol_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    {i j k l : Fin d → ℤ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    Ambient.truncated4Infinite (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ i j k l ≤ 0 :=
  Ambient.absence_of_even_bound_states_infinite_vol
    (IsingModel.latticeGraph d) Λ J β hf hij hik hil hjk hjl hkl

/-- **ℤ^d partitionFunction monotone_subgraph** at Λ-induced subgraph:
`G₁ ≤ G₂ ⇒ Z_{G₁} ≤ Z_{G₂}` for ferromagnetic `p`. -/
theorem partitionFunction_monotone_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {G₁ G₂ : SimpleGraph (↑Λ : Type _)}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    IsingModel.partitionFunction G₁ p ≤ IsingModel.partitionFunction G₂ p :=
  IsingModel.partitionFunction_monotone_subgraph h₁₂ p hf

/-- **ℤ^d correlation monotone_subgraph** at Λ-induced subgraph:
`G₁ ≤ G₂ ⇒ ⟨σ^A⟩_{G₁} ≤ ⟨σ^A⟩_{G₂}` for ferromagnetic `p`. -/
theorem correlation_monotone_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {G₁ G₂ : SimpleGraph (↑Λ : Type _)}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation G₁ p A ≤ IsingModel.correlation G₂ p A :=
  IsingModel.correlation_monotone_subgraph h₁₂ p hf A

/-- **ℤ^d log_partitionFunction monotone_subgraph** at Λ-induced subgraph. -/
theorem log_partitionFunction_monotone_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {G₁ G₂ : SimpleGraph (↑Λ : Type _)}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (IsingModel.partitionFunction G₁ p)
      ≤ Real.log (IsingModel.partitionFunction G₂ p) :=
  IsingModel.log_partitionFunction_monotone_subgraph h₁₂ p hf

/-- **ℤ^d freeEnergy monotone_subgraph** at Λ-induced subgraph. -/
theorem freeEnergy_monotone_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {G₁ G₂ : SimpleGraph (↑Λ : Type _)}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    IsingModel.freeEnergy G₁ p ≤ IsingModel.freeEnergy G₂ p :=
  IsingModel.freeEnergy_monotone_subgraph h₁₂ p hf

/-- **ℤ^d correlation_convergent_subgraph at Λ-induced**: for a monotone
sequence of subgraphs on `↑Λ` and ferromagnetic `p`,
`n ↦ correlation (Gn n) p A` converges. -/
theorem correlation_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlation (Gn n) p A)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_subgraph Gn hmono p hf A

/-- **ℤ^d magnetization_convergent_subgraph at Λ-induced**. -/
theorem magnetization_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlation (Gn n) p {i})
      Filter.atTop (nhds L) :=
  IsingModel.magnetization_convergent_subgraph Gn hmono p hf i

/-- **ℤ^d twoPoint_convergent_subgraph at Λ-induced**. -/
theorem twoPoint_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlation (Gn n) p {i, j})
      Filter.atTop (nhds L) :=
  IsingModel.twoPoint_convergent_subgraph Gn hmono p hf i j

/-- **ℤ^d `freeEnergy_convergent_subgraph` at Λ-induced subgraph**:
for a monotone sequence of subgraphs `Gn : ℕ → SimpleGraph ↑Λ` and
ferromagnetic `p`, `n ↦ freeEnergy (Gn n) p` converges. -/
theorem freeEnergy_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.freeEnergy (Gn n) p)
      Filter.atTop (nhds L) :=
  IsingModel.freeEnergy_convergent_subgraph Gn hmono p hf

end Ambient
end IsingModel
