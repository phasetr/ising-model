import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer
import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.Inequalities.HighTemp
import IsingModel.LatticeExpSum
import IsingModel.BetaDerivative
import IsingModel.PseudoMass
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Analysis.BoundedVariation

/-!
# Inequalities and §17 lattice mass at ℤ^d

ℤ^d wrappers for:
1. GHS inequality (truncated3 ≤ 0) and Lebowitz inequality (truncated4 ≤ 0)
2. §17.1/§17.5 lattice mass / correlation length

This module also imports
`IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay` to preserve the
legacy `Inequalities` import path for §5.1 conditional and distance-based
cluster-decay wrappers, and
`IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularity` /
`IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity`
to preserve the legacy path for finite-stage correlation and susceptibility
regularity compatibility names. New code should import the narrower child
modules directly for those declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## §17.1 / §17.5 lattice mass / correlation length foundation

The foundational `HasExponentialDecay` and `latticeMass` API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation`. This
module imports it to preserve the legacy `Inequalities` import path.
-/

/-! ## §5.1 / §17.5 high-temperature lattice-mass bounds

The concrete high-temperature `HasExponentialDecay`, lattice-mass bounds,
antitonicity, and tanh lower-bound API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature`. This
module imports it to preserve the legacy `Inequalities` import path.
-/

/-! ## §17.1 / §17.5 pseudo-mass transfer and critical-temperature bridges

The concrete product-summability, critical inverse temperature, pseudo-mass
transfer, and below-critical cluster / summability bridge API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer`.
This module imports it to preserve the legacy `Inequalities` import path.
-/

/-! ## §17.1 d = 0 special case -/

/-- **Vacuous HasExponentialDecay in dimension zero**: for `d = 0`, the lattice
`Fin 0 → ℤ` is a singleton, so there are no distinct pairs `(i, j)`, and
`HasExponentialDecay 0 Λ p α` holds for every `Λ`, `p`, and `α`. -/
private lemma HasExponentialDecay_dim_zero
    (Λ : Ambient.Exhaustion (Fin 0 → ℤ)) (p : IsingParams ℝ) (α : ℝ) :
    HasExponentialDecay 0 Λ p α :=
  ⟨0, le_refl _, fun _i _j hij =>
    absurd (funext (fun x => Fin.elim0 x)) hij⟩

/-- **Lattice mass is `⊤` in dimension zero**: the set of valid decay rates is all of
`NNReal` (vacuous condition), so `latticeMass = sSup (NNReal → ENNReal) = ⊤`. -/
private lemma latticeMass_eq_top_of_dim_zero
    (Λ : Ambient.Exhaustion (Fin 0 → ℤ)) (p : IsingParams ℝ) :
    latticeMass 0 Λ p = ⊤ := by
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  set α : NNReal := b.toNNReal + 1
  have hαmem : (α : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
      {α : NNReal | HasExponentialDecay 0 Λ p (α : ℝ)} :=
    ⟨α, HasExponentialDecay_dim_zero Λ p (α : ℝ), rfl⟩
  have hα_le_b : (α : ENNReal) ≤ b := hb hαmem
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b := ENNReal.coe_toNNReal hb_ne_top
  have hα_eq : (α : ENNReal) = b + 1 := by
    simp only [α, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hα_eq] at hα_le_b
  exact absurd hα_le_b (not_le.mpr (ENNReal.lt_add_right hb_ne_top one_ne_zero))

/-- **Critical inverse temperature is `⊤` in dimension zero** (GJ §17.1):
for `d = 0` (single-site model, no neighbors), the lattice mass is always `⊤ > 0`,
so all `β ≥ 0` are in the high-temperature set and `criticalInverseTemp 0 J = ⊤`.

Physics: a zero-dimensional Ising model has no ferromagnetic interactions and no
phase transition at any temperature; the "critical temperature" is infinite (β_c = ⊤). -/
theorem criticalInverseTemp_eq_top_of_dim_zero (J : ℝ) :
    criticalInverseTemp 0 J = ⊤ := by
  unfold criticalInverseTemp
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  set β₀ : NNReal := b.toNNReal + 1
  have hmass_pos : 0 < latticeMass 0 (cubicExhaustion 0)
      (⟨J, 0, (β₀ : ℝ)⟩ : IsingParams ℝ) := by
    rw [latticeMass_eq_top_of_dim_zero]
    simp
  have hmem : ENNReal.ofReal (β₀ : ℝ) ∈ ENNReal.ofReal ''
      { β : ℝ | 0 ≤ β ∧ 0 < latticeMass 0 (cubicExhaustion 0)
          (⟨J, 0, β⟩ : IsingParams ℝ) } :=
    ⟨(β₀ : ℝ), ⟨NNReal.coe_nonneg _, hmass_pos⟩, rfl⟩
  have hle : ENNReal.ofReal (β₀ : ℝ) ≤ b := hb hmem
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b := ENNReal.coe_toNNReal hb_ne_top
  have hβ₀_eq : ENNReal.ofReal (β₀ : ℝ) = b + 1 := by
    simp only [β₀, ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hβ₀_eq] at hle
  exact absurd hle (not_le.mpr (ENNReal.lt_add_right hb_ne_top one_ne_zero))

/-! ## §17.1 J = 0 special case -/

/-- **Critical inverse temperature is `⊤` when `J = 0`** (GJ §17.1):
for zero coupling constant, `latticeMass = ⊤` for every `β ≥ 0` (either from
`latticeMass_top_of_beta_zero` at `β = 0`, or from `latticeMass_top_of_J_zero` at `β > 0`),
so the defining set is all of `[0,∞)` and `criticalInverseTemp d 0 = ⊤`.

Physics: with no coupling between sites, no phase transition occurs at any finite inverse
temperature (β_c = ⊤ means T_c = 0). This is the J = 0 companion of
`criticalInverseTemp_eq_top_of_dim_zero`. -/
theorem criticalInverseTemp_eq_top_of_J_zero (d : ℕ) :
    criticalInverseTemp d 0 = ⊤ := by
  apply le_antisymm le_top
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  rw [← ENNReal.ofReal_natCast n]
  apply criticalInverseTemp_ge_ofReal_of_latticeMass_pos (Nat.cast_nonneg n)
  rcases n with _ | n
  · rw [Nat.cast_zero, latticeMass_top_of_beta_zero]; exact ENNReal.zero_lt_top
  · have hf : Ferromagnetic (⟨(0 : ℝ), (0 : ℝ), (↑(n + 1) : ℝ)⟩ : IsingParams ℝ) :=
      ⟨le_refl _, le_refl _, by positivity⟩
    rw [latticeMass_top_of_J_zero d (cubicExhaustion d) 0 _ hf]
    exact ENNReal.zero_lt_top

/-! ## §17.1 Finite susceptibility below critical inverse temperature (Step 149) -/

/-- **Susceptibility bounded above in the high-temperature regime** (GJ §17.1, ℤ^d):
for `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J` (high temperature,
i.e., above the critical temperature `T_c = 1/β_c`),
`susceptibilityInfinite (latticeGraph d) Λ ⟨J,0,β⟩ i`
`  ≤ ∑' j, truncated2Infinite (latticeGraph d) Λ ⟨J,0,β⟩ i j`.

Combines `susceptibilityInfinite_le_tsum_truncated2Infinite` (Step 148, `HighTemp.lean`)
with `truncated2Infinite_summable_of_lt_criticalInverseTemp` (Step 147) to give a concrete
finite upper bound on the susceptibility in the high-temperature regime.

**Physics**: the quantity `∑' j, truncated2Infinite ... i j` (the tsum of the Ursell
2-point function) provides a finite upper bound on the magnetic susceptibility,
a hallmark of the paramagnetic (disordered) phase (β < β_c = criticalInverseTemp).
GJ §17.1 motivates this finiteness as the defining property of exponential clustering. -/
theorem susceptibilityInfinite_latticeGraph_le_tsum_of_lt_criticalInverseTemp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i
      ≤ ∑' j : Fin d → ℤ,
          truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) i j := by
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · -- β = 0: susceptibilityInfinite = 0 and ∑' = 0
    simp only [susceptibilityInfinite_eq_ciSup]
    apply ciSup_le; intro n
    simp only [susceptibilityAlongExhaustion]
    split_ifs with hi
    · rw [susceptibilityΛ_apply, susceptibility_apply]
      simp only [truncated2_beta_zero, Finset.sum_const_zero]
      exact tsum_nonneg (fun j => by rw [truncated2Infinite_beta_zero])
    · exact tsum_nonneg (fun j => by rw [truncated2Infinite_beta_zero])
  · exact susceptibilityInfinite_le_tsum_truncated2Infinite (IsingModel.latticeGraph d) Λ
        ⟨hJ, le_refl _, hβ_pos⟩ i
        (truncated2Infinite_summable_of_lt_criticalInverseTemp Λ hβ_pos.le hJ h i)

/-- **β-derivative bound for two-point function on ℤ^d** (Step 157, GJ §17.5):
For the induced lattice graph on any finite Λ ⊆ ℤ^d, vertices r ≠ s in ↑Λ,
the β-derivative of `correlation G ⟨J,0,β'⟩ {r,s}` is bounded by the Lebowitz sum
plus the uniform constant `J * 4d`.

Combines `correlation_beta_deriv_le_lebowitz_tight` (Step 154) with
`incidentEdgesFinset_inducedLatticeGraph_card_le` (Step 155): the incident-edge
term `J * |{e: r∈e ∨ s∈e}|` is at most `J * 4d`, uniform in |Λ|.

Reference: Glimm–Jaffe §17.5 pp.311–312. -/
theorem inducedLatticeGraph_beta_deriv_le
    {d : ℕ} (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (r s : ↑Λ) (hrs : r ≠ s) :
    ∃ dval : ℝ,
      HasDerivAt (fun β' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) dval β ∧
      dval ≤ J * ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
            Sym2.lift ⟨fun u v =>
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {s, u},
              fun u v => by ring⟩ e
        + J * (4 * ↑d) := by
  set G := inducedGraph (IsingModel.latticeGraph d) Λ
  obtain ⟨dval, hd, hbound⟩ :=
    IsingModel.correlation_beta_deriv_le_lebowitz_tight G J β hJ hβ r s hrs
  refine ⟨dval, hd, ?_⟩
  have h_cast : (↑(G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)).card : ℝ) ≤ 4 * ↑d := by
    exact_mod_cast incidentEdgesFinset_inducedLatticeGraph_card_le d Λ r s
  linarith [mul_le_mul_of_nonneg_left h_cast hJ]

/-- **J-derivative bound for two-point function on ℤ^d** (Step 218):
For the induced lattice graph on any finite Λ ⊆ ℤ^d, vertices r ≠ s in ↑Λ,
the J-derivative of `correlation G ⟨J',0,β⟩ {r,s}` at h = 0 is bounded by the
Lebowitz sum plus the uniform constant `β * 4d`.

Combines `correlation_J_deriv_le_lebowitz_tight` (Step 217) with
`incidentEdgesFinset_inducedLatticeGraph_card_le` (Step 155): the incident-edge
term `β * |{e: r∈e ∨ s∈e}|` is at most `β * 4d`, uniform in |Λ|.

Direct J-direction analogue of `inducedLatticeGraph_beta_deriv_le` (Step 157).

Reference: parallel to Glimm–Jaffe §17.5 pp.311–312. -/
theorem inducedLatticeGraph_J_deriv_le
    {d : ℕ} (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (r s : ↑Λ) (hrs : r ≠ s) :
    ∃ dval : ℝ,
      HasDerivAt (fun J' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J', 0, β⟩ : IsingParams ℝ) {r, s}) dval J ∧
      dval ≤ β * ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
            Sym2.lift ⟨fun u v =>
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {s, u},
              fun u v => by ring⟩ e
        + β * (4 * ↑d) := by
  set G := inducedGraph (IsingModel.latticeGraph d) Λ
  obtain ⟨dval, hd, hbound⟩ :=
    IsingModel.correlation_J_deriv_le_lebowitz_tight G J β hJ hβ r s hrs
  refine ⟨dval, hd, ?_⟩
  have h_cast : (↑(G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)).card : ℝ) ≤ 4 * ↑d := by
    exact_mod_cast incidentEdgesFinset_inducedLatticeGraph_card_le d Λ r s
  linarith [mul_le_mul_of_nonneg_left h_cast hβ.le]

/-- **Bridge: finite-vol correlation ≤ ∞-vol correlation** (Step 158, GJ §17.5):
For any exhaustion Λ of ℤ^d, stage n, and vertices r, s : ↑(Λ.volume n),
the induced-graph correlation is bounded above by the infinite-volume correlation:
```
correlation (inducedGraph (latticeGraph d) Λ_n) ⟨J, 0, β⟩ {r, s}
  ≤ correlationInfinite (latticeGraph d) Λ ⟨J, 0, β⟩ {r.val, s.val}
```

Proof: `correlation G_n p {r,s} = correlationAlongExhaustion G Λ p {r.val,s.val} n`
(by unfolding the exhaustion definition and showing `liftFinset {r.val,s.val} h = {r,s}`)
then apply `correlationAlongExhaustion_le_correlationInfinite`.

Used to bound the Lebowitz sum from Step 157 by the ∞-vol susceptibility.

Reference: Glimm–Jaffe §17.5. -/
theorem correlation_inducedLatticeGraph_le_correlationInfinite
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (n : ℕ) (r s : ↑(Λ.volume n)) :
    IsingModel.correlation
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s}
      ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {r.val, s.val} := by
  have h_sub : {r.val, s.val} ⊆ Λ.volume n :=
    Finset.insert_subset r.2 (Finset.singleton_subset_iff.mpr s.2)
  have heq : IsingModel.correlation
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s}
      = Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {r.val, s.val} n := by
    rw [Ambient.correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
    congr 1
    ext x
    simp only [Ambient.mem_liftFinset, Finset.mem_insert, Finset.mem_singleton,
               Subtype.ext_iff]
  rw [heq]
  exact Ambient.correlationAlongExhaustion_le_correlationInfinite _ _ _ _ _


/-! ## Step 160: Lebowitz sum ≤ product of correlation sums (GJ §17.5) -/

/-- **Dart injection bound** (Step 160 helper): for non-negative `f g : V → ℝ`,
`∑ d : G.Dart, f d.fst * g d.snd ≤ (∑ u, f u) * (∑ v, g v)`.

Proof: the dart-to-pair map `d ↦ (d.fst, d.snd)` injects into `V × V`; adding the
non-negative non-dart pairs to the sum only increases it. -/
private lemma sum_dart_le_mul_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f g : V → ℝ) (hf : ∀ v, 0 ≤ f v) (hg : ∀ v, 0 ≤ g v) :
    ∑ d : G.Dart, f d.fst * g d.snd ≤ (∑ u : V, f u) * (∑ v : V, g v) := by
  classical
  -- Expand RHS to double sum
  rw [Fintype.sum_mul_sum]
  -- Group LHS darts by fst vertex
  rw [(Finset.sum_fiberwise_of_maps_to (fun (d : G.Dart) _ => Finset.mem_univ d.fst)
       (fun d => f d.fst * g d.snd)).symm]
  apply Finset.sum_le_sum
  intro u _
  -- Replace f d.fst by f u (using filter condition d.fst = u), then factor
  have h1 : ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u), f d.fst * g d.snd
      = ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u), f u * g d.snd :=
    Finset.sum_congr rfl (fun d hd => by rw [(Finset.mem_filter.mp hd).2])
  rw [h1, ← Finset.mul_sum, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hf u)
  -- Bound ∑_{d: d.fst=u} g(d.snd) ≤ ∑_v g v via image
  have hinj : ∀ d₁ ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u),
      ∀ d₂ ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u),
      d₁.snd = d₂.snd → d₁ = d₂ := by
    intro d₁ hd₁ d₂ hd₂ h
    exact SimpleGraph.Dart.ext d₁ d₂ (Prod.ext
      ((Finset.mem_filter.mp hd₁).2.trans (Finset.mem_filter.mp hd₂).2.symm) h)
  calc ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u), g d.snd
      = ∑ v ∈ (Finset.univ.filter (fun d : G.Dart => d.fst = u)).image (fun d => d.snd), g v := by
          rw [← Finset.sum_image hinj]
      _ ≤ ∑ v : V, g v := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro v _; exact Finset.mem_univ v
          · intro v _ _; exact hg v

/-- **Lebowitz sum bounded by product of correlation sums** (Step 160, GJ §17.5):
For the induced ℤ^d lattice graph on `Λ`,
```
∑_{e ∈ E(G)} (corr(r,u)·corr(s,v) + corr(r,v)·corr(s,u))
  ≤ (∑_j corr(r,j)) · (∑_j corr(s,j))
```

Proof: apply the dart product sum identity (`sum_edgeFinset_sym2_lift_prod_eq_sum_dart`),
then bound the dart sum by the full Cartesian product via the injectivity of
`d ↦ (d.fst, d.snd)` and GKS non-negativity.

Reference: Glimm–Jaffe §17.5. -/
theorem inducedLatticeGraph_leb_sum_le_corr_sum_mul
    {d : ℕ} (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (r s : ↑Λ) :
    let G := inducedGraph (IsingModel.latticeGraph d) Λ
    let p := (⟨J, 0, β⟩ : IsingParams ℝ)
    ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
            IsingModel.correlation G p {r, u} * IsingModel.correlation G p {s, v} +
            IsingModel.correlation G p {r, v} * IsingModel.correlation G p {s, u},
            fun u v => by ring⟩ e
    ≤ (∑ j : ↑Λ, IsingModel.correlation G p {r, j}) *
      (∑ j : ↑Λ, IsingModel.correlation G p {s, j}) := by
  intro G p
  have hf : Ferromagnetic p := ⟨hJ, le_refl 0, hβ⟩
  have hcorr_nn : ∀ (x y : ↑Λ), 0 ≤ IsingModel.correlation G p {x, y} :=
    fun x y => gks_first G p hf _
  rw [SimpleGraph.sum_edgeFinset_sym2_lift_prod_eq_sum_dart]
  exact sum_dart_le_mul_sum G
    (fun u => IsingModel.correlation G p {r, u})
    (fun v => IsingModel.correlation G p {s, v})
    (fun u => hcorr_nn r u)
    (fun v => hcorr_nn s v)

/-- **Lebowitz sum bounded by susceptibilityAlongExhaustion product** (Step 161, GJ §17.5):
`∑_{e∈E(G_n)} leb_n(e) ≤ susceptibilityAlongExhaustion_n(r) · susceptibilityAlongExhaustion_n(s)`.

Proof: apply Step 160 + identify `∑_j corr_n(r,j) = susceptibilityAlongExhaustion_n(r.val)`
via `susceptibility_h_zero` + `susceptibilityAlongExhaustion_of_mem`.

Reference: Glimm–Jaffe §17.5. -/
theorem inducedLatticeGraph_leb_sum_le_susc_along
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (n : ℕ) (r s : ↑(Λ.volume n)) :
    ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, u},
            fun u v => by ring⟩ e
    ≤ susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val n *
      susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val n := by
  classical
  set G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n) with hG
  -- Identify ∑_j corr_n(r,j) = susceptibilityAlongExhaustion n r.val via h=0
  have hsusc_r : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val n
      = ∑ j : ↑(Λ.volume n), IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, j} := by
    rw [susceptibilityAlongExhaustion_of_mem _ _ _ r.2, susceptibilityΛ_apply,
        IsingModel.susceptibility_h_zero]
  have hsusc_s : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val n
      = ∑ j : ↑(Λ.volume n), IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {s, j} := by
    rw [susceptibilityAlongExhaustion_of_mem _ _ _ s.2, susceptibilityΛ_apply,
        IsingModel.susceptibility_h_zero]
  rw [hsusc_r, hsusc_s]
  exact inducedLatticeGraph_leb_sum_le_corr_sum_mul (Λ.volume n) J β hJ hβ r s

/-- **Lebowitz sum bounded by susceptibilityInfinite product** (Step 162, GJ §17.5):
Under `BddAbove` for the susceptibility sequences,
`∑_{e∈E(G_n)} leb_n(e) ≤ susceptibilityInfinite_r · susceptibilityInfinite_s`.

Proof: Step 161 + `le_ciSup` (monotone convergence to the supremum).

Reference: Glimm–Jaffe §17.5. -/
theorem inducedLatticeGraph_leb_sum_le_susceptibilityInfinite
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (n : ℕ) (r s : ↑(Λ.volume n))
    (hbdd_r : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val m)))
    (hbdd_s : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val m))) :
    ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, u},
            fun u v => by ring⟩ e
    ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) r.val *
      susceptibilityInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) s.val := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  -- Step 161 bound
  have h161 := inducedLatticeGraph_leb_sum_le_susc_along Λ J β hJ hβ n r s
  -- susc_along_n ≤ susc_∞ via le_ciSup
  have hr : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val n
      ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val := by
    rw [susceptibilityInfinite_eq_ciSup]; exact le_ciSup hbdd_r n
  have hs : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val n
      ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val := by
    rw [susceptibilityInfinite_eq_ciSup]; exact le_ciSup hbdd_s n
  -- Non-negativity
  have hr_nn : 0 ≤ susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val n :=
    susceptibilityAlongExhaustion_nonneg _ _ _ hf _ _
  have hs_nn : 0 ≤ susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val n :=
    susceptibilityAlongExhaustion_nonneg _ _ _ hf _ _
  exact h161.trans (mul_le_mul hr hs hs_nn (hr_nn.trans hr))

/-- **Uniform β-derivative bound via susceptibilityInfinite** (Step 163, GJ §17.5):
For the induced ℤ^d lattice graph (stage n), under `BddAbove` for the susceptibilities:
`d/dβ corr_n(r,s) ≤ J · χ_∞(r) · χ_∞(s) + J · 4d`.

Proof: Step 157 (derivative ≤ J·Σ_leb + J·4d) + Step 162 (Σ_leb ≤ χ_∞² under BddAbove).

Reference: Glimm–Jaffe §17.5 (uniform derivative bound for ∞-vol limit). -/
theorem inducedLatticeGraph_beta_deriv_le_susc_sq
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (hbdd_r : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val m)))
    (hbdd_s : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val m))) :
    ∃ dval : ℝ,
      HasDerivAt (fun β' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) dval β ∧
      dval ≤ J * susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) r.val *
               susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) s.val + J * (4 * ↑d) := by
  -- Step 157: derivative ≤ J * Σ_leb + J * 4d
  obtain ⟨dval, hd, hbound⟩ :=
    inducedLatticeGraph_beta_deriv_le (Λ.volume n) J β hJ hβ r s hrs
  -- Step 162: Σ_leb ≤ χ_∞(r) * χ_∞(s)
  have hleb := inducedLatticeGraph_leb_sum_le_susceptibilityInfinite Λ J β hJ hβ n r s hbdd_r hbdd_s
  refine ⟨dval, hd, ?_⟩
  have h_mul : J * ∑ e ∈ _, _ ≤
        J * (susceptibilityInfinite _ _ _ r.val * susceptibilityInfinite _ _ _ s.val) :=
    mul_le_mul_of_nonneg_left hleb hJ
  linarith

/-- **J-derivative bound by χ_∞² on ℤ^d** (Step 219):
For the induced ℤ^d lattice graph (stage n), under `BddAbove` for the susceptibilities:
`d/dJ corr_n(r,s)|_{h=0} ≤ β · χ_∞(r) · χ_∞(s) + β · 4d`.

Direct J-direction analogue of `inducedLatticeGraph_beta_deriv_le_susc_sq` (Step 163).
Combines Step 218 (`inducedLatticeGraph_J_deriv_le`: derivative ≤ β·Σ_leb + β·4d) with
Step 162 (`inducedLatticeGraph_leb_sum_le_susceptibilityInfinite`: Σ_leb ≤ χ_∞²
under BddAbove). -/
theorem inducedLatticeGraph_J_deriv_le_susc_sq
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (hbdd_r : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val m)))
    (hbdd_s : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val m))) :
    ∃ dval : ℝ,
      HasDerivAt (fun J' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J', 0, β⟩ : IsingParams ℝ) {r, s}) dval J ∧
      dval ≤ β * susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) r.val *
               susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) s.val + β * (4 * ↑d) := by
  obtain ⟨dval, hd, hbound⟩ :=
    inducedLatticeGraph_J_deriv_le (Λ.volume n) J β hJ hβ r s hrs
  have hleb := inducedLatticeGraph_leb_sum_le_susceptibilityInfinite Λ J β hJ hβ n r s hbdd_r hbdd_s
  refine ⟨dval, hd, ?_⟩
  have h_mul : β * ∑ e ∈ _, _ ≤
        β * (susceptibilityInfinite _ _ _ r.val * susceptibilityInfinite _ _ _ s.val) :=
    mul_le_mul_of_nonneg_left hleb hβ.le
  linarith

/-- **Unconditional Lebowitz-sum ≤ χ_∞² under high-temperature condition** (Step 165, GJ §17.5):
For any exhaustion `Λ` of `ℤ^d`, `0 ≤ J`, `0 < β`, `βJ·2d < 1`, vertices `r s ∈ Λ_n`:
`∑_{e ∈ E(G_n)} leb(e) ≤ χ_∞(r) · χ_∞(s)`,
with no explicit `BddAbove` hypothesis (supplied automatically by Step 164).

Proof: Step 164 (`susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp`)
provides `BddAbove`; then Step 162
(`inducedLatticeGraph_leb_sum_le_susceptibilityInfinite`) closes the goal.

Reference: Glimm–Jaffe §17.5 p.~312. -/
theorem inducedLatticeGraph_leb_sum_le_susceptibilityInfinite_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let p := (⟨J, 0, β⟩ : IsingParams ℝ)
    ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v =>
        IsingModel.correlation G p {r, u} * IsingModel.correlation G p {s, v} +
        IsingModel.correlation G p {r, v} * IsingModel.correlation G p {s, u},
        fun u v => by ring⟩ e
    ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ p r.val *
      susceptibilityInfinite (IsingModel.latticeGraph d) Λ p s.val := by
  intro G p
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have hbdd_r :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt r.val
  have hbdd_s :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt s.val
  exact inducedLatticeGraph_leb_sum_le_susceptibilityInfinite Λ J β hJ hβ n r s hbdd_r hbdd_s

/-- **Unconditional β-derivative bound via χ_∞² under high-temperature condition**
(Step 166, GJ §17.5):
For any exhaustion `Λ` of `ℤ^d`, `0 ≤ J`, `0 < β`, `βJ·2d < 1`,
vertices `r ≠ s ∈ Λ_n`:
`d/dβ corr_n(r,s)(β) ≤ J · χ_∞(r) · χ_∞(s) + J · 4d`,
with no explicit `BddAbove` hypothesis.

Proof: Step 164 supplies `BddAbove`; then Step 163
(`inducedLatticeGraph_beta_deriv_le_susc_sq`) closes the goal.

Reference: Glimm–Jaffe §17.5 p.~312. -/
theorem inducedLatticeGraph_beta_deriv_le_susc_sq_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s) :
    ∃ dval : ℝ,
      HasDerivAt (fun β' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) dval β ∧
      dval ≤ J * susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) r.val *
               susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) s.val + J * (4 * ↑d) := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have hlt' : β * J * ↑(2 * d) < 1 := by linarith [mul_comm β J, mul_comm J β]
  have hbdd_r :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt' r.val
  have hbdd_s :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt' s.val
  exact inducedLatticeGraph_beta_deriv_le_susc_sq Λ J β hJ hβ n r s hrs hbdd_r hbdd_s

/-- **Unconditional J-derivative bound under high-temperature condition** (Step 220):
For any exhaustion `Λ` of `ℤ^d`, `0 ≤ J`, `0 < β`, `βJ·2d < 1`,
vertices `r ≠ s ∈ Λ_n`:
`d/dJ corr_n(r,s)(J)|_{h=0} ≤ β · χ_∞(r) · χ_∞(s) + β · 4d`,
with no explicit `BddAbove` hypothesis.

Direct J-direction analogue of Step 166 (`inducedLatticeGraph_beta_deriv_le_susc_sq_high_temp`).
Proof: Step 164 supplies `BddAbove`; then Step 219
(`inducedLatticeGraph_J_deriv_le_susc_sq`) closes the goal. -/
theorem inducedLatticeGraph_J_deriv_le_susc_sq_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s) :
    ∃ dval : ℝ,
      HasDerivAt (fun J' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J', 0, β⟩ : IsingParams ℝ) {r, s}) dval J ∧
      dval ≤ β * susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) r.val *
               susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) s.val + β * (4 * ↑d) := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have hlt' : β * J * ↑(2 * d) < 1 := by linarith [mul_comm β J, mul_comm J β]
  have hbdd_r :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt' r.val
  have hbdd_s :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt' s.val
  exact inducedLatticeGraph_J_deriv_le_susc_sq Λ J β hJ hβ n r s hrs hbdd_r hbdd_s


/-- **Helper**: uniform norm bound for each `corr_n` on `[a, b]` (Step 167, GJ §17.5).

For each stage `n` and any β₁ β₂ ∈ [a, b] (with `0 < a ≤ b` and `bJ·2d < 1`):
`‖corr_n(β₂) - corr_n(β₁)‖ ≤ (J·M² + J·4d) · ‖β₂ - β₁‖`
where `M = bJ·2d/(1-bJ·2d)`.

Proof: MVT (`Convex.norm_image_sub_le_of_norm_deriv_le`).
Each derivative `d_β` satisfies `0 ≤ d_β ≤ C`:
- `d_β ≥ 0`: monotonicity (`correlation_monotoneOn_beta`) + `HasDerivWithinAt.nonneg_of_monotoneOn`.
- `d_β ≤ C`: Step 166 + `susceptibilityInfinite_latticeGraph_le_of_high_temp_gen`. -/
private lemma inducedLatticeGraph_correlation_norm_sub_le
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (β₁ β₂ : ℝ) (h₁ : β₁ ∈ Set.Icc a b) (h₂ : β₂ ∈ Set.Icc a b) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    ‖IsingModel.correlation G (⟨J, 0, β₂⟩ : IsingParams ℝ) {r, s} -
     IsingModel.correlation G (⟨J, 0, β₁⟩ : IsingParams ℝ) {r, s}‖ ≤
    (J * M ^ 2 + J * (4 * ↑d)) * ‖β₂ - β₁‖ := by
  intro G M
  have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
  have hb_pos : 0 < b := ha.trans_le hab
  have hM_nn : 0 ≤ M :=
    div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ) (Nat.cast_nonneg _)) hdenom_b.le
  have hC_nn : 0 ≤ J * M ^ 2 + J * (4 * ↑d) :=
    add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
               (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  apply (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (f := fun β' => IsingModel.correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s})
    (C := J * M ^ 2 + J * (4 * ↑d))
  · -- DifferentiableAt at each β ∈ [a, b]
    intro β _
    exact (IsingModel.hasDerivAt_correlation_beta G J β {r, s}).differentiableAt
  · -- ‖deriv f β‖ ≤ C at each β ∈ [a, b]
    intro β hβ
    -- Get the derivative and its HasDerivAt witness
    obtain ⟨dval, hd, hbound⟩ :=
      inducedLatticeGraph_beta_deriv_le_susc_sq_high_temp Λ J β hJ
        (ha.trans_le hβ.1)
        (by have : β ≤ b := hβ.2; nlinarith [mul_le_mul_of_nonneg_right this
              (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))])
        n r s hrs
    -- deriv f β = dval
    have hdeq : deriv (fun β' => IsingModel.correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) β
                = dval := hd.deriv
    -- dval ≥ 0 from monotonicity
    have hβ_pos : 0 < β := ha.trans_le hβ.1
    have hmono : MonotoneOn
        (fun β' => IsingModel.correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) (Set.Ici 0) :=
      IsingModel.correlation_monotoneOn_beta G J hJ {r, s}
    have hacc : AccPt β (Filter.principal (Set.Ici 0)) := by
      rw [accPt_principal_iff_nhdsWithin]
      exact (right_nhdsWithin_Ioo_neBot hβ_pos).mono
        (nhdsWithin_mono β (fun x hx => ⟨le_of_lt hx.1, ne_of_lt hx.2⟩))
    have hdnn : 0 ≤ dval :=
      hd.hasDerivWithinAt.nonneg_of_monotoneOn hacc hmono
    -- dval ≤ C from susceptibility bound
    have hβJ : 0 ≤ β * J := mul_nonneg hβ_pos.le hJ
    have hlt_β : β * J * ↑(2 * d) < 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hβ.2
                  (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))]
    have hsusc_r : susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val ≤ M := by
      calc susceptibilityInfinite _ Λ _ r.val
          ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
            IsingModel.Ambient.susceptibilityInfinite_latticeGraph_le_of_high_temp_gen
              Λ hβJ hlt_β r.val
        _ ≤ M := by
            have hdenom_β : 0 < 1 - β * J * ↑(2 * d) := by linarith
            rw [div_le_div_iff₀ hdenom_β hdenom_b]
            nlinarith [mul_le_mul_of_nonneg_right hβ.2
                        (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))]
    have hsusc_s : susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val ≤ M := by
      calc susceptibilityInfinite _ Λ _ s.val
          ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
            IsingModel.Ambient.susceptibilityInfinite_latticeGraph_le_of_high_temp_gen
              Λ hβJ hlt_β s.val
        _ ≤ M := by
            have hdenom_β : 0 < 1 - β * J * ↑(2 * d) := by linarith
            rw [div_le_div_iff₀ hdenom_β hdenom_b]
            nlinarith [mul_le_mul_of_nonneg_right hβ.2
                        (mul_nonneg hJ (Nat.cast_nonneg (2 * d)))]
    have hsusc_r_nn : 0 ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val :=
      IsingModel.Ambient.susceptibilityInfinite_nonneg _ Λ _ ⟨hJ, le_refl 0, hβ_pos⟩ _
    have hsusc_s_nn : 0 ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val :=
      IsingModel.Ambient.susceptibilityInfinite_nonneg _ Λ _ ⟨hJ, le_refl 0, hβ_pos⟩ _
    have hdval_le : dval ≤ J * M ^ 2 + J * (4 * ↑d) :=
      calc dval ≤ J * susceptibilityInfinite _ Λ _ r.val *
                  susceptibilityInfinite _ Λ _ s.val + J * (4 * ↑d) := hbound
           _ ≤ J * M ^ 2 + J * (4 * ↑d) := by
                nlinarith [mul_le_mul hsusc_r hsusc_s hsusc_s_nn hM_nn,
                           mul_nonneg hJ (pow_nonneg hM_nn 2)]
    -- Conclude ‖dval‖ ≤ C
    rw [hdeq, Real.norm_of_nonneg hdnn]
    exact hdval_le
  · exact h₁
  · exact h₂

/-- **Helper**: uniform norm bound for each `corr_n` on `[a, b]` in J (Step 221).

For each stage `n` and any J₁ J₂ ∈ [a, b] (with `0 < a ≤ b` and `bβ·2d < 1`):
`‖corr_n(J₂) - corr_n(J₁)‖ ≤ (β·M² + β·4d) · ‖J₂ - J₁‖`
where `M = bβ·2d/(1-bβ·2d)`.

Direct J-direction analogue of `inducedLatticeGraph_correlation_norm_sub_le` (Step 167).
Proof: MVT (`Convex.norm_image_sub_le_of_norm_deriv_le`).
Each derivative `d_J` satisfies `0 ≤ d_J ≤ C`:
- `d_J ≥ 0`: `correlation_monotone_J` at h=0 + `HasDerivWithinAt.nonneg_of_monotoneOn`.
- `d_J ≤ C`: Step 220 + `susceptibilityInfinite_latticeGraph_le_of_high_temp_gen`. -/
private lemma inducedLatticeGraph_correlation_norm_sub_le_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (J₁ J₂ : ℝ) (h₁ : J₁ ∈ Set.Icc a b) (h₂ : J₂ ∈ Set.Icc a b) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    ‖IsingModel.correlation G (⟨J₂, 0, β⟩ : IsingParams ℝ) {r, s} -
     IsingModel.correlation G (⟨J₁, 0, β⟩ : IsingParams ℝ) {r, s}‖ ≤
    (β * M ^ 2 + β * (4 * ↑d)) * ‖J₂ - J₁‖ := by
  intro G M
  have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
  have hb_pos : 0 < b := ha.trans_le hab
  have hM_nn : 0 ≤ M :=
    div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le) (Nat.cast_nonneg _)) hdenom_b.le
  have hC_nn : 0 ≤ β * M ^ 2 + β * (4 * ↑d) :=
    add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
               (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  apply (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (f := fun J' => IsingModel.correlation G (⟨J', 0, β⟩ : IsingParams ℝ) {r, s})
    (C := β * M ^ 2 + β * (4 * ↑d))
  · intro J _
    exact (IsingModel.hasDerivAt_correlation_J G J 0 β {r, s}).differentiableAt
  · intro J hJ_mem
    obtain ⟨dval, hd, hbound⟩ :=
      inducedLatticeGraph_J_deriv_le_susc_sq_high_temp Λ J β
        (le_of_lt (ha.trans_le hJ_mem.1))
        hβ
        (by have : J ≤ b := hJ_mem.2; nlinarith [mul_le_mul_of_nonneg_right this
              (mul_nonneg hβ.le (Nat.cast_nonneg (2 * d)))])
        n r s hrs
    have hdeq : deriv (fun J' => IsingModel.correlation G (⟨J', 0, β⟩ : IsingParams ℝ) {r, s}) J
                = dval := hd.deriv
    have hJ_pos : 0 < J := ha.trans_le hJ_mem.1
    -- Monotonicity in J at h = 0
    have hmono : MonotoneOn
        (fun J' => IsingModel.correlation G (⟨J', 0, β⟩ : IsingParams ℝ) {r, s})
        (Set.Ici 0) :=
      IsingModel.correlation_monotone_J G 0 (le_refl 0) β hβ {r, s}
    have hacc : AccPt J (Filter.principal (Set.Ici 0)) := by
      rw [accPt_principal_iff_nhdsWithin]
      exact (right_nhdsWithin_Ioo_neBot hJ_pos).mono
        (nhdsWithin_mono J (fun x hx => ⟨le_of_lt hx.1, ne_of_lt hx.2⟩))
    have hdnn : 0 ≤ dval :=
      hd.hasDerivWithinAt.nonneg_of_monotoneOn hacc hmono
    have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ_pos.le
    have hlt_J : β * J * ↑(2 * d) < 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hJ_mem.2
                  (mul_nonneg hβ.le (Nat.cast_nonneg (2 * d)))]
    have hsusc_r : susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val ≤ M := by
      calc susceptibilityInfinite _ Λ _ r.val
          ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
            IsingModel.Ambient.susceptibilityInfinite_latticeGraph_le_of_high_temp_gen
              Λ hβJ hlt_J r.val
        _ ≤ M := by
            have hdenom_J : 0 < 1 - β * J * ↑(2 * d) := by linarith
            rw [div_le_div_iff₀ hdenom_J hdenom_b]
            nlinarith [mul_le_mul_of_nonneg_right hJ_mem.2
                        (mul_nonneg hβ.le (Nat.cast_nonneg (2 * d)))]
    have hsusc_s : susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val ≤ M := by
      calc susceptibilityInfinite _ Λ _ s.val
          ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
            IsingModel.Ambient.susceptibilityInfinite_latticeGraph_le_of_high_temp_gen
              Λ hβJ hlt_J s.val
        _ ≤ M := by
            have hdenom_J : 0 < 1 - β * J * ↑(2 * d) := by linarith
            rw [div_le_div_iff₀ hdenom_J hdenom_b]
            nlinarith [mul_le_mul_of_nonneg_right hJ_mem.2
                        (mul_nonneg hβ.le (Nat.cast_nonneg (2 * d)))]
    have hsusc_r_nn : 0 ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val :=
      IsingModel.Ambient.susceptibilityInfinite_nonneg _ Λ _ ⟨hJ_pos.le, le_refl 0, hβ⟩ _
    have hsusc_s_nn : 0 ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val :=
      IsingModel.Ambient.susceptibilityInfinite_nonneg _ Λ _ ⟨hJ_pos.le, le_refl 0, hβ⟩ _
    have hdval_le : dval ≤ β * M ^ 2 + β * (4 * ↑d) :=
      calc dval ≤ β * susceptibilityInfinite _ Λ _ r.val *
                  susceptibilityInfinite _ Λ _ s.val + β * (4 * ↑d) := hbound
           _ ≤ β * M ^ 2 + β * (4 * ↑d) := by
                nlinarith [mul_le_mul hsusc_r hsusc_s hsusc_s_nn hM_nn,
                           mul_nonneg hβ.le (pow_nonneg hM_nn 2)]
    rw [hdeq, Real.norm_of_nonneg hdnn]
    exact hdval_le
  · exact h₁
  · exact h₂

/-- **Infinite-volume two-point function is Lipschitz in β** (Step 168, GJ §17.5):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
`β ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}`
is `C`-Lipschitz on `[a, b]`, with `C = J·M² + J·4d`, `M = bJ·2d/(1-bJ·2d)`.

Proof: for β₁ ≤ β₂ in `[a,b]`:
- Monotonicity: `corr_∞(β₁) ≤ corr_∞(β₂)`.
- Upper bound: for each stage `n`, either `corr_n(β₂) ≤ corr_n(β₁) + C·(β₂-β₁)` (Step 167)
  or `corr_n(β₂) = 0 ≤ corr_∞(β₁) + C·(β₂-β₁)`. Taking `ciSup_le` gives
  `corr_∞(β₂) ≤ corr_∞(β₁) + C·(β₂-β₁)`.
  So `|corr_∞(β₂) - corr_∞(β₁)| = corr_∞(β₂) - corr_∞(β₁) ≤ C·|β₂-β₁|`.

Reference: Glimm–Jaffe §17.5 p.~312. -/
theorem correlationInfinite_lipschitzOnWith_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    LipschitzOnWith ⟨J * M ^ 2 + J * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg (le_of_lt (ha.trans_le hab)) hJ)
                       (Nat.cast_nonneg _)) hdenom_b.le
        exact add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
               (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) := by
  intro M
  have hb_pos : 0 < b := ha.trans_le hab
  have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
  have hM_nn : 0 ≤ M :=
    div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ) (Nat.cast_nonneg _)) hdenom_b.le
  have hC_nn : 0 ≤ J * M ^ 2 + J * (4 * ↑d) :=
    add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
               (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  apply LipschitzOnWith.of_dist_le_mul
  intro β₁ h₁ β₂ h₂
  simp only [Real.dist_eq, NNReal.coe_mk]
  rcases le_total β₁ β₂ with hβ | hβ
  · -- Case β₁ ≤ β₂
    have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_beta
        (IsingModel.latticeGraph d) Λ hJ (le_refl 0) {r_val, s_val}
        (Set.mem_Ioi.mpr (ha.trans_le h₁.1)) (Set.mem_Ioi.mpr (ha.trans_le h₂.1)) hβ
    rw [abs_of_nonpos (sub_nonpos_of_le hmono_inf), neg_sub,
        abs_of_nonpos (sub_nonpos.mpr hβ), neg_sub]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le Λ J hJ a b ha hab hlt
                     n r s hrs' β₁ β₂ h₁ h₂
      have hmono_n := IsingModel.correlation_monotoneOn_beta
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) J hJ {r, s}
          (Set.mem_Ici.mpr (ha.trans_le h₁.1).le)
          (Set.mem_Ici.mpr (ha.trans_le h₂.1).le) hβ
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hβ)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J, 0, β₁⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J, 0, β₁⟩ : IsingParams ℝ)
          ⟨hJ, le_refl 0, ha.trans_le h₁.1⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hβ)]
  · -- Case β₂ ≤ β₁: symmetric
    have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_beta
        (IsingModel.latticeGraph d) Λ hJ (le_refl 0) {r_val, s_val}
        (Set.mem_Ioi.mpr (ha.trans_le h₂.1)) (Set.mem_Ioi.mpr (ha.trans_le h₁.1)) hβ
    rw [abs_of_nonneg (sub_nonneg_of_le hmono_inf),
        abs_of_nonneg (sub_nonneg.mpr hβ)]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le Λ J hJ a b ha hab hlt
                     n r s hrs' β₂ β₁ h₂ h₁
      have hmono_n := IsingModel.correlation_monotoneOn_beta
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) J hJ {r, s}
          (Set.mem_Ici.mpr (ha.trans_le h₂.1).le)
          (Set.mem_Ici.mpr (ha.trans_le h₁.1).le) hβ
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hβ)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J, 0, β₂⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
          ⟨hJ, le_refl 0, ha.trans_le h₂.1⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hβ)]

/-- **Infinite-volume two-point function is Lipschitz in J** (Step 222):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
`J ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}`
is `C`-Lipschitz on `[a, b]`, with `C = β·M² + β·4d`, `M = bβ·2d/(1-bβ·2d)`.

Direct J-direction analogue of Step 168. Proof: for J₁ ≤ J₂ in `[a,b]`:
- Monotonicity in J: `corr_∞(J₁) ≤ corr_∞(J₂)`.
- For each stage `n`, either `corr_n(J₂) ≤ corr_n(J₁) + C·(J₂-J₁)` (Step 221)
  or `corr_n(J₂) = 0 ≤ corr_∞(J₁) + C·(J₂-J₁)`. Take `ciSup_le`. -/
theorem correlationInfinite_lipschitzOnWith_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    LipschitzOnWith ⟨β * M ^ 2 + β * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg (le_of_lt (ha.trans_le hab)) hβ.le)
                       (Nat.cast_nonneg _)) hdenom_b.le
        exact add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
               (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) := by
  intro M
  have hb_pos : 0 < b := ha.trans_le hab
  have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
  have hM_nn : 0 ≤ M :=
    div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le) (Nat.cast_nonneg _)) hdenom_b.le
  have hC_nn : 0 ≤ β * M ^ 2 + β * (4 * ↑d) :=
    add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
               (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  apply LipschitzOnWith.of_dist_le_mul
  intro J₁ h₁ J₂ h₂
  simp only [Real.dist_eq, NNReal.coe_mk]
  rcases le_total J₁ J₂ with hJ_le | hJ_le
  · have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_J
        (IsingModel.latticeGraph d) Λ (le_refl 0) hβ {r_val, s_val}
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1)))
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1))) hJ_le
    rw [abs_of_nonpos (sub_nonpos_of_le hmono_inf), neg_sub,
        abs_of_nonpos (sub_nonpos.mpr hJ_le), neg_sub]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le_J Λ β hβ a b ha hab hlt
                     n r s hrs' J₁ J₂ h₁ h₂
      have hmono_n := IsingModel.correlation_monotone_J
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 (le_refl 0) β hβ {r, s}
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1)))
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1))) hJ_le
      simp only [correlationJ] at hmono_n
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hJ_le)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J₁, 0, β⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J₁, 0, β⟩ : IsingParams ℝ)
          ⟨le_of_lt (ha.trans_le h₁.1), le_refl 0, hβ⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hJ_le)]
  · -- Case J₂ ≤ J₁: symmetric
    have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_J
        (IsingModel.latticeGraph d) Λ (le_refl 0) hβ {r_val, s_val}
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1)))
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1))) hJ_le
    rw [abs_of_nonneg (sub_nonneg_of_le hmono_inf),
        abs_of_nonneg (sub_nonneg.mpr hJ_le)]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le_J Λ β hβ a b ha hab hlt
                     n r s hrs' J₂ J₁ h₂ h₁
      have hmono_n := IsingModel.correlation_monotone_J
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 (le_refl 0) β hβ {r, s}
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1)))
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1))) hJ_le
      simp only [correlationJ] at hmono_n
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hJ_le)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J₂, 0, β⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J₂, 0, β⟩ : IsingParams ℝ)
          ⟨le_of_lt (ha.trans_le h₂.1), le_refl 0, hβ⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hJ_le)]

/-- **Continuity of infinite-volume two-point function in β** (Step 169, GJ §17.5):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
`β ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}` is continuous on `[a, b]`.

Follows immediately from the Lipschitz bound of Step 168.

Reference: Glimm–Jaffe §17.5 p.~312. -/
theorem correlationInfinite_continuousOn_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    ContinuousOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) :=
  (correlationInfinite_lipschitzOnWith_beta_of_high_temp Λ r_val s_val hrs J hJ a b ha hab
    hlt).continuousOn

/-- **Continuity of infinite-volume two-point function in J** (Step 223):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
`J ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}` is continuous on `[a, b]`.

Direct J-direction analogue of Step 169. Follows immediately from Step 222
(`correlationInfinite_lipschitzOnWith_J_of_high_temp`). -/
theorem correlationInfinite_continuousOn_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    ContinuousOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) :=
  (correlationInfinite_lipschitzOnWith_J_of_high_temp Λ r_val s_val hrs β hβ a b ha hab
    hlt).continuousOn

/-- **Uniform convergence of finite-volume correlations** (Step 170, GJ §17.5):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
the finite-volume two-point functions converge uniformly on `[a, b]`:
`∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ β ∈ [a,b], |corr_n(β) - corr_∞(β)| < ε`.

In Lean: `TendstoUniformlyOn (fun n β => corr_n(β)) (fun β => corr_∞(β)) atTop (Set.Icc a b)`.

Proof: Dini's theorem (`tendstoUniformlyOn_of_forall_tendsto`) on the compact set `[a, b]`:
1. Each `β ↦ corr_n(β)` is continuous on `[a,b]` (Step 117a for finite-vol case,
   constant 0 otherwise).
2. For each `β ∈ [a,b]`, `n ↦ corr_n(β)` is monotone (`correlationAlongExhaustion_monotone`).
3. The limit `β ↦ corr_∞(β)` is continuous on `[a,b]` (Step 169).
4. Pointwise convergence (`correlationAlongExhaustion_tendsto_ciSup`).

Reference: Glimm–Jaffe §17.5 p.~312 (monotone convergence to thermodynamic limit). -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n β => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc a b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · -- (1) Continuity of each corr_n in β
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      -- Each β ↦ correlation G_n ⟨J,0,β⟩ {r,s} is continuous (Step 117a)
      intro β _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun β' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext β'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact IsingModel.correlation_continuousAt_beta _ J β _
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · -- (2) Monotone in n for each β ∈ [a, b]
    intro β hβ
    exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ, le_refl 0, ha.trans_le hβ.1⟩ {r_val, s_val}
  · -- (3) Continuity of the limit (Step 169)
    exact correlationInfinite_continuousOn_beta_of_high_temp Λ r_val s_val hrs J hJ a b ha hab hlt
  · -- (4) Pointwise convergence
    intro β hβ
    have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨hJ, le_refl 0, ha.trans_le hβ.1⟩
    have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
      (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
    simp only [correlationInfinite_eq_ciSup]
    exact htend

/-- **Uniform convergence of finite-volume correlations in J** (Step 224):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
the finite-volume two-point functions converge uniformly on `[a, b]` in J.

Direct J-direction analogue of Step 170. Proof: Dini's theorem on the compact `[a, b]`:
1. Each `J ↦ corr_n(J)` is continuous (Step 207 + `.continuousAt`).
2. `n ↦ corr_n(J)` is monotone (`correlationAlongExhaustion_monotone`).
3. Limit `J ↦ corr_∞(J)` is continuous (Step 223).
4. Pointwise convergence (`correlationAlongExhaustion_tendsto_ciSup`). -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n J => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc a b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro J _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J', 0, β⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun J' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J', 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext J'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact (IsingModel.correlation_continuous_J _ 0 β _).continuousAt
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · intro J hJ_mem
    exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ)
      ⟨le_of_lt (ha.trans_le hJ_mem.1), le_refl 0, hβ⟩ {r_val, s_val}
  · exact correlationInfinite_continuousOn_J_of_high_temp Λ r_val s_val hrs β hβ a b ha hab hlt
  · intro J hJ_mem
    have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨le_of_lt (ha.trans_le hJ_mem.1), le_refl 0, hβ⟩
    have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
      (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
    simp only [correlationInfinite_eq_ciSup]
    exact htend

/-- **A.e. differentiability of infinite-volume two-point function in β** (Step 171):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
the infinite-volume two-point function `β ↦ corr_∞(β)` is differentiable within `[a,b]`
at Lebesgue-almost every `β ∈ [a,b]`.

Proof: direct from Step 168 (`correlationInfinite_lipschitzOnWith_beta_of_high_temp`)
via Rademacher's theorem (`LipschitzOnWith.ae_differentiableWithinAt_real`).

Analytic corollary of the Lipschitz bound established in the GJ §17.5 derivative program.
Not yet the full everywhere-differentiability claimed by GJ §17.6 Thm 17.6.1 p.313
(that requires uniform convergence of the derivative sequence). -/
theorem correlationInfinite_ae_differentiableWithinAt_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc a b),
    DifferentiableWithinAt ℝ
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) β := by
  have hlip := correlationInfinite_lipschitzOnWith_beta_of_high_temp
    Λ r_val s_val hrs J hJ a b ha hab hlt
  exact LipschitzOnWith.ae_differentiableWithinAt_real hlip measurableSet_Icc

/-- **A.e. differentiability of infinite-volume two-point function in J** (Step 225):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
`J ↦ corr_∞(J)` is differentiable within `[a, b]` at Lebesgue-a.e. J.

Direct J-direction analogue of Step 171. Proof: Step 222 (Lipschitz) +
Rademacher's theorem (`LipschitzOnWith.ae_differentiableWithinAt_real`). -/
theorem correlationInfinite_ae_differentiableWithinAt_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc a b),
    DifferentiableWithinAt ℝ
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) J := by
  have hlip := correlationInfinite_lipschitzOnWith_J_of_high_temp
    Λ r_val s_val hrs β hβ a b ha hab hlt
  exact LipschitzOnWith.ae_differentiableWithinAt_real hlip measurableSet_Icc

/-- **Locally bounded variation of corr_∞ on the open high-temperature interval** (Step 172):
For `0 < J`, `1 ≤ d`, the function `β ↦ corr_∞(β)` has locally bounded variation on
the open interval `Ioo 0 (1/(J·2d))` (the high-temperature region).

Proof: For any `a, b ∈ Ioo 0 (1/(J·2d))` with `a ≤ b`, Step 168 gives
`LipschitzOnWith` on `Icc a b`, which implies `LocallyBoundedVariationOn` on `Icc a b`.
Restricted to `Ioo 0 (1/(J·2d)) ∩ Icc a b ⊆ Icc a b` it remains bounded variation. -/
theorem correlationInfinite_locallyBoundedVariationOn_beta_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    LocallyBoundedVariationOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  intro a b ha hb
  by_cases hab : a ≤ b
  · -- a ≤ b: apply Step 168 on Icc a b
    have ha_pos : 0 < a := ha.1
    have hb_lt : b < 1 / (J * ↑(2 * d)) := hb.2
    have hlt : b * J * ↑(2 * d) < 1 := by
      have h1 : b * (J * ↑(2 * d)) < 1 := by
        have := (lt_div_iff₀ hJ2d_pos).mp hb_lt
        linarith [this]
      linarith [h1]
    have hlip := correlationInfinite_lipschitzOnWith_beta_of_high_temp
      Λ r_val s_val hrs J hJ_pos.le a b ha_pos hab hlt
    have hbv_local := hlip.locallyBoundedVariationOn
    have hbv := hbv_local a b
      (Set.mem_Icc.mpr ⟨le_refl a, hab⟩)
      (Set.mem_Icc.mpr ⟨hab, le_refl b⟩)
    -- hbv : BoundedVariationOn corr_∞ (Icc a b ∩ Icc a b)
    rw [Set.inter_self] at hbv
    -- Need: BoundedVariationOn corr_∞ (Ioo 0 β_c ∩ Icc a b)
    exact hbv.mono Set.inter_subset_right
  · -- a > b: Icc a b is empty, hence intersection is empty
    have hba : b < a := lt_of_not_ge hab
    have hempty : Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) ∩ Set.Icc a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x ⟨_, hx_in⟩
      exact absurd (hx_in.1.trans hx_in.2) (not_le.mpr hba)
    -- BoundedVariationOn on empty set: variation is 0, hence ≠ ⊤
    have : BoundedVariationOn
        (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
        (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) ∩ Set.Icc a b) := by
      rw [hempty]
      have hev : eVariationOn (fun β =>
          correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) (∅ : Set ℝ) = 0 :=
        eVariationOn.subsingleton _ Set.subsingleton_empty
      simp [BoundedVariationOn]
    exact this

/-- **A.e. differentiability of corr_∞ on the open high-temperature interval** (Step 172):
For `0 < J`, `1 ≤ d`, the function `β ↦ corr_∞(β)` is differentiable within
`Ioo 0 (1/(J·2d))` at Lebesgue-a.e. β.

Proof: Step 172 (`correlationInfinite_locallyBoundedVariationOn_beta_of_high_temp`) +
`LocallyBoundedVariationOn.ae_differentiableWithinAt`. -/
theorem correlationInfinite_ae_differentiableWithinAt_beta_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))),
    DifferentiableWithinAt ℝ
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) β := by
  have hbv := correlationInfinite_locallyBoundedVariationOn_beta_of_high_temp
    hd Λ r_val s_val hrs J hJ_pos
  exact LocallyBoundedVariationOn.ae_differentiableWithinAt hbv measurableSet_Ioo

/-- **Locally bounded variation of corr_∞ on Ioo 0 J_c in J** (Step 226):
For `0 < β`, `1 ≤ d`, `J ↦ corr_∞(J)` has locally bounded variation on the open
high-temperature interval `Ioo 0 (1/(β·2d))`.

Direct J-direction analogue of Step 172. Proof: for any `[a, b] ⊂ Ioo 0 (1/(β·2d))`,
Step 222 gives Lipschitz, which implies LocallyBoundedVariationOn. -/
theorem correlationInfinite_locallyBoundedVariationOn_J_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    LocallyBoundedVariationOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hβ2d_pos : 0 < β * ↑(2 * d) := mul_pos hβ_pos h2d_pos
  intro a b ha hb
  by_cases hab : a ≤ b
  · have ha_pos : 0 < a := ha.1
    have hb_lt : b < 1 / (β * ↑(2 * d)) := hb.2
    have hlt : b * β * ↑(2 * d) < 1 := by
      have h1 : b * (β * ↑(2 * d)) < 1 := by
        have := (lt_div_iff₀ hβ2d_pos).mp hb_lt
        linarith [this]
      linarith [h1]
    have hlip := correlationInfinite_lipschitzOnWith_J_of_high_temp
      Λ r_val s_val hrs β hβ_pos a b ha_pos hab hlt
    have hbv_local := hlip.locallyBoundedVariationOn
    have hbv := hbv_local a b
      (Set.mem_Icc.mpr ⟨le_refl a, hab⟩)
      (Set.mem_Icc.mpr ⟨hab, le_refl b⟩)
    rw [Set.inter_self] at hbv
    exact hbv.mono Set.inter_subset_right
  · have hba : b < a := lt_of_not_ge hab
    have hempty : Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) ∩ Set.Icc a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x ⟨_, hx_in⟩
      exact absurd (hx_in.1.trans hx_in.2) (not_le.mpr hba)
    have : BoundedVariationOn
        (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
        (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) ∩ Set.Icc a b) := by
      rw [hempty]
      have hev : eVariationOn (fun J =>
          correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) (∅ : Set ℝ) = 0 :=
        eVariationOn.subsingleton _ Set.subsingleton_empty
      simp [BoundedVariationOn]
    exact this

/-- **A.e. differentiability of corr_∞ on Ioo 0 J_c in J** (Step 226):
For `0 < β`, `1 ≤ d`, `J ↦ corr_∞(J)` is differentiable within `Ioo 0 (1/(β·2d))` at
Lebesgue-a.e. J.

Direct J-direction analogue of Step 172 (open). -/
theorem correlationInfinite_ae_differentiableWithinAt_J_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume
      (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))),
    DifferentiableWithinAt ℝ
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) J := by
  have hbv := correlationInfinite_locallyBoundedVariationOn_J_of_high_temp
    hd Λ r_val s_val hrs β hβ_pos
  exact LocallyBoundedVariationOn.ae_differentiableWithinAt hbv measurableSet_Ioo

/-- **Continuity of corr_∞ on the open high-temperature interval** (Step 173):
For `0 < J`, `1 ≤ d`, the function `β ↦ corr_∞(β)` is continuous on the open
high-temperature interval `Ioo 0 (1/(J·2d))`.

Proof: For each β₀ in the open interval, choose a closed neighborhood `[a, b]`
inside the open interval. Step 169 gives continuity on `[a, b]`, hence at β₀.
Aggregating over β₀ gives continuity on the entire open interval. -/
theorem correlationInfinite_continuousOn_beta_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ContinuousOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  intro β₀ hβ₀
  have hβ₀_pos : 0 < β₀ := hβ₀.1
  have hβ₀_lt : β₀ < 1 / (J * ↑(2 * d)) := hβ₀.2
  -- Choose a closed neighborhood [a, b] with a < β₀ < b inside the open interval
  -- Pick a = β₀/2 and b = (β₀ + βc)/2 where βc = 1/(J·2d)
  have ha_pos : 0 < β₀ / 2 := by positivity
  have ha_lt_β₀ : β₀ / 2 < β₀ := by linarith
  have hβ₀_lt_b : β₀ < (β₀ + 1 / (J * ↑(2 * d))) / 2 := by linarith
  have hb_lt_βc : (β₀ + 1 / (J * ↑(2 * d))) / 2 < 1 / (J * ↑(2 * d)) := by linarith
  have ha_le_β₀ : β₀ / 2 ≤ β₀ := ha_lt_β₀.le
  have hβ₀_le_b : β₀ ≤ (β₀ + 1 / (J * ↑(2 * d))) / 2 := hβ₀_lt_b.le
  have hab : β₀ / 2 ≤ (β₀ + 1 / (J * ↑(2 * d))) / 2 := ha_le_β₀.trans hβ₀_le_b
  have hlt : (β₀ + 1 / (J * ↑(2 * d))) / 2 * J * ↑(2 * d) < 1 := by
    have h1 : (β₀ + 1 / (J * ↑(2 * d))) / 2 * (J * ↑(2 * d)) < 1 := by
      have := (lt_div_iff₀ hJ2d_pos).mp hb_lt_βc
      linarith [this]
    linarith [h1]
  have hcont_Icc := correlationInfinite_continuousOn_beta_of_high_temp
    Λ r_val s_val hrs J hJ_pos.le (β₀ / 2) ((β₀ + 1 / (J * ↑(2 * d))) / 2) ha_pos hab hlt
  apply ContinuousAt.continuousWithinAt
  have h_Icc_nhd : Set.Icc (β₀ / 2) ((β₀ + 1 / (J * ↑(2 * d))) / 2) ∈ nhds β₀ :=
    Icc_mem_nhds ha_lt_β₀ hβ₀_lt_b
  exact (hcont_Icc β₀ ⟨ha_le_β₀, hβ₀_le_b⟩).continuousAt h_Icc_nhd

/-- **Continuity of corr_∞ on Ioo 0 J_c in J** (Step 227):
For `0 < β`, `1 ≤ d`, `J ↦ corr_∞(J)` is continuous on the open
high-temperature interval `Ioo 0 (1/(β·2d))`.

Direct J-direction analogue of Step 173. Proof: for each J₀ in the open interval,
choose `[a, b] ⊂ Ioo 0 (1/(β·2d))` with `J₀ ∈ Ioo a b` (e.g., `a = J₀/2`,
`b = (J₀+J_c)/2`); Step 223 gives continuity on `[a, b]`, hence at J₀. -/
theorem correlationInfinite_continuousOn_J_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ContinuousOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hβ2d_pos : 0 < β * ↑(2 * d) := mul_pos hβ_pos h2d_pos
  intro J₀ hJ₀
  have hJ₀_pos : 0 < J₀ := hJ₀.1
  have hJ₀_lt : J₀ < 1 / (β * ↑(2 * d)) := hJ₀.2
  have ha_pos : 0 < J₀ / 2 := by positivity
  have ha_lt_J₀ : J₀ / 2 < J₀ := by linarith
  have hJ₀_lt_b : J₀ < (J₀ + 1 / (β * ↑(2 * d))) / 2 := by linarith
  have hb_lt_Jc : (J₀ + 1 / (β * ↑(2 * d))) / 2 < 1 / (β * ↑(2 * d)) := by linarith
  have ha_le_J₀ : J₀ / 2 ≤ J₀ := ha_lt_J₀.le
  have hJ₀_le_b : J₀ ≤ (J₀ + 1 / (β * ↑(2 * d))) / 2 := hJ₀_lt_b.le
  have hab : J₀ / 2 ≤ (J₀ + 1 / (β * ↑(2 * d))) / 2 := ha_le_J₀.trans hJ₀_le_b
  have hlt : (J₀ + 1 / (β * ↑(2 * d))) / 2 * β * ↑(2 * d) < 1 := by
    have h1 : (J₀ + 1 / (β * ↑(2 * d))) / 2 * (β * ↑(2 * d)) < 1 := by
      have := (lt_div_iff₀ hβ2d_pos).mp hb_lt_Jc
      linarith [this]
    linarith [h1]
  have hcont_Icc := correlationInfinite_continuousOn_J_of_high_temp
    Λ r_val s_val hrs β hβ_pos (J₀ / 2) ((J₀ + 1 / (β * ↑(2 * d))) / 2) ha_pos hab hlt
  apply ContinuousAt.continuousWithinAt
  have h_Icc_nhd : Set.Icc (J₀ / 2) ((J₀ + 1 / (β * ↑(2 * d))) / 2) ∈ nhds J₀ :=
    Icc_mem_nhds ha_lt_J₀ hJ₀_lt_b
  exact (hcont_Icc J₀ ⟨ha_le_J₀, hJ₀_le_b⟩).continuousAt h_Icc_nhd

/-- **Locally uniform convergence corr_n → corr_∞ on open high-temperature interval** (Step 174):
For `0 < J`, `1 ≤ d`: the finite-volume two-point functions converge locally uniformly to
the infinite-volume limit on the open interval `Ioo 0 (1/(J·2d))`.

Proof: Apply `Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto` (Mathlib Dini) on
the open set `Ioo 0 β_c` using:
1. ContinuousOn of each corr_n (from `correlation_continuousAt_beta`).
2. Monotonicity in n (from `correlationAlongExhaustion_monotone`).
3. ContinuousOn of corr_∞ (Step 173).
4. Pointwise convergence (`correlationAlongExhaustion_tendsto_ciSup`).

Strengthens Step 170 from a fixed compact `[a, b]` to locally uniform on `Ioo 0 β_c`. -/
theorem correlationAlongExhaustion_tendstoLocallyUniformlyOn_beta_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    TendstoLocallyUniformlyOn
      (fun n β => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
  · -- (1) Continuity of each corr_n in β on the open interval
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro β _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun β' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext β'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact IsingModel.correlation_continuousAt_beta _ J β _
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · -- (2) Monotone in n for each β ∈ Ioo 0 β_c
    intro β hβ
    have hβ_pos : 0 < β := hβ.1
    exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · -- (3) Continuity of the limit on Ioo 0 β_c (Step 173)
    exact correlationInfinite_continuousOn_beta_of_high_temp_open hd Λ r_val s_val hrs J hJ_pos
  · -- (4) Pointwise convergence
    intro β hβ
    have hβ_pos : 0 < β := hβ.1
    have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
    have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
      (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
    simp only [correlationInfinite_eq_ciSup]
    exact htend

/-- **Locally uniform convergence of corr_n → corr_∞ on Ioo 0 J_c in J** (Step 228):
For `0 < β`, `1 ≤ d`: corr_n → corr_∞ locally uniformly on `Ioo 0 (1/(β·2d))`.

Direct J-direction analogue of Step 174. Proof:
`Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto` with
(1) ContinuousOn each corr_n in J; (2) Monotonicity in n; (3) ContinuousOn corr_∞ (Step 227);
(4) pointwise convergence. Strengthens Step 224 from compact `[a, b]` to locally uniform on
`Ioo 0 J_c`. -/
theorem correlationAlongExhaustion_tendstoLocallyUniformlyOn_J_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    TendstoLocallyUniformlyOn
      (fun n J => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
  · intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro J _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J', 0, β⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun J' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J', 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext J'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact (IsingModel.correlation_continuous_J _ 0 β _).continuousAt
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · intro J hJ_mem
    have hJ_pos : 0 < J := hJ_mem.1
    exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · exact correlationInfinite_continuousOn_J_of_high_temp_open hd Λ r_val s_val hrs β hβ_pos
  · intro J hJ_mem
    have hJ_pos : 0 < J := hJ_mem.1
    have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
    have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
      (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
    simp only [correlationInfinite_eq_ciSup]
    exact htend

/-- **ContinuousAt of corr_∞ at every β in the open high-temperature interval** (Step 175):
For `0 < J`, `1 ≤ d`, every `β₀ ∈ Ioo 0 (1/(J·2d))`: corr_∞ is continuous at β₀
(as a function ℝ → ℝ, no within-restriction).

Proof: Since `Ioo 0 β_c` is open, it's a neighborhood of any of its points. So
ContinuousOn (Step 173) restricted to a neighborhood gives ContinuousAt. -/
theorem correlationInfinite_continuousAt_beta_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (β₀ : ℝ) (hβ₀ : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ContinuousAt
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      β₀ := by
  have hcont_open := correlationInfinite_continuousOn_beta_of_high_temp_open
    hd Λ r_val s_val hrs J hJ_pos
  have h_nhd : Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) ∈ nhds β₀ :=
    IsOpen.mem_nhds isOpen_Ioo hβ₀
  exact (hcont_open β₀ hβ₀).continuousAt h_nhd

/-- **ContinuousAt of corr_∞ at every J ∈ Ioo 0 J_c** (Step 229):
For `0 < β`, `1 ≤ d`, every `J₀ ∈ Ioo 0 (1/(β·2d))`: corr_∞ is continuous at J₀
(as a function ℝ → ℝ, full neighborhood).

Direct J-direction analogue of Step 175. Proof: open set is a neighborhood of any
interior point ⇒ Step 227 ContinuousOn restricts to ContinuousAt. -/
theorem correlationInfinite_continuousAt_J_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (J₀ : ℝ) (hJ₀ : J₀ ∈ Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) :
    ContinuousAt
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      J₀ := by
  have hcont_open := correlationInfinite_continuousOn_J_of_high_temp_open
    hd Λ r_val s_val hrs β hβ_pos
  have h_nhd : Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) ∈ nhds J₀ :=
    IsOpen.mem_nhds isOpen_Ioo hJ₀
  exact (hcont_open J₀ hJ₀).continuousAt h_nhd

/-- **Per-stage linear bound at β = 0** (Step 176, helper):
For each finite-volume stage `n`, `r ≠ s`, and high-temperature `β ∈ (0, b]` with `bJ·2d < 1`:
`corr_n(r, s, β) ≤ (J·M(b)² + J·4d) · β`.

Proof: For any `0 < a ≤ β`, by Step 167's uniform-in-n Lipschitz on `[a, b]` plus
monotonicity, `corr_n(β) ≤ corr_n(a) + C · β`. Taking `a → 0⁺` and using continuity
of `corr_n` at 0 with `corr_n(0) = 0`, we conclude `corr_n(β) ≤ C · β`. -/
private lemma inducedLatticeGraph_correlation_le_const_mul_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (β : ℝ) (hβ_pos : 0 < β) (hβb : β ≤ b) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      (J * M ^ 2 + J * (4 * ↑d)) * β := by
  intro G M
  set C : ℝ := J * M ^ 2 + J * (4 * ↑d) with hC_def
  -- For each 0 < a ≤ β: corr_n(β) ≤ corr_n(a) + C * (β - a)
  have h_per_a : ∀ a : ℝ, 0 < a → a ≤ β →
      IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s} + C * (β - a) := by
    intro a ha hab
    have h_lip := inducedLatticeGraph_correlation_norm_sub_le Λ J hJ a b ha (hab.trans hβb) hlt
        n r s hrs a β (Set.left_mem_Icc.mpr (hab.trans hβb)) ⟨hab, hβb⟩
    -- h_lip : ‖corr(β) - corr(a)‖ ≤ C * ‖β - a‖ (with let G, let M)
    -- Strip the lets via simp
    simp only at h_lip
    have hβ_minus_a_nonneg : 0 ≤ β - a := by linarith
    have hcorr_diff_nonneg : 0 ≤
        IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s} := by
      have hmono := IsingModel.correlation_monotoneOn_beta G J hJ {r, s}
      have ha_in : a ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr ha.le
      have hβ_in : β ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hβ_pos.le
      linarith [hmono ha_in hβ_in hab]
    have habs1 : ‖IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s}‖ =
        IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s} :=
      Real.norm_of_nonneg hcorr_diff_nonneg
    have habs2 : ‖β - a‖ = β - a := Real.norm_of_nonneg hβ_minus_a_nonneg
    rw [habs1, habs2] at h_lip
    linarith
  -- Now show corr_n(β) ≤ C * β by taking a → 0+
  have h_cont_corr_at_0 : ContinuousAt
      (fun a => IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s}) 0 :=
    IsingModel.correlation_continuousAt_beta G J 0 {r, s}
  have h_corr_at_0 : IsingModel.correlation G (⟨J, 0, 0⟩ : IsingParams ℝ) {r, s} = 0 :=
    IsingModel.correlation_beta_zero_vanish_of_nonempty_A G J 0 {r, s}
      (Finset.insert_nonempty _ _)
  -- The filter nhdsWithin 0 (Ioi 0) is NeBot
  have h_neBot : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  -- g(a) = corr_n(a) + C * (β - a) tends to 0 + C * β = C * β as a → 0+
  have h_g_tendsto : Filter.Tendsto
      (fun a => IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s} + C * (β - a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (C * β)) := by
    have h1 : Filter.Tendsto
        (fun a => IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s})
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have htend := h_cont_corr_at_0.tendsto
      rw [h_corr_at_0] at htend
      exact htend.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto
        (fun a : ℝ => C * (β - a)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (C * β)) := by
      have hf : Continuous fun a : ℝ => C * (β - a) := by
        exact Continuous.mul continuous_const (Continuous.sub continuous_const continuous_id)
      have hcont : Filter.Tendsto (fun a : ℝ => C * (β - a)) (nhds 0) (nhds (C * (β - 0))) :=
        hf.continuousAt (x := (0 : ℝ))
      have heq : C * (β - 0) = C * β := by ring
      rw [heq] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    have hsum := h1.add h2
    simpa using hsum
  -- corr_n(β) ≤ g(a) eventually as a → 0+
  -- Need to restrict to a ≤ β. Use the fact that {a : a ≤ β} contains a neighborhood of 0 in Ioi 0
  have h_eventual : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s} + C * (β - a) := by
    -- Pick the neighborhood {a : a ≤ β} which is in nhds 0 (since 0 < β)
    have h_le : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0), a ≤ β := by
      have h_nhd : Set.Iic β ∈ nhds (0 : ℝ) := Iic_mem_nhds hβ_pos
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h_nhd] with a ha hab
      exact hab
    filter_upwards [self_mem_nhdsWithin, h_le] with a ha hab
    exact h_per_a a ha hab
  exact ge_of_tendsto h_g_tendsto h_eventual

/-- **Linear bound on corr_∞ at β = 0** (Step 176, GJ §17.5):
For `0 ≤ J`, `1 ≤ d`, `0 < b` with `bJ·2d < 1`, and any `r ≠ s`, on the interval `(0, b]`:
`corr_∞(r, s, β) ≤ (J·M(b)² + J·4d) · β`,
where `M(b) = bJ·2d/(1 - bJ·2d)`.

In particular, `corr_∞(r, s, β) → 0` as `β → 0⁺`. -/
theorem correlationInfinite_le_const_mul_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1)
    (β : ℝ) (hβ_pos : 0 < β) (hβb : β ≤ b) :
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤ (J * M ^ 2 + J * (4 * ↑d)) * β := by
  intro M
  set C : ℝ := J * M ^ 2 + J * (4 * ↑d) with hC_def
  have hferro : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ_pos⟩
  -- corr_∞ = ⨆ n, corr_n_along_exhaustion. Use ciSup_le.
  rw [correlationInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  -- For each n: corr_n_along_exhaustion ≤ C * β
  by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · -- Subset case: identify with finite-volume correlation and apply per-stage bound
    have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
    have hsn : s_val ∈ Λ.volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
    have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n =
               IsingModel.correlation
                  (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                ⟨s_val, hsn⟩} := by
      rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
      congr 1
      ext u; rw [mem_liftFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
    rw [heq]
    have hsubsne : (⟨r_val, hrn⟩ : ↑(Λ.volume n)) ≠ ⟨s_val, hsn⟩ :=
      fun h => hrs (congrArg Subtype.val h)
    exact inducedLatticeGraph_correlation_le_const_mul_beta Λ J hJ b hlt n
      ⟨r_val, hrn⟩ ⟨s_val, hsn⟩ hsubsne β hβ_pos hβb
  · -- Non-subset case: corr_n_along_exhaustion = 0
    rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
    have hC_nn : 0 ≤ C := by
      have hb_pos' : 0 < b := hb_pos
      have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
      have hM_nn : 0 ≤ M :=
        div_nonneg (mul_nonneg (mul_nonneg hb_pos'.le hJ) (Nat.cast_nonneg _)) hdenom_b.le
      exact add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
                       (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    exact mul_nonneg hC_nn hβ_pos.le

/-! ## Step 230: linear bound at J = 0 + right-continuity in J -/

/-- **Helper for Step 230**: per-stage finite-volume linear bound at J = 0. -/
private lemma inducedLatticeGraph_correlation_le_const_mul_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hlt : b * β * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (J : ℝ) (hJ_pos : 0 < J) (hJb : J ≤ b) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      (β * M ^ 2 + β * (4 * ↑d)) * J := by
  intro G M
  set C : ℝ := β * M ^ 2 + β * (4 * ↑d) with hC_def
  have h_per_a : ∀ a : ℝ, 0 < a → a ≤ J →
      IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} + C * (J - a) := by
    intro a ha hab
    have h_lip := inducedLatticeGraph_correlation_norm_sub_le_J Λ β hβ a b ha (hab.trans hJb) hlt
        n r s hrs a J (Set.left_mem_Icc.mpr (hab.trans hJb)) ⟨hab, hJb⟩
    simp only at h_lip
    have hJ_minus_a_nonneg : 0 ≤ J - a := by linarith
    have hcorr_diff_nonneg : 0 ≤
        IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} := by
      have hmono := IsingModel.correlation_monotone_J G 0 (le_refl 0) β hβ {r, s}
      have ha_in : a ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr ha.le
      have hJ_in : J ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hJ_pos.le
      have hmono_app : IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} ≤
                       IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} :=
        hmono ha_in hJ_in hab
      linarith
    have habs1 : ‖IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s}‖ =
        IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} :=
      Real.norm_of_nonneg hcorr_diff_nonneg
    have habs2 : ‖J - a‖ = J - a := Real.norm_of_nonneg hJ_minus_a_nonneg
    rw [habs1, habs2] at h_lip
    linarith
  have h_cont_corr_at_0 : ContinuousAt
      (fun a => IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s}) 0 :=
    (IsingModel.correlation_continuous_J G 0 β {r, s}).continuousAt
  have h_corr_at_0 : IsingModel.correlation G (⟨0, 0, β⟩ : IsingParams ℝ) {r, s} = 0 :=
    IsingModel.correlation_zero_params_vanish_of_nonempty_A G β {r, s}
      (Finset.insert_nonempty _ _)
  have h_neBot : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have h_g_tendsto : Filter.Tendsto
      (fun a => IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} + C * (J - a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (C * J)) := by
    have h1 : Filter.Tendsto
        (fun a => IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s})
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have htend := h_cont_corr_at_0.tendsto
      rw [h_corr_at_0] at htend
      exact htend.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto
        (fun a : ℝ => C * (J - a)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (C * J)) := by
      have hf : Continuous fun a : ℝ => C * (J - a) := by
        exact Continuous.mul continuous_const (Continuous.sub continuous_const continuous_id)
      have hcont : Filter.Tendsto (fun a : ℝ => C * (J - a)) (nhds 0) (nhds (C * (J - 0))) :=
        hf.continuousAt (x := (0 : ℝ))
      have heq : C * (J - 0) = C * J := by ring
      rw [heq] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    have hsum := h1.add h2
    simpa using hsum
  have h_eventual : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} + C * (J - a) := by
    have h_le : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0), a ≤ J := by
      have h_nhd : Set.Iic J ∈ nhds (0 : ℝ) := Iic_mem_nhds hJ_pos
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h_nhd] with a ha hab
      exact hab
    filter_upwards [self_mem_nhdsWithin, h_le] with a ha hab
    exact h_per_a a ha hab
  exact ge_of_tendsto h_g_tendsto h_eventual

/-- **Linear bound on corr_∞ at J = 0** (Step 230):
For `0 < β`, `0 < b` with `bβ·2d < 1`, and any `r ≠ s`, on the interval `(0, b]`:
`corr_∞(r, s, J) ≤ (β·M(b)² + β·4d) · J`,
where `M(b) = bβ·2d/(1 - bβ·2d)`.

Direct J-direction analogue of Step 176. As an immediate corollary,
`corr_∞(r, s, J) → 0` as `J → 0⁺` (right-continuity at 0). -/
theorem correlationInfinite_le_const_mul_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1)
    (J : ℝ) (hJ_pos : 0 < J) (hJb : J ≤ b) :
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤ (β * M ^ 2 + β * (4 * ↑d)) * J := by
  intro M
  set C : ℝ := β * M ^ 2 + β * (4 * ↑d) with hC_def
  have hferro : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ_pos.le, le_refl 0, hβ⟩
  rw [correlationInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
    have hsn : s_val ∈ Λ.volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
    have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n =
               IsingModel.correlation
                  (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                ⟨s_val, hsn⟩} := by
      rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
      congr 1
      ext u; rw [mem_liftFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
    rw [heq]
    have hsubsne : (⟨r_val, hrn⟩ : ↑(Λ.volume n)) ≠ ⟨s_val, hsn⟩ :=
      fun h => hrs (congrArg Subtype.val h)
    exact inducedLatticeGraph_correlation_le_const_mul_J Λ β hβ b hlt n
      ⟨r_val, hrn⟩ ⟨s_val, hsn⟩ hsubsne J hJ_pos hJb
  · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
    have hC_nn : 0 ≤ C := by
      have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
      have hM_nn : 0 ≤ M :=
        div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le) (Nat.cast_nonneg _)) hdenom_b.le
      exact add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
                       (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    exact mul_nonneg hC_nn hJ_pos.le

/-- **Helper: corr_∞ vanishes at β = 0 for r ≠ s** (Step 177 helper):
The infinite-volume two-point function at β = 0, h = 0 is zero (since the Boltzmann
weight is constant and the spin product over a non-empty set averages to zero). -/
private lemma correlationInfinite_eq_zero_at_beta_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) :
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      {r_val, s_val} = 0 := by
  rw [correlationInfinite_eq_ciSup]
  apply le_antisymm
  · apply ciSup_le
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} n =
                 IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J, 0, 0⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                  ⟨s_val, hsn⟩} := by
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      rw [IsingModel.correlation_beta_zero_vanish_of_nonempty_A _ J 0 _
            (Finset.insert_nonempty _ _)]
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
  · apply le_ciSup_of_le _ 0
    · by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume 0
      · have hrn : r_val ∈ Λ.volume 0 := Finset.insert_subset_iff.mp h_sub |>.1
        have hsn : s_val ∈ Λ.volume 0 :=
          Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
        have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} 0 =
                   IsingModel.correlation
                      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume 0))
                      (⟨J, 0, 0⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume 0)),
                                                    ⟨s_val, hsn⟩} := by
          rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
          congr 1
          ext u; rw [mem_liftFinset]
          simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        rw [heq]
        rw [IsingModel.correlation_beta_zero_vanish_of_nonempty_A _ J 0 _
              (Finset.insert_nonempty _ _)]
      · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
    · exact ⟨1, fun y hy => by
        obtain ⟨n, rfl⟩ := hy
        exact correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ _ _ _⟩

/-- **ContinuousOn of corr_∞ on closed interval [0, b]** (Step 177):
For `1 ≤ d`, `0 < J`, `0 < b`, `bJ·2d < 1`: `β ↦ corr_∞(r, s, β)` is continuous on `[0, b]`,
extending Step 169 to include β = 0.

Proof: For β > 0 use Step 175 ContinuousAt. For β = 0, use Step 176 squeeze
`0 ≤ corr_∞(β) ≤ C·β` for β ∈ (0, b]. -/
theorem correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    ContinuousOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  have hb_lt_βc : b < 1 / (J * ↑(2 * d)) := by
    rw [lt_div_iff₀ hJ2d_pos]; linarith
  intro β hβ
  rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
  · -- β = 0: right-continuity from Step 176 squeeze
    subst hβ0
    set M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) with hM_def
    set C : ℝ := J * M ^ 2 + J * (4 * ↑d) with hC_def
    have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
    have hM_nn : 0 ≤ M :=
      div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ_pos.le) (Nat.cast_nonneg _)) hdenom_b.le
    have hC_nn : 0 ≤ C :=
      add_nonneg (mul_nonneg hJ_pos.le (pow_nonneg hM_nn 2))
                 (mul_nonneg hJ_pos.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    have h_corr_at_zero : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} = 0 :=
      correlationInfinite_eq_zero_at_beta_zero Λ r_val s_val J
    rw [ContinuousWithinAt]
    show Filter.Tendsto _ _ (nhds _)
    rw [h_corr_at_zero]
    -- Need: Tendsto (fun β => corr_∞(β)) (𝓝[Icc 0 b] 0) (𝓝 0)
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨ε / (C + 1), div_pos hε (by linarith), ?_⟩
    intro x hx_in hx_dist
    have hx_nn : 0 ≤ x := hx_in.1
    have hx_le_b : x ≤ b := hx_in.2
    have hcorr_x_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, x⟩ : IsingParams ℝ) {r_val, s_val} := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_beta_zero]
      · exact correlationInfinite_nonneg _ _ _ ⟨hJ_pos.le, le_refl 0, hx_pos⟩ _
    have hcorr_x_le_Cx : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, x⟩ : IsingParams ℝ) {r_val, s_val} ≤ C * x := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_beta_zero, mul_zero]
      · have hbound := correlationInfinite_le_const_mul_beta_of_high_temp
          Λ r_val s_val hrs J hJ_pos.le b hb_pos hlt x hx_pos hx_le_b
        have heq_M : M = b * J * (2 * ↑d) / (1 - b * J * (2 * ↑d)) := by
          rw [hM_def]; push_cast; ring
        have heq_C : C = J * (b * J * (2 * ↑d) / (1 - b * J * (2 * ↑d))) ^ 2 + J * (4 * ↑d) := by
          rw [hC_def, heq_M]
        rw [heq_C]
        simpa using hbound
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hcorr_x_nn]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx_nn] at hx_dist
    calc correlationInfinite _ _ _ _ ≤ C * x := hcorr_x_le_Cx
      _ ≤ (C + 1) * x := by nlinarith
      _ < (C + 1) * (ε / (C + 1)) := by
        apply (mul_lt_mul_iff_of_pos_left (by linarith)).mpr hx_dist
      _ = ε := by field_simp
  · -- β > 0: from Step 175
    have hβ_lt_βc : β < 1 / (J * ↑(2 * d)) := lt_of_le_of_lt hβ.2 hb_lt_βc
    have hβ_in_open : β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) := ⟨hβ_pos, hβ_lt_βc⟩
    exact (correlationInfinite_continuousAt_beta_of_high_temp
      hd Λ r_val s_val hrs J hJ_pos β hβ_in_open).continuousWithinAt

/-- **Helper: corr_∞ vanishes at J = 0 for r ≠ s** (Step 231 helper):
At J = h = 0 (any β), every Boltzmann weight = exp(0) = 1, so the correlation
sum reduces to the spin-product sum which vanishes for nonempty A. Hence
each `corr_n(J=0) = 0` and `corr_∞(J=0) = ⨆_n 0 = 0`. -/
private lemma correlationInfinite_eq_zero_at_J_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) :
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} = 0 := by
  rw [correlationInfinite_eq_ciSup]
  apply le_antisymm
  · apply ciSup_le
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n =
                 IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨0, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                  ⟨s_val, hsn⟩} := by
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      rw [IsingModel.correlation_zero_params_vanish_of_nonempty_A _ β _
            (Finset.insert_nonempty _ _)]
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
  · apply le_ciSup_of_le _ 0
    · by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume 0
      · have hrn : r_val ∈ Λ.volume 0 := Finset.insert_subset_iff.mp h_sub |>.1
        have hsn : s_val ∈ Λ.volume 0 :=
          Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
        have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                      (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} 0 =
                   IsingModel.correlation
                      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume 0))
                      (⟨0, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume 0)),
                                                    ⟨s_val, hsn⟩} := by
          rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
          congr 1
          ext u; rw [mem_liftFinset]
          simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        rw [heq]
        rw [IsingModel.correlation_zero_params_vanish_of_nonempty_A _ β _
              (Finset.insert_nonempty _ _)]
      · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
    · -- BddAbove of range
      by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume 0
      · exact ⟨1, fun y hy => by
          obtain ⟨n, rfl⟩ := hy
          exact correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ _ _ _⟩
      · exact ⟨1, fun y hy => by
          obtain ⟨n, rfl⟩ := hy
          exact correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ _ _ _⟩

/-- **ContinuousOn of corr_∞ on closed interval [0, b] in J** (Step 231):
For `0 < β`, `0 < b`, `bβ·2d < 1`: `J ↦ corr_∞(r, s, J)` is continuous on `[0, b]`,
extending Step 223 to include J = 0.

Direct J-direction analogue of Step 177. Proof: For J > 0 use Step 229 ContinuousAt.
For J = 0, use Step 230 squeeze `0 ≤ corr_∞(J) ≤ C·J` for J ∈ (0, b]. -/
theorem correlationInfinite_continuousOn_J_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    ContinuousOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hβ2d_pos : 0 < β * ↑(2 * d) := mul_pos hβ_pos h2d_pos
  have hb_lt_Jc : b < 1 / (β * ↑(2 * d)) := by
    rw [lt_div_iff₀ hβ2d_pos]; linarith
  intro J hJ
  rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
  · subst hJ0
    set M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) with hM_def
    set C : ℝ := β * M ^ 2 + β * (4 * ↑d) with hC_def
    have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
    have hM_nn : 0 ≤ M :=
      div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ_pos.le) (Nat.cast_nonneg _)) hdenom_b.le
    have hC_nn : 0 ≤ C :=
      add_nonneg (mul_nonneg hβ_pos.le (pow_nonneg hM_nn 2))
                 (mul_nonneg hβ_pos.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    have h_corr_at_zero : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} = 0 :=
      correlationInfinite_eq_zero_at_J_zero Λ r_val s_val β
    rw [ContinuousWithinAt]
    show Filter.Tendsto _ _ (nhds _)
    rw [h_corr_at_zero]
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨ε / (C + 1), div_pos hε (by linarith), ?_⟩
    intro x hx_in hx_dist
    have hx_nn : 0 ≤ x := hx_in.1
    have hx_le_b : x ≤ b := hx_in.2
    have hcorr_x_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨x, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_J_zero]
      · exact correlationInfinite_nonneg _ _ _ ⟨hx_pos.le, le_refl 0, hβ_pos⟩ _
    have hcorr_x_le_Cx : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨x, 0, β⟩ : IsingParams ℝ) {r_val, s_val} ≤ C * x := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_J_zero, mul_zero]
      · have hbound := correlationInfinite_le_const_mul_J_of_high_temp
          Λ r_val s_val hrs β hβ_pos b hb_pos hlt x hx_pos hx_le_b
        have heq_M : M = b * β * (2 * ↑d) / (1 - b * β * (2 * ↑d)) := by
          rw [hM_def]; push_cast; ring
        have heq_C : C = β * (b * β * (2 * ↑d) / (1 - b * β * (2 * ↑d))) ^ 2 + β * (4 * ↑d) := by
          rw [hC_def, heq_M]
        rw [heq_C]
        simpa using hbound
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hcorr_x_nn]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx_nn] at hx_dist
    calc correlationInfinite _ _ _ _ ≤ C * x := hcorr_x_le_Cx
      _ ≤ (C + 1) * x := by nlinarith
      _ < (C + 1) * (ε / (C + 1)) := by
        apply (mul_lt_mul_iff_of_pos_left (by linarith)).mpr hx_dist
      _ = ε := by field_simp
  · have hJ_lt_Jc : J < 1 / (β * ↑(2 * d)) := lt_of_le_of_lt hJ.2 hb_lt_Jc
    have hJ_in_open : J ∈ Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) := ⟨hJ_pos, hJ_lt_Jc⟩
    exact (correlationInfinite_continuousAt_J_of_high_temp
      hd Λ r_val s_val hrs β hβ_pos J hJ_in_open).continuousWithinAt

/-- **Helper: corr_n vanishes at β = 0** (Step 178 helper):
At β = 0, the finite-volume correlation along exhaustion is zero. -/
private lemma correlationAlongExhaustion_eq_zero_at_beta_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} n = 0 := by
  by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
    have hsn : s_val ∈ Λ.volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
    have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} n =
               IsingModel.correlation
                  (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, 0⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                ⟨s_val, hsn⟩} := by
      rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
      congr 1
      ext u; rw [mem_liftFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
    rw [heq]
    exact IsingModel.correlation_beta_zero_vanish_of_nonempty_A _ J 0 _
      (Finset.insert_nonempty _ _)
  · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]

/-- **TendstoUniformlyOn corr_n → corr_∞ on closed interval [0, b]** (Step 178):
Strengthens Step 170 to include β = 0.

Proof: Apply Dini's theorem (`Monotone.tendstoUniformlyOn_of_forall_tendsto`) on the
compact interval `[0, b]` using continuity of each corr_n, monotonicity in n
(at β = 0 it's trivial since both sides are 0), continuity of corr_∞ (Step 177),
and pointwise convergence. -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_beta_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n β => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc 0 b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · -- (1) ContinuousOn of each corr_n on [0, b]
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro β _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun β' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext β'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact IsingModel.correlation_continuousAt_beta _ J β _
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · -- (2) Monotone in n for each β ∈ [0, b]
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · -- β = 0: corr_n(0) = 0 for all n, monotone trivially
      subst hβ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero, le_refl]
    · -- β > 0: use the standard monotone theorem
      exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · -- (3) Continuity of corr_∞ on [0, b] (Step 177)
    exact correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
      hd Λ r_val s_val hrs J hJ_pos b hb_pos hlt
  · -- (4) Pointwise convergence at each β ∈ [0, b]
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · -- β = 0: both corr_n(0) and corr_∞(0) are 0
      subst hβ0
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero,
                 correlationInfinite_eq_zero_at_beta_zero]
      exact tendsto_const_nhds
    · -- β > 0: use correlationAlongExhaustion_tendsto_ciSup
      have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
        ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
      have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
        (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
      rw [correlationInfinite_eq_ciSup]
      exact htend

/-- **Helper: corr_n vanishes at J = 0** (Step 232 helper):
At J = h = 0 (any β), the finite-volume correlation along exhaustion is zero. -/
private lemma correlationAlongExhaustion_eq_zero_at_J_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n = 0 := by
  by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
    have hsn : s_val ∈ Λ.volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
    have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n =
               IsingModel.correlation
                  (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨0, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                ⟨s_val, hsn⟩} := by
      rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
      congr 1
      ext u; rw [mem_liftFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
    rw [heq]
    exact IsingModel.correlation_zero_params_vanish_of_nonempty_A _ β _
      (Finset.insert_nonempty _ _)
  · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]

/-- **TendstoUniformlyOn corr_n → corr_∞ on closed [0, b] in J including J = 0** (Step 232):
For `0 < β`, `0 < b`, `bβ·2d < 1`: corr_n → corr_∞ uniformly on `[0, b]` in J at h = 0.

Direct J-direction analogue of Step 178. Strengthens Step 224 to include J = 0.
Proof: Dini's theorem (`Monotone.tendstoUniformlyOn_of_forall_tendsto`) on the compact
[0, b] with: (1) ContinuousOn each corr_n; (2) Monotonicity in n at J = 0 trivial,
at J > 0 from `correlationAlongExhaustion_monotone`; (3) ContinuousOn corr_∞ from
Step 231; (4) pointwise convergence at J = 0 trivial, at J > 0 from
`correlationAlongExhaustion_tendsto_ciSup`. -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_J_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n J => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc 0 b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro J _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J', 0, β⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun J' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J', 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext J'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact (IsingModel.correlation_continuous_J _ 0 β _).continuousAt
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · intro J hJ
    rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
    · subst hJ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_J_zero, le_refl]
    · exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · exact correlationInfinite_continuousOn_J_of_high_temp_zero_closed
      hd Λ r_val s_val hrs β hβ_pos b hb_pos hlt
  · intro J hJ
    rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
    · subst hJ0
      simp only [correlationAlongExhaustion_eq_zero_at_J_zero,
                 correlationInfinite_eq_zero_at_J_zero]
      exact tendsto_const_nhds
    · have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
        ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
      have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
        (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
      rw [correlationInfinite_eq_ciSup]
      exact htend

/-- **MonotoneOn corr_∞ in β on closed interval [0, b]** (Step 179 helper):
The infinite-volume two-point function is monotone non-decreasing in β on `[0, b]`.

Proof: at β > 0 use `correlationInfinite_monotone_beta` (MonotoneOn `Ioi 0`);
at β = 0, corr_∞(0) = 0 ≤ corr_∞(β₂) by `correlationInfinite_nonneg`. -/
theorem correlationInfinite_monotoneOn_beta_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) (b : ℝ) :
    MonotoneOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  -- Reduce lambda to be able to rewrite
  simp only
  rcases eq_or_lt_of_le hβ₁.1 with hβ₁0 | hβ₁_pos
  · -- β₁ = 0: corr_∞(0) = 0 ≤ corr_∞(β₂)
    rw [← hβ₁0, correlationInfinite_eq_zero_at_beta_zero]
    rcases eq_or_lt_of_le (hβ₁0.le.trans hβ) with hβ₂0 | hβ₂_pos
    · rw [← hβ₂0, correlationInfinite_eq_zero_at_beta_zero]
    · exact correlationInfinite_nonneg _ _ _ ⟨hJ, le_refl 0, hβ₂_pos⟩ _
  · -- β₁ > 0: use existing MonotoneOn on Ioi 0
    have hβ₁_in : β₁ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos
    have hβ₂_in : β₂ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos.trans_le hβ
    exact correlationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ (le_refl 0) _
      hβ₁_in hβ₂_in hβ

/-- **A.e. differentiability of corr_∞ on closed [0, b]** (Step 179):
For ferromagnetic h = 0, β ∈ [0, b]: `β ↦ corr_∞(β)` is differentiable within `[0, b]` at
Lebesgue-a.e. β.

Proof: corr_∞ is monotone on `[0, b]` (helper above), hence locally bounded variation
(`MonotoneOn.locallyBoundedVariationOn`), hence a.e. differentiable
(`LocallyBoundedVariationOn.ae_differentiableWithinAt`). Strengthens Step 171
from `[a, b]` (a > 0) to closed `[0, b]`. -/
theorem correlationInfinite_ae_differentiableWithinAt_beta_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) (b : ℝ) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 b),
    DifferentiableWithinAt ℝ
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) β := by
  have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Icc

/-- **MonotoneOn corr_∞ in J on closed interval [0, b]** (Step 233 helper):
For `0 < β`: `J ↦ corr_∞(r, s, J)` is monotone non-decreasing on `[0, b]`.

Direct J-direction analogue of `correlationInfinite_monotoneOn_beta_zero_closed`.
Proof: at J > 0 use `correlationInfinite_monotone_J` (MonotoneOn `Ici 0`);
at J = 0, corr_∞(0) = 0 ≤ corr_∞(J₂) by `correlationInfinite_nonneg`. -/
theorem correlationInfinite_monotoneOn_J_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) (b : ℝ) :
    MonotoneOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  intro J₁ hJ₁ J₂ hJ₂ hJ_le
  simp only
  rcases eq_or_lt_of_le hJ₁.1 with hJ₁0 | hJ₁_pos
  · rw [← hJ₁0, correlationInfinite_eq_zero_at_J_zero]
    rcases eq_or_lt_of_le (hJ₁0.le.trans hJ_le) with hJ₂0 | hJ₂_pos
    · rw [← hJ₂0, correlationInfinite_eq_zero_at_J_zero]
    · exact correlationInfinite_nonneg _ _ _ ⟨hJ₂_pos.le, le_refl 0, hβ⟩ _
  · have hJ₁_in : J₁ ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hJ₁_pos.le
    have hJ₂_in : J₂ ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (hJ₁_pos.le.trans hJ_le)
    have hmono := correlationInfinite_monotone_J (IsingModel.latticeGraph d) Λ
      (le_refl 0) hβ {r_val, s_val} hJ₁_in hJ₂_in hJ_le
    exact hmono

/-- **A.e. differentiability of corr_∞ in J on closed [0, b]** (Step 233):
For `0 < β`, `b ∈ ℝ`: `J ↦ corr_∞(J)` is differentiable within `[0, b]` at Lebesgue-a.e. J.

Direct J-direction analogue of Step 179. Proof: corr_∞ is monotone on `[0, b]`
(helper above), hence locally bounded variation, hence a.e. differentiable. -/
theorem correlationInfinite_ae_differentiableWithinAt_J_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) (b : ℝ) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 b),
    DifferentiableWithinAt ℝ
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) J := by
  have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Icc

/-- **Helper for Step 180**: ordered Lipschitz bound on [0, b] (closed including β = 0).
For `0 ≤ β₁ ≤ β₂` with `β₂ ≤ b` and `bJ·2d < 1`:
`corr_∞(β₂) - corr_∞(β₁) ≤ C · (β₂ - β₁)` where `C = J·M² + J·4d`. -/
private lemma correlationInfinite_diff_le_const_mul_diff
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1)
    (β₁ β₂ : ℝ) (hβ₁_nn : 0 ≤ β₁) (hβ : β₁ ≤ β₂) (hβ₂_le_b : β₂ ≤ b) :
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      {r_val, s_val} -
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β₁⟩ : IsingParams ℝ)
      {r_val, s_val} ≤
    (J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d)) *
      (β₂ - β₁) := by
  rcases eq_or_lt_of_le hβ₁_nn with hβ₁0 | hβ₁_pos
  · -- β₁ = 0
    rw [← hβ₁0, correlationInfinite_eq_zero_at_beta_zero, sub_zero, sub_zero]
    rcases eq_or_lt_of_le (hβ₁0.le.trans hβ) with hβ₂0 | hβ₂_pos
    · rw [← hβ₂0, correlationInfinite_eq_zero_at_beta_zero]
      have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
      have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
        div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ) (Nat.cast_nonneg _)) hdenom_b.le
      positivity
    · -- β₂ > 0: use Step 176
      have hbound := correlationInfinite_le_const_mul_beta_of_high_temp
        Λ r_val s_val hrs J hJ b hb_pos hlt β₂ hβ₂_pos hβ₂_le_b
      -- hbound has let M = b*J*↑(2*d)/(1-b*J*↑(2*d)), so we directly get the bound
      simpa using hbound
  · -- β₁ > 0: use Step 168 (LipschitzOnWith on [β₁, b])
    -- Step 168's `let M` wrapper requires explicit type ascription below
    have hlip_let := correlationInfinite_lipschitzOnWith_beta_of_high_temp
      Λ r_val s_val hrs J hJ β₁ b hβ₁_pos (hβ.trans hβ₂_le_b) hlt
    -- Extract the underlying LipschitzOnWith (the `let M :=` is just notation)
    have hlip : LipschitzOnWith
        ⟨J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d), by
          have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
          have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
            div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ)
                         (Nat.cast_nonneg _)) hdenom_b.le
          positivity⟩
        (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
        (Set.Icc β₁ b) := hlip_let
    have hβ₁_in : β₁ ∈ Set.Icc β₁ b := Set.mem_Icc.mpr ⟨le_refl _, hβ.trans hβ₂_le_b⟩
    have hβ₂_in : β₂ ∈ Set.Icc β₁ b := Set.mem_Icc.mpr ⟨hβ, hβ₂_le_b⟩
    have hdist := hlip.dist_le_mul β₁ hβ₁_in β₂ hβ₂_in
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
      have h1 : β₁ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hβ₁_pos.le, hβ.trans hβ₂_le_b⟩
      have h2 : β₂ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hβ₁_pos.le.trans hβ, hβ₂_le_b⟩
      linarith [hmono h1 h2 hβ]
    have hβ_nn : 0 ≤ β₂ - β₁ := by linarith
    simp only [Real.dist_eq] at hdist
    rw [abs_sub_comm β₁ β₂, abs_of_nonneg hβ_nn,
        abs_sub_comm
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val})
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val}),
        abs_of_nonneg hcorr_nn] at hdist
    push_cast at hdist
    -- Convert ↑(2*d) ↔ 2 * ↑d for matching
    convert hdist using 2
    push_cast; ring

/-- **LipschitzOnWith of corr_∞ on closed [0, b] (including β = 0)** (Step 180):
For `0 ≤ J`, `0 < b`, `bJ·2d < 1`: `β ↦ corr_∞(β)` is `C`-Lipschitz on `[0, b]`
with the same constant `C = J·M² + J·4d` as Step 168.

Strengthens Step 168 from `[a, b]` (a > 0) to closed `[0, b]`. -/
theorem correlationInfinite_lipschitzOnWith_beta_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    LipschitzOnWith ⟨J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ)
                       (Nat.cast_nonneg _)) hdenom_b.le
        have := hM_nn
        positivity⟩
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro β₁ hβ₁ β₂ hβ₂
  -- Generic argument: the bound depends on min/max of β₁, β₂
  rcases le_total β₁ β₂ with hβ | hβ
  · -- β₁ ≤ β₂: |f β₁ - f β₂| ≤ K * |β₁ - β₂|
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
      linarith [hmono hβ₁ hβ₂ hβ]
    have hβ_nn : 0 ≤ β₂ - β₁ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm β₁ β₂,
        abs_sub_comm
          ((fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) β₁)
          ((fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) β₂),
        abs_of_nonneg hcorr_nn, abs_of_nonneg hβ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff Λ r_val s_val hrs J hJ b hb_pos hlt
      β₁ β₂ hβ₁.1 hβ hβ₂.2
    push_cast
    push_cast at hbound
    exact hbound
  · -- β₂ ≤ β₁: similar with roles swapped
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
      linarith [hmono hβ₂ hβ₁ hβ]
    have hβ_nn : 0 ≤ β₁ - β₂ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg hcorr_nn, abs_of_nonneg hβ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff Λ r_val s_val hrs J hJ b hb_pos hlt
      β₂ β₁ hβ₂.1 hβ hβ₁.2
    push_cast
    push_cast at hbound
    exact hbound

/-- **Helper for Step 234**: ordered Lipschitz bound on [0, b] in J (closed including J = 0).
For `0 ≤ J₁ ≤ J₂` with `J₂ ≤ b`, `0 < β`, `bβ·2d < 1`:
`corr_∞(J₂) - corr_∞(J₁) ≤ C · (J₂ - J₁)` where `C = β·M² + β·4d`. -/
private lemma correlationInfinite_diff_le_const_mul_diff_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1)
    (J₁ J₂ : ℝ) (hJ₁_nn : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (hJ₂_le_b : J₂ ≤ b) :
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J₂, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} -
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J₁, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤
    (β * (b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))) ^ 2 + β * (4 * ↑d)) *
      (J₂ - J₁) := by
  rcases eq_or_lt_of_le hJ₁_nn with hJ₁0 | hJ₁_pos
  · rw [← hJ₁0, correlationInfinite_eq_zero_at_J_zero, sub_zero, sub_zero]
    rcases eq_or_lt_of_le (hJ₁0.le.trans hJ) with hJ₂0 | hJ₂_pos
    · rw [← hJ₂0, correlationInfinite_eq_zero_at_J_zero]
      have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
      have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
        div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le) (Nat.cast_nonneg _)) hdenom_b.le
      positivity
    · have hbound := correlationInfinite_le_const_mul_J_of_high_temp
        Λ r_val s_val hrs β hβ b hb_pos hlt J₂ hJ₂_pos hJ₂_le_b
      simpa using hbound
  · have hlip_let := correlationInfinite_lipschitzOnWith_J_of_high_temp
      Λ r_val s_val hrs β hβ J₁ b hJ₁_pos (hJ.trans hJ₂_le_b) hlt
    have hlip : LipschitzOnWith
        ⟨β * (b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))) ^ 2 + β * (4 * ↑d), by
          have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
          have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
            div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le)
                         (Nat.cast_nonneg _)) hdenom_b.le
          positivity⟩
        (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
        (Set.Icc J₁ b) := hlip_let
    have hJ₁_in : J₁ ∈ Set.Icc J₁ b := Set.mem_Icc.mpr ⟨le_refl _, hJ.trans hJ₂_le_b⟩
    have hJ₂_in : J₂ ∈ Set.Icc J₁ b := Set.mem_Icc.mpr ⟨hJ, hJ₂_le_b⟩
    have hdist := hlip.dist_le_mul J₁ hJ₁_in J₂ hJ₂_in
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
      have h1 : J₁ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hJ₁_pos.le, hJ.trans hJ₂_le_b⟩
      have h2 : J₂ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hJ₁_pos.le.trans hJ, hJ₂_le_b⟩
      linarith [hmono h1 h2 hJ]
    have hJ_nn : 0 ≤ J₂ - J₁ := by linarith
    simp only [Real.dist_eq] at hdist
    rw [abs_sub_comm J₁ J₂, abs_of_nonneg hJ_nn,
        abs_sub_comm
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val}),
        abs_of_nonneg hcorr_nn] at hdist
    push_cast at hdist
    convert hdist using 2
    push_cast; ring

/-- **LipschitzOnWith of corr_∞ on closed [0, b] (including J = 0) in J** (Step 234):
For `0 < β`, `0 < b`, `bβ·2d < 1`: `J ↦ corr_∞(J)` is `C`-Lipschitz on `[0, b]` in J
with the same constant `C = β·M² + β·4d` as Step 222.

Direct J-direction analogue of Step 180. Strengthens Step 222 from `[a, b]` (a > 0)
to closed `[0, b]`. -/
theorem correlationInfinite_lipschitzOnWith_J_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    LipschitzOnWith ⟨β * (b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))) ^ 2 + β * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le)
                       (Nat.cast_nonneg _)) hdenom_b.le
        have := hM_nn
        positivity⟩
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro J₁ hJ₁ J₂ hJ₂
  rcases le_total J₁ J₂ with hJ_le | hJ_le
  · have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
      linarith [hmono hJ₁ hJ₂ hJ_le]
    have hJ_nn : 0 ≤ J₂ - J₁ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm J₁ J₂,
        abs_sub_comm
          ((fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) J₁)
          ((fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) J₂),
        abs_of_nonneg hcorr_nn, abs_of_nonneg hJ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff_J Λ r_val s_val hrs β hβ b hb_pos hlt
      J₁ J₂ hJ₁.1 hJ_le hJ₂.2
    push_cast
    push_cast at hbound
    exact hbound
  · have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
      linarith [hmono hJ₂ hJ₁ hJ_le]
    have hJ_nn : 0 ≤ J₁ - J₂ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg hcorr_nn, abs_of_nonneg hJ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff_J Λ r_val s_val hrs β hβ b hb_pos hlt
      J₂ J₁ hJ₂.1 hJ_le hJ₁.2
    push_cast
    push_cast at hbound
    exact hbound

/-- **Linear bound on corr_∞ at β = 0** (Step 181, β ≥ 0 version):
For `0 ≤ J`, `0 < b`, `bJ·2d < 1`, and any `r ≠ s`, on the interval `[0, b]`:
`corr_∞(r, s, β) ≤ (J·M(b)² + J·4d) · β`,
where `M(b) = bJ·2d/(1 - bJ·2d)`. Extension of Step 176 to include β = 0
(where both sides are 0).

In particular, `corr_∞(r, s, β) → 0` as `β → 0⁺` (right-continuity at 0). -/
theorem correlationInfinite_le_const_mul_beta_of_high_temp_zero_incl
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1)
    (β : ℝ) (hβ_nn : 0 ≤ β) (hβb : β ≤ b) :
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤ (J * M ^ 2 + J * (4 * ↑d)) * β := by
  intro M
  rcases eq_or_lt_of_le hβ_nn with hβ0 | hβ_pos
  · -- β = 0: both sides are 0
    rw [← hβ0, correlationInfinite_eq_zero_at_beta_zero, mul_zero]
  · -- β > 0: direct from Step 176
    exact correlationInfinite_le_const_mul_beta_of_high_temp
      Λ r_val s_val hrs J hJ b hb_pos hlt β hβ_pos hβb

/-- **Linear bound on corr_∞ at J = 0** (Step 235, J ≥ 0 version):
For `0 < β`, `0 < b`, `bβ·2d < 1`, and any `r ≠ s`, on the interval `[0, b]`:
`corr_∞(r, s, J) ≤ (β·M(b)² + β·4d) · J`,
where `M(b) = bβ·2d/(1 - bβ·2d)`. Direct J-direction analogue of Step 181:
extends Step 230 to include J = 0 (where both sides are 0). -/
theorem correlationInfinite_le_const_mul_J_of_high_temp_zero_incl
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1)
    (J : ℝ) (hJ_nn : 0 ≤ J) (hJb : J ≤ b) :
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤ (β * M ^ 2 + β * (4 * ↑d)) * J := by
  intro M
  rcases eq_or_lt_of_le hJ_nn with hJ0 | hJ_pos
  · rw [← hJ0, correlationInfinite_eq_zero_at_J_zero, mul_zero]
  · exact correlationInfinite_le_const_mul_J_of_high_temp
      Λ r_val s_val hrs β hβ b hb_pos hlt J hJ_pos hJb

/-- **ContinuousOn corr_∞ on Ico 0 β_c (half-open high-temperature interval)** (Step 182):
For `0 < J`, `1 ≤ d`: `β ↦ corr_∞(β)` is continuous on `Ico 0 (1/(J·2d))`
(closed at 0, open at β_c).

Combines Step 173 (continuity on Ioo 0 β_c) with Step 177 (continuity on Icc 0 b).

Proof: for each β₀ in the interval:
- β₀ > 0: use Step 175 ContinuousAt
- β₀ = 0: use Step 177 with b = (β_c)/2 (which is < β_c). -/
theorem correlationInfinite_continuousOn_beta_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ContinuousOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  have hβc_pos : 0 < 1 / (J * ↑(2 * d)) := one_div_pos.mpr hJ2d_pos
  intro β₀ hβ₀
  rcases eq_or_lt_of_le hβ₀.1 with hβ₀0 | hβ₀_pos
  · -- β₀ = 0: use Step 177 with b = β_c/2
    subst hβ₀0
    set b' : ℝ := (1 / (J * ↑(2 * d))) / 2 with hb'_def
    have hb'_pos : 0 < b' := by positivity
    have hb'_lt_βc : b' < 1 / (J * ↑(2 * d)) := by
      have : b' = (1 / (J * ↑(2 * d))) / 2 := rfl
      linarith
    have hlt : b' * J * ↑(2 * d) < 1 := by
      have h1 : b' * (J * ↑(2 * d)) < 1 := by
        have := (lt_div_iff₀ hJ2d_pos).mp hb'_lt_βc
        linarith [this]
      linarith [h1]
    have hcont_closed := correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
      hd Λ r_val s_val hrs J hJ_pos b' hb'_pos hlt
    -- ContinuousOn [0, b'] ⇒ ContinuousWithinAt at 0 within [0, b']
    have hcwa := hcont_closed 0 (Set.mem_Icc.mpr ⟨le_refl _, hb'_pos.le⟩)
    -- Need: ContinuousWithinAt at 0 within Ico 0 β_c
    -- Use the fact that nhdsWithin (Icc 0 b') 0 contains points in (Ico 0 β_c) near 0
    apply hcwa.mono_of_mem_nhdsWithin
    -- Need: Set.Icc 0 b' ∈ 𝓝[Ico 0 β_c] 0
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio b', isOpen_Iio, ?_, ?_⟩
    · exact hb'_pos
    · intro x hx
      have hx_lt_b' : x < b' := hx.1
      have hx_in_Ico : x ∈ Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d))) := hx.2
      exact Set.mem_Icc.mpr ⟨hx_in_Ico.1, hx_lt_b'.le⟩
  · -- β₀ > 0: use Step 175
    have hβ₀_in_open : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) := ⟨hβ₀_pos, hβ₀.2⟩
    exact (correlationInfinite_continuousAt_beta_of_high_temp
      hd Λ r_val s_val hrs J hJ_pos β₀ hβ₀_in_open).continuousWithinAt

/-- **ContinuousOn corr_∞ on Ico 0 J_c (half-open) in J** (Step 236):
For `0 < β`, `1 ≤ d`: `J ↦ corr_∞(J)` is continuous on `Ico 0 (1/(β·2d))`
(closed at 0, open at J_c). Direct J-direction analogue of Step 182. -/
theorem correlationInfinite_continuousOn_J_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ContinuousOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hβ2d_pos : 0 < β * ↑(2 * d) := mul_pos hβ_pos h2d_pos
  have hJc_pos : 0 < 1 / (β * ↑(2 * d)) := one_div_pos.mpr hβ2d_pos
  intro J₀ hJ₀
  rcases eq_or_lt_of_le hJ₀.1 with hJ₀0 | hJ₀_pos
  · subst hJ₀0
    set b' : ℝ := (1 / (β * ↑(2 * d))) / 2 with hb'_def
    have hb'_pos : 0 < b' := by positivity
    have hb'_lt_Jc : b' < 1 / (β * ↑(2 * d)) := by
      have : b' = (1 / (β * ↑(2 * d))) / 2 := rfl
      linarith
    have hlt : b' * β * ↑(2 * d) < 1 := by
      have h1 : b' * (β * ↑(2 * d)) < 1 := by
        have := (lt_div_iff₀ hβ2d_pos).mp hb'_lt_Jc
        linarith [this]
      linarith [h1]
    have hcont_closed := correlationInfinite_continuousOn_J_of_high_temp_zero_closed
      hd Λ r_val s_val hrs β hβ_pos b' hb'_pos hlt
    have hcwa := hcont_closed 0 (Set.mem_Icc.mpr ⟨le_refl _, hb'_pos.le⟩)
    apply hcwa.mono_of_mem_nhdsWithin
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio b', isOpen_Iio, ?_, ?_⟩
    · exact hb'_pos
    · intro x hx
      have hx_lt_b' : x < b' := hx.1
      have hx_in_Ico : x ∈ Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d))) := hx.2
      exact Set.mem_Icc.mpr ⟨hx_in_Ico.1, hx_lt_b'.le⟩
  · have hJ₀_in_open : J₀ ∈ Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) := ⟨hJ₀_pos, hJ₀.2⟩
    exact (correlationInfinite_continuousAt_J_of_high_temp
      hd Λ r_val s_val hrs β hβ_pos J₀ hJ₀_in_open).continuousWithinAt

/-- **MonotoneOn corr_∞ in β on the half-line Ici 0** (Step 183):
For `0 ≤ J`: corr_∞ is monotone non-decreasing in β on the entire half-line `Ici 0`.

Proof: at β > 0 use `correlationInfinite_monotone_beta` (Ioi 0);
at β = 0, corr_∞(0) = 0 ≤ corr_∞(β₂) by nonnegativity. -/
theorem correlationInfinite_monotoneOn_beta_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) :
    MonotoneOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  simp only
  have hβ₁_nn : 0 ≤ β₁ := hβ₁
  rcases eq_or_lt_of_le hβ₁_nn with hβ₁0 | hβ₁_pos
  · rw [← hβ₁0, correlationInfinite_eq_zero_at_beta_zero]
    rcases eq_or_lt_of_le (hβ₁0.le.trans hβ) with hβ₂0 | hβ₂_pos
    · rw [← hβ₂0, correlationInfinite_eq_zero_at_beta_zero]
    · exact correlationInfinite_nonneg _ _ _ ⟨hJ, le_refl 0, hβ₂_pos⟩ _
  · have hβ₁_in : β₁ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos
    have hβ₂_in : β₂ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos.trans_le hβ
    exact correlationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ (le_refl 0) _
      hβ₁_in hβ₂_in hβ

/-- **A.e. differentiability of corr_∞ on Ici 0** (Step 183):
For `0 ≤ J`: `β ↦ corr_∞(β)` is differentiable within `Ici 0` at Lebesgue-a.e. β.

Proof: `MonotoneOn.locallyBoundedVariationOn` (Step 183 monotonicity) +
`LocallyBoundedVariationOn.ae_differentiableWithinAt`. No high-temperature condition needed. -/
theorem correlationInfinite_ae_differentiableWithinAt_beta_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ici (0 : ℝ)),
    DifferentiableWithinAt ℝ
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) β := by
  have hmono := correlationInfinite_monotoneOn_beta_Ici_zero Λ r_val s_val J hJ
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Ici

/-- **MonotoneOn corr_∞ in J on the half-line Ici 0** (Step 237):
For `0 < β`: corr_∞ is monotone non-decreasing in J on the entire half-line `Ici 0`.

Direct J-direction analogue of Step 183. Direct application of
`correlationInfinite_monotone_J` at h = 0. -/
theorem correlationInfinite_monotoneOn_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    MonotoneOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) :=
  correlationInfinite_monotone_J (IsingModel.latticeGraph d) Λ (le_refl 0) hβ {r_val, s_val}

/-- **A.e. differentiability of corr_∞ on Ici 0 in J** (Step 237):
For `0 < β`: `J ↦ corr_∞(J)` is differentiable within `Ici 0` at Lebesgue-a.e. J.

Direct J-direction analogue of Step 183. Proof: `MonotoneOn.locallyBoundedVariationOn`
+ `LocallyBoundedVariationOn.ae_differentiableWithinAt`. No high-temperature condition. -/
theorem correlationInfinite_ae_differentiableWithinAt_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ici (0 : ℝ)),
    DifferentiableWithinAt ℝ
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) J := by
  have hmono := correlationInfinite_monotoneOn_J_Ici_zero Λ r_val s_val β hβ
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Ici

/-- **TendstoLocallyUniformlyOn corr_n → corr_∞ on Ico 0 β_c (half-open)** (Step 184):
For `0 < J`, `1 ≤ d`: corr_n converges locally uniformly to corr_∞ on `Ico 0 (1/(J·2d))`.

Combines Step 174 (Ioo 0 β_c) with Step 178 (Icc 0 b) via Dini's locally-uniform theorem
on the half-open interval. -/
theorem correlationAlongExhaustion_tendstoLocallyUniformlyOn_beta_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    TendstoLocallyUniformlyOn
      (fun n β => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
  · -- (1) ContinuousOn each corr_n on Ico 0 β_c
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro β _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun β' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext β'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact IsingModel.correlation_continuousAt_beta _ J β _
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · -- (2) Monotone in n at each β ∈ Ico 0 β_c
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · subst hβ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero, le_refl]
    · exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · -- (3) ContinuousOn corr_∞ on Ico 0 β_c (Step 182)
    exact correlationInfinite_continuousOn_beta_of_high_temp_Ico hd Λ r_val s_val hrs J hJ_pos
  · -- (4) Pointwise convergence
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · subst hβ0
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero,
                 correlationInfinite_eq_zero_at_beta_zero]
      exact tendsto_const_nhds
    · have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
        ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
      have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
        (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
      rw [correlationInfinite_eq_ciSup]
      exact htend

/-- **TendstoLocallyUniformlyOn corr_n → corr_∞ on Ico 0 J_c (half-open) in J** (Step 238):
For `0 < β`, `1 ≤ d`: corr_n converges locally uniformly to corr_∞ on `Ico 0 (1/(β·2d))` in J.

Direct J-direction analogue of Step 184. Combines Step 228 (Ioo 0 J_c) with Step 232
(Icc 0 b) via Dini's locally-uniform theorem on the half-open interval. -/
theorem correlationAlongExhaustion_tendstoLocallyUniformlyOn_J_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    TendstoLocallyUniformlyOn
      (fun n J => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
  · intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro J _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J', 0, β⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun J' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J', 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext J'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact (IsingModel.correlation_continuous_J _ 0 β _).continuousAt
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · intro J hJ
    rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
    · subst hJ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_J_zero, le_refl]
    · exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · exact correlationInfinite_continuousOn_J_of_high_temp_Ico hd Λ r_val s_val hrs β hβ_pos
  · intro J hJ
    rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
    · subst hJ0
      simp only [correlationAlongExhaustion_eq_zero_at_J_zero,
                 correlationInfinite_eq_zero_at_J_zero]
      exact tendsto_const_nhds
    · have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
        ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
      have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
        (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
      rw [correlationInfinite_eq_ciSup]
      exact htend

/-- **truncated2Infinite ContinuousOn β at h = 0 on Ioo 0 β_c** (Step 185, GJ §17.5):
For `0 < J`, `1 ≤ d`, `r ≠ s`: the infinite-volume Ursell 2-point function is continuous
in β on the open high-temperature interval.

Proof: at h = 0, `truncated2Infinite = correlationInfinite {r, s}` (`truncated2Infinite_h_zero`).
Apply Step 173. -/
theorem truncated2Infinite_continuousOn_beta_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ContinuousOn
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_beta_of_high_temp_open hd Λ r_val s_val hrs J hJ_pos

/-- **truncated2Infinite ContinuousOn β on closed [0, b]** (Step 185 closed variant). -/
theorem truncated2Infinite_continuousOn_beta_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    ContinuousOn
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc (0 : ℝ) b) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
    hd Λ r_val s_val hrs J hJ_pos b hb_pos hlt

/-- **truncated2Infinite ContinuousOn β on Ico 0 β_c (half-open)** (Step 185 Ico variant). -/
theorem truncated2Infinite_continuousOn_beta_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ContinuousOn
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_beta_of_high_temp_Ico hd Λ r_val s_val hrs J hJ_pos

/-- **truncated2Infinite ContinuousOn J on Ioo 0 J_c at h = 0** (Step 239):
J-direction analogue of Step 185 (Ioo variant). At h = 0, truncated2Infinite is
correlationInfinite {r, s}, so the result reduces to Step 227. -/
theorem truncated2Infinite_continuousOn_J_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ContinuousOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_J_of_high_temp_open hd Λ r_val s_val hrs β hβ_pos

/-- **truncated2Infinite ContinuousOn J on closed [0, b] at h = 0** (Step 239 closed variant).
J-direction analogue of Step 185 closed variant. -/
theorem truncated2Infinite_continuousOn_J_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    ContinuousOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc (0 : ℝ) b) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_J_of_high_temp_zero_closed
    hd Λ r_val s_val hrs β hβ_pos b hb_pos hlt

/-- **truncated2Infinite ContinuousOn J on Ico 0 J_c (half-open)** (Step 239 Ico variant). -/
theorem truncated2Infinite_continuousOn_J_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ContinuousOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_J_of_high_temp_Ico hd Λ r_val s_val hrs β hβ_pos

/-- **truncated2Infinite LipschitzOnWith β on [a, b] at h = 0** (Step 186 closed [a, b]).

Wrapper of Step 168 (corr_∞ LipschitzOnWith on [a, b]). -/
theorem truncated2Infinite_lipschitzOnWith_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    LipschitzOnWith ⟨J * M ^ 2 + J * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
        have hb_pos : 0 < b := ha.trans_le hab
        have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ)
                       (Nat.cast_nonneg _)) hdenom_b.le
        exact add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
               (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc a b) := by
  intro M
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_lipschitzOnWith_beta_of_high_temp Λ r_val s_val hrs J hJ a b ha hab hlt

/-- **truncated2Infinite LipschitzOnWith β on closed [0, b] at h = 0** (Step 186 closed [0, b]).

Wrapper of Step 180. -/
theorem truncated2Infinite_lipschitzOnWith_beta_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    LipschitzOnWith ⟨J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ)
                       (Nat.cast_nonneg _)) hdenom_b.le
        have := hM_nn
        positivity⟩
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc 0 b) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_lipschitzOnWith_beta_zero_closed Λ r_val s_val hrs J hJ b hb_pos hlt

/-- **truncated2Infinite ae DifferentiableWithinAt on Ici 0 at h = 0** (Step 186 ae version).

Wrapper of Step 183. No high-temperature condition needed. -/
theorem truncated2Infinite_ae_differentiableWithinAt_beta_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ici (0 : ℝ)),
    DifferentiableWithinAt ℝ
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ici (0 : ℝ)) β := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_ae_differentiableWithinAt_beta_Ici_zero Λ r_val s_val J hJ

/-- **truncated2Infinite MonotoneOn β on Ici 0 at h = 0** (Step 187):
For `0 ≤ J`: truncated2Infinite is monotone non-decreasing in β on `Ici 0` at h = 0.
Wrapper of Step 183 via `truncated2Infinite_h_zero`. -/
theorem truncated2Infinite_monotoneOn_beta_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) :
    MonotoneOn
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ici (0 : ℝ)) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_monotoneOn_beta_Ici_zero Λ r_val s_val J hJ

/-! ## Step 240: truncated2Infinite J-direction Lipschitz/ae diff/MonotoneOn -/

/-- **truncated2Infinite LipschitzOnWith J on [a, b] at h = 0** (Step 240).
J-direction analogue of Step 186 (Icc a b). Wrapper of Step 222. -/
theorem truncated2Infinite_lipschitzOnWith_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    LipschitzOnWith ⟨β * M ^ 2 + β * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
        have hb_pos : 0 < b := ha.trans_le hab
        have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le)
                       (Nat.cast_nonneg _)) hdenom_b.le
        exact add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
               (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc a b) := by
  intro M
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_lipschitzOnWith_J_of_high_temp Λ r_val s_val hrs β hβ a b ha hab hlt

/-- **truncated2Infinite LipschitzOnWith J on closed [0, b] at h = 0** (Step 240).
J-direction analogue of Step 186 (Icc 0 b). Wrapper of Step 234. -/
theorem truncated2Infinite_lipschitzOnWith_J_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    LipschitzOnWith ⟨β * (b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))) ^ 2 + β * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le)
                       (Nat.cast_nonneg _)) hdenom_b.le
        have := hM_nn
        positivity⟩
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc 0 b) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_lipschitzOnWith_J_zero_closed Λ r_val s_val hrs β hβ b hb_pos hlt

/-- **truncated2Infinite ae DifferentiableWithinAt on Ici 0 in J at h = 0** (Step 240).
J-direction analogue of Step 186 (ae version). Wrapper of Step 237. -/
theorem truncated2Infinite_ae_differentiableWithinAt_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ici (0 : ℝ)),
    DifferentiableWithinAt ℝ
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ici (0 : ℝ)) J := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_ae_differentiableWithinAt_J_Ici_zero Λ r_val s_val β hβ

/-- **truncated2Infinite MonotoneOn J on Ici 0 at h = 0** (Step 240).
J-direction analogue of Step 187. Wrapper of Step 237. -/
theorem truncated2Infinite_monotoneOn_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    MonotoneOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ici (0 : ℝ)) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_monotoneOn_J_Ici_zero Λ r_val s_val β hβ

/-! ## Step 241: truncated2Infinite ContinuousAt at every interior point in β + J -/

/-- **truncated2Infinite ContinuousAt every β ∈ Ioo 0 β_c at h = 0** (Step 241).
For any β₀ ∈ Ioo 0 (1/(J·2d)): truncated2Infinite is ContinuousAt at β₀
(full neighborhood, not just within-set). Wrapper of Step 175. -/
theorem truncated2Infinite_continuousAt_beta_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (β₀ : ℝ) (hβ₀ : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ContinuousAt
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      β₀ := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousAt_beta_of_high_temp hd Λ r_val s_val hrs J hJ_pos β₀ hβ₀

/-- **truncated2Infinite ContinuousAt every J ∈ Ioo 0 J_c at h = 0** (Step 241).
For any J₀ ∈ Ioo 0 (1/(β·2d)): truncated2Infinite is ContinuousAt at J₀
(full neighborhood, not just within-set). Wrapper of Step 229. -/
theorem truncated2Infinite_continuousAt_J_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (J₀ : ℝ) (hJ₀ : J₀ ∈ Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) :
    ContinuousAt
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      J₀ := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousAt_J_of_high_temp hd Λ r_val s_val hrs β hβ_pos J₀ hJ₀

end Ambient

end IsingModel
