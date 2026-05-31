import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PerActivePairRateFromUniformTransfer
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.UpperBound
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecay

/-!
# GJ §17.5 Lemma 17.5.2 Part B — large-`K` closure of the upper bound

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development.  It
discharges the uniform `pseudoMassG` transfer bound
`Lemma_17_5_2_UniformTransferPseudoMassGBound`, and hence closes the named
`latticeMass` upper-bound side of GJ Lemma 17.5.2,
`m(σ) ≤ const · m⁻(σ)`, for ferromagnetic high-temperature pairs.

## Mechanism

The transfer bound asks, for each admissible decay rate `a` and each active pair
`(x, z)`, for `correlationInfinite … {x, z} ≤ pseudoMassG α r ((a : ℝ)/K)`.  Two
uniform facts make this provable with a single `K` depending only on
`α, r, d, J, β`:

* every infinite-volume correlation is bounded by `1`
  (`correlationInfinite_latticeGraph_le_one`), a uniform gap below `pseudoMassG`'s
  value `2` at `0`; and
* every admissible decay rate is bounded by `-log(tanh(βJ))`
  (`HasExponentialDecay_rate_le_neg_log_tanh_betaJ`, transferred to an arbitrary
  exhaustion).

Since `pseudoMassG α r` is continuous with `pseudoMassG α r 0 = 2 > 1` and
antitone, it stays `≥ 1` on a neighbourhood `[0, δ]` of `0`; taking `K` large
enough that `(a : ℝ)/K ≤ δ` for every admissible `a` gives
`correlationInfinite ≤ 1 ≤ pseudoMassG α r ((a : ℝ)/K)`.

The resulting constant `const = ofReal K` is **uniform but not sharp**: this
proves the qualitative Glimm--Jaffe statement `m ≤ const · m⁻` (which only asserts
the existence of such a constant), via the uniform lower bound
`m⁻(x, z) ≥ pseudoMassG⁻¹(1)` that `correlationInfinite ≤ 1` yields, rather than
the sharper transfer-matrix correlation length.

Tracking issue: <https://github.com/phasetr/ising-model/issues/3378>
(parent <https://github.com/phasetr/ising-model/issues/1645>).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Filter Topology

/-- **`pseudoMassG α r` stays `≥ 1` on a neighbourhood of `0`**: since it is
continuous within `[0, ∞)` at `0` with value `pseudoMassG α r 0 = 2 > 1`, there is
`δ > 0` with `1 ≤ pseudoMassG α r t` for all `t ∈ [0, δ]`. -/
theorem exists_pos_forall_pseudoMassG_ge_one_near_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t ≤ δ → 1 ≤ pseudoMassG α r t := by
  have hcont : ContinuousWithinAt (pseudoMassG α r) (Set.Ici 0) 0 :=
    pseudoMassG_continuousWithinAt_Ici_zero α hr le_rfl
  have h2 : (1 : ℝ) < pseudoMassG α r 0 := by rw [pseudoMassG_zero hα r]; norm_num
  have hev : ∀ᶠ t in 𝓝[Set.Ici 0] (0 : ℝ), (1 : ℝ) < pseudoMassG α r t :=
    hcont.eventually (lt_mem_nhds h2)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, by linarith, fun t ht htδ => ?_⟩
  have hdist : dist t (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht]; linarith
  exact (hball hdist (Set.mem_Ici.mpr ht)).le

/-- **Uniform `K` making `pseudoMassG α r ((a : ℝ)/K) ≥ 1` for all rates `≤ A`**:
given a real upper bound `A` on the admissible rates, choosing `K` large enough
forces `(a : ℝ)/K` into the near-zero region where `pseudoMassG ≥ 1`.

No sign hypothesis on `A` is needed: if `A < 0` no nonnegative rate satisfies
`(a : ℝ) ≤ A`, so the bound is vacuous. -/
theorem exists_K_forall_pseudoMassG_ge_one_of_rate_bound
    {α : ℕ} (hα : 1 ≤ α) {r A : ℝ} (hr : 0 < r) :
    ∃ K : ℝ, 0 < K ∧
      ∀ a : NNReal, (a : ℝ) ≤ A → 1 ≤ pseudoMassG α r ((a : ℝ) / K) := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_forall_pseudoMassG_ge_one_near_zero hα hr
  refine ⟨max 1 (A / δ), lt_of_lt_of_le one_pos (le_max_left _ _), fun a ha => ?_⟩
  set K : ℝ := max 1 (A / δ) with hK_def
  have hK_pos : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h_aK_nonneg : 0 ≤ (a : ℝ) / K := div_nonneg (NNReal.coe_nonneg a) hK_pos.le
  have hAδK : A ≤ δ * K := by
    have hAδ_le : A / δ ≤ K := le_max_right _ _
    have h := mul_le_mul_of_nonneg_left hAδ_le hδ.le
    rwa [mul_div_cancel₀ A hδ.ne'] at h
  have h_aK_le : (a : ℝ) / K ≤ δ := by
    rw [div_le_iff₀ hK_pos]
    calc (a : ℝ) ≤ A := ha
      _ ≤ δ * K := hAδK
  exact hδle _ h_aK_nonneg h_aK_le

/-- **Uniform `pseudoMassG` transfer bound from a real rate bound**: if every
admissible decay rate is bounded by a real constant `A`, then
`Lemma_17_5_2_UniformTransferPseudoMassGBound` holds for some `K`.

The active-pair correlations are uniformly `≤ 1`
(`correlationInfinite_latticeGraph_le_one`), which is `≤ pseudoMassG α r ((a : ℝ)/K)`
for the `K` from `exists_K_forall_pseudoMassG_ge_one_of_rate_bound`. -/
theorem exists_uniform_transfer_pseudoMassG_of_rate_bound
    {α d : ℕ} (hα : 1 ≤ α) {r A : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ)
    (hrate : ∀ a : NNReal,
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
        (a : ℝ) ≤ A) :
    ∃ K : ℝ, Lemma_17_5_2_UniformTransferPseudoMassGBound (α := α) (r := r)
      Λ J β K := by
  obtain ⟨K, hK, hKbound⟩ :=
    exists_K_forall_pseudoMassG_ge_one_of_rate_bound (α := α) (r := r) (A := A) hα hr
  have hpred : Lemma_17_5_2_UniformTransferPseudoMassGBound (α := α) (r := r)
      Λ J β K := by
    refine ⟨hK, ?_⟩
    intro a ha x z _hxz
    have h1 : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ≤ 1 :=
      correlationInfinite_le_one (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
    exact h1.trans (hKbound a (hrate a ha))
  exact ⟨K, hpred⟩

/-- **`-log(tanh(βJ)) ≥ 0`** for `0 < J`, `0 < β`: `tanh(βJ) ∈ (0, 1)`, so its log
is nonpositive. -/
theorem neg_log_tanh_betaJ_nonneg {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    0 ≤ -Real.log (Real.tanh (β * J)) := by
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hJ)) (Real.cosh_pos _)
  have htanh_lt_one : Real.tanh (β * J) < 1 := Real.tanh_lt_one _
  have hlog : Real.log (Real.tanh (β * J)) ≤ 0 :=
    Real.log_nonpos htanh_pos.le htanh_lt_one.le
  linarith

/-- **Admissible decay rates are bounded by `-log(tanh(βJ))`** on an arbitrary
exhaustion: transfer the validating decay to the cubic exhaustion, apply the
high-temperature all-rate cap, and convert the `ENNReal` bound to reals. -/
theorem admissible_rate_le_neg_log_tanh
    {d : ℕ} (hd : 0 < d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {a : NNReal}
    (ha : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ)) :
    (a : ℝ) ≤ -Real.log (Real.tanh (β * J)) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have ha_cubic :
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) :=
    HasExponentialDecay_transfer_exhaustion Λ (Ambient.cubicExhaustion d) hf ha
  have hcap : (a : ENNReal) ≤
      ENNReal.ofReal (-Real.log (Real.tanh (β * J))) :=
    HasExponentialDecay_rate_le_neg_log_tanh_betaJ hd hJ hβ ha_cubic
  have hcoe : ENNReal.ofReal (a : ℝ) ≤
      ENNReal.ofReal (-Real.log (Real.tanh (β * J))) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_le_ofReal_iff (neg_log_tanh_betaJ_nonneg hJ hβ)).mp hcoe

/-- **Unconditional uniform `pseudoMassG` transfer bound at high temperature**:
for `0 < d`, `0 < J`, `0 < β`, `1 ≤ α`, `0 < r`, some `K` validates
`Lemma_17_5_2_UniformTransferPseudoMassGBound`.  The real rate bound
`A = -log(tanh(βJ))` is supplied by `admissible_rate_le_neg_log_tanh`. -/
theorem exists_uniform_transfer_pseudoMassG
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    ∃ K : ℝ, Lemma_17_5_2_UniformTransferPseudoMassGBound (α := α) (r := r)
      Λ J β K :=
  exists_uniform_transfer_pseudoMassG_of_rate_bound (A := -Real.log (Real.tanh (β * J)))
    hα hr Λ J β
    (fun _a ha => admissible_rate_le_neg_log_tanh hd Λ hJ hβ ha)

/-- **GJ §17.5 Lemma 17.5.2 upper bound, closed unconditionally at high
temperature**: for a ferromagnetic high-temperature active pair `(x, z)`, there is
a (uniform, non-sharp) constant `ofReal K` with
`latticeMass ≤ ofReal K · ofReal m⁻(x, z)`, i.e. the named
`Lemma_17_5_2_UpperBound`.

This is the upper side of Glimm--Jaffe Lemma 17.5.2 `m ≤ const · m⁻`: the constant
exists and is uniform in the pair, established through the system pseudo-mass
reduction (`Lemma_17_5_2_GlobalAllRateComparison`) and the large-`K` transfer
bound.  It does not produce the sharp transfer-matrix correlation length. -/
theorem lemma_17_5_2_upper_bound_uniform_transfer
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {x z : Fin d → ℤ}
    (hxz : ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    ∃ K : ℝ, Lemma_17_5_2_UpperBound hα hr Λ J β x z (ENNReal.ofReal K) := by
  obtain ⟨K, hU⟩ := exists_uniform_transfer_pseudoMassG hα hr hd Λ hJ hβ
  exact ⟨K, lemma_17_5_2_upper_bound_of_uniform_transfer_pseudoMassG hα hr Λ J β
    hxz hU⟩

end Ambient
end IsingModel
