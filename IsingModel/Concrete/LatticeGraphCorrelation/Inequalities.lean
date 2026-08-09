import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundationTrivialSliceAndIndep
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferSummabilityCharacterization
import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp
import IsingModel.LatticeExpSum
import IsingModel.BetaDerivative

/-!
# ℤ^d degenerate cases of the critical inverse temperature (§17.1)

The critical inverse temperature of the `d`-dimensional lattice is `⊤` wherever no
ferromagnetic interaction is present: in dimension zero, and at vanishing coupling in every
dimension. The zero-dimensional case rests on file-private observations that the vertex type
`Fin 0 → ℤ` admits no pair of distinct sites, so exponential decay holds vacuously at every
rate and the lattice mass is `⊤`; the vanishing-coupling case runs instead through the
lattice mass being `⊤` at every non-negative inverse temperature. No statement here carries a
hypothesis, and no instance argument is taken.

This module also gathers, for callers that want them behind a single import, the ℤ^d
correlation-inequality and lattice-mass surfaces proved in the modules it imports.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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

end Ambient

end IsingModel
