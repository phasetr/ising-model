import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellInfiniteVolumeBound
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Contraction

/-!
# Cubic-shell tight `derivBoundTight` bounded by a spatial-decay sum (Issue #2965, Phase B)

Applies the infinite-volume spatial exponential decay
`correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair` termwise to
the diagonal-free cubic-shell bound
`derivBoundTight_inducedGraph_cubic_le_infiniteVolume_sum`, replacing each
infinite-volume two-point correlation `g{x,y}` by its decay bound
`(contractionFactor)^{dist(x,y)/(r₀+2)}`.

Because the tight bound carries only the cross products
`g{r,a}·g{s,b} + g{r,b}·g{s,a}` (no diagonal `g{r,s}·g{a,b}` term), every factor
genuinely decays in the distance from `r`/`s` to the cut vertices, so this is the
diagonal-free decay-sum input from which a geometric per-stage rate is extracted
(the remaining shell-edge distance/counting aggregation is downstream).

## Main declaration

* `IsingModel.Ambient.derivBoundTight_inducedGraph_cubic_le_decay_sum`.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Cubic-shell tight bound by a spatial-decay sum** (Issue #2965, Phase B): in
the high-temperature regime `contractionFactor d (cubicExhaustion d) p r₀ < 1`, for
sites `r, s ∈ box_n` on no edge of `E₀`, the tight ball-boundary derivative bound is
dominated by `β·J` times the edge sum of products of `contractionFactor` powers,
each exponent the lattice distance from `r`/`s` to a cut vertex divided by `r₀+2`:
`derivBoundTight … E₀ … ≤ β·J·∑_{⟨a,b⟩∈E₀}[cf^{d(r,a)/(r₀+2)}·cf^{d(s,b)/(r₀+2)} +
cf^{d(r,b)/(r₀+2)}·cf^{d(s,a)/(r₀+2)}]`. Chains
`derivBoundTight_inducedGraph_cubic_le_infiniteVolume_sum` with the per-pair decay
`correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair` applied
termwise (the distinctness `r ≠ a.val` etc. follows from `r, s` being on no
`E₀`-edge). The cross-product-only structure ensures every factor decays. -/
theorem derivBoundTight_inducedGraph_cubic_le_decay_sum (d : ℕ) (hd : 1 ≤ d) (r₀ : ℕ)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d (cubicExhaustion d) p r₀ < 1)
    (n : ℕ) (E₀ : Finset (Sym2 (↑(cubicBox d n) : Type _)))
    {r s : Fin d → ℤ} (hr : r ∈ cubicBox d n) (hs : s ∈ cubicBox d n)
    (hsep : ∀ e ∈ E₀, ¬ Sym2.Mem (⟨r, hr⟩ : (↑(cubicBox d n) : Type _)) e ∧
      ¬ Sym2.Mem (⟨s, hs⟩ : (↑(cubicBox d n) : Type _)) e) :
    derivBoundTight (inducedGraph (latticeGraph d) (cubicBox d n)) E₀ p ⟨r, hr⟩ ⟨s, hs⟩
      ≤ p.β * p.J * ∑ e ∈ E₀, Sym2.lift ⟨fun a b =>
          contractionFactor d (cubicExhaustion d) p r₀ ^
              (latticeDistance d r a.val / (r₀ + 2)) *
            contractionFactor d (cubicExhaustion d) p r₀ ^
              (latticeDistance d s b.val / (r₀ + 2)) +
          contractionFactor d (cubicExhaustion d) p r₀ ^
              (latticeDistance d r b.val / (r₀ + 2)) *
            contractionFactor d (cubicExhaustion d) p r₀ ^
              (latticeDistance d s a.val / (r₀ + 2)),
          fun a b => by ring⟩ e := by
  refine (derivBoundTight_inducedGraph_cubic_le_infiniteVolume_sum d p hf n E₀ hr hs).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  obtain ⟨hrmem, hsmem⟩ := hsep _ he
  have hr_a : r ≠ a.val := fun h => hrmem (Sym2.mem_iff.mpr (Or.inl (Subtype.ext h)))
  have hr_b : r ≠ b.val := fun h => hrmem (Sym2.mem_iff.mpr (Or.inr (Subtype.ext h)))
  have hs_a : s ≠ a.val := fun h => hsmem (Sym2.mem_iff.mpr (Or.inl (Subtype.ext h)))
  have hs_b : s ≠ b.val := fun h => hsmem (Sym2.mem_iff.mpr (Or.inr (Subtype.ext h)))
  have hcf_nonneg : 0 ≤ contractionFactor d (cubicExhaustion d) p r₀ :=
    contractionFactor_nonneg d (cubicExhaustion d) p hf r₀
  have dra := correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair d hd r₀
    (cubicExhaustion d) p hf hh hα hr_a
  have drb := correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair d hd r₀
    (cubicExhaustion d) p hf hh hα hr_b
  have dsa := correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair d hd r₀
    (cubicExhaustion d) p hf hh hα hs_a
  have dsb := correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair d hd r₀
    (cubicExhaustion d) p hf hh hα hs_b
  refine add_le_add
    (mul_le_mul dra dsb (correlationInfinite_nonneg _ _ _ hf _) (pow_nonneg hcf_nonneg _))
    (mul_le_mul drb dsa (correlationInfinite_nonneg _ _ _ hf _) (pow_nonneg hcf_nonneg _))

end Ambient
end IsingModel
