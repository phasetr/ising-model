import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicDerivativeProfileLebowitz
import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellInfiniteVolumeBound

/-!
# Infinite-volume Lebowitz bound for the cubic β-derivative profile (Issue #2965, Phase C)

Bridges the finite-volume Lebowitz cross sum of
`derivative_profile_cubic_le_lebowitz_tight` to the **infinite-volume** two-point
function: each finite-volume cross correlation is dominated by its infinite-volume
value (`correlation_inducedGraph_cubic_le_correlationInfinite`), so the
β-derivative profile is bounded by the infinite-volume Lebowitz cross sum plus the
`O(1)` incident-edge error.

Since the infinite-volume cross products `g{x,u}·g{z,v}` decay in the distance from
`x`/`z` to the cut vertices (Phase B spatial decay) and the lattice susceptibility
is summable, this exhibits the β-derivative profiles as bounded by a single
infinite-volume two-point object — the form on which the per-stage increment
analysis required by the GJ §17.5 Lemma 17.5.2 capstone is built.

## Main declaration

* `IsingModel.Ambient.derivative_profile_cubic_le_infiniteVolume_lebowitz`.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Infinite-volume Lebowitz bound for the cubic β-derivative profile** (Issue
#2965, Phase C): for `0 ≤ J`, `0 < β`, distinct sites `x ≠ z` with
`{x,z} ⊆ volume n`, the β-derivative of the finite-volume two-point profile is
bounded by `J` times the **infinite-volume** Lebowitz cross sum over the stage-`n`
edges plus `J` times the incident-edge count:
`∂_β c_n ≤ J·∑_{⟨u,v⟩∈E}[g{x,u}g{z,v} + g{x,v}g{z,u}] + J·|incident|`, where
`g{a,b} = correlationInfinite (latticeGraph d) (cubicExhaustion d) ⟨J,0,β⟩ {a,b}`.
Composes `derivative_profile_cubic_le_lebowitz_tight` with the termwise
finite-volume ≤ infinite-volume bridge
`correlation_inducedGraph_cubic_le_correlationInfinite` (products monotone since
correlations are nonnegative). The infinite-volume cross products decay spatially
(Phase B), so this exhibits `F_n` controlled by a single infinite-volume object. -/
theorem derivative_profile_cubic_le_infiniteVolume_lebowitz (d : ℕ) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) {n : ℕ}
    (hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n) :
    deriv (fun β' => correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β
      ≤ J * ∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset,
          Sym2.lift ⟨fun u v =>
              correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} *
                correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} +
              correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} *
                correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val},
            fun u v => by ring⟩ e
        + J * ((inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
            (fun e => (⟨x, hsub (Finset.mem_insert_self x {z})⟩ :
                (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
              (⟨z, hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))⟩ :
                (↑((cubicExhaustion d).volume n) : Type _)) ∈ e)).card := by
  have hx : x ∈ (cubicExhaustion d).volume n := hsub (Finset.mem_insert_self x {z})
  have hz : z ∈ (cubicExhaustion d).volume n :=
    hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  refine (derivative_profile_cubic_le_lebowitz_tight d J β hJ hβ hxz hsub).trans ?_
  apply add_le_add _ (le_refl _)
  apply mul_le_mul_of_nonneg_left _ hJ
  apply Finset.sum_le_sum
  intro e _he
  obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  have bxu := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨x, hx⟩ u
  have bzv := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨z, hz⟩ v
  have bxv := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨x, hx⟩ v
  have bzu := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨z, hz⟩ u
  refine add_le_add
    (mul_le_mul bxu bzv (gks_first _ _ hf _) (correlationInfinite_nonneg _ _ _ hf _))
    (mul_le_mul bxv bzu (gks_first _ _ hf _) (correlationInfinite_nonneg _ _ _ hf _))

/-- **Per-edge Ursell summand bounded by an infinite-volume cross product** (Issue
#2965, Phase C): for a non-degenerate edge `{u,v}` of `inducedGraph (latticeGraph d)
(volume n)` whose endpoints are distinct from the lifted sites `⟨x⟩, ⟨z⟩`, the
Ursell summand of the β-derivative profile is bounded by the infinite-volume
Lebowitz cross product
`g{x,u}g{z,v} + g{x,v}g{z,u}`, where `g{a,b} = correlationInfinite …`. Composes the
finite-volume Lebowitz summand bound `summand_le_lebowitz_of_disjoint` with the
termwise finite ≤ infinite bridge `correlation_inducedGraph_cubic_le_correlationInfinite`.
This is the per-edge handle used to sum the Ursell terms over the *new shell edges*
of a stage (which are far from `x, z`, so the cross products decay) in the
β-derivative increment analysis. -/
theorem ursell_cubic_le_infiniteVolume_cross (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {n : ℕ} {x z : Fin d → ℤ} (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n) (u v : (↑((cubicExhaustion d).volume n) : Type _))
    (hxz : (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ≠ ⟨z, hz⟩)
    (hxu : (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ≠ u)
    (hxv : (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ≠ v)
    (hzu : (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ≠ u)
    (hzv : (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) ≠ v)
    (huv : u ≠ v) :
    correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff {⟨x, hx⟩, ⟨z, hz⟩} {u, v}) -
        correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) {⟨x, hx⟩, ⟨z, hz⟩} *
          correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
            (⟨J, 0, β⟩ : IsingParams ℝ) {u, v}
      ≤ correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} *
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} +
        correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} *
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val} := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  refine (summand_le_lebowitz_of_disjoint
    (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)) J β hf
    ⟨x, hx⟩ ⟨z, hz⟩ u v hxz hxu hxv hzu hzv huv).trans ?_
  have bxu := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨x, hx⟩ u
  have bzv := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨z, hz⟩ v
  have bxv := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨x, hx⟩ v
  have bzu := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨z, hz⟩ u
  exact add_le_add
    (mul_le_mul bxu bzv (gks_first _ _ hf _) (correlationInfinite_nonneg _ _ _ hf _))
    (mul_le_mul bxv bzu (gks_first _ _ hf _) (correlationInfinite_nonneg _ _ _ hf _))

end Ambient
end IsingModel
