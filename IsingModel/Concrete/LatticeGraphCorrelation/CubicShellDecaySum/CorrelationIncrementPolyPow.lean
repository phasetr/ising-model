import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellDecaySum.ShellDecaySumBound
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPerStageIncrement
import IsingModel.AmbientLattice.CorrelationInfinite.Basic
import IsingModel.AmbientLattice.Exhaustion

/-!
# Cubic-shell decay sum (2/4): correlation increment in polynomial × geometric form

Structural split (2/4) of `Concrete.LatticeGraphCorrelation.CubicShellDecaySum`.  This child
transports the shell bound of the sibling `...ShellDecaySumBound` to the per-stage
correlation increment along the cubic exhaustion: the one-sided polynomial × geometric
increment, its two-sided absolute form obtained from ferromagnetic monotonicity, the same
bound written directly in terms of `correlation` on the induced cubic graphs, and the
high-temperature simplification absorbing the `β·J·2·d` prefactor into the clean
`(2k+3)^d · cf^{(k+1−R)/(r₀+2)}` shape.  See the
`Concrete.LatticeGraphCorrelation.CubicShellDecaySum` facade module for the full contents
overview.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Polynomial × geometric per-stage correlation increment** (Issue #2965,
Phase B): combining the tight cubic per-stage increment
`correlationAlongExhaustion_cubic_succ_sub_le_derivBoundTight` with the
polynomial × geometric shell bound `derivBoundTight_cubic_shell_le_poly_pow`, the
successive correlation difference along the cubic exhaustion is bounded by
`β·J · 2·d·(2(k+1)+1)^d · cf^{(k+1−R)/(r₀+2)}` — a fixed polynomial in `k` times a
geometric factor `cf^{·/(r₀+2)}` with `cf < 1`, i.e. the `M·(2k+3)^d·ratio^k` form
of the per-stage increment. (The two shell terms compose directly now that the
outer induced-lattice-graph edge-set instance is the shared canonical one; see the
lowered-priority `Fintype edgeSet` fallback instances in `CubicPerStageIncrement`
and `CubicShellInfiniteVolumeBound`.) -/
theorem correlationAlongExhaustion_cubic_succ_sub_le_poly_pow (d : ℕ) (hd : 1 ≤ d)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d (cubicExhaustion d) p r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (by omega) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (by omega) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e) :
    correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} (k + 1)
        - correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} k
      ≤ p.β * p.J * (2 * (d * (2 * (k + 1) + 1) ^ d) *
          contractionFactor d (cubicExhaustion d) p r₀ ^ ((k + 1 - R) / (r₀ + 2))) :=
  (correlationAlongExhaustion_cubic_succ_sub_le_derivBoundTight d p hf hh hrs k
    (cubicBox_mono d hRk hr) (cubicBox_mono d hRk hs) hsep).trans
    (derivBoundTight_cubic_shell_le_poly_pow d hd r₀ hr₀ p hf hh hα k R hRk hr hs hsep)

/-- **Abs form of cubic per-stage correlation increment** (Issue #3054). Combines
`correlationAlongExhaustion_cubic_succ_sub_le_poly_pow` (the one-sided ≤ form)
with the ferromagnetic monotonicity
`correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone`
(`c_k ≤ c_{k+1}` for ferromagnetic; here applied with `Λ.mono (Nat.le_succ k)`)
to give the two-sided abs bound shape required by the `h_real_inc` slots of the
poly-geometric CE-route bundle constructors (PRs #3099-#3105). -/
theorem abs_correlationAlongExhaustion_cubic_succ_sub_le_poly_pow (d : ℕ) (hd : 1 ≤ d)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d (cubicExhaustion d) p r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (by omega) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (by omega) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e) :
    |correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} k
        - correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} (k + 1)|
      ≤ p.β * p.J * (2 * (d * (2 * (k + 1) + 1) ^ d) *
          contractionFactor d (cubicExhaustion d) p r₀ ^ ((k + 1 - R) / (r₀ + 2))) := by
  have hmono :=
    correlationAlongExhaustion_monotone (latticeGraph d) (cubicExhaustion d) p hf {r, s}
      (Nat.le_succ k)
  have hub :=
    correlationAlongExhaustion_cubic_succ_sub_le_poly_pow d hd r₀ hr₀ p hf hh hα k R hRk hrs hr hs
      hsep
  -- Since c_k ≤ c_{k+1}, c_k - c_{k+1} ≤ 0, so |c_k - c_{k+1}| = c_{k+1} - c_k.
  have hsub_nn :
      0 ≤ correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} (k + 1)
          - correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) p {r, s} k :=
    sub_nonneg.mpr hmono
  rw [abs_sub_comm]
  exact (abs_of_nonneg hsub_nn).trans_le hub

/-- **Cubic abs increment in direct correlation form** (Issue #3054). Rewrites
`abs_correlationAlongExhaustion_cubic_succ_sub_le_poly_pow` in the direct
`correlation (inducedGraph (latticeGraph d) (cubicBox d _)) ⟨J, 0, β⟩ (liftFinset {r, s} _)`
form, matching exactly the shape required by the `h_real_inc` slots of the
poly-geometric CE-route bundle constructors (PRs #3099-#3105). Uses
`correlationAlongExhaustion_eq_correlation_inducedGraph` to unfold both stages. -/
theorem abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow (d : ℕ) (hd : 1 ≤ d)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J β : ℝ)
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hα : contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (by omega) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (by omega) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e)
    (hcov_k : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k) :
    |correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) -
        correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k))))|
      ≤ β * J * (2 * (d * (2 * (k + 1) + 1) ^ d) *
          contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
            ((k + 1 - R) / (r₀ + 2))) := by
  have heq_k :
      correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} k
        = correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) :=
    correlationAlongExhaustion_of_subset (latticeGraph d)
      (cubicExhaustion d) _ hcov_k
  have heq_k1 :
      correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} (k + 1)
        = correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k)))) :=
    correlationAlongExhaustion_of_subset (latticeGraph d)
      (cubicExhaustion d) _
      (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k)))
  rw [← heq_k, ← heq_k1]
  exact abs_correlationAlongExhaustion_cubic_succ_sub_le_poly_pow d hd r₀ hr₀
    (⟨J, 0, β⟩ : IsingParams ℝ) hf rfl hα k R hRk hrs hr hs hsep

/-- **High-temperature simplification of the cubic abs increment** (Issue #3054).
Under the high-temperature condition `β · J · 2 · d ≤ 1`, the `β · J · 2 · d`
prefactor in `abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow` is
absorbed, leaving the clean poly·geometric bound
`(2k+3)^d · cf^{(k+1-R)/(r₀+2)}`. This is the form directly compatible with
the `R_inc_seq k := (2k+3)^d · ratio^k` shape required by the poly-geometric
CE-route bundle constructors (PRs #3099-#3105). Positivity of the right-hand
side uses `contractionFactor_nonneg`. -/
theorem abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow_high_temp (d : ℕ) (hd : 1 ≤ d)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J β : ℝ)
    (hβJ2d : β * J * (2 * d) ≤ 1)
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hα : contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨r, cubicBox_mono d (by omega) hr⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, cubicBox_mono d (by omega) hs⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e)
    (hcov_k : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k) :
    |correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) -
        correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k))))|
      ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d *
        contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
          ((k + 1 - R) / (r₀ + 2)) := by
  have hbound :=
    abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow d hd r₀ hr₀ J β hf hα k R hRk hrs hr hs
      hsep
      hcov_k
  have hcf_nn :
      (0 : ℝ) ≤ contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ :=
    contractionFactor_nonneg d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf r₀
  -- Simplify the indexing: (2 * ((k : ℝ) + 1) + 1) = ((2 * k + 3 : ℕ) : ℝ)
  have hidx : (2 * ((k : ℝ) + 1) + 1) = ((2 * k + 3 : ℕ) : ℝ) := by push_cast; ring
  -- Build the simplification inequality.
  have hcf_pow_nn :
      0 ≤ contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
            ((k + 1 - R) / (r₀ + 2)) :=
    pow_nonneg hcf_nn _
  have hpow_nn : (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d := pow_nonneg (by positivity) _
  have hprod_nn :
      (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2)) := mul_nonneg hpow_nn hcf_pow_nn
  -- Rearrange the cubic bound RHS to extract β·J·2·d factor and the matching prefactor.
  -- p.β · p.J · (2 · (d · (2(k+1)+1)^d) · cf^...)
  --   = (β · J · 2 · d) · ((2k+3)^d · cf^...)
  refine hbound.trans ?_
  -- Show: β * J * (2 * (d * (2(k+1)+1)^d) * cf^...) ≤ (2k+3)^d * cf^...
  have hrhs_eq :
      β * J * (2 * ((d : ℝ) * (2 * ((k : ℝ) + 1) + 1) ^ d) *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2)))
      = (β * J * (2 * d)) *
          (((2 * k + 3 : ℕ) : ℝ) ^ d *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2))) := by
    rw [hidx]; ring
  rw [hrhs_eq]
  calc β * J * (2 * (d : ℝ)) *
          (((2 * k + 3 : ℕ) : ℝ) ^ d *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2)))
      ≤ 1 *
          (((2 * k + 3 : ℕ) : ℝ) ^ d *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2))) :=
        mul_le_mul_of_nonneg_right hβJ2d hprod_nn
    _ = ((2 * k + 3 : ℕ) : ℝ) ^ d *
            contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((k + 1 - R) / (r₀ + 2)) := one_mul _

end Ambient
end IsingModel
