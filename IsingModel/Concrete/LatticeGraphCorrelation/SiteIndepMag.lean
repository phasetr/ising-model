import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationSiteIndep
import IsingModel.TranslationInvariance

/-!
# ℤ^d site-independent magnetization and its spontaneous limit

Defines the uniform magnetization and the uniform spontaneous magnetization at
`IsingModel.latticeGraph d` along `Ambient.cubicExhaustion d` as the value of
`magnetizationInfinite`, respectively of `spontaneousMagnetization`, at the origin.
Naming the magnetization at the origin loses nothing: under `Ferromagnetic` the
infinite-volume magnetization along the cubic exhaustion takes the same value at every
site, recorded here as a `@[simp]` rewrite towards the uniform form.

The uniform magnetization unfolds to its definition without a hypothesis. It is at least
`Real.tanh (β * h)` for a non-negative coupling, a non-negative field and a positive
inverse temperature, and under `Ferromagnetic` it also agrees with the infinite-volume
magnetization at the origin computed along any other `Ambient.Exhaustion` of `Fin d → ℤ`.

The uniform spontaneous magnetization is the limit of the uniform magnetization as the
external field decreases to zero from above, and it is a lower bound for the uniform
magnetization at every strictly positive field. Both of those assume a non-negative
coupling and a positive inverse temperature, the second a strictly positive field as well.
No instance argument is taken anywhere in this module.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Uniform magnetization on ℤ^d**: since the ∞-vol magnetization is
site-independent on the translation-invariant ℤ^d lattice (PR #257),
we package the value at `0` as a scalar `uniformMagnetization d p`.

`uniformMagnetization d p := magnetizationInfinite (latticeGraph d)
(cubicExhaustion d) p 0`. -/
noncomputable def uniformMagnetization (d : ℕ) (p : IsingParams ℝ) : ℝ :=
  magnetizationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **Unfolding of `uniformMagnetization`**:
`uniformMagnetization d p = magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p 0`. -/
theorem uniformMagnetization_apply (d : ℕ) (p : IsingParams ℝ) :
    uniformMagnetization d p
      = magnetizationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 := rfl

/-- **ℤ^d `uniformMagnetization ≥ tanh(β·h)`** (ferromagnetic). -/
theorem uniformMagnetization_ge_tanh
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.tanh (β * h)
      ≤ uniformMagnetization d (⟨J, h, β⟩ : IsingParams ℝ) :=
  magnetizationInfinite_ge_tanh (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ 0

/-- **`uniformMagnetization` equals `magnetizationInfinite` under any
Exhaustion** (ferromagnetic): bridges the fixed-`cubicExhaustion` form
to arbitrary Exhaustions via `magnetizationInfinite_indep_exhaustion`. -/
theorem uniformMagnetization_eq_magnetizationInfinite_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    uniformMagnetization d p
      = magnetizationInfinite (IsingModel.latticeGraph d) Λ' p 0 := by
  rw [uniformMagnetization_apply]
  exact magnetizationInfinite_indep_exhaustion (IsingModel.latticeGraph d) _ Λ' p hf 0

/-- **Bridge**: for ferromagnetic `p` and any site `i : Fin d → ℤ`,
`magnetizationInfinite ... p i = uniformMagnetization d p`.

Immediate from `magnetizationInfinite_latticeGraph_cubicExhaustion_eq`
(PR #257) at `i, 0`. -/
@[simp]
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_eq_uniform
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p i
      = uniformMagnetization d p :=
  magnetizationInfinite_latticeGraph_cubicExhaustion_eq d p hf i 0

/-- **Uniform spontaneous magnetization on ℤ^d**: by site-independence
of spontaneous magnetization on the translation-invariant ℤ^d lattice
(PR #257), we package the value at `0` as a scalar.

`uniformSpontaneousMagnetization d J β := spontaneousMagnetization
(latticeGraph d) (cubicExhaustion d) J β 0`. -/
noncomputable def uniformSpontaneousMagnetization
    (d : ℕ) (J β : ℝ) : ℝ :=
  spontaneousMagnetization (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β 0

/-- **Right-limit** `uniformMagnetization` → `uniformSpontaneousMagnetization`
as `h → 0⁺`.

Concrete specialization of the abstract
`tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT`
at site `0` on the `(latticeGraph d, cubicExhaustion d)` pair. Realises
the spontaneous magnetization as the right limit of the uniform
(site-independent) magnetization as the external field `h` approaches
zero from above. -/
theorem tendsto_uniformMagnetization_uniformSpontaneousMagnetization_nhdsGT
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    Filter.Tendsto
      (fun h : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (uniformSpontaneousMagnetization d J β)) :=
  tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) hJ hβ 0

/-- **`uniformSpontaneousMagnetization ≤ uniformMagnetization` at `h > 0`**:
for `0 ≤ J`, `0 < β`, `0 < h`,

`uniformSpontaneousMagnetization d J β
  ≤ uniformMagnetization d ⟨J, h, β⟩`.

Direct specialization of `spontaneousMagnetization_le_magnetizationInfinite`
at site `0` combined with the uniform recasts. The Ising parameter
record `⟨J, h, β⟩` with `0 < h` is ferromagnetic, so the
`uniformMagnetization` bridge applies. -/
theorem uniformSpontaneousMagnetization_le_uniformMagnetization
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) :
    uniformSpontaneousMagnetization d J β
      ≤ uniformMagnetization d ⟨J, h, β⟩ :=
  spontaneousMagnetization_le_magnetizationInfinite
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) hJ hβ hh 0

end Ambient
end IsingModel
