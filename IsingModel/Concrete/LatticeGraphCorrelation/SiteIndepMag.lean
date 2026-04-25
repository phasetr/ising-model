import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG

/-!
# Site-independent magnetization and two-point bounds at ℤ^d

- `uniformMagnetization` definition and basic properties.
- Basic bounds on the ℤ^d two-point functions (`twoPointFunction`).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Site-independent magnetization on ℤ^d -/

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

/-- **Nonnegativity of `uniformMagnetization`** (ferromagnetic).
Specialization of the abstract `magnetizationInfinite_nonneg`. -/
theorem uniformMagnetization_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ uniformMagnetization d p :=
  magnetizationInfinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf 0

/-- **Upper bound on `uniformMagnetization`**:
`uniformMagnetization d p ≤ 1`. -/
theorem uniformMagnetization_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    uniformMagnetization d p ≤ 1 :=
  magnetizationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **`-1 ≤ uniformMagnetization`** unconditionally. Specialization of
`neg_one_le_magnetizationInfinite` at site `0`. -/
theorem neg_one_le_uniformMagnetization
    (d : ℕ) (p : IsingParams ℝ) :
    -1 ≤ uniformMagnetization d p :=
  neg_one_le_magnetizationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **`|uniformMagnetization| ≤ 1`** unconditionally. Specialization of
`abs_magnetizationInfinite_le_one` at site `0`. -/
theorem abs_uniformMagnetization_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    |uniformMagnetization d p| ≤ 1 :=
  abs_magnetizationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **`uniformMagnetization² ≤ 1`** unconditionally. Specialization of
`magnetizationInfinite_sq_le_one` at site `0`. -/
theorem uniformMagnetization_sq_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    uniformMagnetization d p ^ 2 ≤ 1 :=
  magnetizationInfinite_sq_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0


/-- **Uniform spontaneous magnetization on ℤ^d**: by site-independence
of spontaneous magnetization on the translation-invariant ℤ^d lattice
(PR #257), we package the value at `0` as a scalar.

`uniformSpontaneousMagnetization d J β := spontaneousMagnetization
(latticeGraph d) (cubicExhaustion d) J β 0`. -/
noncomputable def uniformSpontaneousMagnetization
    (d : ℕ) (J β : ℝ) : ℝ :=
  spontaneousMagnetization (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β 0

/-- **Unfolding of `uniformSpontaneousMagnetization`**:
`uniformSpontaneousMagnetization d J β = spontaneousMagnetization
(latticeGraph d) (cubicExhaustion d) J β 0`. -/
theorem uniformSpontaneousMagnetization_apply (d : ℕ) (J β : ℝ) :
    uniformSpontaneousMagnetization d J β
      = spontaneousMagnetization (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) J β 0 := rfl

/-- **`uniformSpontaneousMagnetization` equals `spontaneousMagnetization`
under any Exhaustion** (ferromagnetic): bridges fixed-`cubicExhaustion`
definition to arbitrary Exhaustions via
`spontaneousMagnetization_indep_exhaustion`. -/
theorem uniformSpontaneousMagnetization_eq_spontaneousMagnetization_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    uniformSpontaneousMagnetization d J β
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ' J β 0 := by
  rw [uniformSpontaneousMagnetization_apply]
  exact spontaneousMagnetization_indep_exhaustion (IsingModel.latticeGraph d)
    _ Λ' hJ hβ 0

/-- **J-monotonicity of `uniformSpontaneousMagnetization` on ℤ^d**. -/
theorem uniformSpontaneousMagnetization_monotone_J
    (d : ℕ) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => uniformSpontaneousMagnetization d J β)
      (Set.Ici 0) :=
  spontaneousMagnetization_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hβ 0

/-- **β-monotonicity of `uniformSpontaneousMagnetization` on ℤ^d**. -/
theorem uniformSpontaneousMagnetization_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) :
    MonotoneOn
      (fun β : ℝ => uniformSpontaneousMagnetization d J β)
      (Set.Ioi 0) :=
  spontaneousMagnetization_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ 0

/-- **Bridge**: for `0 ≤ J`, `0 < β`, and any site `i : Fin d → ℤ`,
`spontaneousMagnetization ... J β i = uniformSpontaneousMagnetization d J β`.

Immediate from `spontaneousMagnetization_latticeGraph_cubicExhaustion_eq`
(PR #257). -/
theorem spontaneousMagnetization_latticeGraph_cubicExhaustion_eq_uniform
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β i
      = uniformSpontaneousMagnetization d J β :=
  spontaneousMagnetization_latticeGraph_cubicExhaustion_eq d hJ hβ i 0

/-- **Nonnegativity of `uniformSpontaneousMagnetization`**. -/
theorem uniformSpontaneousMagnetization_nonneg
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    0 ≤ uniformSpontaneousMagnetization d J β :=
  spontaneousMagnetization_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **Upper bound on `uniformSpontaneousMagnetization`**:
`uniformSpontaneousMagnetization d J β ≤ 1`. -/
theorem uniformSpontaneousMagnetization_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    uniformSpontaneousMagnetization d J β ≤ 1 :=
  spontaneousMagnetization_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **`-1 ≤ uniformSpontaneousMagnetization`** (ferromagnetic).
Direct from `uniformSpontaneousMagnetization_nonneg`. -/
theorem neg_one_le_uniformSpontaneousMagnetization
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    -1 ≤ uniformSpontaneousMagnetization d J β := by
  have := uniformSpontaneousMagnetization_nonneg d hJ hβ
  linarith

/-- **`|uniformSpontaneousMagnetization| ≤ 1`** (ferromagnetic). -/
theorem abs_uniformSpontaneousMagnetization_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    |uniformSpontaneousMagnetization d J β| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_uniformSpontaneousMagnetization d hJ hβ,
    uniformSpontaneousMagnetization_le_one d hJ hβ⟩

/-- **`uniformSpontaneousMagnetization² ≤ 1`** (ferromagnetic). -/
theorem uniformSpontaneousMagnetization_sq_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    uniformSpontaneousMagnetization d J β ^ 2 ≤ 1 :=
  spontaneousMagnetization_sq_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **ℤ^d `spontaneousCorrelation` apply** (any-Exhaustion):
`spontaneousCorrelation = ⨅ h ∈ Ioi 0, correlationInfinite ⟨J, h, β⟩ A`. -/
theorem spontaneousCorrelation_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A
      = ⨅ h : ↥(Set.Ioi (0 : ℝ)),
          correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h.val, β⟩ A :=
  spontaneousCorrelation_apply (IsingModel.latticeGraph d) Λ J β A

/-- **ℤ^d `spontaneousMagnetization` apply** (any-Exhaustion):
singleton specialization of `spontaneousCorrelation_apply`. -/
theorem spontaneousMagnetization_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i
      = ⨅ h : ↥(Set.Ioi (0 : ℝ)),
          magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h.val, β⟩ i :=
  spontaneousCorrelation_apply (IsingModel.latticeGraph d) Λ J β {i}

/-- **ℤ^d `-1 ≤ spontaneousMagnetization`** (ferromagnetic). -/
theorem neg_one_le_spontaneousMagnetization_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    -1 ≤ spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i :=
  neg_one_le_spontaneousMagnetization (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d `|spontaneousMagnetization| ≤ 1`** (ferromagnetic). -/
theorem abs_spontaneousMagnetization_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    |spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i| ≤ 1 :=
  abs_spontaneousMagnetization_le_one (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d spontaneousMagnetization ≥ 0** (ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    0 ≤ spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i :=
  spontaneousMagnetization_nonneg (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d spontaneousMagnetization ≤ 1** (ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i ≤ 1 :=
  spontaneousMagnetization_le_one (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d J-direction monotonicity of `spontaneousMagnetization`**
(ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun J : ℝ => spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i)
      (Set.Ici 0) :=
  spontaneousMagnetization_monotone_J (IsingModel.latticeGraph d) Λ hβ i

/-- **ℤ^d β-direction monotonicity of `spontaneousMagnetization`**
(ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) (i : Fin d → ℤ) :
    MonotoneOn
      (fun β : ℝ => spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i)
      (Set.Ioi 0) :=
  spontaneousMagnetization_monotone_beta (IsingModel.latticeGraph d) Λ hJ i

/-- **`uniformMagnetization` at `β = 0`**:
`uniformMagnetization d ⟨J, h, 0⟩ = 0`.

Concrete specialisation of `magnetizationInfinite_beta_zero` at site `0`:
at infinite temperature (`β = 0`) all spin correlations vanish, in
particular the magnetization. No ferromagnetic hypothesis needed. -/
theorem uniformMagnetization_beta_zero
    (d : ℕ) (J h : ℝ) :
    uniformMagnetization d (⟨J, h, 0⟩ : IsingParams ℝ) = 0 :=
  magnetizationInfinite_beta_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J h 0

/-- **J-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ 0

/-- **h-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **β-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ioi 0) :=
  magnetizationInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh 0

/-- **`uniformMagnetization` at `J = 0`**:
`uniformMagnetization d ⟨0, h, β⟩ = tanh(β · h)` (ferromagnetic).

Concrete specialisation of `magnetizationInfinite_J_zero` at site `0`
on the `(latticeGraph d, cubicExhaustion d)` pair. Non-interacting
slice: at `J = 0` the Ising Hamiltonian has no coupling, so each site
is an independent two-state system with Boltzmann weight `exp(β h s)`,
giving `M = tanh(β h)`. -/
theorem uniformMagnetization_J_zero
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ)) :
    uniformMagnetization d (⟨0, h, β⟩ : IsingParams ℝ) = Real.tanh (β * h) :=
  magnetizationInfinite_J_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) h β hf 0

/-- **`uniformMagnetization` at `J = h = 0`**:
`uniformMagnetization d ⟨0, 0, β⟩ = 0`.

At `J = h = 0` the Hamiltonian vanishes identically, so all site-level
correlations are zero. Direct from `correlationInfinite_zero_params_vanish`
at the singleton `{0}`. -/
theorem uniformMagnetization_zero_params
    (d : ℕ) (β : ℝ) :
    uniformMagnetization d (⟨0, 0, β⟩ : IsingParams ℝ) = 0 := by
  unfold uniformMagnetization magnetizationInfinite
  exact correlationInfinite_zero_params_vanish
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) β
    {(0 : Fin d → ℤ)} (by simp)

/-- **Z₂ symmetry at `h = 0`**: `uniformMagnetization d ⟨J, 0, β⟩ = 0`.

Concrete specialisation of `magnetizationInfinite_zero_at_h_zero` at
site `0` on the `(latticeGraph d, cubicExhaustion d)` pair. At `h = 0`
the finite-volume Ising model is Z₂-symmetric (flip `σ ↦ −σ`), so
the magnetization vanishes stage-by-stage, hence at ∞-vol. -/
theorem uniformMagnetization_zero_at_h_zero
    (d : ℕ) (J β : ℝ) :
    uniformMagnetization d ⟨J, 0, β⟩ = 0 :=
  magnetizationInfinite_zero_at_h_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β 0

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

/-! ## Basic bounds on the ℤ^d two-point functions -/

/-- **Nonnegativity of `twoPointFunction`** (GKS-I).
`0 ≤ twoPointFunction d p r`. -/
theorem twoPointFunction_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    0 ≤ twoPointFunction d p r :=
  correlationInfinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf {(0 : Fin d → ℤ), r}

/-- **Upper bound on `twoPointFunction`** (boundedness of correlation).
`twoPointFunction d p r ≤ 1`. -/
theorem twoPointFunction_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    twoPointFunction d p r ≤ 1 :=
  correlationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **`-1 ≤ twoPointFunction`** unconditionally. Direct specialization
of `neg_one_le_correlationInfinite` at `A = {0, r}`. -/
theorem neg_one_le_twoPointFunction
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    -1 ≤ twoPointFunction d p r :=
  neg_one_le_correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **ℤ^d `twoPointFunction ≥ tanh(β·h)²` for `r ≠ 0`** (ferromagnetic):
specialization of `correlationInfinite_ge_tanh_pow_card` at `A = {0, r}`
where `A.card = 2` (since `r ≠ 0`). -/
theorem twoPointFunction_ge_tanh_sq_of_ne
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    {r : Fin d → ℤ} (hr : r ≠ 0) :
    Real.tanh (β * h) ^ 2 ≤ twoPointFunction d (⟨J, h, β⟩ : IsingParams ℝ) r := by
  have hcard : ({(0 : Fin d → ℤ), r} : Finset (Fin d → ℤ)).card = 2 := by
    rw [Finset.card_pair (Ne.symm hr)]
  have := correlationInfinite_ge_tanh_pow_card (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ ({(0 : Fin d → ℤ), r} : Finset _)
  rw [hcard] at this
  exact this

/-- **`|twoPointFunction| ≤ 1`** unconditionally. Direct specialization
of `abs_correlationInfinite_le_one` at `A = {0, r}`. -/
theorem abs_twoPointFunction_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    |twoPointFunction d p r| ≤ 1 :=
  abs_correlationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **`twoPointFunction² ≤ 1`** unconditionally. Direct specialization
of `correlationInfinite_sq_le_one` at `A = {0, r}`. -/
theorem twoPointFunction_sq_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    twoPointFunction d p r ^ 2 ≤ 1 :=
  correlationInfinite_sq_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **`twoPointFunction` at `h = 0, r = 0` vanishes** (Z₂ via
`twoPointFunction_zero` + `magnetizationInfinite_zero_at_h_zero`):
`twoPointFunction d ⟨J, 0, β⟩ 0 = 0`. -/
theorem twoPointFunction_h_zero_at_zero (d : ℕ) (J β : ℝ) :
    twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) 0 = 0 := by
  rw [twoPointFunction_zero,
      magnetizationInfinite_zero_at_h_zero]

/-- **`truncated2TwoPoint` at `h = 0, r = 0` vanishes**: at `r = 0`,
`truncated2TwoPoint = M · (1 − M)`; at `h = 0`, `M = 0` by Z₂, so the
product is `0`. -/
theorem truncated2TwoPoint_h_zero_at_zero (d : ℕ) (J β : ℝ) :
    truncated2TwoPoint d (⟨J, 0, β⟩ : IsingParams ℝ) 0 = 0 := by
  rw [truncated2TwoPoint_zero,
      magnetizationInfinite_zero_at_h_zero]
  ring

/-- **J-monotonicity of `twoPointFunction`** (GJ Prop 4.2.1):
for `0 ≤ h, 0 < β`, `twoPointFunction d ⟨J, h, β⟩ r` is monotone in
`J` on `Ici 0`. Direct specialization of
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_J` at
`A = {0, r}`. -/
theorem twoPointFunction_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (r : Fin d → ℤ) :
    MonotoneOn (fun J : ℝ => twoPointFunction d ⟨J, h, β⟩ r) (Set.Ici 0) :=
  correlationInfinite_latticeGraph_cubicExhaustion_monotone_J d hh hβ
    {(0 : Fin d → ℤ), r}

/-- **h-monotonicity of `twoPointFunction`** (GJ Prop 4.2.4):
for `0 ≤ J, 0 < β`, `twoPointFunction d ⟨J, h, β⟩ r` is monotone in
`h` on `Ici 0`. Direct specialization of
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_h`. -/
theorem twoPointFunction_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (r : Fin d → ℤ) :
    MonotoneOn (fun h : ℝ => twoPointFunction d ⟨J, h, β⟩ r) (Set.Ici 0) :=
  correlationInfinite_latticeGraph_cubicExhaustion_monotone_h d hJ hβ
    {(0 : Fin d → ℤ), r}

/-- **β-monotonicity of `twoPointFunction`** (GJ Prop 4.2.4):
for `0 ≤ J, 0 ≤ h`, `twoPointFunction d ⟨J, h, β⟩ r` is monotone in
`β` on `Ioi 0`. Direct specialization of
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_beta`. -/
theorem twoPointFunction_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (r : Fin d → ℤ) :
    MonotoneOn (fun β : ℝ => twoPointFunction d ⟨J, h, β⟩ r) (Set.Ioi 0) :=
  correlationInfinite_latticeGraph_cubicExhaustion_monotone_beta d hJ hh
    {(0 : Fin d → ℤ), r}

/-- **Nonnegativity of `truncated2TwoPoint`** (GKS-II).
`0 ≤ truncated2TwoPoint d p r`. -/
theorem truncated2TwoPoint_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    0 ≤ truncated2TwoPoint d p r :=
  truncated2Infinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf 0 r

/-- **Two-point function bounded below by magnetization squared**:
for ferromagnetic `p` and any `r : Fin d → ℤ`,

`(magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p 0)^2
  ≤ twoPointFunction d p r`.

Proof: from `truncated2TwoPoint_nonneg` (GKS-II) and the identity
`truncated2TwoPoint d p r = twoPointFunction d p r − M²` (PR #261),
we get `0 ≤ twoPointFunction d p r − M²`, hence `M² ≤ twoPointFunction
d p r`. This is a classical physical bound: the 2-point function at
infinite volume is at least as large as the squared magnetization. -/
theorem twoPointFunction_ge_magnetization_sq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    (magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p 0)^2
      ≤ twoPointFunction d p r := by
  have h_nonneg := truncated2TwoPoint_nonneg d p hf r
  have h_identity := truncated2TwoPoint_eq_twoPointFunction_sub_magnetization_sq
    d p hf r
  linarith [h_identity.symm ▸ h_nonneg]

/-- **Symmetry of `truncated3TwoPoint` under `(r, s)` swap**:
`truncated3TwoPoint d p r s = truncated3TwoPoint d p s r`.

Reduces to the pairwise-symmetry of the Ursell 3-point function in
its last two arguments, via unfolding and commutativity of the
relevant Finset literals and products. -/
theorem truncated3TwoPoint_symm_rs
    (d : ℕ) (p : IsingParams ℝ) (r s : Fin d → ℤ) :
    truncated3TwoPoint d p r s = truncated3TwoPoint d p s r := by
  unfold truncated3TwoPoint truncated3Infinite
  -- `{0, r, s} = {0, s, r}` (unordered).
  have h_triple : ({(0 : Fin d → ℤ), r, s} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ), s, r} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h_rs : ({r, s} : Finset (Fin d → ℤ)) = {s, r} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [h_triple, h_rs]
  ring

/-- **Symmetry of `truncated4TwoPoint` under `(r, s)` swap**:
`truncated4TwoPoint d p r s u = truncated4TwoPoint d p s r u`.

From the Lebowitz 4-point definition: swapping `j ↔ k` in
`truncated4Infinite ... i j k l` permutes the three pair-products,
yielding the same sum. -/
theorem truncated4TwoPoint_symm_rs
    (d : ℕ) (p : IsingParams ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u = truncated4TwoPoint d p s r u := by
  unfold truncated4TwoPoint truncated4Infinite
  have h_quad : ({(0 : Fin d → ℤ), r, s, u} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ), s, r, u} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have h_rs : ({r, s} : Finset (Fin d → ℤ)) = {s, r} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [h_quad, h_rs]
  ring

/-- **Symmetry of `truncated4TwoPoint` under `(s, u)` swap**:
`truncated4TwoPoint d p r s u = truncated4TwoPoint d p r u s`.

Same Lebowitz-permutation argument applied to swap of `k ↔ l`. -/
theorem truncated4TwoPoint_symm_su
    (d : ℕ) (p : IsingParams ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u = truncated4TwoPoint d p r u s := by
  unfold truncated4TwoPoint truncated4Infinite
  have h_quad : ({(0 : Fin d → ℤ), r, s, u} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ), r, u, s} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have h_su : ({s, u} : Finset (Fin d → ℤ)) = {u, s} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [h_quad, h_su]
  ring

/-- **Symmetry of `truncated4TwoPoint` under `(r, u)` swap**:
`truncated4TwoPoint d p r s u = truncated4TwoPoint d p u s r`. Derived by
chaining `_symm_rs`, `_symm_su`, `_symm_rs` to implement the transposition
`(r, u)` via adjacent swaps. -/
theorem truncated4TwoPoint_symm_ru
    (d : ℕ) (p : IsingParams ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u = truncated4TwoPoint d p u s r := by
  rw [truncated4TwoPoint_symm_rs d p r s u,
      truncated4TwoPoint_symm_su d p s r u,
      truncated4TwoPoint_symm_rs d p s u r]

end Ambient
end IsingModel
