import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `spontaneousMagnetization_latticeGraph` sign/bound wrappers

Narrow child module for the four ℤ^d `spontaneousMagnetization_latticeGraph`
sign-range and absolute-bound wrappers:

* `neg_one_le_spontaneousMagnetization_latticeGraph`,
* `abs_spontaneousMagnetization_latticeGraph_le_one`,
* `spontaneousMagnetization_latticeGraph_nonneg`,
* `spontaneousMagnetization_latticeGraph_le_one`.

Each result is a thin pass-through to the corresponding ambient
`spontaneousMagnetization_*` lemma at `IsingModel.latticeGraph d`.
The theorem names are unchanged from the former
`SiteIndepMagSpontaneous` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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

end Ambient

end IsingModel
