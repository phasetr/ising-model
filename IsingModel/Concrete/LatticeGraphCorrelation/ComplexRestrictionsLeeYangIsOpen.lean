import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.RealAxis

/-!
# Concrete Complex leeYang + slitPlane-locus openness wrappers

Narrow child module for 4 ℤ^d Complex leeYangSubdomain inclusion +
slitPlane-locus openness wrappers extracted from
`ComplexRestrictions.lean`:

* `leeYangSubdomain_subset_slitPlane_locus_latticeGraph`,
* `mem_slitPlane_locus_of_mem_leeYangSubdomain_latticeGraph`,
* `isOpen_logZ_slitPlane_locus_latticeGraph`,
* `isOpen_slitPlane_locus_h_beta_latticeGraph`.

Each is a thin pass-through of the corresponding ambient
`IsingModel.{leeYangSubdomain_subset_slitPlane_locus,
mem_slitPlane_locus_of_mem_leeYangSubdomain,
isOpen_logZ_slitPlane_locus, isOpen_slitPlane_locus_h_beta}` lemma at
`Ambient.inducedGraph (IsingModel.latticeGraph d) Λ`. The theorem
names are unchanged from the former `ComplexRestrictions` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `leeYangSubdomain ⊆ slitPlane_locus`** (Λ-induced,
ferromagnetic `β > 0`). -/
theorem leeYangSubdomain_subset_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _)))
      ⊆ {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane} :=
  IsingModel.leeYangSubdomain_subset_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `h ∈ leeYangSubdomain ⇒ Z_ℂ ∈ slitPlane`** (Λ-induced). -/
theorem mem_slitPlane_locus_of_mem_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane :=
  IsingModel.mem_slitPlane_locus_of_mem_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J hh

/-- **ℤ^d `logZ` slitPlane-locus is open** (Λ-induced). -/
theorem isOpen_logZ_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    IsOpen {h : ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_logZ_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d slitPlane-locus open in `(h, β)`** (Λ-induced). -/
theorem isOpen_slitPlane_locus_h_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℂ) :
    IsOpen {z : ℂ × ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J z.1 z.2
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_slitPlane_locus_h_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J

end Ambient

end IsingModel
