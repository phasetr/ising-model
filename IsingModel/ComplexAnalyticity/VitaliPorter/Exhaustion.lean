import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Analysis.Complex.Basic

/-!
# Vitali–Porter: compact exhaustion of an open subset of `ℂ`

Building block toward eliminating the declared scope-excluded axiom
`vitaliPorter_tendstoLocallyUniformlyOn` (Issue #4280). It packages a **compact exhaustion** of an
open set `U ⊆ ℂ` *as subsets of `ℂ`*: an increasing-in-content sequence `K : ℕ → Set ℂ` of compact
subsets of `U` whose union covers `U` and such that **every** compact `C ⊆ U` lies in some `K m`.
This is what the diagonal Montel extraction needs to reduce locally-uniform convergence on `U` to
uniform convergence on each `K m`.

It is obtained from `CompactExhaustion.choice` on the open subspace `↥U` (locally compact +
σ-compact, as an open subset of the second-countable locally compact space `ℂ`), pushed forward
along `Subtype.val`.

**Reference:** standard point-set topology (σ-compact exhaustion). -/

namespace IsingModel
namespace FunctionTheory

open Set Topology

/-- **Compact exhaustion of an open `U ⊆ ℂ` by subsets of `ℂ`**.

There is a sequence `K : ℕ → Set ℂ` with: each `K m` compact and contained in `U`; every point of
`U` lies in some `K m`; and every compact `C ⊆ U` is contained in some `K m`. -/
theorem exists_compactExhaustion_of_isOpen
    {U : Set ℂ} (hU : IsOpen U) :
    ∃ K : ℕ → Set ℂ, (∀ m, IsCompact (K m)) ∧ (∀ m, K m ⊆ U) ∧
      (∀ z ∈ U, ∃ m, z ∈ K m) ∧
      (∀ C : Set ℂ, IsCompact C → C ⊆ U → ∃ m, C ⊆ K m) := by
  haveI hlc : LocallyCompactSpace U := hU.locallyCompactSpace
  haveI : SigmaCompactSpace U := by infer_instance
  let E := CompactExhaustion.choice U
  have hrange : range (Subtype.val : U → ℂ) = U := Subtype.range_coe
  refine ⟨fun m => Subtype.val '' (E m), ?_, ?_, ?_, ?_⟩
  · -- compactness of each `K m`
    intro m
    exact (E.isCompact m).image continuous_subtype_val
  · -- `K m ⊆ U`
    intro m
    exact Subtype.coe_image_subset U (E m)
  · -- every point of `U` is in some `K m`
    intro z hz
    refine ⟨E.find ⟨z, hz⟩, ⟨z, hz⟩, E.mem_find ⟨z, hz⟩, rfl⟩
  · -- every compact `C ⊆ U` lies in some `K m`
    intro C hC hCU
    set s : Set U := Subtype.val ⁻¹' C with hs_def
    have hval_s : Subtype.val '' s = C := by
      rw [hs_def, image_preimage_eq_inter_range, hrange, inter_eq_left.mpr hCU]
    have hs_compact : IsCompact s := by
      rw [IsEmbedding.subtypeVal.isCompact_iff, hval_s]
      exact hC
    obtain ⟨m, hsm⟩ := E.exists_superset_of_isCompact hs_compact
    refine ⟨m, ?_⟩
    calc C = Subtype.val '' s := hval_s.symm
      _ ⊆ Subtype.val '' (E m) := image_mono hsm

end FunctionTheory
end IsingModel
