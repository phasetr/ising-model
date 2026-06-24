import IsingModel.ComplexAnalyticity.VitaliPorter.PerCompact
import IsingModel.ComplexAnalyticity.VitaliPorter.Exhaustion

/-!
# Vitali–Porter: Montel diagonal extraction

Building block toward eliminating the declared scope-excluded axiom
`vitaliPorter_tendstoLocallyUniformlyOn` (Issue #4280). Assembling the per-compact Arzelà–Ascoli
extraction (`PerCompact.lean`) over a compact exhaustion (`Exhaustion.lean`) by a diagonal argument
gives the full **Montel** theorem: a locally uniformly bounded family of holomorphic functions on an
open `U ⊆ ℂ` has a subsequence converging **locally uniformly on `U`** to a holomorphic limit.

This file provides the **uniform-bound-on-compacts** helper feeding that extraction: a locally
uniformly bounded family is uniformly bounded on every compact subset (so the per-compact
Arzelà–Ascoli hypothesis is met at each stage of the exhaustion). The diagonal assembly follows in a
subsequent step.

**Reference:** Conway, *Functions of One Complex Variable I*, VII §2 (Montel / normal families). -/

namespace IsingModel
namespace FunctionTheory

open Filter Topology Metric Set

/-- **A locally uniformly bounded family is uniformly bounded on each compact subset**.

From the local-boundedness data (each point of `U` has a ball on which the whole family is bounded)
and compactness of `K ⊆ U`, a finite subcover yields a single bound `M` valid for all `n` and all
`z ∈ K`. -/
theorem exists_bound_on_compact_of_locallyBounded
    {U : Set ℂ} {F : ℕ → ℂ → ℂ}
    (hbdd : ∀ z ∈ U, ∃ r M : ℝ, 0 < r ∧ ball z r ⊆ U ∧
      ∀ n, ∀ w ∈ ball z r, ‖F n w‖ ≤ M)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖F n z‖ ≤ M := by
  classical
  -- Per-point ball radius and bound.
  choose! r M hr hball hbound using hbdd
  -- Open cover of `K` by the balls `ball ↑z (r ↑z)`, indexed by `z : ↥K`.
  have hcover : K ⊆ ⋃ z : K, ball (↑z) (r ↑z) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr z (hKU hz))⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => ball (↑z) (r ↑z))
    (fun _ => isOpen_ball) hcover
  rcases t.eq_empty_or_nonempty with rfl | htne
  · -- empty subcover forces `K = ∅`; any bound works
    exact ⟨0, fun n z hz => absurd (ht hz) (by simp)⟩
  · refine ⟨t.sup' htne (fun z : K => M ↑z), fun n z hz => ?_⟩
    obtain ⟨i, hit, hzi⟩ := mem_iUnion₂.mp (ht hz)
    calc ‖F n z‖ ≤ M ↑i := hbound (↑i) (hKU i.2) n z hzi
      _ ≤ t.sup' htne (fun z : K => M ↑z) := Finset.le_sup' (fun z : K => M ↑z) hit

end FunctionTheory
end IsingModel
