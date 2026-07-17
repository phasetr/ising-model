import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Archimedean

/-!
# GJ §17.5 Theorem 17.5.1 — Step-2: an infimum of uniformly-Lipschitz functions is Lipschitz

The pure real-analysis core of GJ's `A↑ℝ^d` limit (p.312): GJ proves `m⁻(σ,A)^{2α+1}` is Lipschitz
in `σ` with a constant *uniform in the bounded region A*, and then concludes for the system mass
`m⁻(σ) = inf_A m⁻(σ,A)`.  The passage from "each finite-region power is `L`-Lipschitz with the
*same* `L`" to "the infimum over `A` is `L`-Lipschitz" needs no differentiation and no attainment
of the infimum: it is the two-point inequality
`|inf_i g_i b − inf_i g_i a| ≤ sup_i |g_i b − g_i a| ≤ L`.

This is precisely why the apparent "binding-pair existence" obstruction (the infinite `sInf` over
pairs is not attained in the Ornstein--Zernike regime; cf. #4320) **dissolves**: one does not take
the inf over pairs and differentiate it, but rather the inf over the *finite, attained* regions `A`
of functions that are *already* (uniformly) Lipschitz.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Two-point bound for an infimum of uniformly-close families** (GJ p.312, `A↑` step): for two
families `fa, fb : ι → ℝ` (values at the two endpoints) with bounded-below ranges and a uniform
pairwise bound `|fb i − fa i| ≤ L`, the infima differ by at most `L`:
`|sInf (range fb) − sInf (range fa)| ≤ L`.

Pure `sInf` algebra: `sInf (range fa) − L` is a lower bound of `range fb` (`fb i ≥ fa i − L`), so
`sInf (range fa) − L ≤ sInf (range fb)` (`le_csInf`); symmetrically `sInf (range fb) − L ≤
sInf (range fa)`.  No differentiation and no attainment of either infimum is used. -/
theorem abs_csInf_range_sub_csInf_range_le {ι : Type*} [Nonempty ι] {fa fb : ι → ℝ} {L : ℝ}
    (hbdda : BddBelow (Set.range fa)) (hbddb : BddBelow (Set.range fb))
    (hlip : ∀ i, |fb i - fa i| ≤ L) :
    |sInf (Set.range fb) - sInf (Set.range fa)| ≤ L := by
  have hnea : (Set.range fa).Nonempty := Set.range_nonempty fa
  have hneb : (Set.range fb).Nonempty := Set.range_nonempty fb
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- `−L ≤ sInf (range fb) − sInf (range fa)`, i.e. `sInf (range fa) − L ≤ sInf (range fb)`.
    have hlb : ∀ y ∈ Set.range fb, sInf (Set.range fa) - L ≤ y := by
      rintro y ⟨i, rfl⟩
      have h1 : sInf (Set.range fa) ≤ fa i := csInf_le hbdda ⟨i, rfl⟩
      have h2 := (abs_le.mp (hlip i)).1
      linarith
    have := le_csInf hneb hlb
    linarith
  · -- `sInf (range fb) − sInf (range fa) ≤ L`, i.e. `sInf (range fb) − L ≤ sInf (range fa)`.
    have hlb : ∀ y ∈ Set.range fa, sInf (Set.range fb) - L ≤ y := by
      rintro y ⟨i, rfl⟩
      have h1 : sInf (Set.range fb) ≤ fb i := csInf_le hbddb ⟨i, rfl⟩
      have h2 := (abs_le.mp (hlip i)).2
      linarith
    have := le_csInf hnea hlb
    linarith

/-- **Infimum of uniformly-Lipschitz functions is Lipschitz** (GJ p.312, `A↑` step): if a family
`g : ι → ℝ → ℝ` of functions satisfies the *same* interval-Lipschitz increment bound
`|g i β₂ − g i β₁| ≤ L·(β₂ − β₁)` for every `i`, and the pointwise ranges are bounded below, then
the lower envelope `G β = sInf (range (g · β))` obeys `|G β₂ − G β₁| ≤ L·(β₂ − β₁)`.

Direct corollary of `abs_csInf_range_sub_csInf_range_le` with `fa = g · β₁`, `fb = g · β₂`. -/
theorem abs_csInf_envelope_sub_le_of_uniform_lipschitz {ι : Type*} [Nonempty ι]
    {g : ι → ℝ → ℝ} {β₁ β₂ L : ℝ}
    (hbdd₁ : BddBelow (Set.range (fun i => g i β₁)))
    (hbdd₂ : BddBelow (Set.range (fun i => g i β₂)))
    (hlip : ∀ i, |g i β₂ - g i β₁| ≤ L * (β₂ - β₁)) :
    |sInf (Set.range (fun i => g i β₂)) - sInf (Set.range (fun i => g i β₁))|
      ≤ L * (β₂ - β₁) :=
  abs_csInf_range_sub_csInf_range_le hbdd₁ hbdd₂ hlip

end Ambient
end IsingModel
