import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivative
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivativeSuscSq

/-!
# §17.5 high-temperature Lebowitz / β/J derivative wrappers

Narrow child module for three unconditional high-temperature
`inducedLatticeGraph_*_high_temp` wrappers extracted from
`LatticeMassLebowitzDerivative.lean`:

* `inducedLatticeGraph_leb_sum_le_susceptibilityInfinite_high_temp`,
* `inducedLatticeGraph_beta_deriv_le_susc_sq_high_temp`,
* `inducedLatticeGraph_J_deriv_le_susc_sq_high_temp`.

Each wrapper combines Step 164
(`susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp`)
with the corresponding `BddAbove`-conditioned step (Steps 162 / 163 / 219),
removing the explicit `BddAbove` hypothesis.
-/

namespace IsingModel
namespace Ambient

/-- **Unconditional Lebowitz-sum ≤ χ_∞² under high-temperature condition** (Step 165, GJ §17.5):
For any exhaustion `Λ` of `ℤ^d`, `0 ≤ J`, `0 < β`, `βJ·2d < 1`, vertices `r s ∈ Λ_n`:
`∑_{e ∈ E(G_n)} leb(e) ≤ χ_∞(r) · χ_∞(s)`,
with no explicit `BddAbove` hypothesis (supplied automatically by Step 164).

Proof: Step 164 (`susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp`)
provides `BddAbove`; then Step 162
(`inducedLatticeGraph_leb_sum_le_susceptibilityInfinite`) closes the goal.

Reference: Glimm–Jaffe §17.5 p.~312. -/
theorem inducedLatticeGraph_leb_sum_le_susceptibilityInfinite_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let p := (⟨J, 0, β⟩ : IsingParams ℝ)
    ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v =>
        IsingModel.correlation G p {r, u} * IsingModel.correlation G p {s, v} +
        IsingModel.correlation G p {r, v} * IsingModel.correlation G p {s, u},
        fun u v => by ring⟩ e
    ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ p r.val *
      susceptibilityInfinite (IsingModel.latticeGraph d) Λ p s.val := by
  intro G p
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have hbdd_r :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt r.val
  have hbdd_s :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt s.val
  exact inducedLatticeGraph_leb_sum_le_susceptibilityInfinite Λ J β hJ hβ n r s hbdd_r hbdd_s

/-- **Unconditional β-derivative bound via χ_∞² under high-temperature condition**
(Step 166, GJ §17.5):
For any exhaustion `Λ` of `ℤ^d`, `0 ≤ J`, `0 < β`, `βJ·2d < 1`,
vertices `r ≠ s ∈ Λ_n`:
`d/dβ corr_n(r,s)(β) ≤ J · χ_∞(r) · χ_∞(s) + J · 4d`,
with no explicit `BddAbove` hypothesis.

Proof: Step 164 supplies `BddAbove`; then Step 163
(`inducedLatticeGraph_beta_deriv_le_susc_sq`) closes the goal.

Reference: Glimm–Jaffe §17.5 p.~312. -/
theorem inducedLatticeGraph_beta_deriv_le_susc_sq_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s) :
    ∃ dval : ℝ,
      HasDerivAt (fun β' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) dval β ∧
      dval ≤ J * susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) r.val *
               susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) s.val + J * (4 * ↑d) := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have hlt' : β * J * ↑(2 * d) < 1 := by linarith [mul_comm β J, mul_comm J β]
  have hbdd_r :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt' r.val
  have hbdd_s :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt' s.val
  exact inducedLatticeGraph_beta_deriv_le_susc_sq Λ J β hJ hβ n r s hrs hbdd_r hbdd_s

/-- **Unconditional J-derivative bound under high-temperature condition** (Step 220):
For any exhaustion `Λ` of `ℤ^d`, `0 ≤ J`, `0 < β`, `βJ·2d < 1`,
vertices `r ≠ s ∈ Λ_n`:
`d/dJ corr_n(r,s)(J)|_{h=0} ≤ β · χ_∞(r) · χ_∞(s) + β · 4d`,
with no explicit `BddAbove` hypothesis.

Direct J-direction analogue of Step 166 (`inducedLatticeGraph_beta_deriv_le_susc_sq_high_temp`).
Proof: Step 164 supplies `BddAbove`; then Step 219
(`inducedLatticeGraph_J_deriv_le_susc_sq`) closes the goal. -/
theorem inducedLatticeGraph_J_deriv_le_susc_sq_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s) :
    ∃ dval : ℝ,
      HasDerivAt (fun J' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J', 0, β⟩ : IsingParams ℝ) {r, s}) dval J ∧
      dval ≤ β * susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) r.val *
               susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) s.val + β * (4 * ↑d) := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have hlt' : β * J * ↑(2 * d) < 1 := by linarith [mul_comm β J, mul_comm J β]
  have hbdd_r :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt' r.val
  have hbdd_s :=
    IsingModel.Ambient.susceptibilityAlongExhaustion_bddAbove_latticeGraph_of_high_temp
      Λ hβJ hlt' s.val
  exact inducedLatticeGraph_J_deriv_le_susc_sq Λ J β hJ hβ n r s hrs hbdd_r hbdd_s

end Ambient
end IsingModel
