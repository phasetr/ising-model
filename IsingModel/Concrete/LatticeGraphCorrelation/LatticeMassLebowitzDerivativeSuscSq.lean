import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivative

/-!
# ℤ^d derivative bounds through the infinite-volume susceptibility (§17.5)

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` at a fixed stage and at zero external field, the bound on the derivative of the
correlation of two distinct vertices of the stage volume by the product of the
infinite-volume susceptibilities at those vertices, scaled by the parameter held fixed, plus
a term linear in the dimension. The bound is given in the inverse-temperature direction and
in the coupling direction, and each assumes `0 ≤ J`, `0 < β`, distinctness of the two
vertices, and that the susceptibility sequence along the exhaustion at each of them is
bounded above.
-/

namespace IsingModel
namespace Ambient

/-- **Uniform β-derivative bound via susceptibilityInfinite** (Step 163, GJ §17.5):
For the induced ℤ^d lattice graph (stage n), under `BddAbove` for the susceptibilities:
`d/dβ corr_n(r,s) ≤ J · χ_∞(r) · χ_∞(s) + J · 4d`.

Proof: Step 157 (derivative ≤ J·Σ_leb + J·4d) + Step 162 (Σ_leb ≤ χ_∞² under BddAbove).

Reference: Glimm–Jaffe §17.5 (uniform derivative bound for ∞-vol limit). -/
theorem inducedLatticeGraph_beta_deriv_le_susc_sq
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (hbdd_r : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val m)))
    (hbdd_s : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val m))) :
    ∃ dval : ℝ,
      HasDerivAt (fun β' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) dval β ∧
      dval ≤ J * susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) r.val *
               susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) s.val + J * (4 * ↑d) := by
  -- Step 157: derivative ≤ J * Σ_leb + J * 4d
  obtain ⟨dval, hd, hbound⟩ :=
    inducedLatticeGraph_beta_deriv_le (Λ.volume n) J β hJ hβ r s hrs
  -- Step 162: Σ_leb ≤ χ_∞(r) * χ_∞(s)
  have hleb := inducedLatticeGraph_leb_sum_le_susceptibilityInfinite Λ J β hJ hβ n r s hbdd_r hbdd_s
  refine ⟨dval, hd, ?_⟩
  have h_mul : J * ∑ e ∈ _, _ ≤
        J * (susceptibilityInfinite _ _ _ r.val * susceptibilityInfinite _ _ _ s.val) :=
    mul_le_mul_of_nonneg_left hleb hJ
  linarith

/-- **J-derivative bound by χ_∞² on ℤ^d** (Step 219):
For the induced ℤ^d lattice graph (stage n), under `BddAbove` for the susceptibilities:
`d/dJ corr_n(r,s)|_{h=0} ≤ β · χ_∞(r) · χ_∞(s) + β · 4d`.

Direct J-direction analogue of `inducedLatticeGraph_beta_deriv_le_susc_sq` (Step 163).
Combines Step 218 (`inducedLatticeGraph_J_deriv_le`: derivative ≤ β·Σ_leb + β·4d) with
Step 162 (`inducedLatticeGraph_leb_sum_le_susceptibilityInfinite`: Σ_leb ≤ χ_∞²
under BddAbove). -/
theorem inducedLatticeGraph_J_deriv_le_susc_sq
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (hbdd_r : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val m)))
    (hbdd_s : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val m))) :
    ∃ dval : ℝ,
      HasDerivAt (fun J' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J', 0, β⟩ : IsingParams ℝ) {r, s}) dval J ∧
      dval ≤ β * susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) r.val *
               susceptibilityInfinite (IsingModel.latticeGraph d) Λ
                 (⟨J, 0, β⟩ : IsingParams ℝ) s.val + β * (4 * ↑d) := by
  obtain ⟨dval, hd, hbound⟩ :=
    inducedLatticeGraph_J_deriv_le (Λ.volume n) J β hJ hβ r s hrs
  have hleb := inducedLatticeGraph_leb_sum_le_susceptibilityInfinite Λ J β hJ hβ n r s hbdd_r hbdd_s
  refine ⟨dval, hd, ?_⟩
  have h_mul : β * ∑ e ∈ _, _ ≤
        β * (susceptibilityInfinite _ _ _ r.val * susceptibilityInfinite _ _ _ s.val) :=
    mul_le_mul_of_nonneg_left hleb hβ.le
  linarith

end Ambient
end IsingModel
