import IsingModel.Basic
import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Core
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.CorrelationInfinite.Basic
import IsingModel.AmbientLattice.CorrelationInfinite.Bounds
import IsingModel.PseudoMass.Basic
import IsingModel.PseudoMass.Ext
import IsingModel.PseudoMass.Profile
import IsingModel.PseudoMass.FromParamsBasic.BasicSlices

/-!
# Regularity of concrete pseudo-mass beta profiles (5/5): the `m⁻` correlation majorant

Structural split (5/5) of
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity`.
This child holds the `m⁻` majorant `correlationInfinite ≤ 2 / (1 + (m⁻ · r) ^ α)` and its
pair-product form, the Lebowitz IIIb cross-product input.  It is independent of the other four
children.  See the
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity`
facade module for the full contents overview.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 (p. 312).
-/

namespace IsingModel

open Set

namespace Ambient

/-- **GJ §17.5 m⁻ majorant for `correlationInfinite`** (GJ §17.5 p. 311).

For any active pair `(x, z)` (i.e., `correlationInfinite {x, z} ∈ Ioo 0 2`), the
two-point function is dominated by the rational `pseudoMassG`-majorant:

    correlationInfinite ⟨J, 0, β⟩ {x, z} ≤ 2 / (1 + (m⁻ · r)^α)

where `m⁻ = pseudoMassFromParamsAtPair hα hr d Λ ⟨J, 0, β⟩ x z` and `r > 0` is the
fixed radius parameter of the pseudo-mass. Direct corollary of the defining identity
`pseudoMassG α r m⁻ = correlationInfinite` (`pseudoMass_spec`) combined with the
pointwise rational bound `pseudoMassG α r t ≤ 2 / (1 + (t·r)^α)`
(`pseudoMassG_le_two_div_one_add_pow`) — i.e., dropping the `e^(-tr) ≤ 1` factor.

This is the **pseudo-mass majorant** used in GJ p. 312 to substitute
`⟨φ(x)φ(z)⟩ / A → 2/(1+(m⁻·d(x,z))^α)` in the proof of Theorem 17.5.1, the first
step in deriving the HLS comparison form `|c'| ≤ K·c/m⁻^(2α)`. -/
theorem correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ≤ 2 / (1 + (pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ^ α) := by
  -- Defining identity: pseudoMassG α r (pseudoMassFromParamsAtPair …) = correlationInfinite
  set m : ℝ := pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z with hm_def
  set c : ℝ := Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} with hc_def
  -- Rewrite m via pseudoMassExt
  -- (pseudoMassFromParamsAtPair = pseudoMassExt ∘ correlationInfinite by definition)
  have hm_eq : m = pseudoMassExt hα hr c := rfl
  -- On the active range, pseudoMassExt c = pseudoMass hα hr hcorr
  have hm_pseudoMass : m = pseudoMass hα hr hcorr := by
    rw [hm_eq, pseudoMassExt_of_mem hα hr hcorr]
  -- Defining identity pseudoMassG α r (pseudoMass) = c
  have hspec : pseudoMassG α r m = c := by
    rw [hm_pseudoMass]; exact pseudoMass_spec hα hr hcorr
  -- Non-negativity of m
  have hm_nn : 0 ≤ m :=
    pseudoMassFromParamsAtPair_nonneg hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z
  -- Apply the pointwise rational bound
  calc c = pseudoMassG α r m := hspec.symm
    _ ≤ 2 / (1 + (m * r) ^ α) := pseudoMassG_le_two_div_one_add_pow α hm_nn hr

/-- **GJ §17.5 pair-product m⁻ majorant** (GJ §17.5 p. 312, Step 119 plan Step 5.2).

For two active pairs `(x, z)` and `(y, z)` (both `correlationInfinite ∈ Ioo 0 2`),
the product of the two-point functions is dominated by the product of pseudo-mass majorants:

    ⟨σ_x σ_z⟩ · ⟨σ_y σ_z⟩
      ≤ 4 / ((1 + (m⁻_xz · r)^α) · (1 + (m⁻_yz · r)^α))

where `m⁻_xz = pseudoMassFromParamsAtPair ⟨J,0,β⟩ x z` and similarly for `m⁻_yz`.

Direct corollary of `correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair`
applied twice via `mul_le_mul` (with non-negativity from GKS-I /
`correlationInfinite_nonneg`).

This is the pair-product form used in GJ p. 312 inside `∑_z ⟨φ(x₀)φ(z)⟩⟨φ(y₀)φ(z)⟩` —
the Lebowitz IIIb cross-product term whose sum over `z` gives the HLS comparison
form `|c'| ≤ K · c / m⁻^(2α)`. -/
theorem correlationInfinite_pair_product_le_four_div_one_add_pow_pseudoMassFromParamsAtPair
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) {d : ℕ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x y z : Fin d → ℤ)
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hcxz : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hcyz : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {y, z} ∈ Set.Ioo (0 : ℝ) 2) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
      ≤ 2 / (1 + (pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ^ α) *
        (2 / (1 + (pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) y z * r) ^ α)) := by
  -- Two instances of the m⁻ majorant
  have hxz := correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
    hα hr Λ J β x z hcxz
  have hyz := correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
    hα hr Λ J β y z hcyz
  -- Non-negativity of correlations (GKS-I)
  have hxz_nn : 0 ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} :=
    Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf {x, z}
  have hyz_nn : 0 ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) {y, z} :=
    Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf {y, z}
  -- Right-hand side non-negativity
  have hm_xz_nn : 0 ≤ pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    pseudoMassFromParamsAtPair_nonneg hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z
  have hRHS_xz_pos : 0 < 1 + (pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ^ α := by
    have h : 0 ≤ (pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ^ α :=
      pow_nonneg (mul_nonneg hm_xz_nn hr.le) α
    linarith
  have hRHS_xz_nn : 0 ≤ 2 / (1 + (pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ^ α) :=
    div_nonneg (by norm_num) hRHS_xz_pos.le
  -- Apply mul_le_mul
  exact mul_le_mul hxz hyz hyz_nn hRHS_xz_nn

end Ambient

end IsingModel
