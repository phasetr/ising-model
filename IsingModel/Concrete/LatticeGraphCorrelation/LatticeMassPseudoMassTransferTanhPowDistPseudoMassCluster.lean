import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferTanhPowDist

/-!
# Lattice-mass: pseudoMass cluster on tanh-power profile

Narrow child module for four ℤ^d
`pseudoMass{Ext}_twoPointFunction_*_of_pseudoMassG_le_tanh_pow_dist`
wrappers extracted from `LatticeMassPseudoMassTransferTanhPowDist.lean`:

* `pseudoMassExt_twoPointFunction_eq_pseudoMass_of_pseudoMassG_le_tanh_pow_dist`,
* `pseudoMass_twoPointFunction_pos_of_pseudoMassG_le_tanh_pow_dist`,
* `pseudoMassExt_twoPointFunction_pos_of_pseudoMassG_le_tanh_pow_dist`,
* `pseudoMassExt_twoPointFunction_ne_zero_of_pseudoMassG_le_tanh_pow_dist`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **The totalized two-point pseudo-mass equals the ordinary pseudo-mass under
the tanh-power profile bound**: the profile condition supplies the active-range
membership needed to remove the totalization.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_eq_pseudoMass_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z) =
      pseudoMass hα hr
        (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
          (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh) := by
  rw [pseudoMassExt_of_mem hα hr
    (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)]

/-- **Ordinary two-point pseudo-mass positivity from a tanh-power profile
bound**: the active-range theorem supplies the `Ioo 0 2` argument required by
`pseudoMass_pos`.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMass_twoPointFunction_pos_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    0 < pseudoMass hα hr
      (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
        (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh) :=
  pseudoMass_pos hα hr
    (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)

/-- **Totalized two-point pseudo-mass positivity from a tanh-power profile
bound**: under the profile condition, the anchored two-point function is active,
so `pseudoMassExt` is strictly positive.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_pos_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    0 < pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z) :=
  pseudoMassExt_pos_of_mem hα hr
    (twoPointFunction_mem_Ioo_zero_two_of_pseudoMassG_le_tanh_pow_dist
      (α := α) (r := r) hr hJ hβ hlt hz hprofile_tanh)

/-- **Totalized two-point pseudo-mass non-vanishing from a tanh-power profile
bound**: a direct non-zero corollary of positivity.

Reference: Glimm--Jaffe §17.5 pp. 304--306 and Lemma 17.5.2 pp. 311--312. -/
theorem pseudoMassExt_twoPointFunction_ne_zero_of_pseudoMassG_le_tanh_pow_dist
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ} (hz : z ≠ 0)
    (hprofile_tanh : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 z) :
    pseudoMassExt hα hr (twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) z) ≠ 0 :=
  ne_of_gt
    (pseudoMassExt_twoPointFunction_pos_of_pseudoMassG_le_tanh_pow_dist
      hα hr hJ hβ hlt hz hprofile_tanh)


end Ambient

end IsingModel
