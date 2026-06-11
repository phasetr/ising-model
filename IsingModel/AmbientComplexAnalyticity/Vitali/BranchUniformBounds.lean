import IsingModel.AmbientComplexAnalyticity.Basic.BranchBounds
import IsingModel.AmbientComplexAnalyticity.Vitali.BranchData

/-!
# Stage-uniform branch bounds on half-radius balls (GJ §4.6 Thm 4.6.2)

The Lee–Yang application of the Borel–Carathéodory half-radius bound (Issue #628): a stage
branch has real part `log ‖Z‖ / N` (the exponential identity), which the free-energy norm bound
controls stage-uniformly; the centre value is the principal free energy by normalisation; hence
the full branch is bounded by `2(A+1) + 3A = 5A + 2` on the half-radius closed ball, and the
deviation from the principal free energy by `6A + 2`, with constants depending only on the
free-energy bound `A`.

* `re_freeEnergyComplexAlongExhaustion_eq` — `Re F_m = log ‖Z_m‖ / N_m`.
* `re_branchFamily_le_of_norm_le` — the branch real-part control.
* `norm_branchFamily_le_on_half` — the stage-uniform half-radius branch bound.
* `norm_branchFamily_sub_freeEnergy_le_on_half` — the deviation bound.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel

namespace Ambient

open Metric

variable {V : Type*} [DecidableEq V]

/-- **The real part of the principal stage free energy** is the normalised log-norm of the
stage partition function. -/
theorem re_freeEnergyComplexAlongExhaustion_eq (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℂ) (n : ℕ) :
    (freeEnergyComplexAlongExhaustion G Λ J h β n).re
      = Real.log ‖partitionFunctionComplexAlongExhaustion G Λ J h β n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  rw [show freeEnergyComplexAlongExhaustion G Λ J h β n
      = ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ))⁻¹
        * Complex.log (partitionFunctionComplexAlongExhaustion G Λ J h β n) from rfl]
  rw [show ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ))
      = (((Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) : ℂ) from by push_cast; rfl]
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.log_re, div_eq_inv_mul]

/-- **Branch real-part control from the free-energy norm bound**: on the selected ball the
branch real part equals the normalised log-norm of `Z`, i.e. `Re F_m`, hence any stage
free-energy norm bound controls it. -/
theorem re_branchFamily_le_of_norm_le (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)] {J β : ℂ}
    (data : LeeYangAllStageBranchData G Λ J β)
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) (m : ℕ) {A : ℝ}
    (hA : ∀ z ∈ Metric.ball (h₀ : ℂ) (data.radius h₀),
      ‖freeEnergyComplexAlongExhaustion G Λ J z β m‖ ≤ A)
    {z : ℂ} (hz : z ∈ Metric.ball (h₀ : ℂ) (data.radius h₀)) :
    (data.branchFamily h₀ m z).re ≤ A := by
  have hcard : (0 : ℝ) < (Fintype.card (↑(Λ.volume m) : Type _) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hexp := (data.branch_spec h₀ m).2 z hz
  have hre := re_eq_log_norm_div_of_exp_eq hcard (w := data.branchFamily h₀ m z)
    (Zv := partitionFunctionComplexAlongExhaustion G Λ J z β m)
    (by
      rw [show (((Fintype.card (↑(Λ.volume m) : Type _) : ℝ)) : ℂ)
          = ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ)) from by push_cast; rfl]
      exact hexp)
  rw [hre, ← re_freeEnergyComplexAlongExhaustion_eq G Λ J z β m]
  calc (freeEnergyComplexAlongExhaustion G Λ J z β m).re
      ≤ |(freeEnergyComplexAlongExhaustion G Λ J z β m).re| := le_abs_self _
    _ ≤ ‖freeEnergyComplexAlongExhaustion G Λ J z β m‖ := Complex.abs_re_le_norm _
    _ ≤ A := hA z hz

/-- **Stage-uniform branch bound on the half-radius closed ball** (Borel–Carathéodory): with a
stage free-energy norm bound `A` on the selected ball and the centre normalisation, every
stage branch satisfies `‖f_m‖ ≤ 2(A+1) + 3A` on the half-radius closed ball. -/
theorem norm_branchFamily_le_on_half (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)] {J β : ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData G Λ J β)
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ m, ∀ z ∈ Metric.ball (h₀ : ℂ) (data.branchData.radius h₀),
      ‖freeEnergyComplexAlongExhaustion G Λ J z β m‖ ≤ A)
    (m : ℕ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (h₀ : ℂ) (data.branchData.radius h₀ / 2)) :
    ‖data.branchData.branchFamily h₀ m z‖ ≤ 2 * (A + 1) + 3 * A := by
  have hcentre : (h₀ : ℂ) ∈ Metric.ball (h₀ : ℂ) (data.branchData.radius h₀) :=
    Metric.mem_ball_self (data.branchData.radius_pos h₀)
  have hfc : ‖data.branchData.branchFamily h₀ m (h₀ : ℂ)‖ ≤ A := by
    rw [data.centre_normalized h₀ m]
    exact hA m _ hcentre
  have hbc := norm_le_of_re_le_on_half (M := A + 1) (by linarith)
    (data.branchData.radius_pos h₀)
    ((data.branchData.branch_spec h₀ m).1.differentiableOn)
    (fun w hw => le_trans
      (re_branchFamily_le_of_norm_le G Λ data.branchData h₀ m (hA m) hw) (by linarith))
    hz
  calc ‖data.branchData.branchFamily h₀ m z‖
      ≤ 2 * (A + 1) + 3 * ‖data.branchData.branchFamily h₀ m (h₀ : ℂ)‖ := hbc
    _ ≤ 2 * (A + 1) + 3 * A := by linarith

/-- **Stage-uniform deviation bound on the half-radius closed ball**: the branch differs from
the principal stage free energy by at most `(2(A+1) + 3A) + A = 6A + 2`. -/
theorem norm_branchFamily_sub_freeEnergy_le_on_half (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)] {J β : ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData G Λ J β)
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ m, ∀ z ∈ Metric.ball (h₀ : ℂ) (data.branchData.radius h₀),
      ‖freeEnergyComplexAlongExhaustion G Λ J z β m‖ ≤ A)
    (m : ℕ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (h₀ : ℂ) (data.branchData.radius h₀ / 2)) :
    ‖data.branchData.branchFamily h₀ m z
        - freeEnergyComplexAlongExhaustion G Λ J z β m‖
      ≤ (2 * (A + 1) + 3 * A) + A := by
  have hzball : z ∈ Metric.ball (h₀ : ℂ) (data.branchData.radius h₀) :=
    Metric.closedBall_subset_ball
      (show data.branchData.radius h₀ / 2 < data.branchData.radius h₀ by
        have := data.branchData.radius_pos h₀
        linarith) hz
  calc ‖data.branchData.branchFamily h₀ m z
        - freeEnergyComplexAlongExhaustion G Λ J z β m‖
      ≤ ‖data.branchData.branchFamily h₀ m z‖
        + ‖freeEnergyComplexAlongExhaustion G Λ J z β m‖ := norm_sub_le _ _
    _ ≤ (2 * (A + 1) + 3 * A) + A :=
        add_le_add (norm_branchFamily_le_on_half G Λ data h₀ hA0 hA m hz)
          (hA m z hzball)

end Ambient

end IsingModel
