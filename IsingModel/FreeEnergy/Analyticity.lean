import IsingModel.FreeEnergy.LeeYangBridge

/-!
# Free energy analyticity

Mechanical child split from `IsingModel.FreeEnergy`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Analyticity of the free energy (Theorem 4.6.2)

The free energy `f(h) = |ι|⁻¹ ln Z(h)` is real-analytic in the external
field `h` on `(0, ∞)`.

The proof strategy:
1. Each Boltzmann weight `w(σ, h) = exp(a(σ) + b(σ)·h)` is real-analytic in `h`
   (exponential of an affine function).
2. `Z(h) = Σ_σ w(σ, h)` is a finite sum of real-analytic functions, hence
   real-analytic.
3. `Z(h) > 0` for all `h` (`partitionFunction_pos`).
4. `ln Z(h)` is real-analytic where `Z > 0` (`AnalyticAt.log`).
5. `f(h) = |ι|⁻¹ · ln Z(h)` is real-analytic.

Reference: Glimm–Jaffe, *Quantum Physics*, §4.6, Theorem 4.6.2, pp. 67–70.
The finite-volume real-analyticity is the starting point for the complex
analyticity established via Lee-Yang and Vitali convergence. -/

omit [DecidableEq ι] in
/-- Each Boltzmann weight is real-analytic in `h` (exponential of affine). -/
private theorem boltzmannWeight_analyticAt_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (σ : Config ι) (h₀ : ℝ) :
    AnalyticAt ℝ (fun h => boltzmannWeight G ⟨J, h, β⟩ σ) h₀ := by
  unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
  simp only
  fun_prop

/-- The partition function is real-analytic in the external field `h`.
`Z(h) = Σ_σ exp(a(σ) + b(σ)·h)` is a finite sum of real-analytic
functions, hence real-analytic. -/
theorem partitionFunctionH_analyticAt
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (h₀ : ℝ) :
    AnalyticAt ℝ (fun h => partitionFunction G ⟨J, h, β⟩) h₀ := by
  unfold partitionFunction
  exact Finset.analyticAt_fun_sum _ (fun σ _ =>
    boltzmannWeight_analyticAt_h G J β σ h₀)

/-- **Theorem 4.6.2** (Glimm–Jaffe, §4.6, p. 68, finite-volume real version).
The free energy per site `f(h) = |ι|⁻¹ ln Z(h)` is real-analytic in the
external field `h` on `(0, ∞)`.

Since `Z(h) > 0` for all `h`, `ln Z(h)` is defined and real-analytic.
The restriction to `h > 0` matches the domain of the complex analyticity
in Theorem 4.6.2 (where `|Im h| < Re h` gives `Re h > 0`). -/
theorem freeEnergyH_analyticOn
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) :
    AnalyticOn ℝ (freeEnergyH G J β) (Set.Ioi 0) := by
  intro h₀ hh₀
  unfold freeEnergyH freeEnergy
  exact (analyticAt_const.mul
    ((partitionFunctionH_analyticAt G J β h₀).log
      (partitionFunction_pos G ⟨J, h₀, β⟩))).analyticWithinAt

omit [DecidableEq ι] in
/-- Each Boltzmann weight is real-analytic in `J` (exponential of affine). -/
private theorem boltzmannWeight_analyticAt_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (σ : Config ι) (J₀ : ℝ) :
    AnalyticAt ℝ (fun J => boltzmannWeight G ⟨J, h, β⟩ σ) J₀ := by
  unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
  simp only
  fun_prop

/-- The partition function is real-analytic in the coupling constant `J`. -/
theorem partitionFunctionJ_analyticAt
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (J₀ : ℝ) :
    AnalyticAt ℝ (fun J => partitionFunction G ⟨J, h, β⟩) J₀ := by
  unfold partitionFunction
  exact Finset.analyticAt_fun_sum _ (fun σ _ =>
    boltzmannWeight_analyticAt_J G h β σ J₀)

/-- The free energy is real-analytic in `J` on `(0, ∞)`.
Since `Z > 0` always holds, `ln Z(J)` is defined and real-analytic. -/
theorem freeEnergyJ_analyticOn
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) :
    AnalyticOn ℝ (freeEnergyJ G h β) (Set.Ioi 0) := by
  intro J₀ _
  unfold freeEnergyJ freeEnergy
  exact (analyticAt_const.mul
    ((partitionFunctionJ_analyticAt G h β J₀).log
      (partitionFunction_pos G ⟨J₀, h, β⟩))).analyticWithinAt

end IsingModel
