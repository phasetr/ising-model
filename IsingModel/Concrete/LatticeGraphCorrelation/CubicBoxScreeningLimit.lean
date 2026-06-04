import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxScreeningCapstone

/-!
# Cubic-box screening and the infinite-volume `+` state (Issue #3565)

The final assembly of the nearest-neighbour screening of the cubic-box `+` state.
Using the pointwise weight factoring `boltzmannWeightBC_cubicBox_succ_pointwise`
(#3574), any boundary-condition sum of an observable depending only on the inner
configuration factors over the box-`m` one times the shell constant
(`bcSum_cubicBox_succ_factor`).  The shell constant cancels in the normalised
expectation, so the `+` box expectation is **independent of the ambient box size**
for `m ≥ n + 1` (`gibbsExpectationBC_cubicBox_succ`,
`plusBoxExpectation_screening`): only the immediate `+` boundary layer matters.

* `bcSum_cubicBox_succ_factor` — the boundary-condition sum factoring.
* `gibbsExpectationBC_cubicBox_succ` — the single-step ambient screening.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Lemma 3.22, §6.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **Shell-indicator sum collapse**: `∑_{σ₂} (if σ₂ ≡ + then C else 0) = C`
(only the all-`+` shell configuration contributes). -/
theorem sum_shell_ite_eq {d m : ℕ}
    (C : ℝ) :
    (∑ σ₂ : {x : (↑(cubicBox d (m + 1)) : Type _) // x.val ∉ cubicBox d m} → Spin,
        (if (∀ v, σ₂ v = Spin.up) then C else 0)) = C := by
  classical
  rw [Fintype.sum_eq_single (fun _ => Spin.up)]
  · simp
  · intro σ₂ hσ₂
    have : ¬ (∀ v, σ₂ v = Spin.up) := by
      intro hall
      exact hσ₂ (funext fun v => hall v)
    rw [if_neg this]

/-- **Boundary-condition sum factoring over the ambient successor box**: for an
observable `F` on `cubicBox d (m+1)` that depends only on the inner configuration
(`F ((equiv).symm (σ₁,σ₂)) = F' σ₁`), the boundary-condition sum over
`cubicBox d (m+1)` factors as the box-`m` sum times the shell constant. -/
theorem bcSum_cubicBox_succ_factor {d n m : ℕ} (hnm : n + 1 ≤ m)
    {J h β : ℝ} (h12 : cubicBox d m ⊆ cubicBox d (m + 1))
    [Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
      (cubicBox d (m + 1))).edgeSet]
    (F : Config (↑(cubicBox d (m + 1)) : Type _) → ℝ)
    (F' : Config (↑(cubicBox d m) : Type _) → ℝ)
    (hF : ∀ σ₁ σ₂, F ((configEquivSubtypeProd h12).symm (σ₁, σ₂)) = F' σ₁) :
    (∑ σ : Config (↑(cubicBox d (m + 1)) : Type _),
        F σ * boltzmannWeightBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d (m + 1)))
          β (fun _ => J) h (plusBoxInterior d n (m + 1)) (plusConfig _) σ)
      = (∑ σ₁ : Config (↑(cubicBox d m) : Type _),
          F' σ₁ * boltzmannWeightBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m))
            β (fun _ => J) h (plusBoxInterior d n m) (plusConfig _) σ₁)
        * cubicBoxShellConst d m J h β := by
  rw [← Fintype.sum_equiv (configEquivSubtypeProd h12).symm _
    (fun σ => F σ * boltzmannWeightBC (inducedGraph (IsingModel.latticeGraph d)
      (cubicBox d (m + 1))) β (fun _ => J) h (plusBoxInterior d n (m + 1)) (plusConfig _) σ)
    (fun x => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun σ₁ _ => ?_)
  simp_rw [hF, boltzmannWeightBC_cubicBox_succ_pointwise hnm h12]
  rw [show (fun σ₂ : {x : (↑(cubicBox d (m + 1)) : Type _) // x.val ∉ cubicBox d m} → Spin =>
        F' σ₁ * (boltzmannWeightBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m))
          β (fun _ => J) h (plusBoxInterior d n m) (plusConfig _) σ₁
          * (if (∀ v, σ₂ v = Spin.up) then cubicBoxShellConst d m J h β else 0)))
      = (fun σ₂ => (F' σ₁ * boltzmannWeightBC (inducedGraph (IsingModel.latticeGraph d)
          (cubicBox d m)) β (fun _ => J) h (plusBoxInterior d n m) (plusConfig _) σ₁)
          * (if (∀ v, σ₂ v = Spin.up) then cubicBoxShellConst d m J h β else 0)) from by
    funext σ₂; ring]
  rw [← Finset.mul_sum, sum_shell_ite_eq]

/-- **Partition-function factoring over the ambient successor box**:
`Z^+_{cubicBox d (m+1)} = Z^+_{cubicBox d m} · shellConst`. -/
theorem partitionFunctionBC_cubicBox_succ {d n m : ℕ} (hnm : n + 1 ≤ m)
    {J h β : ℝ} (h12 : cubicBox d m ⊆ cubicBox d (m + 1))
    [Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
      (cubicBox d (m + 1))).edgeSet] :
    partitionFunctionBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d (m + 1)))
        β (fun _ => J) h (plusBoxInterior d n (m + 1)) (plusConfig _)
      = partitionFunctionBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m))
          β (fun _ => J) h (plusBoxInterior d n m) (plusConfig _)
        * cubicBoxShellConst d m J h β := by
  unfold partitionFunctionBC
  have h := bcSum_cubicBox_succ_factor (n := n) (J := J) (h := h) (β := β) hnm h12
    (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ _ => rfl)
  simpa only [one_mul] using h

/-- **Single-step ambient screening of the `+` box expectation**: for an
observable `φ` on `cubicBox d (m+1)` depending only on the inner configuration
(`φ ((equiv).symm (σ₁,σ₂)) = φ' σ₁`) and `n + 1 ≤ m`, the `+` boundary expectation
on `cubicBox d (m+1)` equals that on `cubicBox d m`: the shell constant cancels in
the normalised ratio. -/
theorem gibbsExpectationBC_cubicBox_succ {d n m : ℕ} (hnm : n + 1 ≤ m)
    {J h β : ℝ} (h12 : cubicBox d m ⊆ cubicBox d (m + 1))
    (φ : Config (↑(cubicBox d (m + 1)) : Type _) → ℝ)
    (φ' : Config (↑(cubicBox d m) : Type _) → ℝ)
    (hφ : ∀ σ₁ σ₂, φ ((configEquivSubtypeProd h12).symm (σ₁, σ₂)) = φ' σ₁) :
    gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d (m + 1)))
        β (fun _ => J) h (plusBoxInterior d n (m + 1)) (plusConfig _) φ
      = gibbsExpectationBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m))
          β (fun _ => J) h (plusBoxInterior d n m) (plusConfig _) φ' := by
  haveI : Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
    (cubicBox d (m + 1))).edgeSet := Fintype.ofFinite _
  unfold gibbsExpectationBC
  rw [bcSum_cubicBox_succ_factor hnm h12 φ φ' hφ, partitionFunctionBC_cubicBox_succ hnm h12]
  have hC : cubicBoxShellConst d m J h β ≠ 0 := ne_of_gt (cubicBoxShellConst_pos d m J h β)
  have hZ : partitionFunctionBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m))
      β (fun _ => J) h (plusBoxInterior d n m) (plusConfig _) ≠ 0 :=
    partitionFunctionBC_ne_zero _ _ _ _ _ _
  field_simp

/-- **Single-step ambient screening of the single-site `+` box spin**: for
`n + 1 ≤ m` and `x ∈ cubicBox d m`, the single-site `+` box spin is unchanged when
the ambient box grows by one, `plusBoxSpin d n (m+1) … x = plusBoxSpin d n m … x`
(only the immediate `+` boundary layer matters, not the ambient box size).  The
single-spin observable depends only on the inner configuration via
`restrictConfig_configEquivSubtypeProd_symm`. -/
theorem plusBoxSpin_screening_succ {d n m : ℕ} (hnm : n + 1 ≤ m) {J h β : ℝ}
    (h12 : cubicBox d m ⊆ cubicBox d (m + 1))
    (x : Fin d → ℤ) (hx : x ∈ cubicBox d m) :
    plusBoxSpin d n (m + 1) J h β x (h12 hx) = plusBoxSpin d n m J h β x hx := by
  unfold plusBoxSpin plusBoxExpectation
  refine gibbsExpectationBC_cubicBox_succ hnm h12
    (fun σ => Spin.sign ℝ (σ ⟨x, h12 hx⟩)) (fun σ => Spin.sign ℝ (σ ⟨x, hx⟩)) (fun σ₁ σ₂ => ?_)
  exact congr_arg (Spin.sign ℝ)
    (congrFun (restrictConfig_configEquivSubtypeProd_symm h12 σ₁ σ₂) ⟨x, hx⟩)

end Ambient

end IsingModel
