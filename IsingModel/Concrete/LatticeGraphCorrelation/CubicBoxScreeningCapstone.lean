import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxScreeningDecomp

/-!
# Cubic-box screening: edge-spin frozen evaluation (Issue #3565)

The frozen-`+` edge-spin evaluation feeding the `hextra` hypothesis of
`boltzmannWeight_inducedGraph_restrict_factor_const` (#3571) on the cubic box: for
a configuration that agrees with `+` off `cubicBox d n`, every extra edge (touching
the shell, with both endpoints outside `cubicBox d n` by #3572) has `edgeSpin = 1`.

* `edgeSpin_eq_one_of_agreesOff_extra` — the frozen extra-edge spin value.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Lemma 3.22, §6.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **Frozen extra-edge spin**: for `n + 1 ≤ m`, if `σ` agrees with `+` off
`cubicBox d n` and `e` is an extra edge (of the induced graph on `cubicBox d (m+1)`
but not the extension graph over `cubicBox d m`), then `edgeSpin σ e = 1`.  Both
endpoints lie outside `cubicBox d n` (`cubicBox_extra_edge_endpoints_not_mem_inner`,
#3572), hence carry the frozen `+` spin. -/
theorem edgeSpin_eq_one_of_agreesOff_extra {d n m : ℕ} (hnm : n + 1 ≤ m)
    [Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
      (cubicBox d (m + 1))).edgeSet]
    {σ : Config (↑(cubicBox d (m + 1)) : Type _)}
    (hσ : agreesOff (plusBoxInterior d n (m + 1)) (plusConfig _) σ)
    {e : Sym2 (↑(cubicBox d (m + 1)) : Type _)}
    (he : e ∈ (inducedGraph (IsingModel.latticeGraph d) (cubicBox d (m + 1))).edgeFinset \
        (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
          (cubicBox d (m + 1))).edgeFinset) :
    edgeSpin (K := ℝ) σ e = 1 := by
  have hend : ∀ u ∈ e, (u : Fin d → ℤ) ∉ cubicBox d n :=
    cubicBox_extra_edge_endpoints_not_mem_inner hnm he
  have hup : ∀ u ∈ e, σ u = Spin.up := fun u hu =>
    hσ u (fun hi => hend u hu ((mem_plusBoxInterior (j := u)).mp hi))
  revert hup
  refine Sym2.ind (fun a b hup => ?_) e
  have ha := hup a (Sym2.mem_mk_left a b)
  have hb := hup b (Sym2.mem_mk_right a b)
  simp [edgeSpin, Sym2.lift_mk, ha, hb, Spin.sign, Spin.toSign]

/-- **The shell constant** of the cubic-box `+` screening: the exponential factor
collecting the frozen shell field and the frozen extra-edge interaction, depending
only on the box sizes (not on the free configuration). -/
noncomputable def cubicBoxShellConst (d m : ℕ) (J h β : ℝ)
    [Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
      (cubicBox d (m + 1))).edgeSet] : ℝ :=
  Real.exp (-β *
    ((-h) * (Fintype.card {x : (↑(cubicBox d (m + 1)) : Type _) // ¬ (x.val ∈ cubicBox d m)} : ℝ)
      + (-J) * (((inducedGraph (IsingModel.latticeGraph d) (cubicBox d (m + 1))).edgeFinset \
          (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
            (cubicBox d (m + 1))).edgeFinset).card : ℝ)))

/-- The shell constant is strictly positive. -/
theorem cubicBoxShellConst_pos (d m : ℕ) (J h β : ℝ)
    [Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
      (cubicBox d (m + 1))).edgeSet] :
    0 < cubicBoxShellConst d m J h β := Real.exp_pos _

/-- **Pointwise `+` boundary weight factoring on the cubic box**: under the
configuration split `configEquivSubtypeProd (cubicBox d m ⊆ cubicBox d (m+1))`, the
`+` boundary Boltzmann weight on `cubicBox d (m+1)` of the recombined configuration
factors as the `+` boundary weight on `cubicBox d m` of `σ₁` times the shell
constant when `σ₂` is all-`+`, and is `0` otherwise (the boundary indicator forces
the shell to be `+`).  This is the per-configuration heart of the screening. -/
theorem boltzmannWeightBC_cubicBox_succ_pointwise {d n m : ℕ} (hnm : n + 1 ≤ m)
    {J h β : ℝ}
    (h12 : cubicBox d m ⊆ cubicBox d (m + 1))
    [Fintype (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
      (cubicBox d (m + 1))).edgeSet]
    (σ₁ : Config (↑(cubicBox d m) : Type _))
    (σ₂ : {x : (↑(cubicBox d (m + 1)) : Type _) // x.val ∉ cubicBox d m} → Spin) :
    boltzmannWeightBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d (m + 1)))
        β (fun _ => J) h (plusBoxInterior d n (m + 1)) (plusConfig _)
        ((configEquivSubtypeProd h12).symm (σ₁, σ₂))
      = boltzmannWeightBC (inducedGraph (IsingModel.latticeGraph d) (cubicBox d m))
          β (fun _ => J) h (plusBoxInterior d n m) (plusConfig _) σ₁
        * (if (∀ v, σ₂ v = Spin.up) then cubicBoxShellConst d m J h β else 0) := by
  set τ := (configEquivSubtypeProd h12).symm (σ₁, σ₂) with hτ_def
  by_cases hσ₂ : ∀ v, σ₂ v = Spin.up
  · rw [if_pos hσ₂]
    by_cases h1 : agreesOff (plusBoxInterior d n m) (plusConfig _) σ₁
    · have hτ : agreesOff (plusBoxInterior d n (m + 1)) (plusConfig _) τ :=
        (agreesOff_plus_configEquiv_iff (by omega) h12 σ₁ σ₂).mpr ⟨h1, hσ₂⟩
      have hcompl : ∀ v : {x : (↑(cubicBox d (m + 1)) : Type _) // ¬ (x.val ∈ cubicBox d m)},
          τ v.val = Spin.up := fun v => by
        rw [hτ_def, configEquivSubtypeProd_symm_apply_compl]; exact hσ₂ v
      have hextra : ∀ e ∈
          (inducedGraph (IsingModel.latticeGraph d) (cubicBox d (m + 1))).edgeFinset \
          (extendGraphFromΛ₁ (IsingModel.latticeGraph d) (cubicBox d m)
            (cubicBox d (m + 1))).edgeFinset, edgeSpin (K := ℝ) τ e = 1 :=
        fun e he => edgeSpin_eq_one_of_agreesOff_extra hnm hτ he
      rw [boltzmannWeightBC_of_agrees _ _ _ _ hτ, boltzmannWeightJ_uniform_eq,
        boltzmannWeight_inducedGraph_restrict_factor_const (IsingModel.latticeGraph d) h12
          (⟨J, h, β⟩ : IsingParams ℝ) τ hcompl hextra,
        hτ_def, restrictConfig_configEquivSubtypeProd_symm,
        ← boltzmannWeightJ_uniform_eq, ← boltzmannWeightBC_of_agrees _ _ _ _ h1]
      rfl
    · have hτ : ¬ agreesOff (plusBoxInterior d n (m + 1)) (plusConfig _) τ := fun hτ =>
        h1 ((agreesOff_plus_configEquiv_iff (by omega) h12 σ₁ σ₂).mp hτ).1
      rw [boltzmannWeightBC_of_not_agrees _ _ _ _ hτ,
        boltzmannWeightBC_of_not_agrees _ _ _ _ h1, zero_mul]
  · rw [if_neg hσ₂, mul_zero]
    have hτ : ¬ agreesOff (plusBoxInterior d n (m + 1)) (plusConfig _) τ := fun hτ =>
      hσ₂ ((agreesOff_plus_configEquiv_iff (by omega) h12 σ₁ σ₂).mp hτ).2
    rw [boltzmannWeightBC_of_not_agrees _ _ _ _ hτ]

end Ambient

end IsingModel
