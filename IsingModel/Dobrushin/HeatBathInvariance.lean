import IsingModel.Dobrushin.SingleSiteObservableComparison

/-!
# Heat-bath single-site invariance of the boundary-condition Gibbs measure (GJ §17.1, Issue #4201)

The single-site **heat-bath operator** `K_x f (σ) = ⟨f⟩^σ_{x}` replaces an observable `f` by its
single-site conditional expectation at `x` given the rest of the configuration `σ`. The
finite-volume boundary-condition Gibbs measure `μ^η_Λ` is **invariant** under `K_x` for `x ∈ Λ`:
`⟨K_x f⟩^η_Λ = ⟨f⟩^η_Λ` (re-sampling the spin at `x` from its conditional law does not change the
measure — the finite-volume DLR/heat-bath consistency). This is the first step of the Dobrushin
comparison-theorem telescoping (Issue #4201): iterating `K_x` over the sites of `Λ` and tracking the
oscillation via the influence matrix yields the comparison bound (later PRs).

* `sum_indicator_agreesOff_erase` — the `{x}`-coordinate split of an `agreesOff Λ`-conditioned sum
  (`x ∈ Λ`): `∑_σ 1[agreesOff Λ η] g = ∑_τ 1[agreesOff (Λ.erase x) η] (g(τ[x↦↑]) + g(τ[x↦↓]))`.
* `gibbsExpectationBC_singleton_boundary_update` — the single-site conditional ignores the boundary
  value at `x` itself.
* `heatBath` — the single-site heat-bath operator `K_x`.
* `gibbsExpectationBC_heatBath_invariant` — `⟨K_x f⟩^η_Λ = ⟨f⟩^η_Λ` for `x ∈ Λ`.

The multi-site Dobrushin comparison theorem itself is not formalized here.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet]

omit [Fintype ι] [Fintype G.edgeSet] in
/-- **Boundary agreement off `{x}` ignores the value at `x`**: `agreesOff {x} (η[x↦s])` and
`agreesOff {x} η` are the same predicate (agreement is required only away from `x`). -/
theorem agreesOff_singleton_boundary_update (x : ι) (s : Spin) (τ ρ : Config ι) :
    agreesOff {x} (Function.update τ x s) ρ ↔ agreesOff {x} τ ρ := by
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  have hix : i ≠ x := by simpa using hi
  rw [Function.update_of_ne hix]

/-- **The single-site Boltzmann weight ignores the boundary value at `x`**. -/
theorem boltzmannWeightBC_singleton_boundary_update (β J h : ℝ) (x : ι) (s : Spin) (τ : Config ι) :
    boltzmannWeightBC G β (fun _ => J) h {x} (Function.update τ x s)
      = boltzmannWeightBC G β (fun _ => J) h {x} τ := by
  funext σ
  unfold boltzmannWeightBC
  rw [show {σ | agreesOff {x} (Function.update τ x s) σ} = {σ | agreesOff {x} τ σ} from
    Set.ext fun σ' => agreesOff_singleton_boundary_update x s τ σ']

/-- **The single-site partition function ignores the boundary value at `x`**. -/
theorem partitionFunctionBC_singleton_boundary_update (β J h : ℝ) (x : ι) (s : Spin)
    (τ : Config ι) :
    partitionFunctionBC G β (fun _ => J) h {x} (Function.update τ x s)
      = partitionFunctionBC G β (fun _ => J) h {x} τ := by
  unfold partitionFunctionBC
  rw [boltzmannWeightBC_singleton_boundary_update]

/-- **The single-site conditional expectation ignores the boundary value at `x`**: conditioning the
free site `x` on the rest depends only on the configuration away from `x`. -/
theorem gibbsExpectationBC_singleton_boundary_update (β J h : ℝ) (x : ι) (s : Spin) (τ : Config ι)
    (f : Config ι → ℝ) :
    gibbsExpectationBC G β (fun _ => J) h {x} (Function.update τ x s) f
      = gibbsExpectationBC G β (fun _ => J) h {x} τ f := by
  unfold gibbsExpectationBC
  rw [partitionFunctionBC_singleton_boundary_update, boltzmannWeightBC_singleton_boundary_update]

omit [Fintype G.edgeSet] in
/-- **The `{x}`-coordinate split of an `agreesOff Λ`-conditioned sum** (`x ∈ Λ`): summing the
indicator of `agreesOff Λ η` against `g` equals summing, over configurations agreeing off
`Λ.erase x`, the two single-site updates at `x`. The boundary value at `x` is free inside `Λ`. -/
theorem sum_indicator_agreesOff_erase {Λ : Finset ι} (x : ι) (hx : x ∈ Λ) (η : Config ι)
    (g : Config ι → ℝ) :
    ∑ σ : Config ι, Set.indicator {σ | agreesOff Λ η σ} g σ
      = ∑ τ : Config ι, Set.indicator {τ | agreesOff (Λ.erase x) η τ}
          (fun τ => g (Function.update τ x Spin.up) + g (Function.update τ x Spin.down)) τ := by
  classical
  have hL : ∑ σ : Config ι, Set.indicator {σ | agreesOff Λ η σ} g σ
      = ∑ σ ∈ univ.filter (fun σ => agreesOff Λ η σ), g σ := by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun σ _ => by rw [Set.indicator_apply]; rfl
  have hR : ∑ τ : Config ι, Set.indicator {τ | agreesOff (Λ.erase x) η τ}
        (fun τ => g (Function.update τ x Spin.up) + g (Function.update τ x Spin.down)) τ
      = ∑ τ ∈ univ.filter (fun τ => agreesOff (Λ.erase x) η τ),
          (g (Function.update τ x Spin.up) + g (Function.update τ x Spin.down)) := by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun τ _ => by rw [Set.indicator_apply]; rfl
  rw [hL, hR]
  have hsplit : ∀ τ : Config ι,
      g (Function.update τ x Spin.up) + g (Function.update τ x Spin.down)
        = ∑ s : Spin, g (Function.update τ x s) :=
      fun τ => (sum_spin (fun s => g (Function.update τ x s))).symm
  rw [Finset.sum_congr rfl fun τ _ => hsplit τ, ← Finset.sum_product']
  refine Finset.sum_bij' (fun σ _ => (Function.update σ x (η x), σ x))
    (fun p _ => Function.update p.1 x p.2) ?_ ?_ ?_ ?_ ?_
  · -- forward: (update σ x (η x), σ x) ∈ T ×ˢ univ
    intro σ hσ
    refine Finset.mk_mem_product (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      (Finset.mem_univ _)
    intro i hi_erase
    by_cases hix : i = x
    · subst hix; rw [Function.update_self]
    · rw [Function.update_of_ne hix]
      exact (Finset.mem_filter.mp hσ).2 i
        (fun hiL => hi_erase (Finset.mem_erase.mpr ⟨hix, hiL⟩))
  · -- backward: update p.1 x p.2 ∈ S
    intro p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro i hiL
    have hix : i ≠ x := fun he => hiL (he ▸ hx)
    change Function.update p.1 x p.2 i = η i
    rw [Function.update_of_ne hix]
    exact (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2 i
      (fun hie => hiL (Finset.mem_of_mem_erase hie))
  · -- left inverse: update (update σ x (η x)) x (σ x) = σ
    intro σ _
    change Function.update (Function.update σ x (η x)) x (σ x) = σ
    rw [Function.update_idem, Function.update_eq_self]
  · -- right inverse: (update (update p.1 x p.2) x (η x), (update p.1 x p.2) x) = p
    intro p hp
    have hp1x : p.1 x = η x :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2 x (Finset.notMem_erase x Λ)
    refine Prod.ext ?_ (Function.update_self x p.2 p.1)
    change Function.update (Function.update p.1 x p.2) x (η x) = p.1
    rw [Function.update_idem, ← hp1x, Function.update_eq_self]
  · -- value: g σ = g (update (update σ x (η x)) x (σ x))
    intro σ _
    change g σ = g (Function.update (Function.update σ x (η x)) x (σ x))
    rw [Function.update_idem, Function.update_eq_self]

/-- **The single-site heat-bath operator** `K_x f (σ) = ⟨f⟩^σ_{x}`: replaces `f` by its single-site
conditional expectation at `x`, with the rest of the configuration `σ` acting as the boundary. -/
noncomputable def heatBath (β J h : ℝ) (x : ι) (f : Config ι → ℝ) (σ : Config ι) : ℝ :=
  gibbsExpectationBC G β (fun _ => J) h {x} σ f

/-- **Heat-bath single-site invariance** (GJ §17.1): the finite-volume boundary-condition Gibbs
measure is invariant under the single-site heat-bath operator at any free site `x ∈ Λ`,
`⟨K_x f⟩^η_Λ = ⟨f⟩^η_Λ`. Re-sampling the spin at `x` from its conditional law leaves the measure
unchanged (the finite-volume heat-bath/DLR consistency); this is the first telescoping step of the
Dobrushin comparison theorem (Issue #4201). -/
theorem gibbsExpectationBC_heatBath_invariant {Λ : Finset ι} (x : ι) (hx : x ∈ Λ)
    (β J h : ℝ) (η : Config ι) (f : Config ι → ℝ) :
    gibbsExpectationBC G β (fun _ => J) h Λ η (heatBath G β J h x f)
      = gibbsExpectationBC G β (fun _ => J) h Λ η f := by
  classical
  -- push the observable inside the indicator and collapse the {x}-coordinate
  have hnum : ∀ F : Config ι → ℝ,
      ∑ σ : Config ι, F σ * boltzmannWeightBC G β (fun _ => J) h Λ η σ
        = ∑ τ : Config ι, Set.indicator {τ | agreesOff (Λ.erase x) η τ}
            (fun τ => F (Function.update τ x Spin.up)
                * boltzmannWeightJ G β (fun _ => J) h (Function.update τ x Spin.up)
              + F (Function.update τ x Spin.down)
                * boltzmannWeightJ G β (fun _ => J) h (Function.update τ x Spin.down)) τ := by
    intro F
    have hpush : ∀ σ : Config ι, F σ * boltzmannWeightBC G β (fun _ => J) h Λ η σ
        = Set.indicator {σ | agreesOff Λ η σ}
            (fun σ => F σ * boltzmannWeightJ G β (fun _ => J) h σ) σ := by
      intro σ
      unfold boltzmannWeightBC
      by_cases hσ : agreesOff Λ η σ
      · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem hσ]
      · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem hσ, mul_zero]
    rw [Finset.sum_congr rfl (fun σ _ => hpush σ),
      sum_indicator_agreesOff_erase x hx η
        (fun σ => F σ * boltzmannWeightJ G β (fun _ => J) h σ)]
  -- per-coordinate heat-bath identity: K_x averages f over the {x}-conditional
  have hkey : ∀ τ : Config ι,
      heatBath G β J h x f (Function.update τ x Spin.up)
          * boltzmannWeightJ G β (fun _ => J) h (Function.update τ x Spin.up)
        + heatBath G β J h x f (Function.update τ x Spin.down)
          * boltzmannWeightJ G β (fun _ => J) h (Function.update τ x Spin.down)
      = f (Function.update τ x Spin.up)
          * boltzmannWeightJ G β (fun _ => J) h (Function.update τ x Spin.up)
        + f (Function.update τ x Spin.down)
          * boltzmannWeightJ G β (fun _ => J) h (Function.update τ x Spin.down) := by
    intro τ
    have hb_up : heatBath G β J h x f (Function.update τ x Spin.up)
        = gibbsExpectationBC G β (fun _ => J) h {x} τ f :=
      gibbsExpectationBC_singleton_boundary_update G β J h x Spin.up τ f
    have hb_dn : heatBath G β J h x f (Function.update τ x Spin.down)
        = gibbsExpectationBC G β (fun _ => J) h {x} τ f :=
      gibbsExpectationBC_singleton_boundary_update G β J h x Spin.down τ f
    have hZx : partitionFunctionBC G β (fun _ => J) h {x} τ
        = boltzmannWeightJ G β (fun _ => J) h (Function.update τ x Spin.up)
          + boltzmannWeightJ G β (fun _ => J) h (Function.update τ x Spin.down) := by
      unfold partitionFunctionBC
      simpa using sum_F_boltzmannBC_singleton G β J h x τ (fun _ => (1 : ℝ))
    have hZne : boltzmannWeightJ G β (fun _ => J) h (Function.update τ x Spin.up)
        + boltzmannWeightJ G β (fun _ => J) h (Function.update τ x Spin.down) ≠ 0 := by
      have h1 := boltzmannWeightJ_pos G β (fun _ => J) h (Function.update τ x Spin.up)
      have h2 := boltzmannWeightJ_pos G β (fun _ => J) h (Function.update τ x Spin.down)
      positivity
    rw [hb_up, hb_dn, gibbsExpectationBC, sum_F_boltzmannBC_singleton, hZx]
    field_simp
  rw [gibbsExpectationBC, gibbsExpectationBC]
  congr 1
  rw [hnum (heatBath G β J h x f), hnum f]
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases hτ : agreesOff (Λ.erase x) η τ
  · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ]; exact hkey τ
  · rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ]

end Dobrushin

end IsingModel
