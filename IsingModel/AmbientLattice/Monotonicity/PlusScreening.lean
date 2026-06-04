import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxScreeningCapstone

/-!
# General-ambient `+` boundary screening (Issue #3581 PR 3)

The cubic-box `+` screening (`gibbsExpectationBC_cubicBox_succ`) generalised to an
arbitrary ambient pair `Λ₁ ⊆ Λ₂` with an inner conditioning region `I : Finset ↑Λ₁`
whose nearest-neighbour shell is separated from `I`.  Under that separation
hypothesis, the `+` boundary expectation of an observable depending only on the
inner configuration is **independent of the ambient** (`Λ₁` versus `Λ₂`): the shell
is frozen `+` and factors out of the normalised ratio.

This is the ambient-independence input for the translation-invariance squeeze
(Issue #3581): the translated cubic box is not itself a cubic box, so the cubic
screening does not apply directly, but the general screening does.

* `agreesOff_plus_configEquivSubtypeProd_iff` — boundary agreement splits along the
  configuration split.
* `edgeSpin_eq_one_of_agreesOff_extra_general` — frozen extra-edge spin.
* `boltzmannWeightBC_extendGraph_pointwise` — the per-configuration weight factoring.
* `gibbsExpectationBC_extendGraph_screening` — the general ambient independence.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17, pp. 100–104.
-/

namespace IsingModel

namespace Ambient

open Finset

variable {V : Type*} [DecidableEq V]

/-- The canonical injection `↑Λ₁ ↪ ↑Λ₂` as a `Function.Embedding` (for `Finset.map`). -/
def subtypeInclEmb {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂) : (↑Λ₁ : Type _) ↪ (↑Λ₂ : Type _) :=
  ⟨subtypeIncl h12, subtypeIncl_injective h12⟩

/-- **Boundary agreement splits along the configuration split**: a recombined
configuration agrees with `+` off the lifted inner region `I` iff its `Λ₁`-part
agrees with `+` off `I` and its shell part is all-`+`. -/
theorem agreesOff_plus_configEquivSubtypeProd_iff {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    (I : Finset (↑Λ₁ : Type _)) (σ₁ : Config (↑Λ₁ : Type _))
    (σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin) :
    agreesOff (I.map (subtypeInclEmb h12)) (plusConfig _)
        ((configEquivSubtypeProd h12).symm (σ₁, σ₂))
      ↔ agreesOff I (plusConfig _) σ₁ ∧ (∀ v, σ₂ v = Spin.up) := by
  classical
  have hres : ∀ k : (↑Λ₁ : Type _),
      ((configEquivSubtypeProd h12).symm (σ₁, σ₂)) (subtypeIncl h12 k) = σ₁ k := by
    intro k
    have hr := congrFun (restrictConfig_configEquivSubtypeProd_symm h12 σ₁ σ₂) k
    simpa only [restrictConfig, Function.comp_apply] using hr
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun v => ?_⟩
    · have hjnotI : subtypeIncl h12 k ∉ I.map (subtypeInclEmb h12) := by
        rw [Finset.mem_map]
        rintro ⟨a, ha, hae⟩
        simp only [subtypeInclEmb, Function.Embedding.coeFn_mk] at hae
        exact hk (subtypeIncl_injective h12 hae ▸ ha)
      have := h (subtypeIncl h12 k) hjnotI
      rwa [hres k] at this
    · have hvnotI : v.val ∉ I.map (subtypeInclEmb h12) := by
        rw [Finset.mem_map]
        rintro ⟨a, _, hae⟩
        have ha2 : ((subtypeInclEmb h12) a).val ∈ Λ₁ := a.2
        exact v.2 (hae ▸ ha2)
      have := h v.val hvnotI
      rwa [configEquivSubtypeProd_symm_apply_compl h12 σ₁ σ₂ v] at this
  · rintro ⟨h1, h2⟩ j hj
    by_cases hjΛ : j.val ∈ Λ₁
    · have hknotI : (⟨j.val, hjΛ⟩ : (↑Λ₁ : Type _)) ∉ I := by
        intro hkI
        exact hj (Finset.mem_map.mpr ⟨⟨j.val, hjΛ⟩, hkI, Subtype.ext rfl⟩)
      have hjk : j = subtypeIncl h12 ⟨j.val, hjΛ⟩ := Subtype.ext rfl
      rw [hjk, hres ⟨j.val, hjΛ⟩]
      exact h1 ⟨j.val, hjΛ⟩ hknotI
    · have := configEquivSubtypeProd_symm_apply_compl h12 σ₁ σ₂ ⟨j, hjΛ⟩
      rw [this]
      exact h2 _

variable (G : SimpleGraph V)

/-- **Frozen extra-edge spin** (general): if `σ` agrees with `+` off the lifted
inner region `I` and every extra edge (of `Λ₂` but not the extension of `Λ₁`) has
its endpoints outside `I` (`hsep`), then every extra edge has `edgeSpin σ e = 1`. -/
theorem edgeSpin_eq_one_of_agreesOff_extra_general {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (I : Finset (↑Λ₁ : Type _))
    (hsep : ∀ e ∈ (inducedGraph G Λ₂).edgeFinset \ (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset,
        ∀ u ∈ e, u ∉ I.map (subtypeInclEmb h12))
    {σ : Config (↑Λ₂ : Type _)} (hσ : agreesOff (I.map (subtypeInclEmb h12)) (plusConfig _) σ)
    {e : Sym2 (↑Λ₂ : Type _)}
    (he : e ∈ (inducedGraph G Λ₂).edgeFinset \ (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset) :
    edgeSpin (K := ℝ) σ e = 1 := by
  have hup : ∀ u ∈ e, σ u = Spin.up := fun u hu => hσ u (hsep e he u hu)
  revert hup
  refine Sym2.ind (fun a b hup => ?_) e
  have ha := hup a (Sym2.mem_mk_left a b)
  have hb := hup b (Sym2.mem_mk_right a b)
  simp [edgeSpin, Sym2.lift_mk, ha, hb, Spin.sign, Spin.toSign]

/-- **The general shell constant**: the exponential factor collecting the frozen
shell field and frozen extra-edge interaction, depending only on `Λ₁, Λ₂`. -/
noncomputable def plusShellConst {Λ₁ Λ₂ : Finset V} (_h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet] (J h β : ℝ) : ℝ :=
  Real.exp (-β *
    ((-h) * (Fintype.card {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)} : ℝ)
      + (-J) * (((inducedGraph G Λ₂).edgeFinset \
          (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset).card : ℝ)))

/-- The general shell constant is strictly positive. -/
theorem plusShellConst_pos {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet] (J h β : ℝ) :
    0 < plusShellConst G h12 J h β := Real.exp_pos _

/-- **Pointwise `+` boundary weight factoring** (general ambient): under the
configuration split, the `+` boundary Boltzmann weight on `Λ₂` of the recombined
configuration factors as the `+` boundary weight on `Λ₁` of `σ₁` times the shell
constant when `σ₂` is all-`+`, and is `0` otherwise. -/
theorem boltzmannWeightBC_extendGraph_pointwise {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet] [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (I : Finset (↑Λ₁ : Type _)) {J h β : ℝ}
    (hsep : ∀ e ∈ (inducedGraph G Λ₂).edgeFinset \ (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset,
        ∀ u ∈ e, u ∉ I.map (subtypeInclEmb h12))
    (σ₁ : Config (↑Λ₁ : Type _)) (σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin) :
    boltzmannWeightBC (inducedGraph G Λ₂) β (fun _ => J) h
        (I.map (subtypeInclEmb h12)) (plusConfig _)
        ((configEquivSubtypeProd h12).symm (σ₁, σ₂))
      = boltzmannWeightBC (inducedGraph G Λ₁) β (fun _ => J) h I (plusConfig _) σ₁
        * (if (∀ v, σ₂ v = Spin.up) then plusShellConst G h12 J h β else 0) := by
  set τ := (configEquivSubtypeProd h12).symm (σ₁, σ₂) with hτ_def
  by_cases hσ₂ : ∀ v, σ₂ v = Spin.up
  · rw [if_pos hσ₂]
    by_cases h1 : agreesOff I (plusConfig _) σ₁
    · have hτ : agreesOff (I.map (subtypeInclEmb h12)) (plusConfig _) τ :=
        (agreesOff_plus_configEquivSubtypeProd_iff h12 I σ₁ σ₂).mpr ⟨h1, hσ₂⟩
      have hcompl : ∀ v : {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)}, τ v.val = Spin.up :=
        fun v => by rw [hτ_def, configEquivSubtypeProd_symm_apply_compl]; exact hσ₂ v
      have hextra : ∀ e ∈ (inducedGraph G Λ₂).edgeFinset \
          (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset, edgeSpin (K := ℝ) τ e = 1 :=
        fun e he => edgeSpin_eq_one_of_agreesOff_extra_general G h12 I hsep hτ he
      rw [boltzmannWeightBC_of_agrees _ _ _ _ hτ, boltzmannWeightJ_uniform_eq,
        boltzmannWeight_inducedGraph_restrict_factor_const G h12
          (⟨J, h, β⟩ : IsingParams ℝ) τ hcompl hextra,
        hτ_def, restrictConfig_configEquivSubtypeProd_symm,
        ← boltzmannWeightJ_uniform_eq, ← boltzmannWeightBC_of_agrees _ _ _ _ h1]
      simp only [plusShellConst]
    · have hτ : ¬ agreesOff (I.map (subtypeInclEmb h12)) (plusConfig _) τ := fun hτ =>
        h1 ((agreesOff_plus_configEquivSubtypeProd_iff h12 I σ₁ σ₂).mp hτ).1
      rw [boltzmannWeightBC_of_not_agrees _ _ _ _ hτ,
        boltzmannWeightBC_of_not_agrees _ _ _ _ h1, zero_mul]
  · rw [if_neg hσ₂, mul_zero]
    have hτ : ¬ agreesOff (I.map (subtypeInclEmb h12)) (plusConfig _) τ := fun hτ =>
      hσ₂ ((agreesOff_plus_configEquivSubtypeProd_iff h12 I σ₁ σ₂).mp hτ).2
    rw [boltzmannWeightBC_of_not_agrees _ _ _ _ hτ]

/-- **Shell-indicator sum collapse** (general): only the all-`+` shell contributes. -/
theorem sum_shell_ite_eq_general {Λ₁ Λ₂ : Finset V} (C : ℝ) :
    (∑ σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin,
        (if (∀ v, σ₂ v = Spin.up) then C else 0)) = C := by
  classical
  rw [Fintype.sum_eq_single (fun _ => Spin.up)]
  · simp
  · intro σ₂ hσ₂
    rw [if_neg (fun hall => hσ₂ (funext fun v => hall v))]

/-- **Boundary-condition sum factoring** (general ambient): for an observable `F`
on `Λ₂` depending only on the inner configuration, the boundary-condition sum over
`Λ₂` factors as the `Λ₁` sum times the shell constant. -/
theorem bcSum_extendGraph_factor {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet] [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (I : Finset (↑Λ₁ : Type _)) {J h β : ℝ}
    (hsep : ∀ e ∈ (inducedGraph G Λ₂).edgeFinset \ (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset,
        ∀ u ∈ e, u ∉ I.map (subtypeInclEmb h12))
    (F : Config (↑Λ₂ : Type _) → ℝ) (F' : Config (↑Λ₁ : Type _) → ℝ)
    (hF : ∀ σ₁ σ₂, F ((configEquivSubtypeProd h12).symm (σ₁, σ₂)) = F' σ₁) :
    (∑ σ : Config (↑Λ₂ : Type _),
        F σ * boltzmannWeightBC (inducedGraph G Λ₂) β (fun _ => J) h
          (I.map (subtypeInclEmb h12)) (plusConfig _) σ)
      = (∑ σ₁ : Config (↑Λ₁ : Type _),
          F' σ₁ * boltzmannWeightBC (inducedGraph G Λ₁) β (fun _ => J) h I (plusConfig _) σ₁)
        * plusShellConst G h12 J h β := by
  rw [← Fintype.sum_equiv (configEquivSubtypeProd h12).symm _
    (fun σ => F σ * boltzmannWeightBC (inducedGraph G Λ₂) β (fun _ => J) h
      (I.map (subtypeInclEmb h12)) (plusConfig _) σ) (fun x => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun σ₁ _ => ?_)
  simp_rw [hF, boltzmannWeightBC_extendGraph_pointwise G h12 I hsep]
  rw [show (fun σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin =>
        F' σ₁ * (boltzmannWeightBC (inducedGraph G Λ₁) β (fun _ => J) h I (plusConfig _) σ₁
          * (if (∀ v, σ₂ v = Spin.up) then plusShellConst G h12 J h β else 0)))
      = (fun σ₂ => (F' σ₁ * boltzmannWeightBC (inducedGraph G Λ₁) β (fun _ => J) h I
          (plusConfig _) σ₁)
          * (if (∀ v, σ₂ v = Spin.up) then plusShellConst G h12 J h β else 0)) from by
    funext σ₂; ring]
  rw [← Finset.mul_sum, sum_shell_ite_eq_general]

/-- **Partition-function factoring** (general ambient). -/
theorem partitionFunctionBC_extendGraph_factor {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet] [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (I : Finset (↑Λ₁ : Type _)) {J h β : ℝ}
    (hsep : ∀ e ∈ (inducedGraph G Λ₂).edgeFinset \ (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset,
        ∀ u ∈ e, u ∉ I.map (subtypeInclEmb h12)) :
    partitionFunctionBC (inducedGraph G Λ₂) β (fun _ => J) h
        (I.map (subtypeInclEmb h12)) (plusConfig _)
      = partitionFunctionBC (inducedGraph G Λ₁) β (fun _ => J) h I (plusConfig _)
        * plusShellConst G h12 J h β := by
  unfold partitionFunctionBC
  have hh := bcSum_extendGraph_factor (J := J) (h := h) (β := β) G h12 I hsep
    (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ _ => rfl)
  simpa only [one_mul] using hh

/-- **General-ambient `+` boundary screening** (the ambient-independence input for
the translation-invariance squeeze, Issue #3581): for `Λ₁ ⊆ Λ₂` with the inner
region `I`'s extra-edge shell separated from `I` (`hsep`), the `+` boundary
expectation of an observable depending only on the inner configuration is the same
on `Λ₂` as on `Λ₁`. -/
theorem gibbsExpectationBC_extendGraph_screening {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet] [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (I : Finset (↑Λ₁ : Type _)) {J h β : ℝ}
    (hsep : ∀ e ∈ (inducedGraph G Λ₂).edgeFinset \ (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset,
        ∀ u ∈ e, u ∉ I.map (subtypeInclEmb h12))
    (φ : Config (↑Λ₂ : Type _) → ℝ) (φ' : Config (↑Λ₁ : Type _) → ℝ)
    (hφ : ∀ σ₁ σ₂, φ ((configEquivSubtypeProd h12).symm (σ₁, σ₂)) = φ' σ₁) :
    gibbsExpectationBC (inducedGraph G Λ₂) β (fun _ => J) h
        (I.map (subtypeInclEmb h12)) (plusConfig _) φ
      = gibbsExpectationBC (inducedGraph G Λ₁) β (fun _ => J) h I (plusConfig _) φ' := by
  unfold gibbsExpectationBC
  rw [bcSum_extendGraph_factor G h12 I hsep φ φ' hφ,
    partitionFunctionBC_extendGraph_factor G h12 I hsep]
  have hC : plusShellConst G h12 J h β ≠ 0 := ne_of_gt (plusShellConst_pos G h12 J h β)
  have hZ : partitionFunctionBC (inducedGraph G Λ₁) β (fun _ => J) h I (plusConfig _) ≠ 0 :=
    partitionFunctionBC_ne_zero _ _ _ _ _ _
  field_simp

end Ambient

end IsingModel
