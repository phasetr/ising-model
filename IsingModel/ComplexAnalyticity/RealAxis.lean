import IsingModel.ComplexAnalyticity.FugacityCalculus

/-!
# Real-Axis and Joint Analyticity Restatements

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-- `real_pos_mem_leeYangDomain` specialized: any positive real is
in Lee-Yang. -/
theorem real_pos_mem_leeYangDomain' (h₀ : ℝ) (hpos : 0 < h₀) :
    (h₀ : ℂ) ∈ leeYangDomain :=
  real_pos_mem_leeYangDomain hpos

/-- All positive reals contained in Lee-Yang: formulated as a subset
statement. -/
theorem real_positives_subset_leeYangDomain :
    ((fun h₀ : ℝ => (h₀ : ℂ)) '' Set.Ioi 0) ⊆ leeYangDomain := by
  rintro h ⟨h₀, hpos, rfl⟩
  exact real_pos_mem_leeYangDomain hpos

/-- All positive reals contained in Lee-Yang subdomain. -/
theorem real_positives_subset_leeYangSubdomain (β : ℝ) (N : ℕ) :
    ((fun h₀ : ℝ => (h₀ : ℂ)) '' Set.Ioi 0) ⊆ leeYangSubdomain β N := by
  rintro h ⟨h₀, hpos, rfl⟩
  exact real_pos_mem_leeYangSubdomain β N hpos

/-- `leeYangDomain` contains all points with `Re h > 0 ∧ Im h = 0`. -/
theorem real_axis_pos_subset_leeYangDomain :
    {h : ℂ | 0 < h.re ∧ h.im = 0} ⊆ leeYangDomain := by
  intro h ⟨hre, him⟩
  change |h.im| < h.re
  rw [him, abs_zero]
  exact hre

/-- `leeYangDomain` is `IsOpen`; use for nhd calculations. -/
theorem leeYangDomain_mem_nhds {h : ℂ} (hmem : h ∈ leeYangDomain) :
    leeYangDomain ∈ nhds h :=
  isOpen_leeYangDomain.mem_nhds hmem

/-- `leeYangSubdomain` is in the neighbourhoods of any of its points. -/
theorem leeYangSubdomain_mem_nhds (β : ℝ) (N : ℕ) {h : ℂ}
    (hmem : h ∈ leeYangSubdomain β N) :
    leeYangSubdomain β N ∈ nhds h :=
  (isOpen_leeYangSubdomain β N).mem_nhds hmem

/-- Any member of `leeYangDomain` has positive real part. -/
theorem re_pos_of_mem_leeYangDomain {h : ℂ} (hh : h ∈ leeYangDomain) :
    0 < h.re := by
  have h1 : |h.im| < h.re := hh
  linarith [abs_nonneg h.im]

/-- Any member of `leeYangSubdomain` has positive real part. -/
theorem re_pos_of_mem_leeYangSubdomain (β : ℝ) (N : ℕ) {h : ℂ}
    (hh : h ∈ leeYangSubdomain β N) : 0 < h.re :=
  re_pos_of_mem_leeYangDomain hh.1

/-- Any member of `leeYangDomain` is non-zero. -/
theorem ne_zero_of_mem_leeYangDomain {h : ℂ} (hh : h ∈ leeYangDomain) :
    h ≠ 0 := by
  intro hz
  have hre_pos : 0 < h.re := re_pos_of_mem_leeYangDomain hh
  rw [hz] at hre_pos
  simp at hre_pos

/-- Any member of `leeYangSubdomain` is non-zero. -/
theorem ne_zero_of_mem_leeYangSubdomain (β : ℝ) (N : ℕ) {h : ℂ}
    (hh : h ∈ leeYangSubdomain β N) : h ≠ 0 :=
  ne_zero_of_mem_leeYangDomain hh.1

/-- The positive real axis embedded into ℂ is a subset of leeYangDomain. -/
theorem real_pos_axis_subset_leeYangDomain :
    Set.range (fun x : Set.Ioi (0 : ℝ) => (x.1 : ℂ)) ⊆ leeYangDomain := by
  rintro h ⟨⟨x, hx⟩, rfl⟩
  exact real_pos_mem_leeYangDomain hx

/-- For fixed real `β > 0`, the Lee-Yang domain is a subset of the
analyticity locus of `freeEnergyComplex` via branches. (Symbolic form.)
-/
theorem leeYangDomain_subset_branch_locus
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) [Nonempty ι] :
    ∀ h ∈ leeYangDomain,
      ∃ f : ℂ → ℂ, AnalyticAt ℂ f h ∧
        Complex.exp ((Fintype.card ι : ℂ) * f h)
          = partitionFunctionComplex G (J : ℂ) h (β : ℂ) := fun h hh => by
  obtain ⟨f, hf_ana, hf_exp, _⟩ :=
    exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain G hβ hJ hh
  exact ⟨f, hf_ana, hf_exp⟩

/-- Headline: `freeEnergyComplex` has an analytic local branch at every
point of the Lee-Yang domain (restatement without the equality at the
basepoint). -/
theorem freeEnergyComplex_exists_analyticBranch
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) [Nonempty ι] :
    ∀ h ∈ leeYangDomain, ∃ f : ℂ → ℂ, AnalyticAt ℂ f h ∧
        Complex.exp ((Fintype.card ι : ℂ) * f h)
          = partitionFunctionComplex G (J : ℂ) h (β : ℂ) :=
  fun _ hh =>
    let ⟨f, hfa, hfexp, _⟩ :=
      exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain G hβ hJ hh
    ⟨f, hfa, hfexp⟩

/-- **Strong form**: existence of `f` with (a) AnalyticAt, (b)
`exp(|ι|·f) = Z`, (c) `f` equals the principal-branch freeEnergyComplex
at the basepoint. Pointwise statement over all of leeYangDomain. -/
theorem freeEnergyComplex_exists_analyticBranch_strong
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) [Nonempty ι] :
    ∀ h ∈ leeYangDomain, ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h
      ∧ Complex.exp ((Fintype.card ι : ℂ) * f h)
          = partitionFunctionComplex G (J : ℂ) h (β : ℂ)
      ∧ f h = freeEnergyComplex G (J : ℂ) h (β : ℂ) := fun _ hh =>
  exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain G hβ hJ hh

/-- `freeEnergyComplex G J h β` is an entire function of `(J, h, β)`
restricted to the slitPlane locus. Packaged joint version. -/
theorem freeEnergyComplex_analyticOnNhd_slitPlane_locus_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => freeEnergyComplex G z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | partitionFunctionComplex G z.1 z.2.1 z.2.2
                        ∈ Complex.slitPlane} := by
  intro z hmem
  exact freeEnergyComplex_analyticAt_joint G z hmem

/-- The joint slitPlane locus is open. -/
theorem isOpen_freeEnergy_analyticity_locus_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    IsOpen {z : ℂ × ℂ × ℂ |
              partitionFunctionComplex G z.1 z.2.1 z.2.2
                ∈ Complex.slitPlane} := by
  exact (continuous_partitionFunctionComplex_joint G).isOpen_preimage _
    Complex.isOpen_slitPlane

/-- For real parameters `p : IsingParams ℝ`, the joint-analyticity point
`((p.J : ℂ), (p.h : ℂ), (p.β : ℂ))` is in the slitPlane locus. -/
theorem real_params_in_analyticity_locus_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) ∈
      {z : ℂ × ℂ × ℂ | partitionFunctionComplex G z.1 z.2.1 z.2.2
                        ∈ Complex.slitPlane} :=
  partitionFunctionComplex_mem_slitPlane_of_real G p

/-- The real parameter slice is in the analyticity locus. -/
theorem real_params_analyticAt_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    AnalyticAt ℂ
      (fun z : ℂ × ℂ × ℂ => freeEnergyComplex G z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  freeEnergyComplex_analyticAt_joint G _
    (partitionFunctionComplex_mem_slitPlane_of_real G p)

/-- **Image of `IsingParams ℝ` under cast**: `(J, h, β) ↦ ((J:ℂ), (h:ℂ), (β:ℂ))`
sends every real-parameter point into the joint analyticity locus. -/
theorem real_params_image_subset_analyticity_locus_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (fun p : IsingParams ℝ => ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)))
      '' Set.univ ⊆
      {z : ℂ × ℂ × ℂ | partitionFunctionComplex G z.1 z.2.1 z.2.2
                        ∈ Complex.slitPlane} := by
  rintro z ⟨p, _, rfl⟩
  exact partitionFunctionComplex_mem_slitPlane_of_real G p

/-- **Continuity of `freeEnergyComplex` jointly on the analyticity
locus**. -/
theorem freeEnergyComplex_continuousOn_slitPlane_locus_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    ContinuousOn
      (fun z : ℂ × ℂ × ℂ => freeEnergyComplex G z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | partitionFunctionComplex G z.1 z.2.1 z.2.2
                        ∈ Complex.slitPlane} := fun z hmem =>
  ((freeEnergyComplex_analyticAt_joint G z hmem).continuousAt).continuousWithinAt

/-- `DifferentiableOn` form of the above. -/
theorem freeEnergyComplex_differentiableOn_slitPlane_locus_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    DifferentiableOn ℂ
      (fun z : ℂ × ℂ × ℂ => freeEnergyComplex G z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | partitionFunctionComplex G z.1 z.2.1 z.2.2
                        ∈ Complex.slitPlane} := fun z hmem =>
  (freeEnergyComplex_analyticAt_joint G z hmem).differentiableAt.differentiableWithinAt

/-- **log Z analyticity locus is open**. -/
theorem isOpen_logZ_slitPlane_locus
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ) :
    IsOpen {h : ℂ | partitionFunctionComplex G J h β ∈ Complex.slitPlane} :=
  isOpen_freeEnergy_analyticity_locus G J β

/-- Jointly in (h, β) at fixed real `J > 0`, the slitPlane locus is open. -/
theorem isOpen_slitPlane_locus_h_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℂ) :
    IsOpen {z : ℂ × ℂ |
              partitionFunctionComplex G J z.1 z.2 ∈ Complex.slitPlane} := by
  have hcont : Continuous
      (fun z : ℂ × ℂ => partitionFunctionComplex G J z.1 z.2) := by
    refine continuous_iff_continuousAt.mpr fun z => ?_
    -- Joint entireness implies continuity.
    have := continuous_partitionFunctionComplex_joint G
    have hp : ContinuousAt
        (fun z : ℂ × ℂ × ℂ =>
          partitionFunctionComplex G z.1 z.2.1 z.2.2) (J, z.1, z.2) :=
      this.continuousAt
    exact hp.comp ((continuous_const (y := J)).prodMk continuous_id).continuousAt
  exact hcont.isOpen_preimage _ Complex.isOpen_slitPlane

/-- The analyticity locus contains every `(h₀ : ℂ)` at real `h₀` (cast). -/
theorem real_coe_mem_slitPlane_locus_h
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (h₀ : ℝ) :
    (h₀ : ℂ) ∈
      {h : ℂ | partitionFunctionComplex G (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane} :=
  partitionFunctionComplex_mem_slitPlane_of_real G ⟨J, h₀, β⟩

/-- **The positive real axis (cast) sits in the h-slitPlane locus**:
for every `h₀ > 0` real, `Z(↑J, ↑h₀, ↑β) ∈ slitPlane` (at real
parameters). -/
theorem real_axis_in_slitPlane_locus_h
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    ((fun h₀ : ℝ => (h₀ : ℂ)) '' Set.univ) ⊆
      {h : ℂ | partitionFunctionComplex G (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane} := by
  rintro h ⟨h₀, _, rfl⟩
  exact real_coe_mem_slitPlane_locus_h G J β h₀

/-- `freeEnergyComplex` `AnalyticAt` at every real (cast to complex) `h₀`. -/
theorem freeEnergyComplex_analyticAt_h_real_coe
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (h₀ : ℝ) :
    AnalyticAt ℂ
      (fun h => freeEnergyComplex G (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  freeEnergyComplex_analyticAt_h_ofReal G J h₀ β

/-- **Finite-volume `freeEnergy` is Differentiable at every real h₀**
(in the complex sense). -/
theorem freeEnergyComplex_differentiableAt_h_real_coe
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (h₀ : ℝ) :
    DifferentiableAt ℂ
      (fun h => freeEnergyComplex G (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  (freeEnergyComplex_analyticAt_h_real_coe G J β h₀).differentiableAt

/-- **Finite-volume `freeEnergy` is Continuous at every real h₀**. -/
theorem freeEnergyComplex_continuousAt_h_real_coe
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (h₀ : ℝ) :
    ContinuousAt
      (fun h => freeEnergyComplex G (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  (freeEnergyComplex_analyticAt_h_real_coe G J β h₀).continuousAt

/-- The image of the positive real axis lies inside `leeYangDomain`. -/
theorem range_real_axis_subset_leeYangDomain :
    Set.range (fun x : {x : ℝ // 0 < x} => (x.1 : ℂ)) ⊆ leeYangDomain := by
  rintro h ⟨⟨x, hx⟩, rfl⟩
  exact real_pos_mem_leeYangDomain hx

/-- **Restriction of `freeEnergyComplex` to the real axis equals
`freeEnergy`**: an explicit function-extending statement. -/
theorem freeEnergyComplex_restrict_real_axis_eq_freeEnergy
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    (fun h : ℝ =>
        freeEnergyComplex G (J : ℂ) (h : ℂ) (β : ℂ))
      = fun h : ℝ => ((freeEnergy G ⟨J, h, β⟩ : ℝ) : ℂ) := by
  funext h
  exact freeEnergyComplex_at_real G J h β

/-- `partitionFunctionComplex` restricted to the real axis equals the
cast of the real `partitionFunction`. -/
theorem partitionFunctionComplex_restrict_real_axis_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    (fun h : ℝ =>
        partitionFunctionComplex G (J : ℂ) (h : ℂ) (β : ℂ))
      = fun h : ℝ => ((partitionFunction G ⟨J, h, β⟩ : ℝ) : ℂ) := by
  funext h
  exact (partitionFunction_ofReal_eq_partitionFunctionComplex
    G ⟨J, h, β⟩).symm

/-- The joint complex partition function equals the real cast on
`IsingParams ℝ`-points. -/
theorem partitionFunctionComplex_restrict_joint_real_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (fun p : IsingParams ℝ =>
        partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = fun p : IsingParams ℝ => ((partitionFunction G p : ℝ) : ℂ) := by
  funext p
  exact (partitionFunction_ofReal_eq_partitionFunctionComplex G p).symm

/-- `freeEnergyComplex` restricted to `IsingParams ℝ`-points. -/
theorem freeEnergyComplex_restrict_joint_real_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (fun p : IsingParams ℝ =>
        freeEnergyComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = fun p : IsingParams ℝ => ((freeEnergy G p : ℝ) : ℂ) := by
  funext p
  exact freeEnergyComplex_ofReal_eq_freeEnergy G p

/-- `partitionFunctionComplex` norm (modulus) at real parameters. -/
theorem norm_partitionFunctionComplex_eq_partitionFunction_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    ‖partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)‖
      = partitionFunction G p :=
  norm_partitionFunctionComplex_at_real G p

/-- `freeEnergyComplex` jointly continuous on its slitPlane locus
(including the real slice). -/
theorem continuous_freeEnergyComplex_on_locus
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    ContinuousOn
      (fun z : ℂ × ℂ × ℂ => freeEnergyComplex G z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | partitionFunctionComplex G z.1 z.2.1 z.2.2
                        ∈ Complex.slitPlane} :=
  freeEnergyComplex_continuousOn_slitPlane_locus_joint G

/-- At `(J, h, β)` all real, the joint `freeEnergyComplex` is
continuous. -/
theorem continuousAt_freeEnergyComplex_at_real_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    ContinuousAt
      (fun z : ℂ × ℂ × ℂ => freeEnergyComplex G z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  (real_params_analyticAt_joint G p).continuousAt

/-- `differentiableAt` joint form at real parameters. -/
theorem differentiableAt_freeEnergyComplex_at_real_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    DifferentiableAt ℂ
      (fun z : ℂ × ℂ × ℂ => freeEnergyComplex G z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  (real_params_analyticAt_joint G p).differentiableAt

/-- `partitionFunctionComplex` is entire in each parameter: alias
re-packaged for convenience. -/
theorem partitionFunctionComplex_entire_h
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ) :
    Differentiable ℂ (fun h => partitionFunctionComplex G J h β) := fun h =>
  (partitionFunctionComplex_analyticAt_h G J β h).differentiableAt

/-- `partitionFunctionComplex` is entire in `J`. -/
theorem partitionFunctionComplex_entire_J
    (G : SimpleGraph ι) [Fintype G.edgeSet] (h β : ℂ) :
    Differentiable ℂ (fun J => partitionFunctionComplex G J h β) := fun J =>
  (partitionFunctionComplex_analyticAt_J G h β J).differentiableAt

/-- `partitionFunctionComplex` is entire in `β`. -/
theorem partitionFunctionComplex_entire_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J h : ℂ) :
    Differentiable ℂ (fun β => partitionFunctionComplex G J h β) := fun β =>
  (partitionFunctionComplex_analyticAt_beta G J h β).differentiableAt

/-- `partitionFunctionComplex` is jointly Differentiable on ℂ³. -/
theorem partitionFunctionComplex_entire_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Differentiable ℂ
      (fun z : ℂ × ℂ × ℂ => partitionFunctionComplex G z.1 z.2.1 z.2.2) :=
    fun z => (partitionFunctionComplex_analyticAt_joint G z).differentiableAt

/-- `partitionFunctionComplex` is `AnalyticOnNhd` on all of ℂ³. -/
theorem partitionFunctionComplex_analyticOnNhd_univ_joint'
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => partitionFunctionComplex G z.1 z.2.1 z.2.2)
      Set.univ := fun z _ =>
  partitionFunctionComplex_analyticAt_joint G z





/-- **GJ §4.6 Thm 4.6.2 finite-volume (AnalyticOnNhd form)**: there is
an analytic family of local log-branches of `Z` covering all of
`leeYangDomain`. For each point `h₀`, the local branch `f` from
`exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain` is
analytic at `h₀` and satisfies `exp(|ι|·f) = Z` near `h₀`. -/
theorem analyticBranch_freeEnergyComplex_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) [Nonempty ι] :
    ∀ h₀ ∈ leeYangDomain,
      ∃ f : ℂ → ℂ,
          AnalyticAt ℂ f h₀
        ∧ Complex.exp ((Fintype.card ι : ℂ) * f h₀)
            = partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ)
        ∧ f h₀ = freeEnergyComplex G (J : ℂ) h₀ (β : ℂ) := fun _ hmem =>
  exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain G hβ hJ hmem


end IsingModel
