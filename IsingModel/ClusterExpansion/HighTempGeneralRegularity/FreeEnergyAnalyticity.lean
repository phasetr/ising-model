import IsingModel.ClusterExpansion.HighTempGeneralRegularity.PolymerBounds

/-!
# High-temperature free energy analyticity

Mechanical child split from `ClusterExpansion.HighTempGeneralRegularity`.
-/

namespace IsingModel

open Finset
/-- **Partition function `AnalyticAt ℝ` in `β` at general `h`** (§18.6
extension): for any `(J, h, β)`, `Z(β) = ∑_σ exp(-β · H(σ))` is real-
analytic in `β`. Direct proof: each summand `exp(-β · H(σ))` is
`exp ∘ (linear in β)`, which is analytic; sum of analytic functions
over a finite finset is analytic. Extends `partitionFunction_analyticAt_beta_h_zero`
(Step 563) from `h = 0` to arbitrary `h`. -/
theorem partitionFunction_analyticAt_beta_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => partitionFunction G ⟨J, h, β'⟩) β := by
  have h_eq : (fun β' : ℝ => partitionFunction G ⟨J, h, β'⟩) =
      fun β' : ℝ => ∑ σ : Config ι,
        Real.exp ((-hamiltonian G ⟨J, h, β⟩ σ) * β') := by
    funext β'
    unfold partitionFunction boltzmannWeight
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    have h_ham : hamiltonian G ⟨J, h, β'⟩ σ = hamiltonian G ⟨J, h, β⟩ σ := rfl
    rw [h_ham]; ring_nf
  rw [h_eq]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  exact analyticAt_rexp.comp (analyticAt_const.mul analyticAt_id)

/-- **Free energy `AnalyticAt ℝ` in `β` at general `h`** (§18.6
extension): `f = (1/|ι|) · log Z` is real-analytic in `β` at every
point, for any `J, h`. Composes `partitionFunction_analyticAt_beta_general_h`
with `AnalyticAt.log` (using `partitionFunction_pos`). -/
theorem freeEnergy_analyticAt_beta_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergy G ⟨J, h, β'⟩) β := by
  unfold freeEnergy
  refine analyticAt_const.mul ?_
  exact (partitionFunction_analyticAt_beta_general_h G J h β).log
    (partitionFunction_pos G _)

/-- **Partition function `AnalyticAt ℝ` in `J` at general `h`** (§18.6
extension): for any `(β, h, J)`, `Z(J) = ∑_σ exp(-β · H(σ))` is real-
analytic in `J`, since the Hamiltonian depends linearly on `J` (only
through the interaction term). Direct proof analogous to
`partitionFunction_analyticAt_beta_general_h`. -/
theorem partitionFunction_analyticAt_J_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => partitionFunction G ⟨J', h, β⟩) J := by
  have h_eq : (fun J' : ℝ => partitionFunction G ⟨J', h, β⟩) =
      fun J' : ℝ => ∑ σ : Config ι,
        Real.exp ((β * (∑ e ∈ G.edgeFinset, edgeSpin σ e)) * J' +
          (-β * externalFieldEnergy h σ)) := by
    funext J'
    unfold partitionFunction boltzmannWeight hamiltonian interactionEnergy
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    ring_nf
  rw [h_eq]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_rexp.comp ?_
  exact (analyticAt_const.mul analyticAt_id).add analyticAt_const

/-- **Free energy `AnalyticAt ℝ` in `J` at general `h`** (§18.6
extension): `f = (1/|ι|) · log Z` is real-analytic in `J` at every
point, for any `β, h`. Composes `partitionFunction_analyticAt_J_general_h`
with `AnalyticAt.log` (using `partitionFunction_pos`). -/
theorem freeEnergy_analyticAt_J_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergy G ⟨J', h, β⟩) J := by
  unfold freeEnergy
  refine analyticAt_const.mul ?_
  exact (partitionFunction_analyticAt_J_general_h G β h J).log
    (partitionFunction_pos G _)

/-- **Free energy `AnalyticOnNhd ℝ` in `J` at general `h`** (§18.6
extension): global form of `freeEnergy_analyticAt_J_general_h`. -/
theorem freeEnergy_analyticOnNhd_J_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β h : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => freeEnergy G ⟨J', h, β⟩) Set.univ :=
  fun J _ => freeEnergy_analyticAt_J_general_h G β h J

/-- **Free energy `AnalyticOnNhd ℝ` in `β` at general `h`** (§18.6
extension): global form of `freeEnergy_analyticAt_beta_general_h`. -/
theorem freeEnergy_analyticOnNhd_beta_general_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => freeEnergy G ⟨J, h, β'⟩) Set.univ :=
  fun β _ => freeEnergy_analyticAt_beta_general_h G J h β

/-- **Partition function `AnalyticAt ℝ` in `h`** (§18.6 extension):
for any `(J, β, h)`, `Z(h) = ∑_σ exp(-β · H(σ))` is real-analytic in
`h`. The Hamiltonian is linear in `h` via
`externalFieldEnergy h σ = -h · ∑_i Spin.sign(σ_i)`. Direct proof
analogous to PRs #1528, #1529. -/
theorem partitionFunction_analyticAt_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => partitionFunction G ⟨J, h', β⟩) h := by
  have h_eq : (fun h' : ℝ => partitionFunction G ⟨J, h', β⟩) =
      fun h' : ℝ => ∑ σ : Config ι,
        Real.exp ((β * (∑ i : ι, Spin.sign ℝ (σ i))) * h' +
          (-β * interactionEnergy G J σ)) := by
    funext h'
    unfold partitionFunction boltzmannWeight hamiltonian externalFieldEnergy
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    ring_nf
  rw [h_eq]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_rexp.comp ?_
  exact (analyticAt_const.mul analyticAt_id).add analyticAt_const

/-- **Free energy `AnalyticAt ℝ` in `h`** (§18.6 extension):
`f = (1/|ι|) · log Z` is real-analytic in `h` at every point, for
any `J, β`. -/
theorem freeEnergy_analyticAt_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => freeEnergy G ⟨J, h', β⟩) h := by
  unfold freeEnergy
  refine analyticAt_const.mul ?_
  exact (partitionFunction_analyticAt_h G J β h).log
    (partitionFunction_pos G _)

/-- **Free energy `AnalyticOnNhd ℝ` in `h`** (§18.6 extension): global
form of `freeEnergy_analyticAt_h`. -/
theorem freeEnergy_analyticOnNhd_h
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) :
    AnalyticOnNhd ℝ (fun h' : ℝ => freeEnergy G ⟨J, h', β⟩) Set.univ :=
  fun h _ => freeEnergy_analyticAt_h G J β h

/-- **Partition function jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
extension): for any `(β, J, h)`, `Z(β, J, h) = ∑_σ exp(-β · H(σ))` is
real-analytic JOINTLY in all three Ising parameters at every point.

Proof: each summand `exp(β·J·A_σ + β·h·B_σ)` is `exp ∘ polynomial in
(β, J, h)`, which is analytic jointly via `analyticAt_rexp` composed
with the polynomial; sum over `σ` preserves analyticity. -/
theorem partitionFunction_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩)
      (β, J, h) := by
  -- p = (β', J', h')
  have h_eq : (fun p : ℝ × ℝ × ℝ =>
      partitionFunction G ⟨p.2.1, p.2.2, p.1⟩) =
      fun p : ℝ × ℝ × ℝ => ∑ σ : Config ι,
        Real.exp (p.1 * p.2.1 * (∑ e ∈ G.edgeFinset, edgeSpin σ e) +
          p.1 * p.2.2 * (∑ i : ι, Spin.sign ℝ (σ i))) := by
    funext p
    unfold partitionFunction boltzmannWeight hamiltonian
      interactionEnergy externalFieldEnergy
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    ring
  rw [h_eq]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_rexp.comp ?_
  -- Linear combination of polynomials in (β, J, h).
  have h_β : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) (β, J, h) := analyticAt_fst
  have h_snd : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2) (β, J, h) := analyticAt_snd
  have h_J : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) (β, J, h) :=
    analyticAt_fst.comp h_snd
  have h_h : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) (β, J, h) :=
    analyticAt_snd.comp h_snd
  exact ((h_β.mul h_J).mul analyticAt_const).add ((h_β.mul h_h).mul analyticAt_const)

/-- **Free energy jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
capstone, jointly): `f = (1/|ι|) · log Z` is real-analytic jointly
in all three Ising parameters at every point. -/
theorem freeEnergy_analyticAt_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergy G ⟨p.2.1, p.2.2, p.1⟩)
      (β, J, h) := by
  have h_pos : 0 < partitionFunction G ⟨J, h, β⟩ := partitionFunction_pos G _
  set f : ℝ × ℝ × ℝ → ℝ :=
    fun p => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩ with hf_def
  have h_inner : AnalyticAt ℝ f (β, J, h) :=
    partitionFunction_analyticAt_joint G β J h
  have h_f_val : f (β, J, h) = partitionFunction G ⟨J, h, β⟩ := rfl
  have h_outer : AnalyticAt ℝ Real.log (f (β, J, h)) := by
    rw [h_f_val]; exact analyticAt_log h_pos
  have h_log :
      AnalyticAt ℝ
        (fun p : ℝ × ℝ × ℝ => Real.log (f p))
        (β, J, h) := h_outer.comp h_inner
  unfold freeEnergy
  exact analyticAt_const.mul h_log

/-- **Partition function jointly `AnalyticOnNhd ℝ` over `Set.univ`**
(§18.6 extension): global form of `partitionFunction_analyticAt_joint`. -/
theorem partitionFunction_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => partitionFunction_analyticAt_joint G β J h

/-- **Free energy jointly `AnalyticOnNhd ℝ` over `Set.univ`** (§18.6
capstone, jointly): global form of `freeEnergy_analyticAt_joint`. -/
theorem freeEnergy_analyticOnNhd_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergy G ⟨p.2.1, p.2.2, p.1⟩)
      Set.univ :=
  fun ⟨β, J, h⟩ _ => freeEnergy_analyticAt_joint G β J h

/-- **Partition function jointly `Continuous` in `(β, J, h)`** (§18.6,
direct corollary of `partitionFunction_analyticAt_joint` via
`AnalyticAt → ContinuousAt`). -/
theorem partitionFunction_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩) :=
  continuous_iff_continuousAt.mpr fun ⟨β, J, h⟩ =>
    (partitionFunction_analyticAt_joint G β J h).continuousAt

/-- **Partition function jointly `Differentiable ℝ` in `(β, J, h)`**
(§18.6, direct corollary of `partitionFunction_analyticAt_joint` via
`AnalyticAt → DifferentiableAt`). -/
theorem partitionFunction_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => partitionFunction G ⟨p.2.1, p.2.2, p.1⟩) :=
  fun ⟨β, J, h⟩ => (partitionFunction_analyticAt_joint G β J h).differentiableAt

/-- **Free energy jointly `Continuous` in `(β, J, h)`** (§18.6,
direct corollary of `freeEnergy_analyticAt_joint`). -/
theorem freeEnergy_continuous_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ => freeEnergy G ⟨p.2.1, p.2.2, p.1⟩) :=
  continuous_iff_continuousAt.mpr fun ⟨β, J, h⟩ =>
    (freeEnergy_analyticAt_joint G β J h).continuousAt

/-- **Free energy jointly `Differentiable ℝ` in `(β, J, h)`** (§18.6,
direct corollary of `freeEnergy_analyticAt_joint`). -/
theorem freeEnergy_differentiable_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergy G ⟨p.2.1, p.2.2, p.1⟩) :=
  fun ⟨β, J, h⟩ => (freeEnergy_analyticAt_joint G β J h).differentiableAt

end IsingModel
