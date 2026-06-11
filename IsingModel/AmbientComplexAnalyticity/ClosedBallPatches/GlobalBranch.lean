import IsingModel.ComplexAnalyticity.SegmentPrimitive
import IsingModel.AmbientComplexAnalyticity.ClosedBallPatches.UniformBoundOverlap

/-!
# The global stage branch on the convex Lee-Yang cone (GJ §4.6 Thm 4.6.2)

The eventual-overlap input of the overlap-only endpoint (PR #3902) is discharged by a *global*
branch: the Lee-Yang domain `{|Im h| < Re h}` is a convex cone, so each per-stage normalised
logarithmic derivative `Z'/(N·Z)` (holomorphic and denominator-free there by the Lee-Yang
theorem) has a segment primitive from any base point. Anchored at the principal free-energy
value of the base point, the primitive is a per-stage holomorphic logarithm
(`exp(N·g) = Z`, by the zero-derivative ratio argument on the convex domain) defined on the
*whole* domain. Using this single function as the selected branch at every Lee-Yang centre
makes the eventual-overlap predicate trivially true.

* `globalLogDerivStage` — the normalised logarithmic derivative `Z'/(N·Z)` per stage.
* `analyticOnNhd_globalLogDerivStage` — its holomorphy on the Lee-Yang domain.
* `globalBranchStage` — the anchored segment primitive.
* `globalBranchStage_base` — base normalisation `g(b) = F(b)`.
* `hasDerivAt_globalBranchStage` / `analyticOnNhd_globalBranchStage` — holomorphy.
* `exp_card_mul_globalBranchStage` — the exponential identity `exp(N·g) = Z` on the domain.
* `exists_globalLeeYangAllStageBranchData` — all-stage branch data with the global branch at
  every centre, satisfying `OverlapEventually`.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel

namespace Ambient

open Metric

variable {V : Type*} [DecidableEq V]

/-- **Normalised per-stage logarithmic derivative**: `Z'/(N·Z)` in the complex field variable,
where `N` is the stage volume cardinality. This is the derivative of any per-stage logarithm
branch and is holomorphic on the whole Lee-Yang domain. -/
noncomputable def globalLogDerivStage (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun h =>
    ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ))⁻¹ *
      (deriv (fun h' => partitionFunctionComplexAlongExhaustion G Λ J h' β n) h
        / partitionFunctionComplexAlongExhaustion G Λ J h β n)

/-- **Holomorphy of the normalised logarithmic derivative** on the Lee-Yang domain
(ferromagnetic positive real parameters): the Lee-Yang theorem clears the denominator. -/
theorem analyticOnNhd_globalLogDerivStage (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ) :
    AnalyticOnNhd ℂ (globalLogDerivStage G Λ (J : ℂ) (β : ℂ) n)
      IsingModel.leeYangDomain :=
  analyticOnNhd_const.mul
    (IsingModel.logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain
      (inducedGraph G (Λ.volume n)) hβ hJ)

/-- **Global stage branch**: the segment primitive of the normalised logarithmic derivative
from a Lee-Yang base point, anchored at the principal free-energy value of the base point.
A single function of the field variable, defined on the whole Lee-Yang domain — the selected
branch at *every* centre. -/
noncomputable def globalBranchStage (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (b : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun z =>
    freeEnergyComplexAlongExhaustion G Λ J b β n +
      segmentPrimitive (globalLogDerivStage G Λ J β n) b z

/-- **Base normalisation of the global branch**: at the base point the segment integral
vanishes, leaving the principal free-energy value. -/
theorem globalBranchStage_base (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (b : ℂ) (n : ℕ) :
    globalBranchStage G Λ J β b n b
      = freeEnergyComplexAlongExhaustion G Λ J b β n := by
  rw [globalBranchStage, segmentPrimitive_base, add_zero]

/-- **Derivative of the global branch**: differentiating the segment primitive on the convex
open Lee-Yang domain recovers the normalised logarithmic derivative. -/
theorem hasDerivAt_globalBranchStage (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    {b z : ℂ} (hb : b ∈ IsingModel.leeYangDomain) (hz : z ∈ IsingModel.leeYangDomain) :
    HasDerivAt (globalBranchStage G Λ (J : ℂ) (β : ℂ) b n)
      (globalLogDerivStage G Λ (J : ℂ) (β : ℂ) n z) z := by
  have hana := analyticOnNhd_globalLogDerivStage G Λ hβ hJ (n := n)
  have hf : ∀ w ∈ IsingModel.leeYangDomain,
      HasDerivAt (globalLogDerivStage G Λ (J : ℂ) (β : ℂ) n)
        (deriv (globalLogDerivStage G Λ (J : ℂ) (β : ℂ) n) w) w :=
    fun w hw => (hana w hw).differentiableAt.hasDerivAt
  have hf'c : ContinuousOn (deriv (globalLogDerivStage G Λ (J : ℂ) (β : ℂ) n))
      IsingModel.leeYangDomain :=
    hana.deriv.continuousOn
  exact (hasDerivAt_segmentPrimitive IsingModel.convex_leeYangDomain
    IsingModel.isOpen_leeYangDomain hf hf'c hb hz).const_add
    (freeEnergyComplexAlongExhaustion G Λ (J : ℂ) b (β : ℂ) n)

/-- **Holomorphy of the global branch** on the Lee-Yang domain. -/
theorem analyticOnNhd_globalBranchStage (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    {b : ℂ} (hb : b ∈ IsingModel.leeYangDomain) :
    AnalyticOnNhd ℂ (globalBranchStage G Λ (J : ℂ) (β : ℂ) b n)
      IsingModel.leeYangDomain := by
  refine DifferentiableOn.analyticOnNhd ?_ IsingModel.isOpen_leeYangDomain
  exact fun z hz =>
    (hasDerivAt_globalBranchStage G Λ hβ hJ n hb hz).differentiableAt.differentiableWithinAt

/-- **Exponential identity for the global branch**: `exp(N·g) = Z` on the Lee-Yang domain.
The ratio `exp(N·g)/Z` has vanishing derivative on the convex domain, hence is constant, and
equals `1` at the base point by the principal-logarithm identity. -/
theorem exp_card_mul_globalBranchStage (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ)
    {b z : ℂ} (hb : b ∈ IsingModel.leeYangDomain) (hz : z ∈ IsingModel.leeYangDomain) :
    Complex.exp
        ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) *
          globalBranchStage G Λ (J : ℂ) (β : ℂ) b n z)
      = partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) z (β : ℂ) n := by
  classical
  set N : ℂ := (Fintype.card (↑(Λ.volume n) : Type _) : ℂ) with hN
  set Z : ℂ → ℂ := fun h => partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n
    with hZ
  set g : ℂ → ℂ := globalBranchStage G Λ (J : ℂ) (β : ℂ) b n with hg
  have hNne' : ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hNne : N ≠ 0 := by rw [hN]; exact hNne'
  have hZne : ∀ w ∈ IsingModel.leeYangDomain, Z w ≠ 0 := fun w hw =>
    partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage G Λ hβ hJ n hw
  have hZdiff : ∀ w : ℂ, HasDerivAt Z (deriv Z w) w := fun w =>
    ((IsingModel.partitionFunctionComplex_analyticAt_h
      (inducedGraph G (Λ.volume n)) (J : ℂ) (β : ℂ) w).differentiableAt).hasDerivAt
  -- the ratio has vanishing derivative on the domain
  set D : ℂ → ℂ := fun w => Complex.exp (N * g w) * (Z w)⁻¹ with hD
  have hDderiv : ∀ w ∈ IsingModel.leeYangDomain, HasDerivAt D 0 w := by
    intro w hw
    have hgw := hasDerivAt_globalBranchStage G Λ hβ hJ n hb hw
    have hexp : HasDerivAt (fun w' => Complex.exp (N * g w'))
        (Complex.exp (N * g w) * (N * globalLogDerivStage G Λ (J : ℂ) (β : ℂ) n w)) w :=
      (hgw.const_mul N).cexp
    have hinv : HasDerivAt (fun w' => (Z w')⁻¹)
        (-(deriv Z w) / (Z w) ^ 2) w := (hZdiff w).inv (hZne w hw)
    have hmul := hexp.mul hinv
    have hZw := hZne w hw
    have hkey : N * globalLogDerivStage G Λ (J : ℂ) (β : ℂ) n w = deriv Z w / Z w := by
      rw [globalLogDerivStage, hN, hZ]
      field_simp
    rw [hD]
    convert hmul using 1
    rw [hkey]
    field_simp
    ring
  -- constancy on the convex domain
  have hconst : D z = D b := by
    refine IsingModel.convex_leeYangDomain.is_const_of_fderivWithin_eq_zero
      (fun w hw => (hDderiv w hw).differentiableAt.differentiableWithinAt) ?_ hz hb
    intro w hw
    rw [fderivWithin_of_isOpen IsingModel.isOpen_leeYangDomain hw,
      (hDderiv w hw).hasFDerivAt.fderiv]
    simp
  -- the base value is `1` by the principal-logarithm identity
  have hbase : D b = 1 := by
    rw [hD]
    simp only
    rw [hg, globalBranchStage_base]
    have hNF : N * freeEnergyComplexAlongExhaustion G Λ (J : ℂ) b (β : ℂ) n
        = Complex.log (Z b) := by
      rw [freeEnergyComplexAlongExhaustion]
      simp only [freeEnergyComplex]
      rw [hN, hZ]
      field_simp
      rfl
    rw [hNF, Complex.exp_log (hZne b hb)]
    field_simp [hZne b hb]
  have hfinal : Complex.exp (N * g z) * (Z z)⁻¹ = 1 := by
    have : D z = 1 := hconst.trans hbase
    rwa [hD] at this
  exact (mul_inv_eq_one₀ (hZne z hz)).mp hfinal

/-- **All-stage branch data from the global branch**: choosing the global branch at every
Lee-Yang centre (with any inscribed-ball radii) produces all-stage branch data whose
eventual-overlap predicate holds trivially — the selected branches at distinct centres are
the *same* function. -/
theorem exists_globalLeeYangAllStageBranchData (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    (b : {h : ℂ // h ∈ IsingModel.leeYangDomain}) :
    ∃ data : LeeYangAllStageBranchData G Λ (J : ℂ) (β : ℂ),
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
        data.branchFamily h₀ n = globalBranchStage G Λ (J : ℂ) (β : ℂ) (b : ℂ) n) ∧
      data.OverlapEventually := by
  classical
  choose r hr hball using fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
    Metric.isOpen_iff.mp IsingModel.isOpen_leeYangDomain (h₀ : ℂ) h₀.2
  refine ⟨{ radius := r
            radius_pos := hr
            ball_subset := hball
            branchFamily := fun _ => globalBranchStage G Λ (J : ℂ) (β : ℂ) (b : ℂ)
            branch_spec := fun h₀ n => ⟨?_, ?_⟩ }, fun _ _ => rfl, ?_⟩
  · exact (analyticOnNhd_globalBranchStage G Λ hβ hJ n b.2).mono (hball h₀)
  · exact fun z hz => exp_card_mul_globalBranchStage G Λ hβ hJ n b.2 (hball h₀ hz)
  · intro h₀ h₁
    exact Filter.Eventually.of_forall fun _ => Set.eqOn_refl _ _

end Ambient

end IsingModel
