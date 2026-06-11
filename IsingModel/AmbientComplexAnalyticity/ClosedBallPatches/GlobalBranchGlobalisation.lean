import IsingModel.AmbientComplexAnalyticity.ClosedBallPatches.GlobalBranchRealAxis

/-!
# GJ Theorem 4.6.2: analyticity of the infinite-volume free energy (GJ §4.6)

The domain-wide globalisation: for positive real ferromagnetic parameters with bounded edge
density and the field-uniform disjoint-tower hypotheses, there is a single function analytic
on the whole Lee-Yang cone agreeing with the infinite-volume free energy at every positive
real field. Per target point, the real-axis-identified compact patch (over the segment from
the real anchor) is restricted to a convex open tube around the segment; any two such tubes
intersect in a convex open set containing a real interval near the anchor where both patches
equal the infinite-volume free energy, so the identity theorem for analytic functions glues
the patches into one global function.

* `freeEnergyComplex_infiniteVolume_analyticOnNhd_leeYangDomain` — **GJ Theorem 4.6.2**.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel

namespace Ambient

open Metric

variable {V : Type*} [DecidableEq V]

/-- **Convex-tube compact patch**: for every point of the Lee-Yang cone there are a convex
open tube around the segment from the real anchor `1` — containing the anchor and the point,
inside the cone — and a function holomorphic on the tube agreeing with the infinite-volume
free energy at every positive real field in the tube. -/
theorem exists_convex_tube_patch (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    (hBED : BoundedEdgeDensity G Λ)
    (hconv' : ∀ x : ℝ, 0 < x → Filter.Tendsto
      (fun n => freeEnergyAlongExhaustion G Λ ⟨J, x, β⟩ n)
      Filter.atTop (nhds (freeEnergyInfinite G Λ ⟨J, x, β⟩)))
    {z : ℂ} (hz : z ∈ IsingModel.leeYangDomain) :
    ∃ V' : Set ℂ, IsOpen V' ∧ Convex ℝ V' ∧ ((1 : ℝ) : ℂ) ∈ V' ∧ z ∈ V' ∧
      V' ⊆ IsingModel.leeYangDomain ∧
      ∃ gz : ℂ → ℂ, DifferentiableOn ℂ gz V' ∧
        ∀ x : ℝ, 0 < x → (x : ℂ) ∈ V' →
          gz (x : ℂ) = ((freeEnergyInfinite G Λ ⟨J, x, β⟩ : ℝ) : ℂ) := by
  classical
  set p : IsingParams ℝ := ⟨J, 1, β⟩ with hp
  have h1dom : ((1 : ℝ) : ℂ) ∈ IsingModel.leeYangDomain :=
    IsingModel.real_pos_mem_leeYangDomain one_pos
  -- the segment from the anchor to the target, as a parametrised image
  set S : Set ℂ :=
    (fun t : ℝ => ((1 : ℝ) : ℂ) + (t : ℂ) * (z - ((1 : ℝ) : ℂ))) '' Set.Icc 0 1 with hS
  have hScomp : IsCompact S := by
    rw [hS]
    exact isCompact_Icc.image (by fun_prop)
  have hSsub : S ⊆ IsingModel.leeYangDomain := by
    rw [hS]
    rintro w ⟨t, ht, rfl⟩
    exact IsingModel.segmentPoint_mem IsingModel.convex_leeYangDomain h1dom hz ht
  have h1S : ((1 : ℝ) : ℂ) ∈ S := by
    rw [hS]
    exact ⟨0, ⟨le_refl 0, zero_le_one⟩, by simp⟩
  have hzS : z ∈ S := by
    rw [hS]
    refine ⟨1, ⟨zero_le_one, le_refl 1⟩, ?_⟩
    push_cast
    ring
  -- the real-axis-identified compact patch over the segment
  obtain ⟨U, hUo, hSU, hUdom, σ, hσ, g, hgd, _hgconv, hgreal⟩ :=
    freeEnergyComplexAlongExhaustion_posReal_globalBranch_holomorphicExtension_realAxis_of_tendsto
      G Λ p hBED (fun x hx => hconv' x hx) hβ hJ hScomp hSsub h1S
  -- the convex open tube inside `U`
  obtain ⟨δ, hδ, hthick⟩ := hScomp.exists_thickening_subset_open hUo hSU
  have hSconv : Convex ℝ S := by
    rw [hS]
    rintro w₁ ⟨t₁, ht₁, rfl⟩ w₂ ⟨t₂, ht₂, rfl⟩ a b ha hb hab
    refine ⟨a * t₁ + b * t₂, (convex_Icc (0 : ℝ) 1) ht₁ ht₂ ha hb hab, ?_⟩
    have habC : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    linear_combination -habC
  refine ⟨thickening δ S, isOpen_thickening, ?_, ?_, ?_, ?_, g, ?_, ?_⟩
  · exact hSconv.thickening δ
  · exact self_subset_thickening hδ S h1S
  · exact self_subset_thickening hδ S hzS
  · exact hthick.trans hUdom
  · exact hgd.mono hthick
  · intro x hx hxV
    exact hgreal x hx (hthick hxV)

/-- **GJ Theorem 4.6.2 — analyticity of the infinite-volume free energy**: for positive real
ferromagnetic parameters with bounded edge density and the field-uniform disjoint-tower
hypotheses, there is a single function analytic on the whole Lee-Yang cone
`{|Im h| < Re h}` whose value at every positive real field is the infinite-volume free
energy. The convex-tube patches around the segments from the real anchor agree pairwise on
the (convex, hence preconnected) tube intersections by the identity theorem — both equal the
infinite-volume free energy on a real interval accumulating at the anchor — so they glue to
one global function. -/
theorem freeEnergyComplex_infiniteVolume_analyticOnNhd_leeYangDomain
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    (hBED : BoundedEdgeDensity G Λ)
    (hconv' : ∀ x : ℝ, 0 < x → Filter.Tendsto
      (fun n => freeEnergyAlongExhaustion G Λ ⟨J, x, β⟩ n)
      Filter.atTop (nhds (freeEnergyInfinite G Λ ⟨J, x, β⟩))) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g IsingModel.leeYangDomain ∧
      ∀ x : ℝ, 0 < x →
        g (x : ℂ) = ((freeEnergyInfinite G Λ ⟨J, x, β⟩ : ℝ) : ℂ) := by
  classical
  have h1dom : ((1 : ℝ) : ℂ) ∈ IsingModel.leeYangDomain :=
    IsingModel.real_pos_mem_leeYangDomain one_pos
  -- choose a convex-tube patch per point
  have main := fun (z : ℂ) (hz : z ∈ IsingModel.leeYangDomain) =>
    exists_convex_tube_patch G Λ hβ hJ hBED hconv' hz
  choose Vt hVopen hVconv hV1 hVz hVdom gz hgzdiff hgzreal using main
  -- pairwise agreement on tube intersections by the identity theorem
  have hagree : ∀ (z : ℂ) (hz : z ∈ IsingModel.leeYangDomain)
      (z₀ : ℂ) (hz₀ : z₀ ∈ IsingModel.leeYangDomain),
      Set.EqOn (gz z hz) (gz z₀ hz₀) (Vt z hz ∩ Vt z₀ hz₀) := by
    intro z hz z₀ hz₀
    set W : Set ℂ := Vt z hz ∩ Vt z₀ hz₀ with hW
    have hWopen : IsOpen W := (hVopen z hz).inter (hVopen z₀ hz₀)
    have hWconv : Convex ℝ W := (hVconv z hz).inter (hVconv z₀ hz₀)
    have h1W : ((1 : ℝ) : ℂ) ∈ W := ⟨hV1 z hz, hV1 z₀ hz₀⟩
    have hana₁ : AnalyticOnNhd ℂ (gz z hz) W :=
      ((hgzdiff z hz).mono Set.inter_subset_left).analyticOnNhd hWopen
    have hana₂ : AnalyticOnNhd ℂ (gz z₀ hz₀) W :=
      ((hgzdiff z₀ hz₀).mono Set.inter_subset_right).analyticOnNhd hWopen
    -- a real sequence inside `W` accumulating at the anchor where both patches agree
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hWopen _ h1W
    have hmem : ∀ n : ℕ, (((1 + ε / (n + 2) : ℝ)) : ℂ) ∈ W := by
      intro n
      refine hball ?_
      rw [Metric.mem_ball]
      have h1 : dist (((1 + ε / (n + 2) : ℝ)) : ℂ) (((1 : ℝ)) : ℂ)
          = |ε / ((n : ℝ) + 2)| := by
        rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        congr 1
        ring
      rw [h1, abs_of_pos (div_pos hε (by positivity))]
      have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      calc ε / ((n : ℝ) + 2) < ε / 1 := by
            apply div_lt_div_of_pos_left hε (by norm_num) hn2
        _ = ε := div_one ε
    have heq : ∀ n : ℕ,
        gz z hz (((1 + ε / (n + 2) : ℝ)) : ℂ)
          = gz z₀ hz₀ (((1 + ε / (n + 2) : ℝ)) : ℂ) := by
      intro n
      have hxpos : (0 : ℝ) < 1 + ε / (n + 2) := by
        have := div_pos hε (by positivity : (0 : ℝ) < (n : ℝ) + 2)
        linarith
      rw [hgzreal z hz _ hxpos ((hmem n).1), hgzreal z₀ hz₀ _ hxpos ((hmem n).2)]
    have htend : Filter.Tendsto (fun n : ℕ => (((1 + ε / (n + 2) : ℝ)) : ℂ))
        Filter.atTop (nhdsWithin (((1 : ℝ)) : ℂ) {(((1 : ℝ)) : ℂ)}ᶜ) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hr : Filter.Tendsto (fun n : ℕ => (1 + ε / (n + 2) : ℝ))
            Filter.atTop (nhds 1) := by
          have hdiv : Filter.Tendsto (fun n : ℕ => ε / (n + 2 : ℝ))
              Filter.atTop (nhds 0) := by
            apply Filter.Tendsto.div_atTop tendsto_const_nhds
            exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
          simpa using Filter.Tendsto.const_add 1 hdiv
        exact (Complex.continuous_ofReal.tendsto _).comp hr
      · refine Filter.Eventually.of_forall fun n => ?_
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hcontra
        have : (1 + ε / (n + 2) : ℝ) = 1 := by exact_mod_cast hcontra
        have hpos : (0 : ℝ) < ε / (n + 2) :=
          div_pos hε (by positivity : (0 : ℝ) < (n : ℝ) + 2)
        linarith
    have hfreq : ∃ᶠ w in nhdsWithin (((1 : ℝ)) : ℂ) {(((1 : ℝ)) : ℂ)}ᶜ,
        gz z hz w = gz z₀ hz₀ w :=
      htend.frequently (Filter.Frequently.of_forall heq)
    exact hana₁.eqOn_of_preconnected_of_frequently_eq hana₂
      hWconv.isPreconnected h1W hfreq
  -- the glued global function
  set g : ℂ → ℂ := fun w =>
    if hw : w ∈ IsingModel.leeYangDomain then gz w hw w else 0 with hg
  refine ⟨g, ?_, ?_⟩
  · -- analyticity at every point of the domain
    intro z₀ hz₀
    have hloc : Set.EqOn g (gz z₀ hz₀) (Vt z₀ hz₀) := by
      intro w hw
      have hwdom : w ∈ IsingModel.leeYangDomain := hVdom z₀ hz₀ hw
      have : g w = gz w hwdom w := by rw [hg]; simp [hwdom]
      rw [this]
      exact hagree w hwdom z₀ hz₀ ⟨hVz w hwdom, hw⟩
    have hana : AnalyticAt ℂ (gz z₀ hz₀) z₀ :=
      (((hgzdiff z₀ hz₀).analyticOnNhd (hVopen z₀ hz₀))) z₀ (hVz z₀ hz₀)
    refine hana.congr ?_
    have : Vt z₀ hz₀ ∈ nhds z₀ := (hVopen z₀ hz₀).mem_nhds (hVz z₀ hz₀)
    filter_upwards [this] with w hw
    exact (hloc hw).symm
  · -- the value at every positive real field
    intro x hx
    have hxdom : ((x : ℝ) : ℂ) ∈ IsingModel.leeYangDomain :=
      IsingModel.real_pos_mem_leeYangDomain hx
    have : g ((x : ℝ) : ℂ) = gz _ hxdom ((x : ℝ) : ℂ) := by rw [hg]; simp [hxdom]
    rw [this]
    exact hgzreal _ hxdom x hx (hVz _ hxdom)

/-- **GJ Theorem 4.6.2, disjoint-tower form**: the field-uniform real convergence input is
supplied by the disjoint-tower Fekete theorem. -/
theorem freeEnergyComplex_infiniteVolume_analyticOnNhd_leeYangDomain_of_disjointTower
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    (hBED : BoundedEdgeDensity G Λ)
    (hd' : ∀ x : ℝ, 0 < x → DisjointTowerHypotheses G Λ ⟨J, x, β⟩) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g IsingModel.leeYangDomain ∧
      ∀ x : ℝ, 0 < x →
        g (x : ℂ) = ((freeEnergyInfinite G Λ ⟨J, x, β⟩ : ℝ) : ℂ) :=
  freeEnergyComplex_infiniteVolume_analyticOnNhd_leeYangDomain G Λ hβ hJ hBED
    fun x hx => freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses G Λ _ hBED
      (hd' x hx)

end Ambient

end IsingModel
