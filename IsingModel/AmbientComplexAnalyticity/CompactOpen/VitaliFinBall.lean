import IsingModel.AmbientComplexAnalyticity.CompactOpen.VitaliBall

/-!
# Ambient compact-open extraction split — compact-open Vitali fin-ball and overlap bridges

Part of the split ambient compact-open layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Finite-ball compact-open diagonal extraction plus subsequence Vitali
bridge**: for finitely many Lee-Yang balls indexed by `Fin n`, compact-open
compactness of each restricted branch family yields one common strictly
increasing subsequence, locally uniform convergence on every ball, and a
holomorphic limit on every ball. This is the finite local-cover diagonal
handoff; it does not assert overlap compatibility of the local limits. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β m)
        ∧ F i m (h0 i) = freeEnergyComplexAlongExhaustion G Λ J (h0 i) β m) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i, ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball (h0 i) (r i), ℂ),
          fc ∈ A i ∧
            ∀ z (hz : z ∈ Metric.ball (h0 i) (r i)), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F i (σ m) z) f Filter.atTop (Metric.ball (h0 i) (r i)) ∧
        DifferentiableOn ℂ f (Metric.ball (h0 i) (r i)) := by
  letI : ∀ i : Fin n, LocallyCompactSpace (Metric.ball (h0 i) (r i)) :=
    fun _ => Metric.isOpen_ball.locallyCompactSpace
  letI : ∀ i : Fin n, FirstCountableTopology C(Metric.ball (h0 i) (r i), ℂ) :=
    fun _ => inferInstance
  rcases IsingModel.exists_subseq_fin_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
      n (s := fun i : Fin n => Metric.ball (h0 i) (r i))
      (hs := fun _ => Metric.isOpen_ball)
      (A := A) (hA := hA) (Fc := Fc) (hFc_mem := hFc_mem)
      (F := F) (hF := hFres) with
    ⟨σ, hσ, hlim⟩
  refine ⟨σ, hσ, ?_⟩
  intro i
  rcases hlim i with ⟨fc, f, hfcA, hf_agree, hconv⟩
  haveI : LocallyCompactSpace (Metric.ball (h0 i) (r i)) :=
    Metric.isOpen_ball.locallyCompactSpace
  have hbranch_sub : ∀ m,
      AnalyticOnNhd ℂ ((fun m z => F i (σ m) z) m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) *
                (fun m z => F i (σ m) z) m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
        ∧ (fun m z => F i (σ m) z) m (h0 i)
            = freeEnergyComplexAlongExhaustion G Λ J (h0 i) β (σ m) := by
    intro m
    simpa using hbranch i (σ m)
  have hdiff :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ J β (σ := σ) hbranch_sub hconv
  exact ⟨f, ⟨fc, hfcA, hf_agree⟩, hconv, hdiff⟩

/-- **Finite-ball compact-open diagonal extraction with overlap compatibility**:
under the same compact-open hypotheses as
`freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball`, if
the chosen stage branches are eventually equal on every pairwise overlap, then
the extracted holomorphic local limits are pairwise equal on those overlaps.

The overlap assumption is explicit: this theorem packages compatibility once a
coherent branch choice has supplied it; it does not construct that coherent
choice. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_overlap
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β m)
        ∧ F i m (h0 i) = freeEnergyComplexAlongExhaustion G Λ J (h0 i) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : Fin n → ℂ → ℂ,
        (∀ i,
          (∃ fc : C(Metric.ball (h0 i) (r i), ℂ),
            fc ∈ A i ∧
              ∀ z (hz : z ∈ Metric.ball (h0 i) (r i)), f i z = fc ⟨z, hz⟩) ∧
          TendstoLocallyUniformlyOn
            (fun m z => F i (σ m) z) (f i) Filter.atTop
              (Metric.ball (h0 i) (r i)) ∧
          DifferentiableOn ℂ (f i) (Metric.ball (h0 i) (r i))) ∧
        ∀ i j, Set.EqOn (f i) (f j)
          (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j)) := by
  classical
  rcases freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball
      G Λ J β n hA hFc_mem hFres hbranch with
    ⟨σ, hσ, hlim⟩
  choose f hf using hlim
  refine ⟨σ, hσ, f, hf, ?_⟩
  refine IsingModel.pairwise_eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn
    n (s := fun i : Fin n => Metric.ball (h0 i) (r i))
    (F := fun i m z => F i (σ m) z) (f := f) ?_ ?_
  · intro i
    exact (hf i).2.1
  · intro i j
    exact hσ.tendsto_atTop.eventually (hoverlap i j)


end Ambient
end IsingModel
