import IsingModel.AmbientComplexAnalyticity.Vitali

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Compact-open extraction handoff on Lee-Yang balls

The previous subsequence handoffs start after a locally uniformly convergent
subsequence of branch witnesses has already been selected. The next wrappers
package the standard topological extraction step available once the local
branch witnesses are known to lie in a compact subset of the compact-open
function space on a ball. This still does not prove Montel compactness of the
branch family; compactness is an explicit hypothesis. -/

/-- **Compact-open extraction plus subsequence Vitali bridge on a ball**:
if a local branch family on a ball is represented by continuous maps whose
range lies in a compact subset of `C(ball, ℂ)`, then a subsequence converges
locally uniformly on the ball and its limit is holomorphic there. This is the
post-Montel compactness-to-Vitali handoff. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_bridge_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {F : ℕ → ℂ → ℂ}
    {A : Set C(Metric.ball h₀ r, ℂ)}
    {Fc : ℕ → C(Metric.ball h₀ r, ℂ)}
    (hA : IsCompact A)
    (hFc_mem : ∀ n, Fc n ∈ A)
    (hFres : ∀ n z (hz : z ∈ Metric.ball h₀ r),
      F n z = Fc n ⟨z, hz⟩)
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β n)
        ∧ F n h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball h₀ r, ℂ),
          fc ∈ A ∧ ∀ z (hz : z ∈ Metric.ball h₀ r), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F (σ m) z) f Filter.atTop (Metric.ball h₀ r) ∧
        DifferentiableOn ℂ f (Metric.ball h₀ r) := by
  haveI : LocallyCompactSpace (Metric.ball h₀ r) :=
    Metric.isOpen_ball.locallyCompactSpace
  rcases IsingModel.exists_subseq_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
      Metric.isOpen_ball hA hFc_mem hFres with
    ⟨σ, hσ, fc, f, hfcA, hf_agree, hconv⟩
  have hbranch_sub : ∀ m,
      AnalyticOnNhd ℂ ((fun m z => F (σ m) z) m) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) *
                (fun m z => F (σ m) z) m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
        ∧ (fun m z => F (σ m) z) m h₀
            = freeEnergyComplexAlongExhaustion G Λ J h₀ β (σ m) := by
    intro m
    simpa using hbranch (σ m)
  have hdiff :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ J β (σ := σ) hbranch_sub hconv
  exact ⟨σ, hσ, f, ⟨fc, hfcA, hf_agree⟩, hconv, hdiff⟩

/-- **Compact-open extraction plus subsequence Vitali bridge with centre
identification**: for a ball centred at a real Lee-Yang parameter, compactness
of the branch family in the compact-open topology yields a locally uniformly
convergent subsequence; the PR #2693 subsequence handoff makes the limit
holomorphic and identifies its centre value with `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_ball_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {r : ℝ} (hr : 0 < r)
    {F : ℕ → ℂ → ℂ}
    {A : Set C(Metric.ball (p.h : ℂ) r, ℂ)}
    {Fc : ℕ → C(Metric.ball (p.h : ℂ) r, ℂ)}
    (hA : IsCompact A)
    (hFc_mem : ∀ n, Fc n ∈ A)
    (hFres : ∀ n z (hz : z ∈ Metric.ball (p.h : ℂ) r),
      F n z = Fc n ⟨z, hz⟩)
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) n)
        ∧ F n (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball (p.h : ℂ) r, ℂ),
          fc ∈ A ∧
            ∀ z (hz : z ∈ Metric.ball (p.h : ℂ) r), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F (σ m) z) f Filter.atTop (Metric.ball (p.h : ℂ) r) ∧
        DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
        f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  haveI : LocallyCompactSpace (Metric.ball (p.h : ℂ) r) :=
    Metric.isOpen_ball.locallyCompactSpace
  rcases IsingModel.exists_subseq_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
      Metric.isOpen_ball hA hFc_mem hFres with
    ⟨σ, hσ, fc, f, hfcA, hf_agree, hconv⟩
  have hbranch_sub : ∀ m,
      AnalyticOnNhd ℂ ((fun m z => F (σ m) z) m)
          (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) *
                (fun m z => F (σ m) z) m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) (σ m))
        ∧ (fun m z => F (σ m) z) m (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m) := by
    intro m
    simpa using hbranch (σ m)
  have hcenter :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
      G Λ p hBED hd hr hσ hbranch_sub hconv
  exact ⟨σ, hσ, f, ⟨fc, hfcA, hf_agree⟩, hconv, hcenter.1, hcenter.2⟩

/-- **Two-ball compact-open diagonal extraction plus subsequence Vitali
bridge**: if branch families on two Lee-Yang balls are represented by
continuous maps whose ranges lie in compact subsets of the corresponding
compact-open function spaces, then a single strictly increasing subsequence can
be chosen so that both branch families converge locally uniformly on their
balls and both limits are holomorphic there. This is the two-ball base case for
finite local-cover diagonal extraction; it does not assert overlap
compatibility of the two limits. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_two_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {h01 h02 : ℂ} {r1 r2 : ℝ}
    {F1 F2 : ℕ → ℂ → ℂ}
    {A1 : Set C(Metric.ball h01 r1, ℂ)}
    {A2 : Set C(Metric.ball h02 r2, ℂ)}
    {Fc1 : ℕ → C(Metric.ball h01 r1, ℂ)}
    {Fc2 : ℕ → C(Metric.ball h02 r2, ℂ)}
    (hA1 : IsCompact A1) (hA2 : IsCompact A2)
    (hFc1_mem : ∀ n, Fc1 n ∈ A1)
    (hFc2_mem : ∀ n, Fc2 n ∈ A2)
    (hFres1 : ∀ n z (hz : z ∈ Metric.ball h01 r1),
      F1 n z = Fc1 n ⟨z, hz⟩)
    (hFres2 : ∀ n z (hz : z ∈ Metric.ball h02 r2),
      F2 n z = Fc2 n ⟨z, hz⟩)
    (hbranch1 : ∀ n,
      AnalyticOnNhd ℂ (F1 n) (Metric.ball h01 r1)
        ∧ (∀ z ∈ Metric.ball h01 r1,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F1 n z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β n)
        ∧ F1 n h01 = freeEnergyComplexAlongExhaustion G Λ J h01 β n)
    (hbranch2 : ∀ n,
      AnalyticOnNhd ℂ (F2 n) (Metric.ball h02 r2)
        ∧ (∀ z ∈ Metric.ball h02 r2,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F2 n z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β n)
        ∧ F2 n h02 = freeEnergyComplexAlongExhaustion G Λ J h02 β n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∃ f1 : ℂ → ℂ,
        (∃ fc1 : C(Metric.ball h01 r1, ℂ),
          fc1 ∈ A1 ∧ ∀ z (hz : z ∈ Metric.ball h01 r1), f1 z = fc1 ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F1 (σ m) z) f1 Filter.atTop (Metric.ball h01 r1) ∧
        DifferentiableOn ℂ f1 (Metric.ball h01 r1)) ∧
      (∃ f2 : ℂ → ℂ,
        (∃ fc2 : C(Metric.ball h02 r2, ℂ),
          fc2 ∈ A2 ∧ ∀ z (hz : z ∈ Metric.ball h02 r2), f2 z = fc2 ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F2 (σ m) z) f2 Filter.atTop (Metric.ball h02 r2) ∧
        DifferentiableOn ℂ f2 (Metric.ball h02 r2)) := by
  haveI : LocallyCompactSpace (Metric.ball h01 r1) :=
    Metric.isOpen_ball.locallyCompactSpace
  haveI : LocallyCompactSpace (Metric.ball h02 r2) :=
    Metric.isOpen_ball.locallyCompactSpace
  rcases IsingModel.exists_subseq_two_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
      Metric.isOpen_ball Metric.isOpen_ball hA1 hA2 hFc1_mem hFc2_mem
      hFres1 hFres2 with
    ⟨σ, hσ, hlim1, hlim2⟩
  rcases hlim1 with ⟨fc1, f1, hfc1A, hf1_agree, hconv1⟩
  rcases hlim2 with ⟨fc2, f2, hfc2A, hf2_agree, hconv2⟩
  have hbranch1_sub : ∀ m,
      AnalyticOnNhd ℂ ((fun m z => F1 (σ m) z) m) (Metric.ball h01 r1)
        ∧ (∀ z ∈ Metric.ball h01 r1,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) *
                (fun m z => F1 (σ m) z) m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
        ∧ (fun m z => F1 (σ m) z) m h01
            = freeEnergyComplexAlongExhaustion G Λ J h01 β (σ m) := by
    intro m
    simpa using hbranch1 (σ m)
  have hbranch2_sub : ∀ m,
      AnalyticOnNhd ℂ ((fun m z => F2 (σ m) z) m) (Metric.ball h02 r2)
        ∧ (∀ z ∈ Metric.ball h02 r2,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) *
                (fun m z => F2 (σ m) z) m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
        ∧ (fun m z => F2 (σ m) z) m h02
            = freeEnergyComplexAlongExhaustion G Λ J h02 β (σ m) := by
    intro m
    simpa using hbranch2 (σ m)
  have hdiff1 :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ J β (σ := σ) hbranch1_sub hconv1
  have hdiff2 :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ J β (σ := σ) hbranch2_sub hconv2
  exact ⟨σ, hσ,
    ⟨f1, ⟨fc1, hfc1A, hf1_agree⟩, hconv1, hdiff1⟩,
    ⟨f2, ⟨fc2, hfc2A, hf2_agree⟩, hconv2, hdiff2⟩⟩

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

/-- **Packaged finite compact-open subsequence branch-limit family**: compact
open compactness on finitely many balls, plus eventual stage-level overlap
equality, produces a structured finite subsequence branch-limit family. This
packages the output of
`freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_overlap`
for later coherent local-cover extraction steps. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen
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
    Nonempty (LeeYangFiniteSubseqBranchLimitFamily G Λ J β n h0 r) := by
  rcases freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_overlap
      G Λ J β n hA hFc_mem hFres hbranch hoverlap with
    ⟨σ, hσ, f, hlocal, hcompat⟩
  exact ⟨{
    stage := σ
    stage_strict := hσ
    branchFamily := fun i m z => F i (σ m) z
    limitFun := f
    branch_spec := by
      intro i m
      rcases hbranch i (σ m) with ⟨han, hexp, _hcenter⟩
      exact ⟨han, hexp⟩
    centre_normalized := by
      intro i m
      exact (hbranch i (σ m)).2.2
    tendsto := by
      intro i
      exact (hlocal i).2.1
    differentiable := by
      intro i
      exact (hlocal i).2.2
    compatible := hcompat }⟩

/-- **Pointwise-normalised all-stage data to finite compact-open subsequence
package**: restrict pre-Montel all-stage branch choices to finitely many
Lee-Yang centres. Under compact-open compactness for the restricted branch
families and explicit eventual overlap equality, the existing finite
compact-open diagonal handoff produces a packaged finite subsequence
branch-limit family. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : LeeYangPointwiseNormalisedAllStageBranchData G Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    Nonempty (LeeYangFiniteSubseqBranchLimitFamily G Λ J β n
      (fun i => (center i : ℂ))
      (fun i => data.branchData.radius (center i))) := by
  exact freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen
    G Λ J β n
    (h0 := fun i => (center i : ℂ))
    (r := fun i => data.branchData.radius (center i))
    (F := fun i m z => data.branchData.branchFamily (center i) m z)
    hA hFc_mem hFres
    (by
      intro i m
      exact ⟨(data.branchData.branch_spec (center i) m).1,
        (data.branchData.branch_spec (center i) m).2,
        data.centre_normalized (center i) m⟩)
    hoverlap

/-- **Packaged finite subsequence branch-limit patching**: a compatible
`LeeYangFiniteSubseqBranchLimitFamily` patches to one function differentiable
on the finite union of its balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    (family : LeeYangFiniteSubseqBranchLimitFamily G Λ J β n h0 r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
      DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) := by
  rcases IsingModel.exists_differentiableOn_iUnion_of_finite_eqOn
      n (s := fun i : Fin n => Metric.ball (h0 i) (r i))
      (f := family.limitFun)
      (hs := fun _ => Metric.isOpen_ball)
      (hdiff := family.differentiable)
      (hcompat := family.compatible) with
    ⟨g, hg_eq, hg_diff⟩
  exact ⟨g, hg_eq, hg_diff⟩

/-- **Packaged finite subsequence branch-limit patching with real-centre
identification**: if one finite-cover ball is centred at the real field
`p.h`, then a compatible `LeeYangFiniteSubseqBranchLimitFamily` patches on the
finite union of balls and the patched value at that real centre agrees with
`↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    (family : LeeYangFiniteSubseqBranchLimitFamily G Λ (p.J : ℂ) (p.β : ℂ) n h0 r)
    (i₀ : Fin n)
    (hcenter : h0 i₀ = (p.h : ℂ))
    (hr : 0 < r i₀) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
      DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) ∧
      g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch
      G Λ (p.J : ℂ) (p.β : ℂ) n family with
    ⟨g, hg_eq, hg_diff⟩
  have hbranch : ∀ m,
      AnalyticOnNhd ℂ (family.branchFamily i₀ m)
          (Metric.ball (p.h : ℂ) (r i₀))
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) (r i₀),
            Complex.exp
              ((Fintype.card (↑(Λ.volume (family.stage m)) : Type _) : ℂ) *
                family.branchFamily i₀ m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) (family.stage m))
        ∧ family.branchFamily i₀ m (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (family.stage m) := by
    intro m
    rcases family.branch_spec i₀ m with ⟨han, hexp⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [hcenter] using han
    · intro z hz
      exact hexp z (by simpa [hcenter] using hz)
    · simpa [hcenter] using family.centre_normalized i₀ m
  have hconv :
      TendstoLocallyUniformlyOn (family.branchFamily i₀) (family.limitFun i₀)
        Filter.atTop (Metric.ball (p.h : ℂ) (r i₀)) := by
    simpa [hcenter] using family.tendsto i₀
  have hidentified :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
      G Λ p hBED hd hr family.stage_strict hbranch hconv
  have hcenter_mem :
      (p.h : ℂ) ∈ Metric.ball (h0 i₀) (r i₀) := by
    have hself : (p.h : ℂ) ∈ Metric.ball (p.h : ℂ) (r i₀) :=
      Metric.mem_ball_self hr
    simpa [hcenter] using hself
  have hg_center : g (p.h : ℂ) = family.limitFun i₀ (p.h : ℂ) :=
    hg_eq i₀ hcenter_mem
  exact ⟨g, hg_eq, hg_diff, hg_center.trans hidentified.2⟩

/-- **Finite Lee-Yang cover branch-limit patching**: a compatible finite
Lee-Yang cover package patches to one differentiable function on the finite
union of its Lee-Yang balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (cover : LeeYangFiniteCoverBranchLimitFamily G Λ J β n center r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g
        (⋃ i : Fin n,
          Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) :=
  freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch
    G Λ J β n cover.family

/-- **Finite Lee-Yang cover branch-limit patching with real-centre
identification**: if one Lee-Yang cover ball is centred at the real field
`p.h`, the finite-cover patch agrees there with `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (cover : LeeYangFiniteCoverBranchLimitFamily
      G Λ (p.J : ℂ) (p.β : ℂ) n center r)
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g
        (⋃ i : Fin n,
          Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
      g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_real
    G Λ p hBED hd n cover.family i₀ hcenter (cover.radius_pos i₀)

/-- **Finite real-centred Lee-Yang cover branch-limit patching**: a finite
Lee-Yang cover package with a bundled real-centre index patches to one
differentiable function on the finite union, with value
`↑freeEnergyInfinite` at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (realCover : LeeYangFiniteRealCoverBranchLimitFamily G Λ p n center r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (realCover.cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g
        (⋃ i : Fin n,
          Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
      g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch_real
    G Λ p hBED hd n realCover.cover realCover.realIndex realCover.real_center

/-- **Compact finite real-centred Lee-Yang cover patching**: a compact target
set covered by a finite real-centred Lee-Yang cover inherits the finite-cover
patch, restricted to differentiability on the compact target, while preserving
the real-centre identification. -/
theorem freeEnergyComplexAlongExhaustion_compactFiniteRealCover_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (K : Set ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (compactCover :
      LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K n center r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g K ∧
      g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_patch
      G Λ p hBED hd n compactCover.realCover with
    ⟨g, hg_eq, hg_diff, hg_real⟩
  exact ⟨g, hg_eq, hg_diff.mono compactCover.cover_subset, hg_real⟩

/-- **Finite compact-open extraction to a patched finite family**:
compact-open compactness on finitely many balls and eventual stage-level
overlap equality produce both a packaged finite subsequence branch-limit family
and a patched function on the finite union of balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen_patch
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
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β m)
        ∧ F i m (h0 i) = freeEnergyComplexAlongExhaustion G Λ J (h0 i) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    ∃ family : LeeYangFiniteSubseqBranchLimitFamily G Λ J β n h0 r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
        DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) := by
  rcases freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen
      G Λ J β n hA hFc_mem hFres hbranch hoverlap with
    ⟨family⟩
  exact ⟨family,
    freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch
      G Λ J β n family⟩

/-- **Pointwise-normalised all-stage data to finite compact-open patch**:
restrict pre-Montel all-stage branch choices to finitely many Lee-Yang centres.
Under compact-open compactness and explicit eventual overlap equality, this
builds the finite subsequence branch-limit package and patches its compatible
local limits on the finite union of the selected balls. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : LeeYangPointwiseNormalisedAllStageBranchData G Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    ∃ family : LeeYangFiniteSubseqBranchLimitFamily G Λ J β n
        (fun i => (center i : ℂ))
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball (center i : ℂ) (data.branchData.radius (center i))) := by
  rcases
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen
      G Λ J β n center data hA hFc_mem hFres hoverlap with
    ⟨family⟩
  exact ⟨family,
    freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch
      G Λ J β n family⟩

/-- **Pointwise-normalised all-stage data to finite Lee-Yang cover package**:
restrict pre-Montel all-stage branch choices to finitely many Lee-Yang centres.
Under compact-open compactness and explicit eventual overlap equality, this
builds the finite Lee-Yang cover branch-limit package by adding the all-stage
radius positivity and Lee-Yang-domain ball containment data. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : LeeYangPointwiseNormalisedAllStageBranchData G Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    Nonempty (LeeYangFiniteCoverBranchLimitFamily G Λ J β n center
      (fun i => data.branchData.radius (center i))) := by
  rcases freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen
      G Λ J β n center data hA hFc_mem hFres hoverlap with
    ⟨family⟩
  exact ⟨{
    radius_pos := fun i => data.branchData.radius_pos (center i)
    ball_subset := fun i => data.branchData.ball_subset (center i)
    family := family }⟩

/-- **Pointwise-normalised all-stage data to finite Lee-Yang cover patch**:
restrict pre-Montel all-stage branch choices to finitely many Lee-Yang centres.
Under compact-open compactness and explicit eventual overlap equality, this
builds the finite Lee-Yang cover package and patches its compatible local
limits on the finite union of the selected Lee-Yang balls. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : LeeYangPointwiseNormalisedAllStageBranchData G Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    ∃ cover : LeeYangFiniteCoverBranchLimitFamily G Λ J β n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball (center i : ℂ) (data.branchData.radius (center i))) := by
  rcases freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen
      G Λ J β n center data hA hFc_mem hFres hoverlap with
    ⟨cover⟩
  exact ⟨cover,
    freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch
      G Λ J β n cover⟩

/-- **Pointwise-normalised all-stage data to finite real-centred Lee-Yang
cover patch**: the all-stage finite-cover bridge gives a finite Lee-Yang cover
package, and a selected real-centre index upgrades it to a real-centred package
whose patch is identified with `↑freeEnergyInfinite` at the real field. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finRealCoverCOpen_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j))))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ realCover : LeeYangFiniteRealCoverBranchLimitFamily G Λ p n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (realCover.cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball (center i : ℂ) (data.branchData.radius (center i))) ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen
      G Λ (p.J : ℂ) (p.β : ℂ) n center data hA hFc_mem hFres hoverlap with
    ⟨cover⟩
  let realCover : LeeYangFiniteRealCoverBranchLimitFamily G Λ p n center
      (fun i => data.branchData.radius (center i)) :=
    { cover := cover
      realIndex := i₀
      real_center := hcenter }
  exact ⟨realCover,
    freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_patch
      G Λ p hBED hd n realCover⟩

/-- **Pointwise-normalised all-stage data to compact real-centred Lee-Yang
cover patch**: for a compact target covered by finitely many selected
all-stage Lee-Yang balls, compact-open compactness and eventual stage-level
overlap equality produce a compact finite real-centred cover package and a
patch differentiable on the compact target, with the real-centre value
identified as `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCoverCOpen_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (K : Set ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (hKcover : K ⊆
      ⋃ i : Fin n,
        Metric.ball (center i : ℂ) (data.branchData.radius (center i)))
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j))))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finRealCoverCOpen_patch
      G Λ p hBED hd n center data hA hFc_mem hFres hoverlap i₀ hcenter with
    ⟨realCover, g, hg_eq, hg_diff, hg_real⟩
  let compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K n center
      (fun i => data.branchData.radius (center i)) :=
    { isCompact := hK
      subset_domain := hKsub
      real_mem := hpK
      cover_subset := hKcover
      realCover := realCover }
  exact ⟨compactCover, g, hg_eq, hg_diff.mono hKcover, hg_real⟩

end Ambient

end IsingModel
