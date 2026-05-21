import IsingModel.ComplexAnalyticity.Branches

/-!
# Vitali and Compact-Open Handoffs

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-- **Vitali bridge**: if a sequence `F_n : ℂ → ℂ` of holomorphic
functions converges locally uniformly on an open set `U` to a function
`f`, then `f` is holomorphic on `U`. Direct application of mathlib's
`TendstoLocallyUniformlyOn.differentiableOn`. This is the abstract
ingredient for the ∞-vol Vitali lift of GJ §4.6 Thm 4.6.2 — to apply
it we must supply locally uniform convergence of the finite-volume
log branches, which in turn follows from `TendstoLocallyUniformlyOn`
and uniform-boundedness (Montel) + pointwise convergence on the real
axis (Fekete). -/
theorem vitali_bridge {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop U) :
    DifferentiableOn ℂ f U :=
  hconv.differentiableOn (Filter.Eventually.of_forall hF) hU

/-- Specialisation of `vitali_bridge` to `U = leeYangDomain`: any limit
of a locally-uniform sequence of functions that are holomorphic on
`leeYangDomain` is itself holomorphic on `leeYangDomain`. -/
theorem vitali_bridge_leeYangDomain
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop leeYangDomain) :
    DifferentiableOn ℂ f leeYangDomain :=
  vitali_bridge isOpen_leeYangDomain hF hconv

omit [Fintype ι] [DecidableEq ι] in
/-- **Compact-open convergence to locally uniform convergence on an open
complex set**: if continuous maps on `s` converge in the compact-open
topology and total functions `F n`, `f` agree with those maps on `s`, then
`F n → f` locally uniformly on `s`. This is the topology bridge used after a
Montel / compactness input has produced compact-open convergence. -/
theorem continuousMap_tendsto_compactOpen_to_tendstoLocallyUniformlyOn
    {s : Set ℂ} (hs : IsOpen s)
    {Fc : ℕ → C(s, ℂ)} {fc : C(s, ℂ)}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n z (hz : z ∈ s), F n z = Fc n ⟨z, hz⟩)
    (hf : ∀ z (hz : z ∈ s), f z = fc ⟨z, hz⟩)
    (hconv : Filter.Tendsto Fc Filter.atTop (nhds fc)) :
    TendstoLocallyUniformlyOn F f Filter.atTop s := by
  haveI : LocallyCompactSpace s := hs.locallyCompactSpace
  have hloc :
      TendstoLocallyUniformly (fun n x => Fc n x) (fun x => fc x) Filter.atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hconv
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  have hF_eq : (fun n (z : s) => F n z) = fun n (z : s) => Fc n z := by
    funext n z
    exact hF n z z.property
  have hf_eq : (f ∘ ((↑) : s → ℂ)) = fun z : s => fc z := by
    funext z
    exact hf z z.property
  simpa [hF_eq, hf_eq] using hloc

omit [Fintype ι] [DecidableEq ι] in
/-- **Compact-open subsequence extraction on an open complex set**: if the
restrictions of a sequence of total functions to `s` lie in a compact subset
of `C(s, ℂ)`, then a subsequence converges locally uniformly on `s` to a total
function agreeing on `s` with the compact-open limit. This is the abstract
post-Montel extraction handoff; compactness of the family is an explicit
hypothesis. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
    {s : Set ℂ} (hs : IsOpen s)
    [FirstCountableTopology C(s, ℂ)]
    {A : Set C(s, ℂ)} (hA : IsCompact A)
    {Fc : ℕ → C(s, ℂ)} (hFc_mem : ∀ n, Fc n ∈ A)
    {F : ℕ → ℂ → ℂ}
    (hF : ∀ n z (hz : z ∈ s), F n z = Fc n ⟨z, hz⟩) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ fc : C(s, ℂ), ∃ f : ℂ → ℂ,
        fc ∈ A ∧
          (∀ z (hz : z ∈ s), f z = fc ⟨z, hz⟩) ∧
          TendstoLocallyUniformlyOn
            (fun m z => F (σ m) z) f Filter.atTop s := by
  classical
  rcases hA.tendsto_subseq hFc_mem with ⟨fc, hfcA, σ, hσ, hconv⟩
  let f : ℂ → ℂ := fun z => if hz : z ∈ s then fc ⟨z, hz⟩ else 0
  have hf : ∀ z (hz : z ∈ s), f z = fc ⟨z, hz⟩ := by
    intro z hz
    simp [f, hz]
  have hconv_lu :
      TendstoLocallyUniformlyOn
        (fun m z => F (σ m) z) f Filter.atTop s :=
    continuousMap_tendsto_compactOpen_to_tendstoLocallyUniformlyOn hs
      (Fc := fun m => Fc (σ m)) (fc := fc)
      (F := fun m z => F (σ m) z) (f := f)
      (fun m z hz => hF (σ m) z hz) hf
      (by simpa [Function.comp_def] using hconv)
  exact ⟨σ, hσ, fc, f, hfcA, hf, hconv_lu⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **Locally uniform convergence is stable under a strictly increasing
subsequence of stages**. This is the small diagonal-extraction utility used
when a later compact-open extraction refines a previously chosen subsequence. -/
theorem tendstoLocallyUniformlyOn_subseq_of_strictMono
    {s : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {σ : ℕ → ℕ}
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop s)
    (hσ : StrictMono σ) :
    TendstoLocallyUniformlyOn (fun m z => F (σ m) z) f Filter.atTop s := by
  intro u hu x hx
  rcases hconv u hu x hx with ⟨t, ht, hF⟩
  exact ⟨t, ht, hσ.tendsto_atTop.eventually hF⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **Two-set compact-open diagonal extraction**: if two families of continuous
restrictions lie in compact subsets of their compact-open function spaces, then
a single strictly increasing subsequence can be chosen so that both total
families converge locally uniformly on their respective open sets. This is the
finite-diagonal base case for later local-cover extraction. -/
theorem exists_subseq_two_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
    {s1 s2 : Set ℂ} (hs1 : IsOpen s1) (hs2 : IsOpen s2)
    [FirstCountableTopology C(s1, ℂ)] [FirstCountableTopology C(s2, ℂ)]
    {A1 : Set C(s1, ℂ)} {A2 : Set C(s2, ℂ)}
    (hA1 : IsCompact A1) (hA2 : IsCompact A2)
    {Fc1 : ℕ → C(s1, ℂ)} {Fc2 : ℕ → C(s2, ℂ)}
    (hFc1_mem : ∀ n, Fc1 n ∈ A1)
    (hFc2_mem : ∀ n, Fc2 n ∈ A2)
    {F1 F2 : ℕ → ℂ → ℂ}
    (hF1 : ∀ n z (hz : z ∈ s1), F1 n z = Fc1 n ⟨z, hz⟩)
    (hF2 : ∀ n z (hz : z ∈ s2), F2 n z = Fc2 n ⟨z, hz⟩) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∃ fc1 : C(s1, ℂ), ∃ f1 : ℂ → ℂ,
        fc1 ∈ A1 ∧
          (∀ z (hz : z ∈ s1), f1 z = fc1 ⟨z, hz⟩) ∧
          TendstoLocallyUniformlyOn
            (fun m z => F1 (σ m) z) f1 Filter.atTop s1) ∧
      (∃ fc2 : C(s2, ℂ), ∃ f2 : ℂ → ℂ,
        fc2 ∈ A2 ∧
          (∀ z (hz : z ∈ s2), f2 z = fc2 ⟨z, hz⟩) ∧
          TendstoLocallyUniformlyOn
            (fun m z => F2 (σ m) z) f2 Filter.atTop s2) := by
  rcases exists_subseq_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
      hs1 hA1 hFc1_mem hF1 with
    ⟨σ1, hσ1, fc1, f1, hfc1A, hf1_agree, hconv1⟩
  rcases exists_subseq_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
      hs2 hA2 (fun m => hFc2_mem (σ1 m))
      (F := fun m z => F2 (σ1 m) z)
      (fun m z hz => hF2 (σ1 m) z hz) with
    ⟨τ, hτ, fc2, f2, hfc2A, hf2_agree, hconv2⟩
  refine ⟨fun m => σ1 (τ m), hσ1.comp hτ, ?_, ?_⟩
  · exact ⟨fc1, f1, hfc1A, hf1_agree,
      tendstoLocallyUniformlyOn_subseq_of_strictMono
        (F := fun m z => F1 (σ1 m) z) hconv1 hτ⟩
  · exact ⟨fc2, f2, hfc2A, hf2_agree, hconv2⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **Finite compact-open diagonal extraction over `Fin n`**: for a finite
family of open complex sets, if each restricted branch family takes values in a
compact subset of the corresponding compact-open continuous-map space, then a
single strictly increasing subsequence can be chosen so that every family
converges locally uniformly on its open set. This is the finite-cover
extraction handoff; it does not assert compatibility of the resulting local
limits on overlaps. -/
theorem exists_subseq_fin_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
    (n : ℕ)
    {s : Fin n → Set ℂ} (hs : ∀ i, IsOpen (s i))
    [∀ i, FirstCountableTopology C(s i, ℂ)]
    {A : ∀ i, Set C(s i, ℂ)} (hA : ∀ i, IsCompact (A i))
    {Fc : ∀ i, ℕ → C(s i, ℂ)}
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    {F : Fin n → ℕ → ℂ → ℂ}
    (hF : ∀ i m z (hz : z ∈ s i), F i m z = Fc i m ⟨z, hz⟩) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i, ∃ fc : C(s i, ℂ), ∃ f : ℂ → ℂ,
        fc ∈ A i ∧
          (∀ z (hz : z ∈ s i), f z = fc ⟨z, hz⟩) ∧
          TendstoLocallyUniformlyOn
            (fun m z => F i (σ m) z) f Filter.atTop (s i) := by
  classical
  induction n with
  | zero =>
      refine ⟨id, strictMono_id, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      rcases exists_subseq_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
          (hs 0) (hA 0) (hFc_mem 0) (hF 0) with
        ⟨σ0, hσ0, fc0, f0, hfc0A, hf0_agree, hconv0⟩
      letI : ∀ i : Fin n, FirstCountableTopology C(s i.succ, ℂ) :=
        fun _ => inferInstance
      rcases ih (s := fun i : Fin n => s i.succ)
          (hs := fun i => hs i.succ)
          (A := fun i : Fin n => A i.succ)
          (hA := fun i => hA i.succ)
          (Fc := fun i m => Fc i.succ (σ0 m))
          (hFc_mem := fun i m => hFc_mem i.succ (σ0 m))
          (F := fun i m z => F i.succ (σ0 m) z)
          (hF := fun i m z hz => hF i.succ (σ0 m) z hz) with
        ⟨τ, hτ, htail⟩
      refine ⟨fun m => σ0 (τ m), hσ0.comp hτ, ?_⟩
      intro i
      refine Fin.cases ?_ ?_ i
      · exact ⟨fc0, f0, hfc0A, hf0_agree,
          tendstoLocallyUniformlyOn_subseq_of_strictMono
            (F := fun m z => F 0 (σ0 m) z) hconv0 hτ⟩
      · intro j
        exact htail j

omit [Fintype ι] [DecidableEq ι] in
/-- **Overlap uniqueness for locally uniform limits**: if two sequences converge
locally uniformly on open sets `s` and `t`, and their stage functions are
eventually equal on the overlap `s ∩ t`, then their limits agree on that
overlap. -/
theorem eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn
    {s t : Set ℂ} {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    (hF : TendstoLocallyUniformlyOn F f Filter.atTop s)
    (hG : TendstoLocallyUniformlyOn G g Filter.atTop t)
    (hEq : ∀ᶠ n in Filter.atTop, Set.EqOn (F n) (G n) (s ∩ t)) :
    Set.EqOn f g (s ∩ t) := by
  intro z hz
  exact tendsto_nhds_unique_of_eventuallyEq
    (hF.tendsto_at hz.1)
    (hG.tendsto_at hz.2)
    (hEq.mono fun n hn => hn hz)

omit [Fintype ι] [DecidableEq ι] in
/-- **Finite-family overlap compatibility for locally uniform limits**: for a
finite family of locally uniformly convergent sequences, pairwise eventual
equality of the stage functions on pairwise overlaps implies pairwise equality
of the limiting functions on those overlaps. -/
theorem pairwise_eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn
    (n : ℕ)
    {s : Fin n → Set ℂ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {f : Fin n → ℂ → ℂ}
    (hconv : ∀ i, TendstoLocallyUniformlyOn (F i) (f i) Filter.atTop (s i))
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m) (s i ∩ s j)) :
    ∀ i j, Set.EqOn (f i) (f j) (s i ∩ s j) := by
  intro i j
  exact eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn
    (hconv i) (hconv j) (hoverlap i j)

omit [Fintype ι] [DecidableEq ι] in
/-- **Indexed-family overlap compatibility for locally uniform limits**: for an
arbitrary indexed family of locally uniformly convergent sequences, pairwise
eventual equality of the stage functions on pairwise overlaps implies pairwise
equality of the limiting functions on those overlaps. -/
theorem pairwise_eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn_indexed
    {α : Type*}
    {s : α → Set ℂ}
    {F : α → ℕ → ℂ → ℂ}
    {f : α → ℂ → ℂ}
    (hconv : ∀ i, TendstoLocallyUniformlyOn (F i) (f i) Filter.atTop (s i))
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m) (s i ∩ s j)) :
    ∀ i j, Set.EqOn (f i) (f j) (s i ∩ s j) := by
  intro i j
  exact eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn
    (hconv i) (hconv j) (hoverlap i j)

omit [Fintype ι] [DecidableEq ι] in
/-- **Finite open-cover patching for differentiable local functions**: a finite
family of differentiable functions on open sets, compatible on all pairwise
overlaps, patches to one function on the finite union.  The patched function
agrees with each local function on its own open set and is differentiable on
the whole union. -/
theorem exists_differentiableOn_iUnion_of_finite_eqOn
    (n : ℕ)
    {s : Fin n → Set ℂ}
    {f : Fin n → ℂ → ℂ}
    (hs : ∀ i, IsOpen (s i))
    (hdiff : ∀ i, DifferentiableOn ℂ (f i) (s i))
    (hcompat : ∀ i j, Set.EqOn (f i) (f j) (s i ∩ s j)) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (f i) (s i)) ∧
      DifferentiableOn ℂ g (⋃ i, s i) := by
  classical
  induction n with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro z hz
        simp at hz
  | succ n ih =>
      rcases ih
          (s := fun i : Fin n => s i.succ)
          (f := fun i : Fin n => f i.succ)
          (hs := fun i => hs i.succ)
          (hdiff := fun i => hdiff i.succ)
          (hcompat := fun i j => hcompat i.succ j.succ) with
        ⟨gTail, hgTail_eq, hgTail_diff⟩
      let tail : Set ℂ := ⋃ i : Fin n, s i.succ
      let g : ℂ → ℂ := Set.piecewise (s 0) (f 0) gTail
      have htail_open : IsOpen tail := isOpen_iUnion (fun i : Fin n => hs i.succ)
      have hg_head : Set.EqOn g (f 0) (s 0) := by
        intro z hz
        simp [g, hz]
      have hg_tail : ∀ i : Fin n, Set.EqOn g (f i.succ) (s i.succ) := by
        intro i z hz
        by_cases hz0 : z ∈ s 0
        · have h0i : f 0 z = f i.succ z := hcompat 0 i.succ ⟨hz0, hz⟩
          simpa [g, hz0] using h0i
        · have htail_i : gTail z = f i.succ z := hgTail_eq i hz
          simpa [g, hz0] using htail_i
      have hg_tail_union : Set.EqOn g gTail tail := by
        intro z hz
        rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
        by_cases hz0 : z ∈ s 0
        · have h0i : f 0 z = f i.succ z := hcompat 0 i.succ ⟨hz0, hzi⟩
          have htail_i : gTail z = f i.succ z := hgTail_eq i hzi
          calc
            g z = f 0 z := by simp [g, hz0]
            _ = f i.succ z := h0i
            _ = gTail z := htail_i.symm
        · simp [g, hz0]
      have hg_diff_head : DifferentiableOn ℂ g (s 0) :=
        (hdiff 0).congr hg_head
      have hg_diff_tail : DifferentiableOn ℂ g tail :=
        hgTail_diff.congr hg_tail_union
      have hg_diff_union : DifferentiableOn ℂ g (s 0 ∪ tail) :=
        DifferentiableOn.union_of_isOpen hg_diff_head hg_diff_tail (hs 0) htail_open
      refine ⟨g, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · exact hg_head
        · intro j
          exact hg_tail j
      · refine hg_diff_union.congr_mono ?_ ?_
        · intro z hz
          rfl
        · intro z hz
          rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
          obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
          · exact Or.inl hzi
          · exact Or.inr (Set.mem_iUnion.mpr ⟨j, hzi⟩)

omit [Fintype ι] [DecidableEq ι] in
/-- **Open-cover patching for differentiable local functions**: a family of
differentiable functions on open sets, compatible on all pairwise overlaps,
patches to one function on the union. The patched function agrees with each
local function on its own open set and is differentiable on the whole union. -/
theorem exists_differentiableOn_iUnion_of_eqOn
    {α : Type*}
    {s : α → Set ℂ}
    {f : α → ℂ → ℂ}
    (hs : ∀ i, IsOpen (s i))
    (hdiff : ∀ i, DifferentiableOn ℂ (f i) (s i))
    (hcompat : ∀ i j, Set.EqOn (f i) (f j) (s i ∩ s j)) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (f i) (s i)) ∧
      DifferentiableOn ℂ g (⋃ i, s i) := by
  classical
  let g : ℂ → ℂ := fun z =>
    if hz : z ∈ ⋃ i, s i then
      f (Classical.choose (Set.mem_iUnion.mp hz)) z
    else 0
  have hg_eq : ∀ i, Set.EqOn g (f i) (s i) := by
    intro i z hz
    have hzU : z ∈ ⋃ i, s i := Set.mem_iUnion.mpr ⟨i, hz⟩
    let j : α := Classical.choose (Set.mem_iUnion.mp hzU)
    have hzj : z ∈ s j := Classical.choose_spec (Set.mem_iUnion.mp hzU)
    have hji : f j z = f i z := hcompat j i ⟨hzj, hz⟩
    change (if hzU' : z ∈ ⋃ i, s i then
        f (Classical.choose (Set.mem_iUnion.mp hzU')) z else 0) = f i z
    rw [dif_pos hzU]
    exact hji
  have hg_diff : DifferentiableOn ℂ g (⋃ i, s i) := by
    intro z hzU
    rcases Set.mem_iUnion.mp hzU with ⟨i, hzi⟩
    have h_eventually : g =ᶠ[nhds z] f i := by
      filter_upwards [((hs i).mem_nhds hzi)] with y hy
      exact hg_eq i hy
    exact ((hdiff i).differentiableAt ((hs i).mem_nhds hzi)).congr_of_eventuallyEq
      h_eventually |>.differentiableWithinAt
  exact ⟨g, hg_eq, hg_diff⟩

end IsingModel
