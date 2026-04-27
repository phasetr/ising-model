import IsingModel.AmbientLattice.TruncatedFunctions

/-!
# Parameter monotonicity of spontaneous observables + Cor 4.3.5 at ∞-volume

Monotonicity of `spontaneousCorrelation` / `spontaneousMagnetization` in
the parameters J, β, and the ambient subgraph. Also lifts GJ §4.3
Corollary 4.3.5 (inductive n-point bound at h=0) to infinite volume.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.3, §5.1.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Parameter monotonicity of `spontaneous*`

Combine the parameter-direction monotonicity of `correlationInfinite`
(PR #95–#97) with the infimum definition of `spontaneousCorrelation`
to obtain monotonicity of the spontaneous correlation function in
`J` and `β`.  The `h`-direction is already collapsed by the infimum
over `h > 0`, so only `J` and `β` remain as free parameters. -/

/-- **J-direction monotonicity of `spontaneousCorrelation`**: for
fixed `β > 0`, $\langle \sigma^A \rangle^*(J, \beta)$ is monotone in
$J \in \mathrm{Ici}\,0$.

Since `correlationInfinite_monotone_J` gives pointwise monotonicity
for each `h ∈ Ioi 0`, the iInf over `h > 0` is also monotone in `J`.
Proof via `ciInf_mono` + `correlationInfinite_bddBelow_on_Ioi`. -/
theorem spontaneousCorrelation_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    MonotoneOn
      (fun J : ℝ => spontaneousCorrelation G Λ J β A)
      (Set.Ici 0) := by
  intro J₁ hJ₁ J₂ _ hJ₁₂
  unfold spontaneousCorrelation
  refine ciInf_mono
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ₁ hβ A) ?_
  intro h
  exact correlationInfinite_monotone_J G Λ h.property.le hβ A
    hJ₁ (hJ₁.trans hJ₁₂) hJ₁₂

/-- **Ambient-subgraph monotonicity of `spontaneousCorrelation`**
(ferromagnetic): for `G₁ ≤ G₂`, `0 ≤ J`, `0 < β`,
`spontaneousCorrelation G₁ Λ J β A ≤ spontaneousCorrelation G₂ Λ J β A`.
Via `ciInf_mono` + `correlationInfinite_monotone_ambient_subgraph`. -/
theorem spontaneousCorrelation_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (hG : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    spontaneousCorrelation G₁ Λ J β A
      ≤ spontaneousCorrelation G₂ Λ J β A := by
  unfold spontaneousCorrelation
  refine ciInf_mono
    (correlationInfinite_bddBelow_on_Ioi G₁ Λ hJ hβ A) ?_
  intro hpos
  have hf : Ferromagnetic (⟨J, hpos.val, β⟩ : IsingParams ℝ) :=
    ⟨hJ, hpos.property.le, hβ⟩
  exact correlationInfinite_monotone_ambient_subgraph hG Λ
    (⟨J, hpos.val, β⟩ : IsingParams ℝ) hf A

/-- **β-direction monotonicity of `spontaneousCorrelation`**: for
fixed `J ≥ 0`, the map `β ↦ spontaneousCorrelation G Λ J β A` is
monotone on `Set.Ioi 0`.

Companion to `spontaneousCorrelation_monotone_J`.  Since
`correlationInfinite_monotone_beta` gives pointwise monotonicity in
`β` for each `h ∈ Ioi 0` (with the remaining parameters bounded
below by `0`), the iInf over `h > 0` is also monotone in `β`.
Proof via `ciInf_mono` + `correlationInfinite_bddBelow_on_Ioi`. -/
theorem spontaneousCorrelation_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) (A : Finset V) :
    MonotoneOn
      (fun β : ℝ => spontaneousCorrelation G Λ J β A)
      (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ _ hβ₁₂
  unfold spontaneousCorrelation
  refine ciInf_mono
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ hβ₁ A) ?_
  intro h
  exact correlationInfinite_monotone_beta G Λ hJ h.property.le A
    hβ₁ (lt_of_lt_of_le hβ₁ hβ₁₂) hβ₁₂

/-- **J-direction monotonicity of `spontaneousMagnetization`**:
specialization of `spontaneousCorrelation_monotone_J` at `A = {i}`. -/
theorem spontaneousMagnetization_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (i : V) :
    MonotoneOn
      (fun J : ℝ => spontaneousMagnetization G Λ J β i)
      (Set.Ici 0) :=
  spontaneousCorrelation_monotone_J G Λ hβ {i}

/-- **β-direction monotonicity of `spontaneousMagnetization`**:
specialization of `spontaneousCorrelation_monotone_beta` at `A = {i}`. -/
theorem spontaneousMagnetization_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) (i : V) :
    MonotoneOn
      (fun β : ℝ => spontaneousMagnetization G Λ J β i)
      (Set.Ioi 0) :=
  spontaneousCorrelation_monotone_beta G Λ hJ {i}

/-- **Ambient-subgraph monotonicity of `spontaneousMagnetization`**
(ferromagnetic): `G₁ ≤ G₂` ⇒ `m*_G₁(i) ≤ m*_G₂(i)`. Specialization of
`spontaneousCorrelation_monotone_ambient_subgraph` at `A = {i}`. -/
theorem spontaneousMagnetization_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (hG : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G₁ Λ J β i
      ≤ spontaneousMagnetization G₂ Λ J β i :=
  spontaneousCorrelation_monotone_ambient_subgraph hG Λ hJ hβ {i}

/-! ## Cor 4.3.5 (inductive n-point at h=0) at infinite volume

Lift `IsingModel.cor_4_3_5_h0` to the thermodynamic limit using the
liftFinset infrastructure from PR #107 and `Finset.sum_bij` to reindex
the powerset sum.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.5, p. 62. -/

/-- **Cor 4.3.5 lifted to infinite volume**: the inductive (n+2)-point
bound holds for `correlationInfinite` at `h = 0`.  For ferromagnetic
Ising at zero external field, any finite set `S`, and distinct sites
`j, k ∉ S`, the infinite-volume correlation satisfies the same
inductive bound as the finite-volume version. -/
theorem correlationInfinite_cor_4_3_5_h0
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    (S : Finset V) {j k : V} (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    correlationInfinite G Λ ⟨J, 0, β⟩ (insert j (insert k S)) ≤
      correlationInfinite G Λ ⟨J, 0, β⟩ S *
        correlationInfinite G Λ ⟨J, 0, β⟩ {j, k} +
      ∑ T ∈ S.powerset,
        correlationInfinite G Λ ⟨J, 0, β⟩ (insert j T) *
          correlationInfinite G Λ ⟨J, 0, β⟩ (insert k (S \ T)) := by
  set p := (⟨J, 0, β⟩ : IsingParams ℝ)
  have hlhs_tendsto := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf (insert j (insert k S))
  have hrhs_main :=
    (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf S).mul
      (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {j, k})
  have hrhs_sum : Filter.Tendsto
      (fun n => ∑ T ∈ S.powerset,
        correlationAlongExhaustion G Λ p (insert j T) n *
          correlationAlongExhaustion G Λ p (insert k (S \ T)) n)
      Filter.atTop
      (nhds (∑ T ∈ S.powerset,
        correlationInfinite G Λ p (insert j T) *
          correlationInfinite G Λ p (insert k (S \ T)))) := by
    refine tendsto_finset_sum _ (fun T _ => ?_)
    exact (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf _).mul
      (tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf _)
  have hrhs_tendsto := hrhs_main.add hrhs_sum
  refine le_of_tendsto_of_tendsto' hlhs_tendsto hrhs_tendsto ?_
  intro n
  by_cases hall : (insert j (insert k S) : Finset V) ⊆ Λ.volume n
  · have hj_vol : j ∈ Λ.volume n := hall (Finset.mem_insert_self _ _)
    have hk_vol : k ∈ Λ.volume n :=
      hall (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hS_vol : S ⊆ Λ.volume n := fun x hx =>
      hall (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have hjk_vol : ({j, k} : Finset V) ⊆ Λ.volume n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hj_vol
      · exact hk_vol
    let j' : (↑(Λ.volume n) : Type _) := ⟨j, hj_vol⟩
    let k' : (↑(Λ.volume n) : Type _) := ⟨k, hk_vol⟩
    let S' : Finset (↑(Λ.volume n) : Type _) := liftFinset S hS_vol
    have hj'_notin : j' ∉ S' := fun h => hj ((mem_liftFinset _ _).mp h)
    have hk'_notin : k' ∉ S' := fun h => hk ((mem_liftFinset _ _).mp h)
    have hjk' : j' ≠ k' := fun h => hjk (Subtype.mk.inj h)
    have hfin := IsingModel.cor_4_3_5_h0
      (inducedGraph G (Λ.volume n)) J β hf S' j' k' hj'_notin hk'_notin hjk'
    rw [correlationAlongExhaustion_of_subset G Λ p hall,
        correlationAlongExhaustion_of_subset G Λ p hS_vol,
        correlationAlongExhaustion_of_subset G Λ p hjk_vol]
    have hlift_jkS :
        liftFinset (insert j (insert k S)) hall = insert j' (insert k' S') := by
      rw [← liftFinset_insert hj_vol (fun x hx =>
        hall (Finset.mem_insert_of_mem hx))]
      simp only [S', k']
      rw [← liftFinset_insert hk_vol hS_vol]
    have hlift_jk :
        liftFinset ({j, k} : Finset V) hjk_vol = ({j', k'} : Finset _) := by
      ext x
      simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton, j', k']
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl (by rfl)
        · exact Or.inr (by rfl)
      · rintro (h | h)
        · exact Or.inl (congrArg Subtype.val h)
        · exact Or.inr (congrArg Subtype.val h)
    rw [hlift_jkS, hlift_jk]
    have hsum_eq :
        ∑ T ∈ S.powerset,
          correlationAlongExhaustion G Λ p (insert j T) n *
            correlationAlongExhaustion G Λ p (insert k (S \ T)) n
        = ∑ T' ∈ S'.powerset,
          correlationΛ G (Λ.volume n) p (insert j' T') *
            correlationΛ G (Λ.volume n) p (insert k' (S' \ T')) := by
      refine Finset.sum_bij
        (fun T hT => liftFinset T
          (fun x hx => hS_vol ((Finset.mem_powerset.mp hT) hx)))
        ?_ ?_ ?_ ?_
      · intro T hT
        simp only [S', Finset.mem_powerset]
        intro x hx
        simp only [mem_liftFinset] at hx ⊢
        exact (Finset.mem_powerset.mp hT) hx
      · intro T₁ hT₁ T₂ hT₂ heq
        have h₁ := Finset.mem_powerset.mp hT₁
        have h₂ := Finset.mem_powerset.mp hT₂
        -- Beta-reduce heq to pure liftFinset equality
        have heq' : liftFinset T₁ (fun x hx => hS_vol (h₁ hx))
            = liftFinset T₂ (fun x hx => hS_vol (h₂ hx)) := heq
        ext x
        by_cases hx_vol : x ∈ Λ.volume n
        · constructor
          · intro hxT₁
            have hlift : (⟨x, hx_vol⟩ : ↑(Λ.volume n))
                ∈ liftFinset T₁ (fun y hy => hS_vol (h₁ hy)) :=
              (mem_liftFinset _ _).mpr hxT₁
            rw [heq'] at hlift
            exact (mem_liftFinset _ _).mp hlift
          · intro hxT₂
            have hlift : (⟨x, hx_vol⟩ : ↑(Λ.volume n))
                ∈ liftFinset T₂ (fun y hy => hS_vol (h₂ hy)) :=
              (mem_liftFinset _ _).mpr hxT₂
            rw [← heq'] at hlift
            exact (mem_liftFinset _ _).mp hlift
        · exact ⟨fun h => absurd (hS_vol (h₁ h)) hx_vol,
                fun h => absurd (hS_vol (h₂ h)) hx_vol⟩
      · intro T' hT'
        simp only [S', Finset.mem_powerset] at hT'
        refine ⟨T'.image (fun x => x.val), ?_, ?_⟩
        · simp only [Finset.mem_powerset]
          intro x hx
          simp only [Finset.mem_image] at hx
          obtain ⟨y, hyT', rfl⟩ := hx
          have := hT' hyT'
          simpa only [mem_liftFinset] using this
        · ext x
          simp only [mem_liftFinset, Finset.mem_image]
          refine ⟨?_, ?_⟩
          · rintro ⟨y, hyT', hyx⟩
            have : y = x := Subtype.ext hyx
            exact this ▸ hyT'
          · intro h
            exact ⟨x, h, rfl⟩
      · intro T hT
        have hT_sub := Finset.mem_powerset.mp hT
        have hjT_vol : (insert j T : Finset V) ⊆ Λ.volume n := fun x hx => by
          simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact hj_vol
          · exact hS_vol (hT_sub hx)
        have hkST_vol : (insert k (S \ T) : Finset V) ⊆ Λ.volume n :=
          fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_sdiff] at hx
            rcases hx with rfl | ⟨hxS, _⟩
            · exact hk_vol
            · exact hS_vol hxS
        rw [correlationAlongExhaustion_of_subset G Λ p hjT_vol,
            correlationAlongExhaustion_of_subset G Λ p hkST_vol]
        have h_liftFinset_jT :
            liftFinset (insert j T) hjT_vol
            = insert j' (liftFinset T (fun x hx => hS_vol (hT_sub hx))) := by
          rw [← liftFinset_insert hj_vol (fun x hx => hS_vol (hT_sub hx))]
        have h_liftFinset_kST :
            liftFinset (insert k (S \ T)) hkST_vol
            = insert k' (S' \ liftFinset T (fun x hx => hS_vol (hT_sub hx))) := by
          rw [← liftFinset_insert hk_vol (fun x hx => hS_vol
            ((Finset.mem_sdiff.mp hx).1))]
          congr 1
          simp only [S']
          exact (liftFinset_sdiff hS_vol (fun x hx => hS_vol (hT_sub hx))).symm
        rw [h_liftFinset_jT, h_liftFinset_kST]
    rw [hsum_eq]
    unfold correlationΛ
    exact hfin
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hall]
    have h_main :
        0 ≤ correlationAlongExhaustion G Λ p S n *
          correlationAlongExhaustion G Λ p {j, k} n :=
      mul_nonneg
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
    have h_sum : 0 ≤ ∑ T ∈ S.powerset,
        correlationAlongExhaustion G Λ p (insert j T) n *
          correlationAlongExhaustion G Λ p (insert k (S \ T)) n := by
      refine Finset.sum_nonneg fun T _ => ?_
      exact mul_nonneg
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
        (correlationAlongExhaustion_nonneg G Λ p hf _ n)
    linarith

/-- **Infinite-volume free energy density** (limsup form).

Defined as the `Filter.limsup` of `freeEnergyAlongExhaustion`, which
is always well-defined for real sequences (even non-convergent ones).
Glimm–Jaffe Proposition 4.6.1 asserts that this limsup equals the
liminf (i.e., the sequence converges); the convergence theorem itself
is deferred pending partition function super-additivity + Fekete's
lemma machinery. -/
noncomputable def freeEnergyInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : ℝ :=
  Filter.limsup (freeEnergyAlongExhaustion G Λ p) Filter.atTop

/-- **Unfolding of `freeEnergyInfinite`**:
`freeEnergyInfinite G Λ p = limsup (freeEnergyAlongExhaustion G Λ p)`
at `atTop`, by definition. -/
theorem freeEnergyInfinite_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyInfinite G Λ p
      = Filter.limsup (freeEnergyAlongExhaustion G Λ p) Filter.atTop := rfl

/-- **Zero-params lower-bound comparison for `freeEnergyAlongExhaustion`**.

For ferromagnetic Ising parameters (`J ≥ 0`, `h ≥ 0`, `β > 0`), the
free energy along the exhaustion dominates the value at zero coupling
and zero external field:
`freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n
  ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n`.

Proof: transitive composition of `_monotone_h` at `J = 0` (giving
`f(0, 0, β) ≤ f(0, h, β)`) with `_monotone_J` at fixed `h`
(giving `f(0, h, β) ≤ f(J, h, β)`). -/
theorem freeEnergyAlongExhaustion_ge_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n
      ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n := by
  have h1 : freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n
      ≤ freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n :=
    freeEnergyAlongExhaustion_monotone_h G Λ le_rfl hβ n
      (Set.self_mem_Ici) hh hh
  have h2 : freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n
      ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n :=
    freeEnergyAlongExhaustion_monotone_J G Λ hh hβ n
      (Set.self_mem_Ici) hJ hJ
  exact h1.trans h2

/-- **Zero-params lower-bound comparison for `partitionFunctionAlongExhaustion`**
(partition function analog of `freeEnergyAlongExhaustion_ge_zero_params`).
For ferromagnetic, `Z(0, 0, β) ≤ Z(J, h, β)`. -/
theorem partitionFunctionAlongExhaustion_ge_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n
      ≤ partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n := by
  have h1 : partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n
      ≤ partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n :=
    partitionFunctionAlongExhaustion_monotone_h G Λ 0 β le_rfl hβ le_rfl hh n
  have h2 : partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n
      ≤ partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n :=
    partitionFunctionAlongExhaustion_monotone_J G Λ h β hh hβ le_rfl hJ n
  exact h1.trans h2

/-- **Uniform lower bound** `freeEnergyAlongExhaustion ≥ log 2` for
ferromagnetic parameters on a nonempty volume.

Combines the zero-params comparison
(`freeEnergyAlongExhaustion_ge_zero_params`, PR #117) with the
explicit value at zero parameters (`freeEnergy_zero_params = log 2`,
PR #120) via `IsingModel.freeEnergy` definitional unfolding.

This is half of the data needed for Glimm–Jaffe §4.6 Proposition 4.6.1
(convergence): the sequence is bounded below by `log 2`. -/
theorem freeEnergyAlongExhaustion_ge_log_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log 2 ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n := by
  have h_zero : freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n = Real.log 2 := by
    change freeEnergyΛ G (Λ.volume n) (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2
    exact IsingModel.freeEnergy_zero_params _ β (Finset.Nonempty.fintype_card_coe_pos hne)
  calc Real.log 2
      = freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n := h_zero.symm
    _ ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n :=
        freeEnergyAlongExhaustion_ge_zero_params G Λ hJ hh hβ n

/-- **Sharp along-exhaustion lower bound**:
for ferromagnetic parameters and nonempty stage,
`log(2·cosh(β·h)) ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n`.

Specialization of `IsingModel.freeEnergy_ge_log_two_cosh` (FreeEnergy.lean)
at the induced subgraph on `Λ.volume n`. Sharpens the `log 2` uniform
lower bound (`freeEnergyAlongExhaustion_ge_log_two`). -/
theorem freeEnergyAlongExhaustion_ge_log_two_cosh
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n := by
  change Real.log (2 * Real.cosh (β * h))
      ≤ IsingModel.freeEnergy (inducedGraph G (Λ.volume n)) ⟨J, h, β⟩
  exact IsingModel.freeEnergy_ge_log_two_cosh _ hJ hh hβ (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Along-exhaustion upper bound for the free energy**:
for nonempty `Λ.volume n`,
`freeEnergyAlongExhaustion G Λ p n ≤
  log 2 + |β|·(|J|·|E_n| + |h|·|Λ_n|) / |Λ_n|`,
where `E_n` is the edge count of the induced subgraph on `Λ.volume n`
and `|Λ_n|` is its cardinality.

Specialization of `IsingModel.freeEnergy_upper_bound` (Conditioning.lean,
Cor. 10.3.2 divided by `|ι|`) to the exhaustion setting. -/
theorem freeEnergyAlongExhaustion_upper_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ p n ≤ Real.log 2 +
      |p.β| * (|p.J| * (inducedGraph G (Λ.volume n)).edgeFinset.card +
          |p.h| * Fintype.card (↑(Λ.volume n) : Type _))
        / Fintype.card (↑(Λ.volume n) : Type _) := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n)) p ≤ _
  exact IsingModel.freeEnergy_upper_bound _ p (Finset.Nonempty.fintype_card_coe_pos hne)


end Ambient
end IsingModel
