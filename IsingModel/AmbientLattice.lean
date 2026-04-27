import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.Monotonicity
import IsingModel.AmbientLattice.CorrelationInfinite
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.MagnetizationInfinite
import IsingModel.AmbientLattice.SpontaneousMagnetization
import IsingModel.AmbientLattice.TruncatedFunctions
import IsingModel.InfiniteVolume
import IsingModel.FreeEnergy
import IsingModel.Inequalities.GHS
import IsingModel.Conditioning
import IsingModel.PhaseTransition
import IsingModel.FieldDerivative

/-!
# Genuine infinite-volume framework: ambient lattice

The existing `IsingModel` framework parametrizes everything by a fixed
`Fintype ι`.  This file introduces a **genuinely infinite ambient
lattice** `V : Type*` (no `Fintype V` assumption) and defines the
finite-volume Ising model on any `Λ : Finset V` by instantiating the
existing framework on the Fintype `(↑Λ : Type _)`.

This is the foundation for the true thermodynamic limit (Phase 2), where
an exhaustion `Λₙ ↑ V` covers the whole ambient lattice.

## Design

- Ambient type `V` carries an ambient `SimpleGraph V` (the interaction
  graph), and we demand `DecidableEq V` + `DecidableRel G.Adj` so that
  finite restrictions remain decidable.
- For `Λ : Finset V`, the type `(↑Λ : Type _)` is Fintype (mathlib
  `Finset.instFintypeCoe`).  The induced subgraph
  `G.induce (↑Λ : Set V)` gives a `SimpleGraph (↑Λ : Type _)` with
  `Fintype edgeSet` derivable from the ambient `DecidableRel`.
- Correlations, partition functions, and free energies on `Λ` are
  defined by forwarding to the existing `IsingModel` constructors.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.2, §4.6 (the thermodynamic limit
  is stated over `Λ ↑ ℝᵈ`, i.e., an infinite ambient).
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

/-! ## Uniform upper bound under bounded edge density

The per-stage upper bound `freeEnergyAlongExhaustion_upper_bound` depends
on `|E_n| / |Λ_n|`; this ratio can diverge for an arbitrary exhaustion.
Under the natural hypothesis `BoundedEdgeDensity`, the sequence is
uniformly bounded above — a step toward Glimm–Jaffe §4.6 Prop 4.6.1
convergence (which still needs super-additivity + Fekete). -/

/-- **Bounded edge density along an exhaustion**: there is `c : ℝ` such
that for every `n` with `Λ.volume n` nonempty,
`|E(G[Λ_n])| ≤ c · |Λ_n|`.

Example: bounded-degree ambient graphs with max degree `Δ` satisfy
this with `c = Δ / 2`. -/
def BoundedEdgeDensity (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] : Prop :=
  ∃ c : ℝ, ∀ n, (Λ.volume n).Nonempty →
    ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
      c * Fintype.card (↑(Λ.volume n) : Type _)

/-- **Uniform upper bound on `freeEnergyAlongExhaustion` under bounded
edge density**: if `BoundedEdgeDensity G Λ` with constant `c`, then for
every `n` with `Λ.volume n` nonempty and any Ising parameters `p`,
`freeEnergyAlongExhaustion G Λ p n ≤ log 2 + |β|·(|J|·c + |h|)`.

Direct consequence of `freeEnergyAlongExhaustion_upper_bound` (PR #122)
and the edge-density bound `|E_n|/|Λ_n| ≤ c`. -/
theorem freeEnergyAlongExhaustion_le_uniform_upper_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _))
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ p n ≤
      Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
  have hcard_pos : (0 : ℝ) < Fintype.card (↑(Λ.volume n) : Type _) := by
    rw [Fintype.card_coe]; exact_mod_cast Finset.card_pos.mpr hne
  have hratio :
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
        Fintype.card (↑(Λ.volume n) : Type _) ≤ c :=
    (div_le_iff₀ hcard_pos).mpr (hc n hne)
  calc freeEnergyAlongExhaustion G Λ p n
      ≤ Real.log 2 +
          |p.β| * (|p.J| * (inducedGraph G (Λ.volume n)).edgeFinset.card +
              |p.h| * Fintype.card (↑(Λ.volume n) : Type _))
            / Fintype.card (↑(Λ.volume n) : Type _) :=
        freeEnergyAlongExhaustion_upper_bound G Λ p n hne
    _ = Real.log 2 +
          |p.β| * (|p.J| *
              ((inducedGraph G (Λ.volume n)).edgeFinset.card /
                Fintype.card (↑(Λ.volume n) : Type _)) + |p.h|) := by
          field_simp
    _ ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
          gcongr

/-! ## β = 0 closed form along exhaustion -/

/-- **Along-exhaustion β=0 closed form**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ, J, h`,
`freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩ n = log 2`.

Specialization of `IsingModel.freeEnergy_beta_zero` (PR #131) via
`change` + definitional unfolding of `freeEnergyAlongExhaustion`
through `freeEnergyΛ` to `IsingModel.freeEnergy (inducedGraph …)`. -/
theorem freeEnergyAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2
  exact IsingModel.freeEnergy_beta_zero _ J h (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Infinite-volume β=0 closed form**:
under `∀ n, (Λ.volume n).Nonempty`, `freeEnergyInfinite G Λ ⟨J, h, 0⟩ = log 2`
for any `J, h, G, Λ`.

The sequence `n ↦ freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩ n` is constantly
`log 2` by `freeEnergyAlongExhaustion_beta_zero`, so its `limsup` on
`atTop` is `log 2` by `Filter.limsup_const`.

Sanity check: the β = 0 slice of the §4.6 Prop 4.6.1 infinite-volume
free energy is trivially the maximum-entropy value.

A weakened version requiring only `∀ᶠ n in atTop, (Λ.volume n).Nonempty`
is provided as `freeEnergyInfinite_beta_zero_of_eventually_nonempty`
in `AmbientLatticeSum.lean`. -/
theorem freeEnergyInfinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergyInfinite
  have hconst : freeEnergyAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ)
      = fun _ : ℕ => Real.log 2 := by
    funext n
    exact freeEnergyAlongExhaustion_beta_zero G Λ J h n (hne n)
  rw [hconst]
  exact Filter.limsup_const (Real.log 2)

/-! ## J = h = 0 closed form along exhaustion -/

/-- **Along-exhaustion J=h=0 closed form**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ` and any `β`,
`freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n = log 2`.

Specialization of `IsingModel.freeEnergy_zero_params` via `change` +
definitional unfolding of `freeEnergyAlongExhaustion` through
`freeEnergyΛ` to `IsingModel.freeEnergy (inducedGraph …)`. -/
theorem freeEnergyAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2
  exact IsingModel.freeEnergy_zero_params _ β (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Infinite-volume J=h=0 closed form**:
under `∀ n, (Λ.volume n).Nonempty`, `freeEnergyInfinite G Λ ⟨0, 0, β⟩ = log 2`
for any `β, G, Λ`.

The sequence `n ↦ freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n` is constantly
`log 2` by `freeEnergyAlongExhaustion_zero_params`, so its `limsup` on
`atTop` is `log 2` by `Filter.limsup_const`.

Companion to `freeEnergyInfinite_beta_zero`: both give the
maximum-entropy value `log 2` from orthogonal degeneracies
(β=0 vs. H ≡ 0).

A weakened version requiring only `∀ᶠ n in atTop, (Λ.volume n).Nonempty`
is provided as `freeEnergyInfinite_zero_params_of_eventually_nonempty`
in `AmbientLatticeSum.lean`. -/
theorem freeEnergyInfinite_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergyInfinite
  have hconst : freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = fun _ : ℕ => Real.log 2 := by
    funext n
    exact freeEnergyAlongExhaustion_zero_params G Λ β n (hne n)
  rw [hconst]
  exact Filter.limsup_const (Real.log 2)

/-! ## J = 0 closed form along exhaustion (graph-independent) -/

/-- **Along-exhaustion J=0 graph-independence**:
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n
  = freeEnergyAlongExhaustion ⊥ Λ ⟨0, h, β⟩ n`
for any `n`, any `G, Λ`, any `h, β` (no nonempty hypothesis).

Lift of `IsingModel.freeEnergy_eq_bot_at_J_zero` (PR #175) through
the definitional unfolding
`freeEnergyAlongExhaustion = freeEnergy (inducedGraph …)`:
apply the base identity on both sides to reduce to the same
`freeEnergy_bot` expression. -/
theorem freeEnergyAlongExhaustion_eq_bot_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (⊥ : SimpleGraph V) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))
          (⟨0, h, β⟩ : IsingParams ℝ)
  rw [IsingModel.freeEnergy_eq_bot_at_J_zero (inducedGraph G (Λ.volume n)),
      IsingModel.freeEnergy_eq_bot_at_J_zero
        (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))]

/-- **Along-exhaustion J=0 closed form (graph-independent)**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ` and any `h, β`,
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n = log (2·cosh(β·h))`.

Specialization of `IsingModel.freeEnergy_J_zero` via `change` +
definitional unfolding. -/
theorem freeEnergyAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  exact IsingModel.freeEnergy_J_zero _ h β (Finset.Nonempty.fintype_card_coe_pos hne)

/-! ## β = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion β=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨J, h, 0⟩ n = 2 ^ |Λ.volume n|`
for any `J, h` and any ambient graph `G, Λ`.

Specialization of `IsingModel.partitionFunction_beta_zero` (every
Boltzmann weight collapses to `exp 0 = 1`) with
`card_config_eq_two_pow` and `Fintype.card_coe`. -/
theorem partitionFunctionAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨J, h, 0⟩ : IsingParams ℝ) = (2 : ℝ) ^ (Λ.volume n).card
  rw [IsingModel.partitionFunction_beta_zero, IsingModel.card_config_eq_two_pow,
      Fintype.card_coe]
  push_cast
  rfl

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨J, h, 0⟩ n)
= |Λ.volume n| · log 2`. Follows from
`partitionFunctionAlongExhaustion_beta_zero` via `Real.log_pow`. -/
theorem log_partitionFunctionAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 := by
  rw [partitionFunctionAlongExhaustion_beta_zero, Real.log_pow]

/-! ## J = h = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion J=h=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n = 2 ^ |Λ.volume n|`
for any ambient graph `G, Λ` and any `β`.

Specialization of `IsingModel.partitionFunction_zero_params`
(`Z_G ⟨0,0,β⟩ = Fintype.card (Config ι)`) with `card_config_eq_two_pow`
(`|Config ι| = 2^|ι|`) and `Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem partitionFunctionAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨0, 0, β⟩ : IsingParams ℝ) = (2 : ℝ) ^ (Λ.volume n).card
  rw [IsingModel.partitionFunction_zero_params, IsingModel.card_config_eq_two_pow,
      Fintype.card_coe]
  push_cast
  rfl

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n)
= |Λ.volume n| · log 2`. Follows from
`partitionFunctionAlongExhaustion_zero_params` via `Real.log_pow`. -/
theorem log_partitionFunctionAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 := by
  rw [partitionFunctionAlongExhaustion_zero_params, Real.log_pow]

/-! ## J = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion J=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n = (2·cosh(β·h))^|Λ.volume n|`
for any `h, β` and any ambient graph `G, Λ`.

Specialization of `IsingModel.partitionFunction_J_zero`
(`Z_G ⟨0, h, β⟩ = (2·cosh(β·h))^|ι|`, graph-independent) with
`Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  rw [IsingModel.partitionFunction_J_zero, Fintype.card_coe]

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n)
= |Λ.volume n| · log (2·cosh(β·h))`. Follows from
`partitionFunctionAlongExhaustion_J_zero` via `Real.log_pow`
(`2·cosh(β·h) > 0`). -/
theorem log_partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log (2 * Real.cosh (β * h)) := by
  rw [partitionFunctionAlongExhaustion_J_zero, Real.log_pow]

/-! ## Free-spin identity for induced subgraph -/

omit [DecidableEq V] in
/-- **Induced subgraph of the empty graph is empty**:
`inducedGraph (⊥ : SimpleGraph V) Λ = ⊥`.

`inducedGraph = induce = comap` and `SimpleGraph.comap_bot`.
Useful rewrite when the ambient graph is `⊥` (free-spin limit). -/
@[simp]
theorem inducedGraph_bot (Λ : Finset V) :
    inducedGraph (⊥ : SimpleGraph V) Λ = (⊥ : SimpleGraph (↑Λ : Type _)) :=
  SimpleGraph.comap_bot _

/-! ## h-symmetry / `|h|`-monotonicity along exhaustion

Specializations of `IsingModel.freeEnergy_neg_h`, `freeEnergy_eq_abs_h`,
and `freeEnergy_monotone_abs_h` (PRs #126–#127) to each stage of the
exhaustion, via the `change` + definitional-unfolding pattern already
used in this file. -/

/-- **Along-exhaustion partition-function h-evenness**:
`partitionFunctionAlongExhaustion G Λ ⟨J, -h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n`. Per-stage lift of
`IsingModel.partitionFunction_neg_h` via the flip involution. -/
theorem partitionFunctionAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_neg_h G (Λ.volume n) J h β

/-- **Along-exhaustion partition-function `|h|`-rewrite**:
`partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. Per-stage lift of
`partitionFunctionΛ_eq_abs_h`. -/
theorem partitionFunctionAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_eq_abs_h G (Λ.volume n) J h β

/-- **Along-exhaustion ferromagnetic `|h|`-monotonicity of partition
function**: for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`partitionFunctionAlongExhaustion G Λ ⟨J, h₁, β⟩ n ≤
partitionFunctionAlongExhaustion G Λ ⟨J, h₂, β⟩ n`. Per-stage lift of
`partitionFunctionΛ_monotone_abs_h`. -/
theorem partitionFunctionAlongExhaustion_monotone_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_monotone_abs_h G (Λ.volume n) J β hJ hβ hh

/-- **Along-exhaustion h-evenness**:
`freeEnergyAlongExhaustion G Λ ⟨J, -h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, -h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, h, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_neg_h _ J h β

/-- **Along-exhaustion `|h|`-rewrite**:
`freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, |h|, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_eq_abs_h _ J h β

/-- **Along-exhaustion ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0` and any real `h₁, h₂` with `|h₁| ≤ |h₂|`,
`freeEnergyAlongExhaustion G Λ ⟨J, h₁, β⟩ n ≤ freeEnergyAlongExhaustion G Λ ⟨J, h₂, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_monotone_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h₁, β⟩ : IsingParams ℝ)
    ≤ IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, h₂, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_monotone_abs_h _ J β hJ hβ hh

/-- **BddAbove for `freeEnergyAlongExhaustion` under bounded edge density**:
assuming `BoundedEdgeDensity G Λ`, the range of the exhaustion free energy
is bounded above.

For nonempty stages the bound is `log 2 + |β|·(|J|·c + |h|)` by the
uniform upper bound above; for empty stages the value is
`(Fintype.card ∅)⁻¹ · log 1 = 0`, which is at most the same constant
(after taking its `max` with `0`). -/
theorem BddAbove_freeEnergyAlongExhaustion_range
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion G Λ p)) := by
  obtain ⟨c, hc⟩ := hBED
  refine ⟨max 0 (Real.log 2 + |p.β| * (|p.J| * c + |p.h|)), ?_⟩
  rintro y ⟨n, rfl⟩
  by_cases hne : (Λ.volume n).Nonempty
  · exact le_max_of_le_right
      (freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ p hc n hne)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hcard : Fintype.card (↑(Λ.volume n) : Type _) = 0 := by
      rw [Fintype.card_coe, hne]; rfl
    have hfe : freeEnergyAlongExhaustion G Λ p n = 0 := by
      change IsingModel.freeEnergy (inducedGraph G (Λ.volume n)) p = 0
      unfold IsingModel.freeEnergy
      rw [hcard, Nat.cast_zero, inv_zero, zero_mul]
    rw [hfe]; exact le_max_left _ _

/-! ## Critical exponents at ∞-volume (GJ §17.7 Thm 17.7.1)

Explicit ∞-vol named aliases for the critical-exponent bounds
`η ≥ 0` and `ζ ≥ 0`, matching the finite-volume
`IsingModel.eta_nonneg_finite_vol` / `zeta_nonneg_finite_vol`
pattern. Direct pass-throughs of `truncated2Infinite_nonneg` (GKS-II
at ∞-vol) and `truncated4Infinite_nonpos_h_zero` (Cor 4.3.3 at ∞-vol). -/

/-- **η ≥ 0 at ∞-volume** (GJ §17.7 Thm 17.7.1, ∞-vol lattice version).
Explicit alias of `truncated2Infinite_nonneg` matching the
`eta_nonneg_finite_vol` naming convention. -/
theorem eta_nonneg_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    0 ≤ truncated2Infinite G Λ p i j :=
  truncated2Infinite_nonneg G Λ p hf i j

/-- **ζ ≥ 0 at ∞-volume** (GJ §17.7 Thm 17.7.1, ∞-vol lattice version,
at `h = 0`). Explicit alias of `truncated4Infinite_nonpos_h_zero` —
`U₄^∞ ≤ 0` for pairwise-distinct sites at `h = 0`. -/
theorem zeta_nonneg_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero G Λ J β hf hij hik hil hjk hjl hkl

/-- **Absence of even bound states — ∞-volume lattice** (Glimm–Jaffe
§17.2, pp. 311–313). ∞-vol version of
`IsingModel.absence_of_even_bound_states_finite_vol`:
`U₄^∞(i,j,k,l) ≤ 0` for ferromagnetic `⟨J, 0, β⟩` and pairwise-distinct
sites. Explicit alias of `truncated4Infinite_nonpos_h_zero`. -/
theorem absence_of_even_bound_states_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero G Λ J β hf hij hik hil hjk hjl hkl

end Ambient
end IsingModel

