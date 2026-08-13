import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.PosAndAntitone

/-!
# Lattice mass at high temperature split — Step 113 J-lower bound on the two-point function

Part of the split high-temperature lattice-mass layer (Issue #1850).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## §17.5 J-lower bound on the two-point function (Step 113) -/

/-- Spin sign of a product: `sign(a.mul b) = sign(a) * sign(b)` over ℝ. -/
private lemma Spin.sign_mul_ℝ (a b : Spin) :
    Spin.sign ℝ (a.mul b) = Spin.sign ℝ a * Spin.sign ℝ b := by
  simp [Spin.sign, Spin.toSign_mul, Int.cast_mul]

/-- Sum over all `Config ι` of `f(σ i)` equals `(∑ a, f a) * 2 ^ (Fintype.card ι - 1)`.

Proof: express `f(σ i) = ∏_k (if k = i then f(σ k) else 1)` via
`Finset.prod_ite_eq'`, then apply `Finset.sum_prod_piFinset` to
interchange the Config-sum with a product over sites.  The `i`-th
factor yields `∑ a, f a`; each `k ≠ i` factor yields `∑ a : Spin, 1 = 2`. -/
private lemma sum_config_apply_eq_mul_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : Spin → ℝ) :
    ∑ σ : Config ι, f (σ i) = (∑ a : Spin, f a) * 2 ^ (Fintype.card ι - 1) := by
  have hprod : ∀ σ : Config ι, f (σ i) = ∏ k : ι, (if k = i then f (σ k) else (1 : ℝ)) := by
    intro σ
    simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  simp_rw [hprod]
  rw [show ∑ σ : Config ι, ∏ k : ι, (if k = i then f (σ k) else (1 : ℝ))
      = ∑ σ ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Spin)),
          ∏ k : ι, (if k = i then f (σ k) else (1 : ℝ)) from by
        rw [Fintype.piFinset_univ]]
  rw [Finset.sum_prod_piFinset (Finset.univ : Finset Spin)
      (fun k a => if k = i then f a else 1)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · rw [show ∏ k ∈ (Finset.univ : Finset ι).erase i,
            ∑ a ∈ (Finset.univ : Finset Spin), (if k = i then f a else (1 : ℝ))
        = ∏ _ ∈ (Finset.univ : Finset ι).erase i, (2 : ℝ) from
      Finset.prod_congr rfl fun k hk => by
        have hki : k ≠ i := (Finset.mem_erase.mp hk).1
        simp only [if_neg hki, Finset.sum_const, Finset.card_univ, card_spin,
                   Nat.smul_one_eq_cast, Nat.cast_ofNat]]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]

/-- **Single-edge correlation at `h = 0`**: for a graph `G` with exactly one edge `{i, j}`
and external field `h = 0`, the two-point correlation equals `tanh(β J)`.

Proof: the bijection `φ(σ)(i) = σ i · σ j`, `φ(σ)(j) = σ i` transforms the edge
coupling `J · σ_i · σ_j` into a site field `J · σ_i`, so after the change of variables
both the numerator `∑ sign(σ i) exp(βJ sign(σ i))` and the denominator `∑ exp(βJ sign(σ i))`
factor via `sum_config_apply_eq_mul_pow`; the common `2^(|ι|−1)` cancels, yielding `tanh`. -/
private lemma correlation_singleEdge_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {i j : ι} (hij : i ≠ j)
    (hG : G.edgeFinset = ({Sym2.mk i j} : Finset (Sym2 ι)))
    (J β : ℝ) :
    IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      = Real.tanh (β * J) := by
  -- Bijection φ: (σ i, σ j, rest) ↦ (σ i · σ j, σ i, rest)
  let φ_fun : Config ι → Config ι := fun σ x =>
    if x = i then (σ i).mul (σ j) else if x = j then σ i else σ x
  let φ_inv : Config ι → Config ι := fun τ x =>
    if x = i then τ j else if x = j then (τ j).mul (τ i) else τ x
  have hφ_linv : Function.LeftInverse φ_inv φ_fun := fun σ => by
    ext x
    by_cases h1 : x = i
    · subst h1; simp [φ_fun, φ_inv, Ne.symm hij]
    · by_cases h2 : x = j
      · subst h2; simp [φ_fun, φ_inv, h1, Spin.mul_mul_cancel]
      · simp [φ_fun, φ_inv, h1, h2]
  have hφ_rinv : Function.RightInverse φ_inv φ_fun := fun τ => by
    ext x
    by_cases h1 : x = i
    · subst h1; simp [φ_fun, φ_inv, Ne.symm hij, Spin.mul_mul_cancel]
    · by_cases h2 : x = j
      · subst h2; simp [φ_fun, φ_inv, h1]
      · simp [φ_fun, φ_inv, h1, h2]
  let φ : Config ι ≃ Config ι := ⟨φ_fun, φ_inv, hφ_linv, hφ_rinv⟩
  -- Hamiltonian: H(σ) = -J · sign(σ i) · sign(σ j) when edgeFinset = {Sym2.mk i j}
  have hH : ∀ σ : Config ι,
      hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
        = -J * (Spin.sign ℝ (σ i) * Spin.sign ℝ (σ j)) := by
    intro σ
    unfold hamiltonian interactionEnergy externalFieldEnergy
    simp only [neg_zero]
    rw [hG, Finset.sum_singleton]
    simp [edgeSpin, Sym2.lift_mk]
  -- Boltzmann weight after φ_inv: exp(β J sign(τ i))
  have hbw : ∀ τ : Config ι,
      boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) (φ_inv τ)
        = Real.exp (β * J * Spin.sign ℝ (τ i)) := fun τ => by
    unfold boltzmannWeight
    rw [hH (φ_inv τ)]
    have hi : φ_inv τ i = τ j := by simp [φ_inv]
    have hj : φ_inv τ j = (τ j).mul (τ i) := by simp [φ_inv, Ne.symm hij]
    rw [hi, hj]
    have key : Spin.sign ℝ (τ j) * Spin.sign ℝ ((τ j).mul (τ i)) = Spin.sign ℝ (τ i) := by
      rw [← Spin.sign_mul_ℝ, Spin.mul_mul_cancel]
    simp only [key]; congr 1; ring
  -- spinProduct {i,j} after φ_inv: sign(τ i)
  have hsp : ∀ τ : Config ι,
      spinProduct ({i, j} : Finset ι) (φ_inv τ) = Spin.sign ℝ (τ i) := fun τ => by
    unfold spinProduct
    rw [Finset.prod_pair hij]
    have hi : φ_inv τ i = τ j := by simp [φ_inv]
    have hj : φ_inv τ j = (τ j).mul (τ i) := by simp [φ_inv, Ne.symm hij]
    rw [hi, hj]
    change Spin.sign ℝ (τ j) * Spin.sign ℝ ((τ j).mul (τ i)) = Spin.sign ℝ (τ i)
    rw [← Spin.sign_mul_ℝ, Spin.mul_mul_cancel]
  -- Partition function via bijection + factorization
  have hZ : ∑ σ : Config ι, boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) σ =
      (∑ a : Spin, Real.exp (β * J * Spin.sign ℝ a)) * 2 ^ (Fintype.card ι - 1) := by
    rw [Fintype.sum_equiv φ (fun σ => boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) σ)
        (fun τ => Real.exp (β * J * Spin.sign ℝ (τ i)))
        (fun σ => by
          have h := hbw (φ σ)
          rw [show φ_inv (φ σ) = σ from hφ_linv σ] at h; exact h)]
    exact sum_config_apply_eq_mul_pow i (fun a => Real.exp (β * J * Spin.sign ℝ a))
  -- Numerator via bijection + factorization
  have hN : ∑ σ : Config ι, spinProduct ({i, j} : Finset ι) σ *
      boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) σ =
      (∑ a : Spin, Spin.sign ℝ a * Real.exp (β * J * Spin.sign ℝ a)) *
        2 ^ (Fintype.card ι - 1) := by
    rw [Fintype.sum_equiv φ
        (fun σ => spinProduct ({i, j} : Finset ι) σ *
            boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) σ)
        (fun τ => Spin.sign ℝ (τ i) * Real.exp (β * J * Spin.sign ℝ (τ i)))
        (fun σ => by
          have hs := hsp (φ σ)
          rw [show φ_inv (φ σ) = σ from hφ_linv σ] at hs
          have hb := hbw (φ σ)
          rw [show φ_inv (φ σ) = σ from hφ_linv σ] at hb
          simp only []
          rw [hs, hb])]
    exact sum_config_apply_eq_mul_pow i
      (fun a => Spin.sign ℝ a * Real.exp (β * J * Spin.sign ℝ a))
  -- Assemble: correlation = N / Z = tanh(βJ)
  unfold correlation gibbsExpectation partitionFunction
  rw [hZ, hN, sum_exp_spin_sign β J, sum_spin_sign_exp_sign β J]
  have h2pow_ne : (2 : ℝ) ^ (Fintype.card ι - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcosh_ne : Real.cosh (β * J) ≠ 0 := (Real.cosh_pos (β * J)).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hcosh_ne, h2pow_ne]

/-- The edgeFinset of `inducedGraph (fromEdgeSet {Sym2.mk 0 r}) Λn` is the singleton
`{Sym2.mk ⟨0,h0n⟩ ⟨r,hrn⟩}` whenever `0, r ∈ Λn` and `0 ≠ r`. -/
private lemma inducedSingleEdge_edgeFinset (d : ℕ)
    {r : Fin d → ℤ} (hr_ne : (0 : Fin d → ℤ) ≠ r)
    {Λn : Finset (Fin d → ℤ)} (h0n : (0 : Fin d → ℤ) ∈ Λn) (hrn : r ∈ Λn)
    [Fintype (inducedGraph (SimpleGraph.fromEdgeSet {Sym2.mk (0 : Fin d → ℤ) r}) Λn).edgeSet] :
    (inducedGraph (SimpleGraph.fromEdgeSet {Sym2.mk (0 : Fin d → ℤ) r}) Λn).edgeFinset
      = ({Sym2.mk (⟨0, h0n⟩ : ↑Λn) (⟨r, hrn⟩ : ↑Λn)} : Finset (Sym2 ↑Λn)) := by
  have hG_adj : ∀ (u v : ↑Λn),
      (inducedGraph (SimpleGraph.fromEdgeSet {Sym2.mk (0 : Fin d → ℤ) r}) Λn).Adj u v
        ↔ (Sym2.mk (u : Fin d → ℤ) v = Sym2.mk 0 r) ∧ (u : Fin d → ℤ) ≠ v := by
    intros u v
    simp only [inducedGraph_apply, SimpleGraph.induce_adj, SimpleGraph.fromEdgeSet_adj,
               Set.mem_singleton_iff]
  apply Finset.ext
  intro e
  rw [SimpleGraph.mem_edgeFinset, Finset.mem_singleton]
  refine Sym2.ind (fun u v => ?_) e
  rw [SimpleGraph.mem_edgeSet, hG_adj, Sym2.eq_iff]
  constructor
  · -- mp: (↑u=0 ∧ ↑v=r ∨ ↑u=r ∧ ↑v=0) ∧ ↑u≠↑v → s(u,v) = s(⟨0⟩,⟨r⟩)
    intro ⟨hmem, _⟩
    rw [Sym2.eq_iff]
    rcases hmem with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inl ⟨Subtype.ext hu, Subtype.ext hv⟩
    · exact Or.inr ⟨Subtype.ext hu, Subtype.ext hv⟩
  · -- mpr: s(u,v) = s(⟨0⟩,⟨r⟩) → (↑u=0 ∧ ↑v=r ∨ ↑u=r ∧ ↑v=0) ∧ ↑u≠↑v
    intro he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have h1 : (↑u : Fin d → ℤ) = 0 := congr_arg Subtype.val hu
      have h2 : (↑v : Fin d → ℤ) = r := congr_arg Subtype.val hv
      exact ⟨Or.inl ⟨h1, h2⟩, fun heq => hr_ne (h1 ▸ h2 ▸ heq)⟩
    · have h1 : (↑u : Fin d → ℤ) = r := congr_arg Subtype.val hu
      have h2 : (↑v : Fin d → ℤ) = 0 := congr_arg Subtype.val hv
      exact ⟨Or.inr ⟨h1, h2⟩, fun heq => hr_ne.symm (h2 ▸ h1 ▸ heq)⟩

/-- **J-lower bound on the two-point function** (GJ §17.1 pp. 304–306):
for adjacent `r` in `latticeGraph d`, ferromagnetic `J ≥ 0`, `β > 0`, `h = 0`:

`tanh(β J) ≤ twoPointFunction d ⟨J, 0, β⟩ r`.

Proof: (1) the single-edge graph `G_single = fromEdgeSet {⟦(0,r)⟧}` satisfies
`G_single ≤ latticeGraph d`; (2) `correlationInfinite G_single = tanh(βJ)` by the
single-edge 2-site computation; (3) apply GKS-II subgraph monotonicity.

Reference: Glimm–Jaffe §17.1 pp. 304–306 (2nd ed.); §4.2 (GKS-II subgraph monotonicity). -/
theorem twoPointFunction_ge_tanh_betaJ_of_adj
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {r : Fin d → ℤ} (hr : (IsingModel.latticeGraph d).Adj 0 r) :
    Real.tanh (β * J) ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) r := by
  -- The ferromagnetic condition
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  -- The single-edge subgraph
  let G_single : SimpleGraph (Fin d → ℤ) :=
    SimpleGraph.fromEdgeSet {Sym2.mk (0 : Fin d → ℤ) r}
  haveI hDecSingle : DecidableRel G_single.Adj := fun u v => by
    simp only [G_single, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
    exact inferInstance
  haveI : ∀ n, Fintype (inducedGraph G_single ((cubicExhaustion d).volume n)).edgeSet :=
    fun n => by
      haveI : DecidableRel (inducedGraph G_single ((cubicExhaustion d).volume n)).Adj :=
        fun ⟨a, _⟩ ⟨b, _⟩ => by unfold inducedGraph SimpleGraph.induce; exact inferInstance
      exact SimpleGraph.fintypeEdgeSet _
  -- G_single ≤ latticeGraph d
  have hG_le : G_single ≤ IsingModel.latticeGraph d := by
    intro u v hadj
    rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at hadj
    obtain ⟨hmem, _⟩ := hadj
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hr
    · exact hr.symm
  -- correlationInfinite G_single (cubicExhaustion d) ⟨J,0,β⟩ {0,r} = tanh(βJ)
  have hcorr : correlationInfinite G_single (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), r}
      = Real.tanh (β * J) := by
    -- The sequence is eventually constant at tanh(βJ)
    have h_event : ∀ᶠ n in Filter.atTop,
        correlationAlongExhaustion G_single (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), r} n
          = Real.tanh (β * J) := by
      obtain ⟨N, hN⟩ := (cubicExhaustion d).exhaust {(0 : Fin d → ℤ), r}
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have hAn : {(0 : Fin d → ℤ), r} ⊆ (cubicExhaustion d).volume n := hN n hn
      have h0n : (0 : Fin d → ℤ) ∈ (cubicExhaustion d).volume n :=
        hAn (Finset.mem_insert_self 0 {r})
      have hrn : r ∈ (cubicExhaustion d).volume n :=
        hAn (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
      have hr_ne : (0 : Fin d → ℤ) ≠ r := hr.ne
      rw [correlationAlongExhaustion_of_subset G_single (cubicExhaustion d) _ hAn,
          correlationΛ_apply]
      -- Rewrite liftFinset to explicit pair to avoid isDefEq timeout on unification
      have hlift : liftFinset {(0 : Fin d → ℤ), r} hAn =
          ({⟨0, h0n⟩, ⟨r, hrn⟩} : Finset (↑((cubicExhaustion d).volume n))) := by
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [hlift]
      exact correlation_singleEdge_h_zero (inducedGraph G_single ((cubicExhaustion d).volume n))
          (by intro heq; exact hr_ne (congr_arg Subtype.val heq))
          (inducedSingleEdge_edgeFinset d hr_ne h0n hrn) J β
    -- The sequence also tends to correlationInfinite (by ferromagnetic monotonicity)
    have h_tendsto := correlationAlongExhaustion_tendsto_ciSup G_single (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) hf {(0 : Fin d → ℤ), r}
    have h_tendsto_const : Filter.Tendsto
        (correlationAlongExhaustion G_single (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), r})
        Filter.atTop (nhds (Real.tanh (β * J))) :=
      tendsto_const_nhds.congr' (h_event.mono (fun _ heq => heq.symm))
    have h_unique : (⨆ n, correlationAlongExhaustion G_single (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), r} n) = Real.tanh (β * J) :=
      tendsto_nhds_unique h_tendsto h_tendsto_const
    simp only [correlationInfinite, h_unique]
  -- Apply subgraph monotonicity
  rw [twoPointFunction_apply, ← hcorr]
  exact correlationInfinite_monotone_ambient_subgraph hG_le (cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) hf {(0 : Fin d → ℤ), r}


end Ambient
end IsingModel
