import IsingModel.Conditioning.HighTempClosed.ClosedForm
import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxScreening

/-!
# `+`-boundary high-temperature representation (FV §3.7.3, eqs. 3.41–3.45)

The high-temperature (random-graph) representation of the `+`-boundary partition
function and one-point function, towards the high-temperature vanishing
`m*(β) = 0` (Issue #3613). This is the boundary-condition analogue of the free-state
representation already established in `Conditioning/HighTempClosed/ClosedForm.lean`.

The new ingredient relative to the free state is the **pinned-boundary parity
collapse**: the `+`-state sums only over configurations agreeing with the boundary
condition off the volume `Λ`, so the per-vertex parity argument of FV (3.44) runs
over the interior vertices only.

* `boltzmannWeight_h_zero_prod` — the per-configuration product form (FV (3.42)).
* `boltzmannWeightBC_h_zero_prod_of_agrees` — the boundary-condition analogue on
  agreeing configurations.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eqs. (3.41)–(3.45), pp. 116–117.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Per-configuration high-temperature product form at zero field** (FV (3.42)):
`e^{-βH} = (cosh βJ)^{|E|} ∏_{e}(1 + tanh(βJ)·σ_iσ_j)` for each configuration `σ`.
The per-configuration identity underlying `partitionFunction_high_temp_expansion_h_zero`,
isolated here for use in the boundary-condition setting. -/
theorem boltzmannWeight_h_zero_prod (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (σ : Config ι) :
    boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) σ =
      Real.cosh (β * J) ^ G.edgeFinset.card *
        ∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e) := by
  unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
  have hsum : (-β : ℝ) * (-J * ∑ e ∈ G.edgeFinset, edgeSpin σ e + -(0 : ℝ) *
        ∑ i : ι, Spin.sign ℝ (σ i))
      = ∑ e ∈ G.edgeFinset, β * J * edgeSpin σ e := by
    rw [show (-β : ℝ) * (-J * ∑ e ∈ G.edgeFinset, edgeSpin σ e + -(0 : ℝ) *
          ∑ i : ι, Spin.sign ℝ (σ i))
        = (β * J) * ∑ e ∈ G.edgeFinset, edgeSpin σ e from by ring, Finset.mul_sum]
  rw [hsum, Real.exp_sum]
  have hedge : ∀ e ∈ G.edgeFinset,
      Real.exp (β * J * edgeSpin σ e) =
        Real.cosh (β * J) * (1 + Real.tanh (β * J) * edgeSpin σ e) := by
    intro e _
    rw [exp_edgeSpin_decomp, Real.tanh_eq_sinh_div_cosh]
    have hcosh_ne : Real.cosh (β * J) ≠ 0 := (Real.cosh_pos _).ne'
    field_simp
  rw [Finset.prod_congr rfl hedge, Finset.prod_mul_distrib, Finset.prod_const]

omit [DecidableEq ι] in
/-- **Boundary-condition per-configuration product form** (FV (3.42), `+` state):
for a configuration `σ` agreeing with the boundary condition `η` off `Λ`, the
boundary-condition Boltzmann weight at zero field equals the high-temperature product
form. Off the agreeing set the weight is `0` (`boltzmannWeightBC_of_not_agrees`). -/
theorem boltzmannWeightBC_h_zero_prod_of_agrees (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) {Λ : Finset ι} {η σ : Config ι} (hσ : agreesOff Λ η σ) :
    boltzmannWeightBC G β (fun _ => J) 0 Λ η σ =
      Real.cosh (β * J) ^ G.edgeFinset.card *
        ∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e) := by
  rw [boltzmannWeightBC_of_agrees G β (fun _ => J) 0 hσ, boltzmannWeightJ_uniform_eq,
    boltzmannWeight_h_zero_prod]

/-- **Pinned-boundary parity collapse** (FV (3.44), `+` boundary): summing the
per-vertex spin monomial `∏_v (σ_v)^{k_v}` over configurations agreeing with the
all-`+` boundary `η = plusConfig` off `Λ` collapses to `2^{|Λ|}` exactly when every
**interior** vertex `v ∈ Λ` has even exponent `k_v` (exterior factors are pinned to
`+1`, hence contribute `1` regardless of parity), and to `0` otherwise. The boundary
analogue of `sum_prod_toSign_pow_real`, with the parity condition restricted to the
interior `Λ`. -/
theorem sum_indicator_agreesOff_plus_prod_pow (Λ : Finset ι) (k : ι → ℕ) :
    (∑ σ : Config ι, Set.indicator {σ : Config ι | agreesOff Λ (plusConfig ι) σ}
        (fun σ => ∏ v : ι, ((σ v).toSign : ℝ) ^ (k v)) σ)
      = if (∀ v ∈ Λ, Even (k v)) then (2 : ℝ) ^ Λ.card else 0 := by
  classical
  -- Step 1: rewrite each indicator summand as a per-vertex product, the boundary
  -- restriction becoming a pinning factor `[σ_v = +1]` on the exterior vertices.
  have hpoint : ∀ σ : Config ι,
      Set.indicator {σ : Config ι | agreesOff Λ (plusConfig ι) σ}
        (fun σ => ∏ v : ι, ((σ v).toSign : ℝ) ^ (k v)) σ
        = ∏ v : ι, (((σ v).toSign : ℝ) ^ (k v) *
            (if v ∈ Λ then 1 else (if σ v = Spin.up then 1 else 0))) := by
    intro σ
    rw [Finset.prod_mul_distrib]
    have hcond : (∏ v : ι, (if v ∈ Λ then (1 : ℝ) else (if σ v = Spin.up then 1 else 0)))
        = if agreesOff Λ (plusConfig ι) σ then (1 : ℝ) else 0 := by
      by_cases hall : agreesOff Λ (plusConfig ι) σ
      · rw [if_pos hall]
        refine Finset.prod_eq_one (fun v _ => ?_)
        by_cases hv : v ∈ Λ
        · rw [if_pos hv]
        · rw [if_neg hv, if_pos (show σ v = Spin.up from hall v hv)]
      · rw [if_neg hall]
        rw [agreesOff] at hall
        push Not at hall
        obtain ⟨j, hj, hjne⟩ := hall
        exact Finset.prod_eq_zero (Finset.mem_univ j)
          (by rw [if_neg hj, if_neg (show ¬ σ j = Spin.up from hjne)])
    rw [hcond]
    by_cases hall : agreesOff Λ (plusConfig ι) σ
    · rw [Set.indicator_of_mem hall, if_pos hall, mul_one]
    · rw [Set.indicator_of_notMem hall, if_neg hall, mul_zero]
  simp_rw [hpoint]
  -- Step 2: Fubini over the product config space.
  have hfub : (∑ σ : Config ι, ∏ v : ι, (((σ v).toSign : ℝ) ^ (k v) *
        (if v ∈ Λ then 1 else (if σ v = Spin.up then 1 else 0))))
      = ∏ v : ι, ∑ s : Spin, (((s.toSign : ℝ) ^ (k v) *
        (if v ∈ Λ then 1 else (if s = Spin.up then 1 else 0)))) :=
    (Fintype.prod_sum (κ := fun _ : ι => Spin)
      (fun v s => ((s.toSign : ℝ) ^ (k v) *
        (if v ∈ Λ then 1 else (if s = Spin.up then 1 else 0))))).symm
  rw [hfub]
  -- Step 3: evaluate the inner single-spin sum per vertex.
  have hup : ((Spin.up.toSign : ℤ) : ℝ) = 1 := by simp [Spin.toSign]
  have hdown : ((Spin.down.toSign : ℤ) : ℝ) = -1 := by simp [Spin.toSign]
  have hinner : ∀ v : ι, (∑ s : Spin, ((s.toSign : ℝ) ^ (k v) *
        (if v ∈ Λ then 1 else (if s = Spin.up then 1 else 0))))
      = if v ∈ Λ then (if Even (k v) then (2 : ℝ) else 0) else 1 := by
    intro v
    rw [show (Finset.univ : Finset Spin) = {Spin.up, Spin.down} from by decide,
      Finset.sum_pair (by decide : Spin.up ≠ Spin.down), hup, hdown, one_pow]
    by_cases hv : v ∈ Λ
    · simp only [if_pos hv, mul_one]
      rcases Nat.even_or_odd (k v) with hk | hk
      · rw [if_pos hk, hk.neg_one_pow]; norm_num
      · rw [if_neg (by simpa using hk), hk.neg_one_pow]; norm_num
    · simp [if_neg hv]
  simp_rw [hinner]
  -- Step 4: the exterior factors are `1`; collapse to a product over `Λ`.
  rw [Finset.prod_ite_mem, Finset.univ_inter]
  -- Step 5: parity over `Λ`.
  by_cases hev : ∀ v ∈ Λ, Even (k v)
  · rw [if_pos hev]
    rw [Finset.prod_congr rfl (fun v hv => if_pos (hev v hv)), Finset.prod_const]
  · rw [if_neg hev]
    push Not at hev
    obtain ⟨j, hj, hjodd⟩ := hev
    exact Finset.prod_eq_zero hj (if_neg hjodd)

omit [DecidableEq ι] in
/-- The `+`-boundary Boltzmann weight at zero field is the agreement-indicator of the
ordinary Boltzmann weight `e^{-βH}`. -/
theorem boltzmannWeightBC_plus_eq_indicator (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (Λ : Finset ι) (σ : Config ι) :
    boltzmannWeightBC G β (fun _ => J) 0 Λ (plusConfig ι) σ
      = Set.indicator {σ : Config ι | agreesOff Λ (plusConfig ι) σ}
          (boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ)) σ := by
  by_cases hσ : agreesOff Λ (plusConfig ι) σ
  · rw [boltzmannWeightBC_of_agrees G β (fun _ => J) 0 hσ, boltzmannWeightJ_uniform_eq,
      Set.indicator_of_mem hσ]
  · rw [boltzmannWeightBC_of_not_agrees G β (fun _ => J) 0 hσ, Set.indicator_of_notMem hσ]

/-- **`+`-boundary partition function high-temperature representation** (FV (3.45),
`+` state): `Z⁺_Λ = 2^{|Λ|}·(cosh βJ)^{|E|}·∑_{X ⊆ E, even on Λ} (tanh βJ)^{|X|}`, the
sum running over subgraphs `X` of `G` with even degree at every **interior** vertex
`v ∈ Λ`. The boundary-condition analogue of
`partitionFunction_high_temp_expansion_h_zero_closed`, with the parity condition
restricted to `Λ` via `sum_indicator_agreesOff_plus_prod_pow`. -/
theorem partitionFunctionBC_plus_h_zero_closed (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (Λ : Finset ι) :
    partitionFunctionBC G β (fun _ => J) 0 Λ (plusConfig ι)
      = (2 : ℝ) ^ Λ.card * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v ∈ Λ, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card := by
  classical
  unfold partitionFunctionBC
  simp_rw [boltzmannWeightBC_plus_eq_indicator G J β Λ]
  -- expand each edge product into a subset sum, pulling the `tanh^|X|` factor out
  have hexpand : ∀ σ : Config ι,
      Set.indicator {σ : Config ι | agreesOff Λ (plusConfig ι) σ}
        (boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ)) σ
        = Real.cosh (β * J) ^ G.edgeFinset.card *
          ∑ X ∈ G.edgeFinset.powerset, Real.tanh (β * J) ^ X.card *
            Set.indicator {σ : Config ι | agreesOff Λ (plusConfig ι) σ}
              (fun σ => ∏ e ∈ X, edgeSpin (K := ℝ) σ e) σ := by
    intro σ
    by_cases hσ : agreesOff Λ (plusConfig ι) σ
    · rw [Set.indicator_of_mem hσ, boltzmannWeight_h_zero_prod G J β σ,
        Finset.prod_one_add G.edgeFinset]
      refine congrArg _ (Finset.sum_congr rfl (fun X _ => ?_))
      rw [Set.indicator_of_mem hσ, Finset.prod_mul_distrib, Finset.prod_const]
    · rw [Set.indicator_of_notMem hσ]
      refine (mul_eq_zero.mpr (Or.inr ?_)).symm
      exact Finset.sum_eq_zero (fun X _ => by
        rw [Set.indicator_of_notMem hσ, mul_zero])
  simp_rw [hexpand]
  rw [← Finset.mul_sum, Finset.sum_comm]
  -- collapse the σ-sum by the pinned-boundary parity lemma
  have hpar : ∀ X ∈ G.edgeFinset.powerset,
      (∑ σ : Config ι, Real.tanh (β * J) ^ X.card *
          Set.indicator {σ : Config ι | agreesOff Λ (plusConfig ι) σ}
            (fun σ => ∏ e ∈ X, edgeSpin (K := ℝ) σ e) σ)
        = Real.tanh (β * J) ^ X.card *
            (if (∀ v ∈ Λ, Even ((X.filter (v ∈ ·)).card))
              then (2 : ℝ) ^ Λ.card else 0) := by
    intro X hX
    rw [← Finset.mul_sum]
    congr 1
    rw [← sum_indicator_agreesOff_plus_prod_pow Λ (fun v => (X.filter (v ∈ ·)).card)]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    by_cases hσ : agreesOff Λ (plusConfig ι) σ
    · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem hσ,
        prod_edgeSpin_eq_prod_pow_filter_card G X (Finset.mem_powerset.mp hX)]
    · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem hσ]
  rw [Finset.sum_congr rfl hpar]
  -- redistribute `2^|Λ|` and collapse to the filtered even-on-`Λ` sum
  have hdist : ∀ X : Finset (Sym2 ι),
      Real.tanh (β * J) ^ X.card *
          (if (∀ v ∈ Λ, Even ((X.filter (v ∈ ·)).card)) then (2 : ℝ) ^ Λ.card else 0)
        = (if (∀ v ∈ Λ, Even ((X.filter (v ∈ ·)).card))
            then (2 : ℝ) ^ Λ.card * Real.tanh (β * J) ^ X.card else 0) := by
    intro X
    by_cases h : ∀ v ∈ Λ, Even ((X.filter (v ∈ ·)).card)
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  simp_rw [hdist]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  ring

end IsingModel
