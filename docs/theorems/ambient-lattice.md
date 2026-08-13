---
layout: default
title: Ambient-lattice theorems
---
[Theorem catalogue](index.html) · [Documentation home](../index.html) · [Current status](../status.html)

## Ambient lattice framework (genuine infinite volume)

`IsingModel/AmbientLattice.lean` introduces the genuine infinite
ambient framework:

| Result | Statement |
|---|---|
| `ConfigOn Λ` | `(↑Λ : Type _) → Spin`, finite-volume configuration type |
| `inducedGraph G Λ` | `SimpleGraph (↑Λ)` induced subgraph |
| `partitionFunctionΛ`, `correlationΛ`, `freeEnergyΛ` | finite-volume objects on `Λ ⊆ V` |
| `partitionFunctionΛ_pos`, `abs_correlationΛ_le_one`, `correlationΛ_le_one`, `correlationΛ_nonneg` | basic properties |
| `Exhaustion V` | structure: monotone `Λₙ` covering any finite set eventually |
| `correlationAlongExhaustion` | correlation along an exhaustion for fixed `A : Finset V` |
| `correlationAlongExhaustion_of_subset` | Unfolding helper: `A ⊆ Λ.volume n ⇒ correlationAlongExhaustion n = correlationΛ (Λ.volume n) (liftFinset A)` |
| `correlationAlongExhaustion_of_not_subset` | Unfolding helper: `A ⊄ Λ.volume n ⇒ correlationAlongExhaustion n = 0` |
| `abs_correlationAlongExhaustion_eventually_le_one` | eventual boundedness |
| `inducedGraph_mono` | `G₁ ≤ G₂ ⇒ G₁.induce Λ ≤ G₂.induce Λ` |
| `partitionFunctionΛ_monotone_ambient_subgraph` | `G₁ ≤ G₂ ⇒ Z_{G₁,Λ} ≤ Z_{G₂,Λ}` |
| `correlationΛ_monotone_ambient_subgraph` | `G₁ ≤ G₂ ⇒ ⟨σ^A⟩_{G₁,Λ} ≤ ⟨σ^A⟩_{G₂,Λ}` |
| `freeEnergyΛ_monotone_ambient_subgraph` | `G₁ ≤ G₂ ⇒ f_{G₁,Λ} ≤ f_{G₂,Λ}` |
| `extendGraphFromΛ₁` | For `Λ₁ ⊆ Λ₂`, graph on `↑Λ₂` with edges only within `Λ₁` |
| `extendGraphFromΛ₁_le_induce` | `extendGraphFromΛ₁ G Λ₁ Λ₂ ≤ inducedGraph G Λ₂` |
| `subtypeIncl` | Canonical injection `↑Λ₁ → ↑Λ₂` when `Λ₁ ⊆ Λ₂` |
| `subtypeIncl_injective` | `subtypeIncl` is injective |
| `restrictConfig` | Restrict `(↑Λ₂ → Spin)` to `(↑Λ₁ → Spin)` |
| `Λ₁subtypeEquiv` | `{x : ↑Λ₂ // x.val ∈ Λ₁} ≃ ↑Λ₁` |
| `configEquivSubtypeProd` | `(↑Λ₂ → Spin) ≃ (↑Λ₁ → Spin) × ({x // x.val ∉ Λ₁} → Spin)` |
| `configEquivSubtypeProd_fst` | First projection = `restrictConfig` |
| `edgeSpin_subtypeIncl` | `edgeSpin σ (Sym2.map subtypeIncl e) = edgeSpin (restrictConfig σ) e` |
| `mem_extendGraph_edgeSet_of_mem_induce` | Induce edge → extendGraph edge (under Sym2.map) |
| `exists_induce_edge_of_extendGraph` | extendGraph edge ← unique induce edge |
| `extendGraph_edgeSum_eq` | `Σ edgeSpin σ` over extendGraph = `Σ edgeSpin (restrictConfig σ)` over G.induce Λ₁ |
| `sum_Λ₁_subtype_eq` | Reindex `Σ f(σ ↑v)` from `{x // x.val ∈ Λ₁}` to `↑Λ₁` with `restrictConfig` |
| `siteSum_partition` | Specialized `Fintype.sum_subtype_add_sum_subtype` for `sign (σ v)` |
| `siteSum_split` | Full split: site sum = Λ₁-part (restrictConfig) + complement-part |
| `hamiltonian_extendGraph_factor` | Hamiltonian on extendGraph = Hamiltonian on G.induce Λ₁ (restrictConfig) + complement site term |
| `boltzmannWeight_extendGraph_factor` | Boltzmann weight on extendGraph = weight on G.induce Λ₁ · exp(βh · complement sign sum) |
| `liftFinset_eq_image_subtypeIncl` | `liftFinset A (hA.trans h12) = (liftFinset A hA).image (subtypeIncl h12)` |
| `spinProduct_lift_eq` | Spin product on ↑Λ₂-lift = spin product on ↑Λ₁-lift under restrictConfig |
| `restrictConfig_configEquivSubtypeProd_symm` | `restrictConfig (equivSymm (σ₁, σ₂)) = σ₁` (content-bearing config factoring identity) |
| `configEquivSubtypeProd_symm_apply_compl` | On complement: `(equivSymm (σ₁, σ₂)) v.val = σ₂ v` |
| `complementFactor` | `F := Σ σ₂, exp(β·h · Σ sign σ₂)` — complement factor for partition function |
| `partitionFunction_extendGraph_factor` | `Z_extend = Z_induceΛ₁ · F` (partition function factoring) |
| `numerator_extendGraph_factor` | `num_extend(lift A) = num_induceΛ₁(lift A) · F` |
| `correlationΛ_extendGraph_eq` | **Correlation equality**: `⟨σ^A⟩_extend = ⟨σ^A⟩_induceΛ₁` (F cancels) |
| **`correlationΛ_monotone_volume`** | **Volume-direction monotonicity main theorem**: `Λ₁ ⊆ Λ₂ ⇒ ⟨σ^A⟩_{Λ₁} ≤ ⟨σ^A⟩_{Λ₂}` |
| `correlationΛ_shifted_monotone_bounded` | Shifted correlation sequence along exhaustion is monotone and bounded by 1 |
| `correlationΛ_shifted_tendsto` | Shifted correlation sequence converges to sup (Tendsto) |
| `correlationAlongExhaustion_monotone` | `correlationAlongExhaustion` is globally monotone (covers `A ⊄ Λ.volume n` by GKS-I ≥ 0) |
| `correlationAlongExhaustion_le_one` | `correlationAlongExhaustion n ≤ 1` for all `n` |
| `correlationAlongExhaustion_bddAbove` | Range of `correlationAlongExhaustion` is bounded above by 1 (helper) |
| **`correlationAlongExhaustion_tendsto_ciSup`** | **Convergence to explicit supremum**: `Tendsto … (nhds (⨆ n, …))` |
| **`correlationAlongExhaustion_convergent`** | Thin wrapper `∃ L, Tendsto …` — genuine thermodynamic limit |
| **`correlationInfinite`** | **Infinite-volume correlation** `:= ⨆ n, correlationAlongExhaustion …` |
| `tendsto_correlationAlongExhaustion_correlationInfinite` | `correlationAlongExhaustion → correlationInfinite` (Tendsto) |
| `correlationInfinite_le_one` | `correlationInfinite ≤ 1` |
| `correlationInfinite_nonneg` | `0 ≤ correlationInfinite` (uses `Λ.exhaust` + GKS-I) |
| `tendsto_correlationΛ_correlationInfinite_of_subset` | Explicit-hypothesis form: given `∀ n ≥ N, A ⊆ Λ.volume n`, `correlationΛ (Λ.volume (m+N)) …` → `correlationInfinite` |
| **`tendsto_correlationΛ_correlationInfinite`** | **Physical identification** (via `Λ.exhaust`): `correlationΛ G (Λ.volume (m+N)) p (lift A) → correlationInfinite` |
| `correlationAlongExhaustion_le_correlationInfinite_of_other` | Sandwich: `correlationAlongExhaustion Λ' n ≤ correlationInfinite Λ` via `Λ.exhaust` on `Λ'.volume n` |
| **`correlationInfinite_indep_exhaustion`** | **Exhaustion-independence**: `correlationInfinite G Λ p A = correlationInfinite G Λ' p A` |
| `correlationAlongExhaustion_monotone_ambient_subgraph` | `G₁ ≤ G₂` ⇒ pointwise monotonicity of `correlationAlongExhaustion` in ambient subgraph |
| **`correlationInfinite_monotone_ambient_subgraph`** | **Ambient-subgraph monotonicity at infinite volume**: `G₁ ≤ G₂` ⇒ `correlationInfinite G₁ Λ ≤ correlationInfinite G₂ Λ` |
| `mem_liftFinset` | membership characterization: `x ∈ liftFinset A hA ↔ x.val ∈ A` |
| `liftFinset_symmDiff` | `liftFinset` commutes with `∆`: `liftFinset A ∆ liftFinset B = liftFinset (A ∆ B)` |
| `liftFinset_insert` | `insert ⟨a, ha⟩ (liftFinset A) = liftFinset (insert a A)` |
| `liftFinset_sdiff` | `liftFinset A \ liftFinset B = liftFinset (A \ B)` |
| **`correlationInfinite_cor_4_3_5_h0`** | **Cor 4.3.5 at infinite volume** (Glimm–Jaffe §4.3 Cor 4.3.5 p. 63): inductive (n+2)-point bound at `h = 0` |
| `freeEnergyAlongExhaustion` | Free energy density sequence `n ↦ freeEnergyΛ G (Λ.volume n) p` (scaffold for §4.6 Prop 4.6.1 ∞-vol lift) |
| `freeEnergyAlongExhaustion_apply` | Definitional unfolding (simp): `= freeEnergyΛ G (Λ.volume n) p` |
| `partitionFunctionAlongExhaustion` | Partition function sequence `n ↦ partitionFunctionΛ G (Λ.volume n) p` (§4.6 Prop 4.6.1 scaffold #2) |
| `partitionFunctionAlongExhaustion_apply` | Definitional unfolding (simp) |
| `partitionFunctionAlongExhaustion_pos` | `0 < partitionFunctionAlongExhaustion` for every `n` |
| `freeEnergyAlongExhaustion_monotone_ambient_subgraph` | `G₁ ≤ G₂` ⇒ pointwise `freeEnergyAlongExhaustion G₁ Λ p n ≤ freeEnergyAlongExhaustion G₂ Λ p n` |
| `partitionFunctionAlongExhaustion_monotone_ambient_subgraph` | Partition-function analog of above |
| `freeEnergyAlongExhaustion_eq_log_div_card` | Log-bridge: `freeEnergyAlongExhaustion = log(partitionFunctionAlongExhaustion) / |Λ.volume n|` |
| `freeEnergyAlongExhaustion_monotone_J` | MonotoneOn (Ici 0) for fixed h ≥ 0, β > 0 |
| `freeEnergyAlongExhaustion_monotone_h` | MonotoneOn (Ici 0) for fixed J ≥ 0, β > 0 |
| `freeEnergyAlongExhaustion_monotone_beta` | MonotoneOn (Ioi 0) for fixed J ≥ 0, h ≥ 0 |
| `partitionFunctionAlongExhaustion_monotone_J` | Pointwise J-monotone (h ≥ 0, β > 0, 0 ≤ J₁ ≤ J₂) |
| `partitionFunctionAlongExhaustion_monotone_h` | Pointwise h-monotone (J ≥ 0, β > 0, 0 ≤ h₁ ≤ h₂) |
| `partitionFunctionAlongExhaustion_monotone_beta` | Pointwise β-monotone (J ≥ 0, h ≥ 0, 0 < β₁ ≤ β₂) |
| `freeEnergyInfinite` | `limsup freeEnergyAlongExhaustion` — API anchor for §4.6 Prop 4.6.1 (convergence pending) |
| `freeEnergyAlongExhaustion_ge_zero_params` | Zero-params comparison: `f(0,0,β) ≤ f(J,h,β)` for ferromagnetic |
| `partitionFunctionAlongExhaustion_ge_zero_params` | Zero-params comparison: `Z(0,0,β) ≤ Z(J,h,β)` for ferromagnetic |
| `hamiltonian_zero_params` (GibbsMeasure.lean) | `hamiltonian G ⟨0, 0, β⟩ σ = 0` identically |
| `partitionFunction_zero_params` (GibbsMeasure.lean) | `Z G ⟨0, 0, β⟩ = Fintype.card (Config ι)` |
| `card_spin` (GibbsMeasure.lean) | `Fintype.card Spin = 2` |
| `card_config_eq_two_pow` (GibbsMeasure.lean) | `Fintype.card (Config ι) = 2 ^ Fintype.card ι` |
| `freeEnergy_zero_params` (FreeEnergy.lean) | `freeEnergy G ⟨0, 0, β⟩ = log 2` (for nonempty ι) |
| `freeEnergyAlongExhaustion_zero_params` | Along-exhaustion specialization: `f_n(0, 0, β) = log 2` per nonempty stage |
| `freeEnergyInfinite_zero_params` | **∞-volume lift**: `freeEnergyInfinite G Λ ⟨0, 0, β⟩ = log 2` (all stages nonempty) |
| `partitionFunctionAlongExhaustion_zero_params` / `log_partitionFunctionAlongExhaustion_zero_params` | Partition-function side: `Z = 2^|Λ.volume n|`, `log Z = |Λ.volume n| · log 2` at `⟨0, 0, β⟩` |
| `partitionFunctionAlongExhaustion_beta_zero` / `log_partitionFunctionAlongExhaustion_beta_zero` | β=0 companion: `Z = 2^|Λ.volume n|`, `log Z = |Λ.volume n| · log 2` at `⟨J, h, 0⟩` (any J, h) |
| `partitionFunction{,Λ,AlongExhaustion}_ge_two_pow_card_of_ferromagnetic` | Strong ferromagnetic lower bound: `2^|ι| ≤ Z_G(p)` (via `⊥` + `cosh ≥ 1` + monotone); log form `|ι| · log 2 ≤ log Z` |
| `log_partitionFunction{,Λ,AlongExhaustion}_ge_card_mul_log_two_cosh_of_ferromagnetic` | **Sharp log-Z lower bound**: `|ι| · log(2·cosh(βh)) ≤ log Z_G(p)` (via `Z ≥ Z_⊥ = (2 cosh(βh))^|ι|` + `Real.log_pow`) |
| `partitionFunction{,Λ,AlongExhaustion}_ge_two_cosh_pow_card_of_ferromagnetic` | **Sharp Z lower bound (non-log)**: `(2·cosh(βh))^|ι| ≤ Z_G(p)` (direct from `partitionFunction_bot` + `monotone_subgraph`); exp-image of the log form |
| **`freeEnergyAlongExhaustion_ge_log_two`** | **Uniform lower bound**: `log 2 ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n` for ferromagnetic + nonempty `Λ.volume n` |
| `freeEnergy_upper_bound` (`Conditioning/FreeEnergyBound.lean`) | **Explicit upper bound** (Cor. 10.3.2 / \|ι\|): `freeEnergy G p ≤ log 2 + \|β\|·(\|J\|·\|E\| + \|h\|·\|ι\|)/\|ι\|` for nonempty ι |
| `freeEnergyAlongExhaustion_upper_bound` | Along-exhaustion specialization of `freeEnergy_upper_bound` |
| `BoundedEdgeDensity` | Hypothesis `∃ c, ∀ n (nonempty), \|E_n\| ≤ c·\|Λ_n\|` (e.g. bounded-degree ambient graphs) |
| `freeEnergyAlongExhaustion_le_uniform_upper_bound` | **Uniform upper bound** under `BoundedEdgeDensity`: `f_n ≤ log 2 + \|β\|·(\|J\|·c + \|h\|)` |
| `BddAbove_freeEnergyAlongExhaustion_range` | `BddAbove (Set.range (freeEnergyAlongExhaustion G Λ p))` under `BoundedEdgeDensity` |
| `hamiltonian_bot` (GibbsMeasure.lean) | `H_⊥(σ) = -h · Σ sign(σ_i)` (interaction term vanishes on empty graph) |
| `sum_spin` / `sum_exp_spin_sign` | Spin-sum lemmas: `Σ_s f(s) = f(up) + f(down)`; `Σ_s exp(β h sign(s)) = 2 cosh(β h)` |
| `partitionFunction_bot` (GibbsMeasure.lean) | `Z_⊥(p) = (2 cosh(β h))^\|ι\|` (free-spin product formula) |
| `freeEnergy_bot` (FreeEnergy.lean) | **Free-spin closed form**: `freeEnergy ⊥ p = log(2 cosh(β h))` (for nonempty ι) |
| `freeEnergy_bot_h_zero` (FreeEnergy.lean) | Corollary at `h = 0`: `freeEnergy ⊥ ⟨J, 0, β⟩ = log 2` for any J, β |
| `partitionFunction_beta_zero` (GibbsMeasure.lean) | `Z G ⟨J, h, 0⟩ = |Config ι|` (all weights collapse to `exp 0 = 1`) |
| `freeEnergy_beta_zero` (FreeEnergy.lean) | β=0 direction: `freeEnergy G ⟨J, h, 0⟩ = log 2` for nonempty ι, any J, h, G |
| `freeEnergyAlongExhaustion_beta_zero` | Along-exhaustion specialization: `f_n(J, h, 0) = log 2` per nonempty stage |
| `freeEnergyInfinite_beta_zero` | **∞-volume lift**: `freeEnergyInfinite G Λ ⟨J, h, 0⟩ = log 2` (all stages nonempty) |
| `freeEnergy_ge_log_two_cosh` (FreeEnergy.lean) | **Sharp ferromagnetic lower bound**: `log(2 cosh(β h)) ≤ freeEnergy G p` (via `freeEnergy_bot` + `freeEnergy_monotone_subgraph`) |
| `freeEnergy_ge_log_two_of_ferromagnetic` (FreeEnergy.lean) | **Unconditional lower bound**: `log 2 ≤ freeEnergy G p` for ferromagnetic + `0 < |ι|` (weakening of `_cosh` via `Real.one_le_cosh`) |
| `freeEnergy_nonneg_of_ferromagnetic` (FreeEnergy.lean) | **Nonnegativity**: `0 ≤ freeEnergy G p` for ferromagnetic + `0 < |ι|` (weakening of `_ge_log_two_of_ferromagnetic` via `Real.log_pos`) |
| `freeEnergyAlongExhaustion_ge_log_two_cosh` | Along-exhaustion specialization of the sharp ferromagnetic lower bound |
| `hamiltonian_neg_h` (Hamiltonian.lean) | `H_G(σ; J, -h, β) = H_G(σ.flip; J, h, β)` (spin-flip / h-sign identity) |
| `partitionFunction_neg_h` (GibbsMeasure.lean) | **Z h-symmetry**: `Z(J, -h, β) = Z(J, h, β)` via flip involution |
| `freeEnergy_neg_h` (FreeEnergy.lean) | **freeEnergy is even in h**: `f(J, -h, β) = f(J, h, β)` |
| `freeEnergy_eq_abs_h` (FreeEnergy.lean) | `f(J, h, β) = f(J, |h|, β)` (case split + h-symmetry) |
| `freeEnergy_monotone_abs_h` (FreeEnergy.lean) | **Ferromagnetic |h|-monotonicity**: `|h₁| ≤ |h₂| → f(J, h₁, β) ≤ f(J, h₂, β)` |
| `freeEnergyAlongExhaustion_neg_h` / `_eq_abs_h` / `_monotone_abs_h` | Along-exhaustion specializations of h-symmetry + |h|-monotonicity |
| `inducedGraph_bot` (AmbientLattice.lean) | `inducedGraph (⊥ : SimpleGraph V) Λ = ⊥` (simp) |
| `correlationAlongExhaustion_nonneg` | `0 ≤ correlationAlongExhaustion G Λ p A n` (ferromagnetic) |
| `correlationΛ_gks_second` | **GKS-II at finite volume**, lifted form: `correlationΛ (lift A) · correlationΛ (lift B) ≤ correlationΛ (lift (A ∆ B))` |
| **`correlationInfinite_gks_second`** | **GKS-II at infinite volume** (Glimm–Jaffe §4.1 Thm 4.1.3, (4.1.11), p. 57): `correlationInfinite A · correlationInfinite B ≤ correlationInfinite (A ∆ B)` |
| `correlationInfinite_fkg_spinProduct` | **FKG for spinProducts at ∞-vol** (Glimm–Jaffe §4.4 p. 67): named alias of GKS-II for the FKG nomenclature |
| `correlationΛ_monotone_h` | `MonotoneOn (h ↦ correlationΛ G Λ ⟨J, h, β⟩ A) (Ici 0)` |
| `correlationAlongExhaustion_monotone_h` | Pointwise h-monotonicity of the exhaustion sequence |
| **`correlationInfinite_monotone_h`** | **h-direction monotonicity at infinite volume** (Glimm–Jaffe Prop 4.2.1, p. 58, applied to the singleton couplings): `MonotoneOn (h ↦ correlationInfinite G Λ ⟨J, h, β⟩ A) (Ici 0)` |
| `correlationΛ_monotone_beta` | `MonotoneOn (β ↦ correlationΛ G Λ ⟨J, h, β⟩ A) (Ioi 0)` |
| `correlationAlongExhaustion_monotone_beta` | Pointwise β-monotonicity of the exhaustion sequence |
| **`correlationInfinite_monotone_beta`** | **β-direction monotonicity at infinite volume** (repo extension not stated by Glimm–Jaffe; reduced to Prop 4.2.1, p. 58, by rescaling): `MonotoneOn (β ↦ correlationInfinite G Λ ⟨J, h, β⟩ A) (Ioi 0)` |
| `correlationΛ_monotone_J` | `MonotoneOn (J ↦ correlationΛ G Λ ⟨J, h, β⟩ A) (Ici 0)` |
| `correlationAlongExhaustion_monotone_J` | Pointwise J-monotonicity of the exhaustion sequence |
| **`correlationInfinite_monotone_J`** | **J-direction monotonicity at infinite volume** (Glimm–Jaffe Prop 4.2.1, p. 58): `MonotoneOn (J ↦ correlationInfinite G Λ ⟨J, h, β⟩ A) (Ici 0)` — three-parameter symmetry complete |
| **`magnetizationInfinite`** | **Infinite-volume single-site magnetization** `:= correlationInfinite G Λ p {i}` |
| `magnetizationInfinite_nonneg` | `0 ≤ magnetizationInfinite G Λ p i` (ferromagnetic) |
| `magnetizationInfinite_le_one` | `magnetizationInfinite G Λ p i ≤ 1` |
| `magnetizationInfinite_indep_exhaustion` | Λ-independence |
| `magnetizationInfinite_monotone_{J,h,beta}` | three-parameter monotonicity (specializations of correlationInfinite versions) |
| `correlationΛ_odd_vanish_h_zero` | At `h = 0`, `correlationΛ ⟨J, 0, β⟩ A = 0` for `Odd A.card` (lifted from `correlation_odd_vanish`) |
| `correlationAlongExhaustion_h_zero` | Pointwise `= 0` at `h = 0` for odd-cardinality `A` |
| `correlationInfinite_h_zero` | `correlationInfinite ⟨J, 0, β⟩ A = 0` for `Odd A.card` (sup of zero sequence) |
| **`magnetizationInfinite_zero_at_h_zero`** | **Z₂ symmetry**: `magnetizationInfinite G Λ ⟨J, 0, β⟩ i = 0` at zero external field |
| **`spontaneousMagnetization`** | **Spontaneous magnetization** `m* := ⨅ h : Set.Ioi 0, magnetizationInfinite ⟨J, h, β⟩ i` (Glimm–Jaffe §5.1 p. 77) |
| `spontaneousMagnetization_nonneg` | `0 ≤ m*` (ferromagnetic) |
| `spontaneousMagnetization_le_one` | `m* ≤ 1` |
| `spontaneousMagnetization_le_magnetizationInfinite` | `m* ≤ M(h)` for any `h > 0` (infimum characterization) |
| `spontaneousMagnetization_indep_exhaustion` | `m*` does not depend on the choice of exhaustion |
| **`tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT`** | **Right-limit**: `Tendsto M(h) (𝓝[>] 0) (𝓝 m*)` — realizes `m*` as the physical right limit of `magnetizationInfinite` |
| **`spontaneousCorrelation`** | **General-A spontaneous correlation** `:= ⨅ h : Set.Ioi 0, correlationInfinite ⟨J, h, β⟩ A` — generalization of `spontaneousMagnetization` |
| `spontaneousCorrelation_nonneg` | `0 ≤ ⟨σ^A⟩*` (ferromagnetic) |
| `spontaneousCorrelation_le_one` | `⟨σ^A⟩* ≤ 1` |
| `spontaneousCorrelation_le_correlationInfinite` | `⟨σ^A⟩* ≤ ⟨σ^A⟩(h)` for `h > 0` |
| `spontaneousCorrelation_indep_exhaustion` | Λ-independence |
| `tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT` | Right-limit Tendsto: `⟨σ^A⟩(h) → ⟨σ^A⟩*` as `h → 0+` |
| `spontaneousCorrelation_singleton_eq_spontaneousMagnetization` | `spontaneousCorrelation ... {i} = spontaneousMagnetization ... i` (definitional) |
| **`truncated2Infinite`** | **Truncated 2-point correlation** `U_2(i,j) := ⟨σᵢσⱼ⟩_∞ - ⟨σᵢ⟩_∞⟨σⱼ⟩_∞` |
| `truncated2Infinite_symm` | `U_2(i,j) = U_2(j,i)` |
| `truncated2Infinite_nonneg_of_ne` | `i ≠ j ⇒ 0 ≤ U_2(i,j)` (direct GKS-II corollary) |
| `truncated2Infinite_nonneg_of_eq` | `0 ≤ U_2(i,i) = M(i)(1-M(i))` |
| **`truncated2Infinite_nonneg`** | **General nonneg**: `0 ≤ U_2(i,j)` for all `i, j` |
| `truncated2Infinite_indep_exhaustion` | Λ-independence |
| `truncated2Infinite_h_zero` | `h = 0` ⇒ `U_2 = ⟨σᵢσⱼ⟩_∞` (general; Z₂ collapses singletons) |
| **`truncated3Infinite`** | **Truncated 3-point correlation** `U_3(i,j,k) := ⟨σ^{i,j,k}⟩_∞ - ⟨σ_i⟩_∞⟨σ^{j,k}⟩_∞ - ⟨σ_j⟩_∞⟨σ^{i,k}⟩_∞ - ⟨σ_k⟩_∞⟨σ^{i,j}⟩_∞ + 2⟨σ_i⟩_∞⟨σ_j⟩_∞⟨σ_k⟩_∞` |
| **`truncated3Infinite_nonpos`** | **GHS at infinite volume** (Glimm–Jaffe §4.3 Cor 4.3.4, p. 62): pairwise distinct ⇒ `U_3 ≤ 0` |
| `truncated3Infinite_h_zero_of_distinct` | `h = 0` + distinct ⇒ `U_3 = 0` (Z₂ symmetry consequence) |
| `truncated3Infinite_indep_exhaustion` | Λ-independence |
| **`truncated4Infinite`** | **Truncated 4-point correlation** `U_4(i,j,k,l) := ⟨σ^{i,j,k,l}⟩_∞ - ⟨σ^{i,j}⟩_∞⟨σ^{k,l}⟩_∞ - ⟨σ^{i,k}⟩_∞⟨σ^{j,l}⟩_∞ - ⟨σ^{i,l}⟩_∞⟨σ^{j,k}⟩_∞` |
| **`truncated4Infinite_nonpos_h_zero`** | **Lebowitz/U_4 ≤ 0 at infinite volume** (Glimm–Jaffe §4.3 Cor 4.3.3 pp. 68ff): `h = 0` + pairwise distinct ⇒ `U_4 ≤ 0` |
| `truncated4Infinite_indep_exhaustion` | Λ-independence |
| `spontaneousCorrelation_monotone_J` | `MonotoneOn (J ↦ spontaneousCorrelation G Λ J β A) (Ici 0)` |
| `spontaneousCorrelation_monotone_beta` | `MonotoneOn (β ↦ spontaneousCorrelation G Λ J β A) (Ioi 0)` |
| `spontaneousMagnetization_monotone_J` | Singleton specialization at `A = {i}` |
| `spontaneousMagnetization_monotone_beta` | Singleton specialization at `A = {i}` |
