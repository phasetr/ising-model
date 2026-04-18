---
layout: default
title: Home
---

## ising-model

Lean 4 + mathlib formalization of Ising model theorems, with particular
emphasis on Glimm–Jaffe, *Quantum Physics: A Functional Integral Point of
View* (2nd ed., 1987).

All theorems are formally proved with **zero `sorry`**.
Pre-existing axioms (four items) cover Lebowitz-type inequalities
whose full proofs require measure theory machinery; see the *Axioms*
section below.

## How to read this page

We distinguish three formalization regimes:

1. **Finite-volume** — the Ising model on a fixed finite graph
   `G : SimpleGraph ι` with `[Fintype ι]`.  Most of the project is here.
2. **Discretized infinite-volume** — a fixed finite ambient `ι` with
   growing subgraphs `G₁ ≤ G₂ ≤ ⋯`.  The "Λ ↑" convergence theorems
   of GJ §4.2 and §4.6 are formalized here: the mechanism of proof is
   identical to GJ, but the ambient lattice is finite.
3. **Genuine infinite-volume** — an unbounded ambient type `V : Type*`
   with `Λ : Finset V` finite volumes and an exhaustion `Λₙ ↑ V`.
   Introduced in `IsingModel/AmbientLattice.lean`.

When a GJ theorem is marked "Done", the adjacent *Regime* column
specifies which of the three above apply.

## Formalized theorems

### Correlation inequalities (§4.1–§4.7)

| Theorem | Statement | File | Regime |
|---|---|---|---|
| **GKS-I** (Thm 4.1.1) | `⟨σ^A⟩ ≥ 0` for ferromagnetic `p` | `Inequalities/GKS.lean` | Finite |
| **GKS-II** (Thm 4.1.1) | `⟨σ^A σ^B⟩ ≥ ⟨σ^A⟩⟨σ^B⟩` | `Inequalities/GKS.lean` | Finite |
| **FKG** (§4.4) | `⟨fg⟩ ≥ ⟨f⟩⟨g⟩` for `f, g` monotone | `Inequalities/FKG.lean` | Finite |
| **Boundedness** (Prop 4.2.2) | `|⟨σ^A⟩| ≤ 1` | `InfiniteVolume.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol |
| **J-monotonicity** (Prop 4.2.1) | `⟨σ^A⟩` monotone in `J ≥ 0` | `InfiniteVolume.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol |
| **h-monotonicity** (Prop 4.2.4) | `⟨σ^A⟩` monotone in `h ≥ 0` | `InfiniteVolume.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol |
| **β-monotonicity** | `⟨σ^A⟩` monotone in `β > 0` | `InfiniteVolume.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol |
| **Subgraph monotonicity** | `G₁ ≤ G₂ ⇒ ⟨σ^A⟩_{G₁} ≤ ⟨σ^A⟩_{G₂}` | `InfiniteVolume.lean` / `AmbientLattice.lean` | Finite + Discretized Λ↑ + genuine ∞-vol |
| **GKS-II at ∞-vol** (Thm 4.2.3) | `⟨σ^A⟩ · ⟨σ^B⟩ ≤ ⟨σ^{A∆B}⟩` | `AmbientLattice.lean` | Genuine ∞-vol (ferromagnetic) |
| **Exhaustion-independence** | `correlationInfinite G Λ = correlationInfinite G Λ'` | `AmbientLattice.lean` | Genuine ∞-vol |
| **Lee–Yang circle theorem** (§4.5) | Ising partition polynomial nonvanishing on polydisk | `LeeYang.lean` | Finite |
| **Lee–Yang (graph form)** | Z ≠ 0 on polydisk for ferromagnetic graph | `FreeEnergy.lean` | Finite |
| **φ⁴ Lebowitz** (Cor 4.3.2) | `lebowitz_third/four/inductive` | `Inequalities/GHS.lean` | Finite, axiom |
| **Cor 4.3.3** | `U₄ ≤ 0` for `h = 0` | `Inequalities/GHS.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol (`truncated4Infinite_nonpos_h_zero`) |
| **GHS** (Cor 4.3.4) | `⟨σᵢ;σⱼ;σₖ⟩ ≤ 0` | `Inequalities/GHS.lean` / `AmbientLattice.lean` | Finite + genuine ∞-vol (`truncated3Infinite_nonpos`) |
| **Cor 4.3.5** | inductive `n`-point bound (`h = 0`) | `Inequalities/GHS.lean` | Finite |

### §4.2: Thermodynamic limit of correlations (Thm 4.2.3)

Original GJ statement: as `Λ ↑ ℝᵈ`, `⟨σ^B⟩_Λ` converges.
Formalized in three regimes:

| Result | Statement | File | Regime |
|---|---|---|---|
| `correlation_convergent` | `⟨σ^A⟩_{(n,h,β)}` converges as `J = n → ∞` | `InfiniteVolume.lean` | Finite |
| `correlation_convergent_h` | `⟨σ^A⟩_{(J,n,β)}` converges as `h = n → ∞` | `InfiniteVolume.lean` | Finite |
| `correlation_convergent_beta` | `⟨σ^A⟩_{(J,h,n+1)}` converges as `β = n+1 → ∞` | `InfiniteVolume.lean` | Finite |
| `correlation_convergent_subgraph` | `⟨σ^A⟩_{Gₙ}` converges for `Gₙ ↑` | `InfiniteVolume.lean` | Discretized Λ↑ |
| `Ambient.correlationInfinite` | `correlationInfinite := ⨆ n, correlationAlongExhaustion G Λ p A n` | `AmbientLattice.lean` | **Genuine ∞-vol (full)**: convergence, Λ-independence, GKS-I/II, J/h/β monotonicity |

Named specializations at `A = {i}`:
- Finite / Discretized: `magnetization_convergent_{J,h,beta,subgraph}`
- Genuine ∞-vol: `Ambient.magnetizationInfinite`
  (nonneg / le_one / indep_exhaustion / monotone_{J,h,beta} inherited from `correlationInfinite`)

### §4.6: Free energy analyticity and thermodynamic limit

| Result | Statement | File | Regime |
|---|---|---|---|
| `freeEnergy_monotone_{J,h,beta,subgraph}` | monotonicity | `FreeEnergy.lean` | Finite / Discretized Λ↑ |
| `freeEnergy_convergent_subgraph` (Prop 4.6.1) | `f_{Gₙ}` converges | `FreeEnergy.lean` | Discretized Λ↑ |
| `freeEnergyH_analyticOn` (Thm 4.6.2, real) | `f(h)` real-analytic for `h > 0` | `FreeEnergy.lean` | Finite |
| `freeEnergyJ_analyticOn` | `f(J)` real-analytic for `J > 0` | `FreeEnergy.lean` | Finite |
| `partitionFunctionH_analyticAt` | `Z(h)` real-analytic | `FreeEnergy.lean` | Finite |
| `partitionFunctionJ_analyticAt` | `Z(J)` real-analytic | `FreeEnergy.lean` | Finite |
| `isingEdgePoly_nonvanishing_of_graph` | Lee–Yang for Ising partition polynomial | `FreeEnergy.lean` | Finite |

**Not yet formalized**: the infinite-volume analyticity of `f(h)` via
Vitali convergence (GJ Thm 4.6.2 full statement).

### §5.1–§5.4: Phase transitions and Peierls' argument

| Result | Statement | File | Regime |
|---|---|---|---|
| `truncated2_nonneg` (§5.1, GKS-II) | `⟨σᵢ;σⱼ⟩ ≥ 0` | `Inequalities/GHS.lean` | Finite |
| `truncated2_le_one` (§5.1) | `⟨σᵢ;σⱼ⟩ ≤ 1` | `PhaseTransition.lean` | Finite |
| `truncated2_convergent_{J,h,beta,subgraph}` | convergence | `PhaseTransition.lean` | Finite / Discretized Λ↑ |
| `mixed_phase_truncated2` (eq. 5.1.5) | `M² − (M(2α−1))² = 4α(1−α)M²` | `PhaseTransition.lean` | Algebraic |
| `mixed_phase_pure_iff` | `4α(1−α)M² = 0 ↔ α ∈ {0,1}` | `PhaseTransition.lean` | Algebraic |
| `meanFieldEnergy_neg` (§5.2) | mean field symmetry at `h = 0` | `PhaseTransition.lean` | Algebraic |
| `meanField_zero_solution` | `tanh(0) = 0` trivial fixed point | `PhaseTransition.lean` | Algebraic |
| `tanh_odd` | `tanh(-x) = -tanh(x)` | `PhaseTransition.lean` | Algebraic |
| `susceptibility_nonneg` (§5.3) | `χᵢ = Σⱼ⟨σᵢ;σⱼ⟩ ≥ 0` | `PhaseTransition.lean` | Finite |
| `susceptibility_convergent_{J,h,beta,subgraph}` | convergence | `PhaseTransition.lean` | Finite / Discretized Λ↑ |
| `magnetization_zero_at_h_zero` | `Mᵢ = 0` at `h = 0` (Z₂) | `PhaseTransition.lean` | Finite |
| `magnetization_monotone_{h,beta}` | monotone in `h`, `β` | `PhaseTransition.lean` | Finite |
| `magnetization_convergent_{J,h,beta,subgraph}` | convergence | `PhaseTransition.lean` | Finite / Discretized Λ↑ |
| `magnetization_total_convergent_subgraph` | Σᵢ Mᵢ converges | `PhaseTransition.lean` | Discretized Λ↑ |
| `peierls_bound` (Prop 5.4.1) | `Pr(γ ⊆ ∂σ) ≤ exp(-2βJ|γ|)` | `Peierls.lean` | Finite |
| `peierls_contour_sum_bound` | `Σ Pr(γ) ≤ N(r) exp(-2βJ r)` | `Peierls.lean` | Finite |
| `prop_5_4_2_self_contained` (Prop 5.4.2) | `0 ≤ 1 − ⟨σᵢ⟩₊ ≤ exp(-cβ)` | `Peierls.lean` | Finite (+ BC) |
| `eta_nonneg_finite_vol` (§17.7) | `η ≥ 0` | `PhaseTransition.lean` | Finite |

**Not yet formalized**: infinite-volume lift of Prop 5.4.2 (requires
boundary-condition infinite-volume measure framework).

### Chapter 10 (Conditioning inequalities)

| Result | Statement | File |
|---|---|---|
| `partitionFunction_monotone_beta` (Cor 10.2.3) | `Z` monotone in `β` | `Conditioning.lean` |
| `hamiltonian_abs_le` (Cor 10.3.2) | `|H| ≤ \|J\|·\|E\| + \|h\|·\|ι\|` | `Conditioning.lean` |
| `partitionFunction_upper/lower` | `Z` bounds | `Conditioning.lean` |
| `ReflectionPositive` (§10.4) | definition + `discriminant_nonneg` | `Conditioning.lean` |
| `iterated_schwarz_sq` (§10.5) | iterated Schwarz bound | `Conditioning.lean` |
| `highTempParam` (§18.1) | `\|tanh(βJ)\| < 1` | `Conditioning.lean` |

### Ambient lattice framework (genuine infinite volume)

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
| **`correlationInfinite_cor_4_3_5_h0`** | **Cor 4.3.5 at infinite volume** (Glimm–Jaffe §4.3 Cor 4.3.5 p. 62): inductive (n+2)-point bound at `h = 0` |
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
| **`freeEnergyAlongExhaustion_ge_log_two`** | **Uniform lower bound**: `log 2 ≤ freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n` for ferromagnetic + nonempty `Λ.volume n` |
| `freeEnergy_upper_bound` (Conditioning.lean) | **Explicit upper bound** (Cor. 10.3.2 / \|ι\|): `freeEnergy G p ≤ log 2 + \|β\|·(\|J\|·\|E\| + \|h\|·\|ι\|)/\|ι\|` for nonempty ι |
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
| `freeEnergy_ge_log_two_cosh` (FreeEnergy.lean) | **Sharp ferromagnetic lower bound**: `log(2 cosh(β h)) ≤ freeEnergy G p` (via `freeEnergy_bot` + `freeEnergy_monotone_subgraph`) |
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
| **`correlationInfinite_gks_second`** | **GKS-II at infinite volume** (Glimm–Jaffe §4.2 Thm 4.2.3): `correlationInfinite A · correlationInfinite B ≤ correlationInfinite (A ∆ B)` |
| `correlationInfinite_fkg_spinProduct` | **FKG for spinProducts at ∞-vol** (Glimm–Jaffe §4.4 p. 67): named alias of GKS-II for the FKG nomenclature |
| `correlationΛ_monotone_h` | `MonotoneOn (h ↦ correlationΛ G Λ ⟨J, h, β⟩ A) (Ici 0)` |
| `correlationAlongExhaustion_monotone_h` | Pointwise h-monotonicity of the exhaustion sequence |
| **`correlationInfinite_monotone_h`** | **h-direction monotonicity at infinite volume** (Glimm–Jaffe Prop 4.2.4): `MonotoneOn (h ↦ correlationInfinite G Λ ⟨J, h, β⟩ A) (Ici 0)` |
| `correlationΛ_monotone_beta` | `MonotoneOn (β ↦ correlationΛ G Λ ⟨J, h, β⟩ A) (Ioi 0)` |
| `correlationAlongExhaustion_monotone_beta` | Pointwise β-monotonicity of the exhaustion sequence |
| **`correlationInfinite_monotone_beta`** | **β-direction monotonicity at infinite volume** (Glimm–Jaffe Prop 4.2.4): `MonotoneOn (β ↦ correlationInfinite G Λ ⟨J, h, β⟩ A) (Ioi 0)` |
| `correlationΛ_monotone_J` | `MonotoneOn (J ↦ correlationΛ G Λ ⟨J, h, β⟩ A) (Ici 0)` |
| `correlationAlongExhaustion_monotone_J` | Pointwise J-monotonicity of the exhaustion sequence |
| **`correlationInfinite_monotone_J`** | **J-direction monotonicity at infinite volume** (Glimm–Jaffe Prop 4.2.4): `MonotoneOn (J ↦ correlationInfinite G Λ ⟨J, h, β⟩ A) (Ici 0)` — three-parameter symmetry complete |
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
| **`truncated3Infinite_nonpos`** | **GHS at infinite volume** (Glimm–Jaffe §4.3 Cor 4.3.4 pp. 68ff): pairwise distinct ⇒ `U_3 ≤ 0` |
| `truncated3Infinite_h_zero_of_distinct` | `h = 0` + distinct ⇒ `U_3 = 0` (Z₂ symmetry consequence) |
| `truncated3Infinite_indep_exhaustion` | Λ-independence |
| **`truncated4Infinite`** | **Truncated 4-point correlation** `U_4(i,j,k,l) := ⟨σ^{i,j,k,l}⟩_∞ - ⟨σ^{i,j}⟩_∞⟨σ^{k,l}⟩_∞ - ⟨σ^{i,k}⟩_∞⟨σ^{j,l}⟩_∞ - ⟨σ^{i,l}⟩_∞⟨σ^{j,k}⟩_∞` |
| **`truncated4Infinite_nonpos_h_zero`** | **Lebowitz/U_4 ≤ 0 at infinite volume** (Glimm–Jaffe §4.3 Cor 4.3.3 pp. 68ff): `h = 0` + pairwise distinct ⇒ `U_4 ≤ 0` |
| `truncated4Infinite_indep_exhaustion` | Λ-independence |
| `spontaneousCorrelation_monotone_J` | `MonotoneOn (J ↦ spontaneousCorrelation G Λ J β A) (Ici 0)` |
| `spontaneousCorrelation_monotone_beta` | `MonotoneOn (β ↦ spontaneousCorrelation G Λ J β A) (Ioi 0)` |
| `spontaneousMagnetization_monotone_J` | Singleton specialization at `A = {i}` |
| `spontaneousMagnetization_monotone_beta` | Singleton specialization at `A = {i}` |

## Axioms

All four axioms are in `Inequalities/GHS.lean` and `ContinuousSpin/Phi4.lean`.
They are mathematically proved (and documented) but formalization requires
heavy measure theory setup:

- `phi4_single_site_nonneg`: non-negativity of the symmetrized 4D
  integral (`ContinuousSpin/Phi4.lean`)
- `lebowitz_third`: 3-site Lebowitz inequality for continuous `φ⁴`,
  transferred to Ising via the `λ → ∞` limit
- `lebowitz_four`: 4-site version, same route
- `lebowitz_inductive`: inductive form of Cor 4.3.2

## Glimm–Jaffe coverage inventory

Per-section status of Ising-relevant discussions. Copilot-verified
inventory (2026-04-17).

### Chapter 2 (Classical Statistical Mechanics)

| Section | Content | Status |
|---|---|---|
| §2.1, §2.2 | Introduction, classical ensembles | Out of scope |
| §2.3 | Ising model definitions | **Done** (`Basic.lean`, `Hamiltonian.lean`, `GibbsMeasure.lean`) |
| §2.4 | Mayer expansion | Out of scope |

### Chapter 4 (Correlation inequalities & Lee–Yang)

| Section | Result | Status | Notes |
|---|---|---|---|
| §4.1 | Thm 4.1.1 GKS-I/II | **Done** | `gks_first`, `gks_second` |
| §4.2 | Prop 4.2.1 (J-monotonicity) | **Done (finite + infinite)** | Finite: `correlation_monotone_J`; Infinite: `correlationInfinite_monotone_J` |
| §4.2 | Prop 4.2.2 (boundedness) | **Done (finite + infinite)** | Finite: `abs_correlation_le_one`; Infinite: `correlationInfinite_le_one` |
| §4.2 | **Thm 4.2.3 (thermodynamic limit)** | **Done (genuine ∞-vol)** | `correlationInfinite_gks_second` (GKS-II), `correlationInfinite_indep_exhaustion`, ambient-subgraph monotonicity |
| §4.2 | Prop 4.2.4 (h-monotonicity) | **Done (finite + infinite)** | Three parameters: `correlationInfinite_monotone_{J,h,beta}` |
| §4.3 | Thm 4.3.1 (φ⁴) | **Done (axiom)** | `phi4_single_site_nonneg` |
| §4.3 | Cor 4.3.2 (Lebowitz) | **Done (axiom)** | 3 axioms |
| §4.3 | Cor 4.3.3 (`U₄ ≤ 0` at h=0) | **Done (finite + infinite)** | Finite: `cor_4_3_3` (axioms); Infinite: `truncated4Infinite_nonpos_h_zero` |
| §4.3 | Cor 4.3.4 (GHS, `U₃ ≤ 0`) | **Done (finite + infinite)** | Finite: `ghs_inequality` (axioms); Infinite: `truncated3Infinite_nonpos`, `_h_zero_of_distinct` |
| §4.3 | Cor 4.3.5 (inductive n-point at h=0) | **Done (finite + infinite)** | Finite: `cor_4_3_5_h0` (axioms); Infinite: `correlationInfinite_cor_4_3_5_h0` |
| §4.4 | FKG inequality (spinProduct case) | **Done (finite + infinite)** | Finite: `fkg_ising`; ∞-vol spinProduct: `correlationInfinite_fkg_spinProduct` (≡ GKS-II). General monotone fn at ∞-vol: out of scope |
| §4.5 | Lee–Yang circle theorem | **Done** | `lee_yang_circle` |
| §4.6 | **Prop 4.6.1 (`f_Λ` convergence)** | **Done (discretized)** | Discretized Λ↑ |
| §4.6 | **Thm 4.6.2 (analyticity)** | **Done (finite/real)** | Full infinite-volume complex analyticity: not yet |
| §4.6 | Lee–Yang nonvanishing (Ising) | **Done** | `isingEdgePoly_nonvanishing_of_graph` |
| §4.7 | Two-component spins | Out of scope | XY model |

### Chapter 5 (Phase transitions)

| Section | Result | Status | Notes |
|---|---|---|---|
| §5.1 | Pure/mixed phase criteria | **Done (algebraic)** | `mixed_phase_truncated2`, `mixed_phase_pure_iff`, `truncated2_le_one` |
| §5.1 | Spontaneous magnetization `m*` (p. 77) | **Done (complete)** | `spontaneousMagnetization` (infimum form) + `tendsto_…_nhdsGT` (right-limit `m* = lim_{h→0+} M(h)`) + nonneg/≤1/≤M(h)/indep_exhaustion |
| §5.2 | Mean field picture | **Done (algebraic)** | `meanFieldEnergy_neg`, `meanField_zero_solution`, `tanh_odd` |
| §5.3 | Symmetry breaking (Z₂ at `h = 0`) | **Done (finite + infinite)** | Finite: `magnetization_zero_at_h_zero`, `susceptibility_nonneg`; Infinite: `magnetizationInfinite_zero_at_h_zero`, `correlationInfinite_h_zero` |
| §5.4 | Prop 5.4.1 (Peierls) | **Done** | `peierls_bound` |
| §5.4 | Prop 5.4.2 (spontaneous magnetization) | **Done (finite +BC)** | Infinite-volume lift: not yet |
| §5.5 | XY example | Out of scope |

### Chapter 10 (Conditioning)

| Section | Result | Status |
|---|---|---|
| §10.2 | Cor 10.2.3 (β-monotonicity of Z) | **Done** |
| §10.3 | Cor 10.3.2 (Z bounds) | **Done** |
| §10.4 | Reflection positivity | **Done** |
| §10.5 | Multiple reflections | **Done** |
| §10.6 | Nonsymmetric reflections | Documented; not formalized |

### Chapter 11 (Fields without cutoffs)

**Not Ising-scope**. Continuum construction.

### Chapter 16 (Phase transitions — continuum)

| Section | Result | Status | Notes |
|---|---|---|---|
| §16.1 | `da/dh = M`, `d²a/dh² = χ ≥ 0` | **Done (lattice)** | `magnetization_monotone_h`, `susceptibility_nonneg` |
| §16.2 | Two phase region (continuum) | Out of scope | φ⁴ Peierls |
| §16.3 | Symmetry unbroken, `d = 2` | Out of scope | Mermin–Wagner (continuous spin) |
| §16.4 | Symmetry broken, `d ≥ 3` | **Done (lattice)** | Peierls (§5.4) |

### Chapter 17 (φ⁴ critical point)

| Section | Result | Status |
|---|---|---|
| §17.2 | Absence of even bound states | **Done** (via Cor 4.3.3) |
| §17.5 | Correlation length | Not formalized (spectral theory) |
| §17.7 | `η ≥ 0`, `ζ ≥ 0` | **Done** |
| §17.8 | `η ≤ 1` | **Done** |

### Chapter 18 (Cluster expansion)

| Section | Result | Status |
|---|---|---|
| §18.1 | High-temperature parameter | **Done** |
| §18.2 | `exp(α·edgeSpin) = cosh α + sinh α · edgeSpin` | **Done** |
| §18.3 | Clustering and analyticity | **Done (lattice)** |
| §18.4–18.7 | Cluster expansion machinery | Not formalized (large) |

### Chapter 19 (Reconstruction)

**Not Ising-scope**. Quantum field theory reconstruction.

### Chapter 20 (Further directions)

| Section | Result | Status |
|---|---|---|
| §20.5 | Low-temperature expansion | **Done (lattice)** = Peierls |
| §20.8 | 3D Ising roughening | Not formalized (specialized) |

## Unformalized infinite-volume theorems

The following GJ Ising infinite-volume discussions are **not yet
formalized**, per the full inventory above:

1. **Genuine thermodynamic limit of cylinder correlations** along an
   exhaustion `Λₙ ↑ V` of an infinite ambient `V`. The
   `AmbientLattice.lean` framework introduces the types and
   `correlationAlongExhaustion`; the convergence theorem itself (i.e.,
   that `correlationAlongExhaustion` is Cauchy / tends to a limit) is
   not yet proved in this setting.
2. **Thm 4.6.2 (full form)**: complex analyticity of the
   infinite-volume free energy via Vitali convergence.
3. **Prop 5.4.2 infinite-volume version**: `0 ≤ 1 − ⟨σᵢ⟩₊∞ ≤ exp(-cβ)`
   in the genuine `+` boundary-condition infinite-volume measure.
4. **§5.1 cluster property** at large separation for pure phases.
5. **§17.5 correlation length continuity** and **§17.8 anomalous
   dimension continuity** — require spectral theory of the transfer
   matrix.
6. **Chapter 18** full cluster expansion machinery (convergence at
   small `tanh(βJ)`).
7. **§20.8 3D Ising roughening** — specialized interface analysis.

## References

### Primary texts

- Glimm, J. and Jaffe, A., *Quantum Physics: A Functional Integral
  Point of View*, 2nd ed., Springer, 1987.
  [Springer](https://link.springer.com/book/10.1007/978-1-4612-4728-9)
  - §4.1–4.6: Correlation inequalities (GKS, FKG, Lee-Yang, GHS),
    free energy analyticity
  - §5.1–5.4: Phase transitions, Peierls argument, spontaneous
    magnetization
  - §10: Conditioning inequalities, reflection positivity
  - §16–18: Phase transitions, critical exponents, cluster expansion
- Friedli, S. and Velenik, Y., *Statistical Mechanics of Lattice
  Systems: A Concrete Mathematical Introduction*.
  [Cambridge UP](https://www.unige.ch/math/folks/velenik/smbook/)
  - Thm 3.21 (FKG), Thm 3.49 (GKS-I/II), Prop 3.44 (Asano contraction)

### Supplementary texts

- Ellis, R.S., *Entropy, Large Deviations, and Statistical Mechanics*.
  [Springer](https://link.springer.com/book/10.1007/3-540-29060-5)
- Ruelle, D., "Extension of the Lee–Yang circle theorem",
  *Ann. of Math.* **171** (2010), 589–603
- Simon, B., *The Statistical Mechanics of Lattice Gases, Vol. I*.
  [Princeton UP](https://press.princeton.edu/books/hardcover/9780691636436/)
- Fernández, R., Fröhlich, J., and Sokal, A.D., *Random Walks,
  Critical Phenomena, and Triviality in Quantum Field Theory*,
  Springer, 1992
