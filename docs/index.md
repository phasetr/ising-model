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
| `sum_eq_map_sup` (§4.6 super-add. prep) | `G ⊕g H = G.map Sum.inl ⊔ H.map Sum.inr` | `SumGraph.lean` | Disjoint-sum lemma |
| `edgeSet_sum` | Edge-set decomposition of `G ⊕g H` | `SumGraph.lean` | Disjoint-sum lemma |
| `disjoint_inl_inr_edgeSet` / `disjoint_inl_inr_edgeFinset` | Set / Finset disjointness of the two images | `SumGraph.lean` | Disjoint-sum lemma |
| `card_edgeFinset_sum` | `#(G ⊕g H).edgeFinset = #G.edgeFinset + #H.edgeFinset` | `SumGraph.lean` | Disjoint-sum lemma |
| `Config.sumEquiv` | `Config (ι ⊕ ι') ≃ Config ι × Config ι'` | `SumModel.lean` | Ising on sum graph |
| `interactionEnergy_sum` / `externalFieldEnergy_sum` | Per-summand additivity of the Hamiltonian's interaction / field contributions on `G ⊕g H` | `SumModel.lean` | Ising on sum graph |
| `hamiltonian_sum` (§4.6 super-add. Step 2-3) | `hamiltonian (G ⊕g H) p (Sum.elim σ₁ σ₂) = hamiltonian G p σ₁ + hamiltonian H p σ₂` | `SumModel.lean` | Ising on sum graph |
| `partitionFunction_sum` (§4.6 super-add. Step 4) | `Z_{G ⊕g H}(p) = Z_G(p) · Z_H(p)` | `SumModel.lean` | Ising on sum graph |
| `log_partitionFunction_sum` | `log Z_{G ⊕g H}(p) = log Z_G(p) + log Z_H(p)` | `SumModel.lean` | Ising on sum graph |
| `partitionFunction_mul_le_of_sum_le` / `log_partitionFunction_add_le_of_sum_le` (§4.6 super-add. Step 5 prep) | `G ⊕g H ≤ G' ⇒ Z_G · Z_H ≤ Z_{G'}` (ferromagnetic), log form | `SumModel.lean` | Ising on sum graph |
| `partitionFunction_map_equiv` / `log_partitionFunction_map_equiv` | `e : V ≃ W ⇒ Z_{G.map e} = Z_G` (iso invariance) | `PartitionFunctionIso.lean` | Step 5 infra |
| `log_partitionFunction_inducedGraph_disjUnion_super_additive` (§4.6 Prop 4.6.1 Step 5 body) | `Disjoint Λ₁ Λ₂ ⇒ log Z_{inducedGraph Λ₁} + log Z_{inducedGraph Λ₂} ≤ log Z_{inducedGraph (Λ₁ ∪ Λ₂)}` (ferromagnetic) | `AmbientLatticeSum.lean` | Step 5 body |
| `Ambient.freeEnergyΛ_weighted_super_additive_of_nonempty` | `|Λ₁|·f_{Λ₁} + |Λ₂|·f_{Λ₂} ≤ |Λ₁∪Λ₂|·f_{Λ₁∪Λ₂}` (disjoint nonempty, ferromagnetic) | `AmbientLatticeSum.lean` | `freeEnergyΛ` wrapper |
| `partitionFunction_ge_one_of_ferromagnetic` / `log_partitionFunction_nonneg_of_ferromagnetic` | `Z_G ≥ 1` (ferromagnetic), log form | `FreeEnergy.lean` | Step 5/Fekete infra |
| `{log_,}partitionFunction{,Λ}_inducedGraph_le_of_disjoint_union` | `Disjoint Λ₁ Λ₂ ⇒ Z_{Λ₁} ≤ Z_{Λ₁∪Λ₂}` (ferromagnetic), log / multiplicative and generic / `Λ`-wrapped forms | `AmbientLatticeSum.lean` | Monotonicity step toward Fekete |
| `Ambient.card_mul_freeEnergyΛ_le_of_disjoint_union` | `Λ₁.Nonempty, Disjoint Λ₁ Λ₂ ⇒ |Λ₁|·f_{Λ₁} ≤ |Λ₁∪Λ₂|·f_{Λ₁∪Λ₂}` (ferromagnetic) | `AmbientLatticeSum.lean` | `freeEnergyΛ` weighted monotonicity |
| `card_mul_freeEnergy_eq_log_partitionFunction` | **Basic identity**: `|ι| · f_G(p) = log Z_G(p)` for `0 < |ι|` (base layer of the existing `Λ` wrapper) | `FreeEnergy.lean` | Unfold `freeEnergy = |ι|⁻¹ · log Z` |
| `Ambient.partitionFunctionAlongExhaustion_monotone_volume` / `log_partitionFunctionAlongExhaustion_monotone_volume` | `Z_{Λ.volume n} ≤ Z_{Λ.volume (n+1)}` (ferromagnetic) along Exhaustion, log form | `AmbientLatticeSum.lean` | Fekete input |
| `Ambient.partitionFunctionAlongExhaustion_monotone` / `log_partitionFunctionAlongExhaustion_monotone` | `Monotone` predicate form (for mathlib convergence lemmas) | `AmbientLatticeSum.lean` | Fekete input wrapper |
| `Ambient.{log_,}partitionFunctionAlongExhaustion_tendsto_atTop` | `Z_n, log Z_n → ∞` along any exhaustion of infinite `V` (ferromagnetic). Uses bot-graph lower bound + `Exhaustion.tendsto_card_atTop` | `AmbientLatticeSum.lean` | `|Λ.volume n|·log 2 ≤ log Z_n` divergence |
| `Ambient.freeEnergyInfinite_{le_uniform_upper_bound,ge_log_two_cosh,ge_log_two,pos,nonneg}` | `0 < log 2 ≤ log(2·cosh(β·h)) ≤ freeEnergyInfinite G Λ p ≤ log 2 + |β|·(|J|·c + |h|)` (ferromagnetic + BoundedEdgeDensity + `[Nonempty V]`) | `AmbientLatticeSum.lean` | `limsup` two-sided bounds + positivity |
| `Ambient.freeEnergyInfinite_eq_of_tendsto` | **Limsup = limit bridge**: `Tendsto (freeEnergyAlongExhaustion G Λ p) atTop (𝓝 L) ⇒ freeEnergyInfinite G Λ p = L` | `AmbientLatticeSum.lean` | Infrastructure for the pending Fekete convergence |
| `Ambient.freeEnergyInfinite_of_eventually_const` | **Eventually-constant corollary**: `∀ᶠ n, f_n = c ⇒ freeEnergyInfinite = c` | `AmbientLatticeSum.lean` | Direct corollary of `_eq_of_tendsto`, generalizes `_beta_zero` / `_zero_params` |
| `Ambient.freeEnergyInfinite_{beta_zero,zero_params}_of_eventually_nonempty` | **Weakened versions**: `∀ᶠ n, (Λ.volume n).Nonempty ⇒ freeEnergyInfinite G Λ ⟨J, h, 0⟩ = log 2` (resp. `⟨0, 0, β⟩`). Hypothesis automatic under `[Nonempty V]` via `Exhaustion.eventually_volume_nonempty`. | `AmbientLatticeSum.lean` | Weakening of the all-stages-nonempty forms via `_of_eventually_const` |
| `{hamiltonian,partitionFunction,freeEnergy}_J_zero` + `_eq_bot_at_J_zero` identities (base + along-exhaustion + ∞-vol) + `freeEnergyInfinite_J_zero_of_eventually_nonempty` | **J=0 graph-independent closed form**: `Z_G ⟨0, h, β⟩ = (2·cosh(βh))^|ι|`, `f_G ⟨0, h, β⟩ = log(2·cosh(βh))` (any `G`). Five core ⊥-equivalence identities (`_eq_bot_at_J_zero` suffix on hamiltonian / partitionFunction / freeEnergy / freeEnergyAlongExhaustion / freeEnergyInfinite) provide graph-independence at every layer; `_J_zero` closed forms are `.trans` compositions with `_bot`. | `GibbsMeasure.lean`, `FreeEnergy.lean`, `AmbientLattice.lean`, `AmbientLatticeSum.lean` | Fourth slice of zero-parameter closed forms (β=0 / J=h=0 / bot / J=0); full ⊥-equivalence chain for reuse |
| `Ambient.freeEnergyAlongExhaustion_J_zero_tendsto_of_eventually_nonempty` | **First non-trivial ∞-vol Tendsto**: `Tendsto (freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩) atTop (𝓝 (log(2·cosh(βh))))` under eventually nonempty. J=0 slice sidesteps the general Fekete program via eventually-constant stagewise sequence. | `AmbientLatticeSum.lean` | §4.6 Prop 4.6.1 J=0 slice, first concrete Tendsto convergence |
| `Ambient.freeEnergyAlongExhaustion_{beta_zero,zero_params}_tendsto_of_eventually_nonempty` | **∞-vol Tendsto for β=0 / J=h=0 slices**: `Tendsto … atTop (𝓝 (log 2))` under eventually nonempty. Same eventually-constant pattern, completes zero-parameter slice Tendsto coverage. | `AmbientLatticeSum.lean` | §4.6 Prop 4.6.1 slice set: β=0, J=h=0, J=0 all now have Tendsto forms |
| `Ambient.freeEnergyInfinite_{J_zero,beta_zero,zero_params}_of_nonempty` | **Slice closed forms without user-supplied hypothesis** under `[Nonempty V]` (uses `Exhaustion.eventually_volume_nonempty` automatically) | `AmbientLatticeSum.lean` | Convenience wrappers |
| `correlation_beta_zero_vanish_of_nonempty_A` | **β=0 correlation vanishes**: `A.Nonempty ⇒ correlation G ⟨J, h, 0⟩ A = 0` (GJ §4.1 infinite-temperature slice). Proof: Boltzmann weight = 1 at β=0; reduces to existing `sum_config_spinProduct_eq_zero` (NonnegCorrelations.lean, via `flipAt` involution). | `Inequalities/NonnegCorrelations.lean` | New β=0 closed form of correlation function |
| `correlation_zero_params_vanish_of_nonempty_A` | **J=h=0 correlation vanishes**: `A.Nonempty ⇒ correlation G ⟨0, 0, β⟩ A = 0`. At J=h=0 the Hamiltonian is identically zero so weight = 1; same `sum_config_spinProduct_eq_zero` chain. | `Inequalities/NonnegCorrelations.lean` | J=h=0 closed form of correlation (companion to β=0) |
| `correlationΛ_zero_params_vanish_of_nonempty` / `correlationAlongExhaustion_zero_params_vanish` / `correlationInfinite_zero_params_vanish` | **3-layer lifts of J=h=0 correlation vanish** (parallel to β=0 lifts PR #183) | `AmbientLattice.lean` | Full J=h=0 correlation coverage across layers |
| `correlationΛ_beta_zero_vanish_of_nonempty` / `correlationAlongExhaustion_beta_zero_vanish` / `correlationInfinite_beta_zero_vanish` | **3-layer lifts of β=0 correlation vanish**: Λ-layer (direct base call), along-exhaustion (dite branching on `A ⊆ Λ.volume n`), ∞-vol (ciSup of zero sequence). | `AmbientLattice.lean` | Full β=0 correlation coverage across layers |
| `correlation_empty` + `correlation{Λ,AlongExhaustion,Infinite}_empty` | **Empty-set correlation = 1** (Gibbs measure normalization): `⟨σ^∅⟩ = 1` at all 4 layers (base + Λ + along-exhaustion + ∞-vol) | `GibbsMeasure.lean`, `AmbientLattice.lean` | GJ §4.1 correlation normalization |
| `correlation_eq_bot_at_J_zero` | **J=0 correlation graph-independence**: `correlation G ⟨0, h, β⟩ A = correlation ⊥ ⟨0, h, β⟩ A`. Extends the `_eq_bot_at_J_zero` identity chain (hamiltonian / partitionFunction / freeEnergy) to the correlation layer; Boltzmann weight numerator and partition function denominator both graph-independent at `J=0`, so the ratio is. | `GibbsMeasure.lean` | Correlation-layer complement of PR #175 J=0 identity chain |
| `correlation_bot_closed` + `correlation_J_zero` | **`⊥`-graph correlation closed form (any `p`)** + **J=0 lift**: `correlation ⊥ p A = tanh(p.β · p.h)^|A|` (J-independent since `⊥` has no edges); composed with graph-independence at J=0 yields `correlation G ⟨0, h, β⟩ A = tanh(β·h)^|A|` for any ambient graph `G`. Proof uses `Fintype.sum_prod_piFinset` for per-site factorisation, `sum_spin_sign_exp_sign` (2·sinh) and `sum_exp_spin_sign` (2·cosh) for site sums. | `GibbsMeasure.lean` | Correlation-layer counterpart to `partitionFunction_J_zero` / `freeEnergy_J_zero`; 5th zero-parameter closed form (β=0 / J=h=0 / bot / J=0 free-energy / J=0 correlation) |
| `magnetizationInfinite_beta_zero` | **β=0 ∞-vol magnetization = 0**: specialization of `correlationInfinite_beta_zero_vanish` at singleton; at infinite temperature all spin averages vanish | `AmbientLattice.lean` | Complements `magnetizationInfinite_zero_at_h_zero` (h=0 case) |
| `magnetization_beta_zero` | **β=0 finite-volume magnetization = 0**: specialization of `correlation_beta_zero_vanish_of_nonempty_A` at singleton; finite-volume companion to `magnetizationInfinite_beta_zero` | `PhaseTransition.lean` | Complements `magnetization_zero_at_h_zero` (h=0 case) |
| `Ambient.freeEnergyInfinite_monotone_ambient_subgraph` | `G₁ ≤ G₂ ⇒ freeEnergyInfinite G₁ Λ p ≤ freeEnergyInfinite G₂ Λ p` (ferromagnetic + BoundedEdgeDensity + `[Nonempty V]`) | `AmbientLatticeSum.lean` | `limsup` ambient subgraph monotonicity |
| `Ambient.freeEnergyInfinite_neg_h` / `freeEnergyInfinite_eq_abs_h` | `h`-evenness: `freeEnergyInfinite G Λ ⟨J, -h, β⟩ = freeEnergyInfinite G Λ ⟨J, h, β⟩ = freeEnergyInfinite G Λ ⟨J, |h|, β⟩` | `AmbientLatticeSum.lean` | `limsup` h-symmetry |
| `Ambient.freeEnergyInfinite_monotone_{J,h,beta,abs_h}` | `MonotoneOn (X ↦ freeEnergyInfinite ...)` in each parameter (ferromagnetic-style + BoundedEdgeDensity + Nonempty V), plus `|h|`-monotonicity | `AmbientLatticeSum.lean` | `limsup` monotonicity package |
| `leeYangDomain` (+ `isOpen_leeYangDomain`, `leeYangDomain_subset_slitPlane`, `real_pos_mem_leeYangDomain`) | **Lee-Yang domain** `{h ∈ ℂ : |Im h| < Re h}` as an open subset of `slitPlane` containing the positive real axis. | `ComplexAnalyticity.lean` | Complex finite, GJ Thm 4.6.2 domain |
| `leeYangFugacity` / `leeYangFugacityVec` (+ norm formula, continuous, entire, coordinatewise `‖·‖ < 1` on Lee-Yang domain, `ne_zero`, scalar `MapsTo` unit ball) | Complex fugacity `h ↦ e^{-2βh}` and its uniform-site vector version; scalar `MapsTo` sends Lee-Yang domain into the open unit disk, and `leeYangFugacityVec_norm_lt_one` gives the coordinatewise unit-disk bound. | `ComplexAnalyticity.lean` | Complex finite |
| `leeYangNormalization` (+ `ne_zero`, `analyticAt_joint`, `ofReal_pos`) | Normalisation prefactor `exp(βJ|E| + βh|ι|)`; entire in `(J,h,β)`, non-vanishing, positive at real parameters. | `ComplexAnalyticity.lean` | Complex finite |
| `isingEdgePoly_eval_leeYangFugacityVec_ne_zero` / `leeYangNormalization_mul_isingEdgePoly_eval_ne_zero` | **Lee-Yang polynomial non-zero on Lee-Yang domain**: at uniform complex fugacity the Ising partition polynomial is non-zero; combined with the non-vanishing normalisation prefactor. | `ComplexAnalyticity.lean` | Complex finite |
| `partitionFunctionComplex_eq_normalization_mul_isingEdgePoly` | **Friedli–Velenik factorisation** (FV (3.63)–(3.65), pp. 122–123): `Z(J, h, β) = exp(βJ|E| + βh|ι|) · P_E(z)` with `z_k = e^{-2βh}`, `t_e = e^{-2βJ}`. Proven via per-site / per-edge Boltzmann factorisation and `configFinsetEquiv` bijection. | `ComplexAnalyticity.lean` | Complex finite (real J, β; complex h) |
| `partitionFunctionComplex_ne_zero_on_leeYangDomain` | **Z ≠ 0 on Lee-Yang domain** (GJ Thm 4.6.2 non-vanishing half): for real ferromagnetic `J > 0`, real `β > 0`, complex `h` with `|Im h| < Re h`, `partitionFunctionComplex ≠ 0`. Direct from FV factorisation + Lee-Yang nonvanishing. | `ComplexAnalyticity.lean` | Complex finite |
| `freeEnergyComplex_analyticAt_h_ofReal` | **Real-slice slitPlane corollary** (preliminary to GJ Thm 4.6.2): for arbitrary real `J, h₀, β`, `freeEnergyComplex G (J:ℂ) h (β:ℂ)` is analytic in `h` at `(h₀:ℂ)`. Uses `partitionFunctionComplex_mem_slitPlane_of_real` + `freeEnergyComplex_analyticAt_h` — no Lee-Yang domain argument, no ferromagnetic hypothesis. | `ComplexAnalyticity.lean` | Complex finite |
| `leeYangSubdomain` (+ `abs_spinSum_le`, `exp_neg_beta_hamiltonian_re_pos`, `partitionFunctionComplex_re_pos_of_leeYangSubdomain`, `_mem_slitPlane_of_leeYangSubdomain`, `freeEnergyComplex_analyticAt_h_of_leeYangSubdomain`) | **Subdomain of Lee-Yang** where `β · |Im h| · |ι| < π/2`: direct `Re Z > 0` proof (each Boltzmann weight has `Re(exp(a + ib)) = exp(a)·cos(b) > 0` under this bound on `|b|`), hence `Z ∈ slitPlane`, hence `freeEnergyComplex` analytic in `h`. Finite-volume `freeEnergyComplex` analyticity on this subdomain is established without a branch argument. Subdomain shrinks as `β·|ι|` grows, so it does not directly lift to the infinite volume limit; full Lee-Yang extension still requires a branch construction. | `ComplexAnalyticity.lean` | Complex finite (subdomain) |
| `vitali_bridge` + `vitali_bridge_leeYangDomain` | **Vitali bridge** (abstract ∞-vol ingredient): locally uniform limit of holomorphic functions on an open set `U` is holomorphic on `U`. Direct application of mathlib `TendstoLocallyUniformlyOn.differentiableOn`. Specialised to `U = leeYangDomain`. | `ComplexAnalyticity.lean` | ∞-vol Vitali (bridge) |
| `norm_partitionFunctionComplex_le_partitionFunction` + `norm_partitionFunctionComplex_le_trivial_bound` + `norm_complex_log_le` + `norm_freeEnergyComplex_le_trivial_bound` | **Uniform-on-compacts bounds for the complex Ising free energy** (Montel input for ∞-vol Vitali). `|Z(J, h, β)| ≤ Z(J, Re h, β)` (real Ising partition function), then combined with `partitionFunction_upper` gives `|Z| ≤ 2^|ι| · exp(|β|·(|J|·|E| + |Re h|·|ι|))`, and with `‖Complex.log z‖ ≤ |Real.log ‖z‖| + π` gives `‖f_complex‖ ≤ (|log ‖Z‖| + π)/|ι|`. These yield the uniform bound on `‖f_complex‖` on compacta of Lee-Yang required to apply Montel and hence Vitali (via `vitali_bridge_leeYangDomain`). | `ComplexAnalyticity.lean` | ∞-vol Vitali (boundedness input) |
| `logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain` + `exists_logZ_branch_on_ball_of_leeYangDomain` + `exists_normalised_logZ_branch_on_ball` + `exists_logZ_holomorphic_branch_on_ball` + `exists_logZ_analytic_branch_on_ball` + `exists_logZ_analyticAt_of_leeYangDomain` + `exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain` + `analyticBranch_freeEnergyComplex_leeYangDomain` | **Full Lee-Yang domain finite-volume log branch** (local branch form of GJ §4.6 Thm 4.6.2). For real ferromagnetic `β > 0`, `J > 0`, `[Nonempty ι]`: at every `h₀ ∈ leeYangDomain`, there is an analytic `f : ℂ → ℂ` with `exp(|ι|·f(h₀)) = Z(h₀)` and `f(h₀) = Complex.log(Z(h₀))/|ι|`. Construction via Morera (`DifferentiableOn.isExactOn_ball`) on a ball around `h₀`, giving a primitive `g` of `Z'/Z`; then `F(z) := exp(g(z))/Z(z)` has derivative `0` by chain + quotient rules, constant on the convex ball, value `1` at centre ⇒ `exp(g) = Z` pointwise on the ball; `g` analytic via `DifferentiableOn.analyticOnNhd`. The principal-branch `freeEnergyComplex` may differ from `f` by a locally-constant `2πi·k/|ι|` shift where `Z` crosses the negative real axis; the local branch `f` is continuous across such crossings. | `ComplexAnalyticity.lean` | Complex finite (full Lee-Yang via local branch) |

**Status (as of 2026-04-19, merged via PR #200 `52ea2f1`).** The
local-branch form of GJ Thm 4.6.2 finite-volume analyticity is
formalised: `exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain`
gives, at every `h₀ ∈ leeYangDomain`, an analytic function `f` with
`exp(|ι|·f(h₀)) = Z(h₀)` and `f(h₀) = freeEnergyComplex(h₀)`
(basepoint). Additionally, the Vitali bridge
`vitali_bridge_leeYangDomain` and all modulus bounds
(`norm_partitionFunctionComplex_le_*`,
`norm_freeEnergyComplex_le_trivial_bound`) are in place.

**Not yet formalized** (future PRs):
- Montel-style locally uniform convergence of `f_Λ` on Lee-Yang
  (uniform boundedness + real-axis Fekete + identity theorem); mathlib
  lacks a direct Montel theorem, so self-implementation is required.
- Piping through `vitali_bridge_leeYangDomain` to conclude `f_∞`
  analytic on Lee-Yang.
- Global branch via patching local branches (simply-connected).
- Note: the principal-branch `freeEnergyComplex` may be discontinuous
  where `Z` crosses the negative real axis; the local-branch form
  is the mathematically correct statement of GJ Thm 4.6.2.

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
| `prop_5_4_2_along_exhaustion` | **Per-stage Peierls bound along an exhaustion** `Λ : Ambient.Exhaustion V`: uniformly `0 ≤ 1 − ⟨σᵢₙ⟩₊^{Λₙ,Bₙ} ≤ exp(-cβ)` for every `n`, given per-stage preconnectedness, non-empty sets of `+`-boundary-condition sites, and the common exponential-bound hypothesis. Direct application of `prop_5_4_2_self_contained` at each `Λ.volume n`. Scaffolding toward the genuine infinite-volume lift. | `PeierlsInfinite.lean` | Exhaustion (+ BC) |
| `prop_5_4_2_limsup_le` | **Direct limsup corollary of Prop 5.4.2 along an exhaustion**: under the same per-stage hypotheses, `Filter.limsup (n ↦ 1 − ⟨σᵢₙ⟩₊^{Λₙ,Bₙ}) atTop ≤ exp(-cβ)`. Proof via `Filter.limsup_le_of_le` + `isCoboundedUnder_le_of_eventually_le` (cobounded from the per-stage nonneg lower bound). No canonical ∞-vol `+`-BC expectation is required. | `PeierlsInfinite.lean` | Exhaustion (+ BC), limsup form |
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
| `freeEnergyAlongExhaustion_zero_params` | Along-exhaustion specialization: `f_n(0, 0, β) = log 2` per nonempty stage |
| `freeEnergyInfinite_zero_params` | **∞-volume lift**: `freeEnergyInfinite G Λ ⟨0, 0, β⟩ = log 2` (all stages nonempty) |
| `partitionFunctionAlongExhaustion_zero_params` / `log_partitionFunctionAlongExhaustion_zero_params` | Partition-function side: `Z = 2^|Λ.volume n|`, `log Z = |Λ.volume n| · log 2` at `⟨0, 0, β⟩` |
| `partitionFunctionAlongExhaustion_beta_zero` / `log_partitionFunctionAlongExhaustion_beta_zero` | β=0 companion: `Z = 2^|Λ.volume n|`, `log Z = |Λ.volume n| · log 2` at `⟨J, h, 0⟩` (any J, h) |
| `partitionFunction{,Λ,AlongExhaustion}_ge_two_pow_card_of_ferromagnetic` | Strong ferromagnetic lower bound: `2^|ι| ≤ Z_G(p)` (via `⊥` + `cosh ≥ 1` + monotone); log form `|ι| · log 2 ≤ log Z` |
| `log_partitionFunction{,Λ,AlongExhaustion}_ge_card_mul_log_two_cosh_of_ferromagnetic` | **Sharp log-Z lower bound**: `|ι| · log(2·cosh(βh)) ≤ log Z_G(p)` (via `Z ≥ Z_⊥ = (2 cosh(βh))^|ι|` + `Real.log_pow`) |
| `partitionFunction{,Λ,AlongExhaustion}_ge_two_cosh_pow_card_of_ferromagnetic` | **Sharp Z lower bound (non-log)**: `(2·cosh(βh))^|ι| ≤ Z_G(p)` (direct from `partitionFunction_bot` + `monotone_subgraph`); exp-image of the log form |
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
| §4.6 | **Prop 4.6.1 (`f_Λ` convergence)** | **Done (disjoint-tower + `BoundedEdgeDensity`) + concrete J=0 / β=0 instances** | Base form: `freeEnergyAlongExhaustion_tendsto_of_superadditive` (4 bundled hypotheses — `hcard_add`, `hsuper`, `hbdd`, `hcard_one`). Relaxed form: `freeEnergyAlongExhaustion_tendsto_of_disjoint_tower` (3 hypotheses: `hcard_add`, `hsuper`, `hcard_one` + the structural `BoundedEdgeDensity G Λ`). The explicit `hbdd` is discharged automatically via `BddAbove_freeEnergyAlongExhaustion_range`. Bundled form: `DisjointTowerHypotheses` record (`card_add`/`super`/`card_one`) + `freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses` wrapper. Generic builder: `DisjointTowerHypotheses.of_log_linear_card` (whenever `log Z_Λ = |Λ| · c` for some constant `c`, super-additivity is automatic equality under `hcard_add`). Concrete J=0 and β=0 instances: `DisjointTowerHypotheses.of_{J_zero,beta_zero}` via the log-linear builder; closed forms `log_partitionFunctionΛ_{J_zero,beta_zero}`. Corollaries `freeEnergyAlongExhaustion_{J_zero,beta_zero}_tendsto_of_hcard_add` give Fekete convergence from `hcard_add + hcard_one + BoundedEdgeDensity` alone. Proof (general): apply mathlib `Subadditive.tendsto_lim` to `u_n := -log Z_{Λ_n}`, translate via `card_n = n · card_1` to `freeEnergyAlongExhaustion`. The super-additivity input is provided by `log_partitionFunctionΛ_disjUnion_super_additive` in the general case. Supporting: `freeEnergy_convergent_subgraph`, `freeEnergyInfinite_eq_of_tendsto`. |
| §4.6 | **Thm 4.6.2 (analyticity)** | **Partial (merged through PR #200, `52ea2f1`): finite-real + real-basepoint finite-complex + Friedli-Velenik factorisation + Z ≠ 0 on Lee-Yang domain + local analytic log-Z branch pointwise on Lee-Yang + Lee-Yang subdomain slitPlane + Vitali bridge + modulus bounds. ∞-vol locally uniform convergence TODO (no Montel in mathlib)** | Finite-real free energy analyticity: `freeEnergyH_analyticOn` etc. Finite-complex support: `partitionFunctionComplex_analyticAt_{h,J,beta}` (Z entire in each parameter) + `freeEnergyComplex_analyticAt_{h,J,beta}` under `Z ∈ Complex.slitPlane` (log via mathlib `AnalyticAt.clog`). Joint analyticity: `partitionFunctionComplex_analyticAt_joint` / `freeEnergyComplex_analyticAt_joint` (3-variable `(J,h,β) ∈ ℂ³`, slitPlane hypothesis for `f`). Real-complex compat: `partitionFunction_ofReal_eq_partitionFunctionComplex` + `freeEnergy_ofReal_eq_freeEnergyComplex`. Real-slice slitPlane: `partitionFunctionComplex_mem_slitPlane_of_real`; real-slice corollary `freeEnergyComplex_analyticAt_h_ofReal` (analyticity of `freeEnergyComplex` at any real basepoint `(h₀:ℂ)`, via slitPlane membership; no Lee-Yang or ferromagnetic hypothesis). Lee-Yang domain infrastructure: `leeYangDomain` (open, `⊆ slitPlane`, contains positive real axis), `leeYangFugacity(Vec)` (entire, maps domain into unit ball), `leeYangNormalization` (entire, non-vanishing, `ofReal_pos`). **Friedli-Velenik factorisation**: `partitionFunctionComplex_eq_normalization_mul_isingEdgePoly` — `Z(J, h, β) = exp(βJ|E| + βh|ι|) · P_E(z)` (FV (3.63)–(3.65) pp. 122–123). **Z ≠ 0 on Lee-Yang domain** (Thm 4.6.2 non-vanishing half): `partitionFunctionComplex_ne_zero_on_leeYangDomain`. (All in `ComplexAnalyticity.lean`.) **Not yet**: slitPlane-membership on the full complex Lee-Yang domain (needs branch-selection / winding-number argument from real-positive basepoint), infinite-volume Vitali lift. |
| §4.6 | Lee–Yang nonvanishing (Ising) | **Done** | `isingEdgePoly_nonvanishing_of_graph` |
| §4.7 | Two-component spins | Out of scope | XY model |

### Chapter 5 (Phase transitions)

| Section | Result | Status | Notes |
|---|---|---|---|
| §5.1 | Pure/mixed phase criteria | **Done (algebraic)** | `mixed_phase_truncated2`, `mixed_phase_pure_iff`, `truncated2_le_one` |
| §5.1 | Spontaneous magnetization `m*` (p. 77) | **Done (complete)** | `spontaneousMagnetization` (infimum form) + `tendsto_…_nhdsGT` (right-limit `m* = lim_{h→0+} M(h)`) + nonneg/≤1/≤M(h)/indep_exhaustion |
| §5.1 | Cluster property — `J = 0` (non-interacting) slice (pp. 72–74) | **Done (trivial slice)** | `truncated2_J_zero_of_ne` (`Inequalities/GHS.lean`): for `i ≠ j` and any `h, β`, `truncated2 G ⟨0, h, β⟩ i j = 0`. Via `correlation_J_zero` (`⟨σ^A⟩ = tanh(β·h)^{\|A\|}`) + `Finset.card_pair`/`card_singleton`. The non-interacting slice: the Hamiltonian has no `J`-coupling, so any two distinct sites factorise identically — no distance / separation / high-temperature hypothesis needed (`β` is arbitrary). General-`J` decay-at-large-separation in pure phases remains unformalized. |
| §5.1 | Cluster property — `β = 0` (infinite-temperature) slice (pp. 72–74) | **Done (trivial slice)** | `truncated2_beta_zero` (`Inequalities/GHS.lean`): for any `J, h` and any sites `i, j` (not necessarily distinct), `truncated2 G ⟨J, h, 0⟩ i j = 0`. Via `correlation_beta_zero_vanish_of_nonempty_A`. Companion to the `J = 0` slice. At `β = 0` the diagonal truncated value also vanishes since `⟨σ_i⟩ = 0`. |
| §5.1 | Cluster property — truncated 3-point trivial slices (pp. 72–74) | **Done (trivial slices)** | `truncated3_J_zero_of_pairwise_distinct` and `truncated3_beta_zero` (`Inequalities/GHS.lean`): the Ursell 3-point function vanishes at `J = 0` (pairwise distinct sites, via `correlation_J_zero` giving the `t³ - 3t³ + 2t³ = 0` combination with `t = tanh(β·h)`) and at `β = 0` (any sites; coincident indices are collapsed at the Finset level in the definition of `truncated3`, so the statement is unconditional on distinctness — cf. `truncated2_beta_zero`). Extension of `truncated2_*` lemmas to the 3-point case. `correlation_beta_zero_vanish_of_nonempty_A` is the common ingredient at `β = 0`. |
| §5.1 | Cluster property — ∞-vol J=0 slice (pp. 72–74) | **Done (trivial slice ∞-vol lift)** | `correlationInfinite_J_zero` (`AmbientLattice.lean`): for ferromagnetic `⟨0, h, β⟩`, `correlationInfinite G Λ ⟨0, h, β⟩ A = tanh(β·h)^{\|A\|}`. Proof via `correlationAlongExhaustion_J_zero_of_subset` (stagewise closed form using `liftFinset_card` helper) + `correlationAlongExhaustion_J_zero_eventually_eq` (eventually-constant sequence) + uniqueness of limits against `correlationAlongExhaustion_tendsto_ciSup`. Corollary: `truncated2Infinite_J_zero_of_ne` — ∞-vol counterpart of `truncated2_J_zero_of_ne` (PR #207). |
| §5.1 | Cluster property — ∞-vol β=0 slice (pp. 72–74) | **Done (trivial slice ∞-vol lift)** | `correlationInfinite_beta_zero_vanish_of_nonempty_A` (`AmbientLattice.lean`): for any `J, h` and nonempty `A`, `correlationInfinite G Λ ⟨J, h, 0⟩ A = 0`. Proof: the sequence `correlationAlongExhaustion G Λ ⟨J, h, 0⟩ A` is pointwise zero (`correlation_beta_zero_vanish_of_nonempty_A` on the lifted subset when `A ⊆ Λ.volume n`; default-0 otherwise), hence `⨆ = 0`. No ferromagnetic hypothesis needed. Corollary: `truncated2Infinite_beta_zero` — ∞-vol counterpart of `truncated2_beta_zero` (PR #208). |
| §5.1 | Cluster property — ∞-vol truncated 3-point trivial slices (pp. 72–74) | **Done (trivial slices ∞-vol lift)** | `truncated3Infinite_J_zero_of_pairwise_distinct` and `truncated3Infinite_beta_zero` (`AmbientLattice.lean`): ∞-vol counterparts of the finite-volume PR #209 slices. J=0 ferromagnetic case via `correlationInfinite_J_zero` + Finset card identities (`t³ - 3·t³ + 2·t³ = 0`). β=0 case via `correlationInfinite_beta_zero_vanish_of_nonempty_A` (all seven Ursell terms zero). |
| §5.1 | Cluster property — Lebowitz 4-point β=0 slice (finite + ∞-vol) (pp. 72–74) | **Done (β=0 trivial slice)** | `truncated4_beta_zero` (`Inequalities/GHS.lean`) and `truncated4Infinite_beta_zero` (`AmbientLattice.lean`): at β=0 the Lebowitz 4-point truncated function vanishes identically, via `correlation_beta_zero_vanish_of_nonempty_A` / `correlationInfinite_beta_zero_vanish_of_nonempty_A`. Note: J=0 does *not* give vanishing (for pairwise distinct sites the Lebowitz 4-point is `-2·t⁴` with `t = tanh(β·h)`), so only the β=0 slice is added.
| §5.1 | Cluster property — Lebowitz 4-point J=0 closed form (finite + ∞-vol) (pp. 72–74) | **Done (J=0 closed form)** | `truncated4_J_zero_of_pairwise_distinct` (`Inequalities/GHS.lean`) and `truncated4Infinite_J_zero_of_pairwise_distinct` (`AmbientLattice.lean`, ferromagnetic): at J=0 with pairwise distinct sites, the Lebowitz 4-point equals `-2·t⁴` with `t = tanh(β·h)`. Via `correlation_J_zero` / `correlationInfinite_J_zero` + Finset card identities (4, 2, 2, 2, 2, 2, 2). This is non-vanishing in general but always `≤ 0`, consistent with Cor 4.3.3's `U₄ ≤ 0` bound at h=0 (the J=0 slice here is a separate special case, not a direct witness). |
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

1. **Prop 4.6.1 (free energy convergence) Fekete completion**:
   Fekete-style convergence of `freeEnergyAlongExhaustion` is now
   available through three API entry points (all in
   `AmbientLatticeSum.lean`):
   `freeEnergyAlongExhaustion_tendsto_of_superadditive` (base, 4
   bundled hypotheses);
   `freeEnergyAlongExhaustion_tendsto_of_disjoint_tower` (relaxed,
   `BoundedEdgeDensity` replaces the explicit `BddAbove`
   hypothesis); and
   `freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses`
   (bundled form taking a `DisjointTowerHypotheses` record).
   Dropping the remaining disjoint-tower hypotheses (`hcard_add`,
   `hsuper`, `hcard_one`) requires translation invariance and is
   a follow-up step.
   *(The `correlationAlongExhaustion` convergence side, originally
   listed here as "not yet proved", is in fact discharged by
   `correlationAlongExhaustion_tendsto_ciSup` +
   `correlationAlongExhaustion_convergent` in
   `AmbientLattice.lean`, and is now covered by the §4.2 Thm 4.2.3
   row in the progress table.)*
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
