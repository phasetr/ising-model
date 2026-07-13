import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer
import IsingModel.BetaDerivative

/-!
# Finite susceptibility and Lebowitz derivative bounds at ℤ^d

This module contains the concrete §17.1 finite-susceptibility wrapper and
§17.5 Lebowitz derivative bound layer split from the original `Inequalities`
module: Step 149 finite susceptibility below the critical inverse temperature,
Steps 157--166 finite-volume derivative bounds, finite-to-infinite correlation
comparison, Lebowitz sum bounds, and high-temperature consequences.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## §17.1 Finite susceptibility below critical inverse temperature (Step 149) -/

/-- **Susceptibility bounded above in the high-temperature regime** (GJ §17.1, ℤ^d):
for `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J` (high temperature,
i.e., above the critical temperature `T_c = 1/β_c`),
`susceptibilityInfinite (latticeGraph d) Λ ⟨J,0,β⟩ i`
`  ≤ ∑' j, truncated2Infinite (latticeGraph d) Λ ⟨J,0,β⟩ i j`.

Combines `susceptibilityInfinite_le_tsum_truncated2Infinite` (Step 148, `HighTemp.lean`)
with `truncated2Infinite_summable_of_lt_criticalInverseTemp` (Step 147) to give a concrete
finite upper bound on the susceptibility in the high-temperature regime.

**Physics**: the quantity `∑' j, truncated2Infinite ... i j` (the tsum of the Ursell
2-point function) provides a finite upper bound on the magnetic susceptibility,
a hallmark of the paramagnetic (disordered) phase (β < β_c = criticalInverseTemp).
GJ §17.1 motivates this finiteness as the defining property of exponential clustering. -/
theorem susceptibilityInfinite_latticeGraph_le_tsum_of_lt_criticalInverseTemp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i
      ≤ ∑' j : Fin d → ℤ,
          truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) i j := by
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · -- β = 0: susceptibilityInfinite = 0 and ∑' = 0
    simp only [susceptibilityInfinite_eq_ciSup]
    apply ciSup_le; intro n
    simp only [susceptibilityAlongExhaustion]
    split_ifs with hi
    · rw [susceptibilityΛ_apply, susceptibility_apply]
      simp only [truncated2_beta_zero, Finset.sum_const_zero]
      exact tsum_nonneg (fun j => by rw [truncated2Infinite_beta_zero])
    · exact tsum_nonneg (fun j => by rw [truncated2Infinite_beta_zero])
  · exact susceptibilityInfinite_le_tsum_truncated2Infinite (IsingModel.latticeGraph d) Λ
        ⟨hJ, le_refl _, hβ_pos⟩ i
        (truncated2Infinite_summable_of_lt_criticalInverseTemp Λ hβ_pos.le hJ h i)

/-- **β-derivative bound for two-point function on ℤ^d** (Step 157, GJ §17.5):
For the induced lattice graph on any finite Λ ⊆ ℤ^d, vertices r ≠ s in ↑Λ,
the β-derivative of `correlation G ⟨J,0,β'⟩ {r,s}` is bounded by the Lebowitz sum
plus the uniform constant `J * 4d`.

Combines `correlation_beta_deriv_le_lebowitz_tight` (Step 154) with
`incidentEdgesFinset_inducedLatticeGraph_card_le` (Step 155): the incident-edge
term `J * |{e: r∈e ∨ s∈e}|` is at most `J * 4d`, uniform in |Λ|.

Reference: Glimm–Jaffe §17.5 pp.311–312. -/
theorem inducedLatticeGraph_beta_deriv_le
    {d : ℕ} (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (r s : ↑Λ) (hrs : r ≠ s) :
    ∃ dval : ℝ,
      HasDerivAt (fun β' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) dval β ∧
      dval ≤ J * ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
            Sym2.lift ⟨fun u v =>
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {s, u},
              fun u v => by ring⟩ e
        + J * (4 * ↑d) := by
  set G := inducedGraph (IsingModel.latticeGraph d) Λ
  obtain ⟨dval, hd, hbound⟩ :=
    IsingModel.correlation_beta_deriv_le_lebowitz_tight G J β hJ hβ r s hrs
  refine ⟨dval, hd, ?_⟩
  have h_cast : (↑(G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)).card : ℝ) ≤ 4 * ↑d := by
    exact_mod_cast incidentEdgesFinset_inducedLatticeGraph_card_le d Λ r s
  linarith [mul_le_mul_of_nonneg_left h_cast hJ]

/-- **J-derivative bound for two-point function on ℤ^d** (Step 218):
For the induced lattice graph on any finite Λ ⊆ ℤ^d, vertices r ≠ s in ↑Λ,
the J-derivative of `correlation G ⟨J',0,β⟩ {r,s}` at h = 0 is bounded by the
Lebowitz sum plus the uniform constant `β * 4d`.

Combines `correlation_J_deriv_le_lebowitz_tight` (Step 217) with
`incidentEdgesFinset_inducedLatticeGraph_card_le` (Step 155): the incident-edge
term `β * |{e: r∈e ∨ s∈e}|` is at most `β * 4d`, uniform in |Λ|.

Direct J-direction analogue of `inducedLatticeGraph_beta_deriv_le` (Step 157).

Reference: parallel to Glimm–Jaffe §17.5 pp.311–312. -/
theorem inducedLatticeGraph_J_deriv_le
    {d : ℕ} (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (r s : ↑Λ) (hrs : r ≠ s) :
    ∃ dval : ℝ,
      HasDerivAt (fun J' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J', 0, β⟩ : IsingParams ℝ) {r, s}) dval J ∧
      dval ≤ β * ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
            Sym2.lift ⟨fun u v =>
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {s, u},
              fun u v => by ring⟩ e
        + β * (4 * ↑d) := by
  set G := inducedGraph (IsingModel.latticeGraph d) Λ
  obtain ⟨dval, hd, hbound⟩ :=
    IsingModel.correlation_J_deriv_le_lebowitz_tight G J β hJ hβ r s hrs
  refine ⟨dval, hd, ?_⟩
  have h_cast : (↑(G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)).card : ℝ) ≤ 4 * ↑d := by
    exact_mod_cast incidentEdgesFinset_inducedLatticeGraph_card_le d Λ r s
  linarith [mul_le_mul_of_nonneg_left h_cast hβ.le]

/-- **Bridge: finite-vol correlation ≤ ∞-vol correlation** (Step 158, GJ §17.5):
For any exhaustion Λ of ℤ^d, stage n, and vertices r, s : ↑(Λ.volume n),
the induced-graph correlation is bounded above by the infinite-volume correlation:
```
correlation (inducedGraph (latticeGraph d) Λ_n) ⟨J, 0, β⟩ {r, s}
  ≤ correlationInfinite (latticeGraph d) Λ ⟨J, 0, β⟩ {r.val, s.val}
```

Proof: `correlation G_n p {r,s} = correlationAlongExhaustion G Λ p {r.val,s.val} n`
(by unfolding the exhaustion definition and showing `liftFinset {r.val,s.val} h = {r,s}`)
then apply `correlationAlongExhaustion_le_correlationInfinite`.

Used to bound the Lebowitz sum from Step 157 by the ∞-vol susceptibility.

Reference: Glimm–Jaffe §17.5. -/
theorem correlation_inducedLatticeGraph_le_correlationInfinite
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (n : ℕ) (r s : ↑(Λ.volume n)) :
    IsingModel.correlation
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s}
      ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {r.val, s.val} := by
  have h_sub : {r.val, s.val} ⊆ Λ.volume n :=
    Finset.insert_subset r.2 (Finset.singleton_subset_iff.mpr s.2)
  have heq : IsingModel.correlation
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s}
      = Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {r.val, s.val} n := by
    rw [Ambient.correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
    congr 1
    ext x
    simp only [Ambient.mem_liftFinset, Finset.mem_insert, Finset.mem_singleton,
               Subtype.ext_iff]
  rw [heq]
  exact Ambient.correlationAlongExhaustion_le_correlationInfinite _ _ _ _ _


/-! ## Step 160: Lebowitz sum ≤ product of correlation sums (GJ §17.5) -/

/-- **Dart injection bound** (Step 160 helper): for non-negative `f g : V → ℝ`,
`∑ d : G.Dart, f d.fst * g d.snd ≤ (∑ u, f u) * (∑ v, g v)`.

Proof: the dart-to-pair map `d ↦ (d.fst, d.snd)` injects into `V × V`; adding the
non-negative non-dart pairs to the sum only increases it. -/
private lemma sum_dart_le_mul_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f g : V → ℝ) (hf : ∀ v, 0 ≤ f v) (hg : ∀ v, 0 ≤ g v) :
    ∑ d : G.Dart, f d.fst * g d.snd ≤ (∑ u : V, f u) * (∑ v : V, g v) := by
  classical
  -- Expand RHS to double sum
  rw [Fintype.sum_mul_sum]
  -- Group LHS darts by fst vertex
  rw [(Finset.sum_fiberwise_of_maps_to (fun (d : G.Dart) _ => Finset.mem_univ d.fst)
       (fun d => f d.fst * g d.snd)).symm]
  apply Finset.sum_le_sum
  intro u _
  -- Replace f d.fst by f u (using filter condition d.fst = u), then factor
  have h1 : ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u), f d.fst * g d.snd
      = ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u), f u * g d.snd :=
    Finset.sum_congr rfl (fun d hd => by rw [(Finset.mem_filter.mp hd).2])
  rw [h1, ← Finset.mul_sum, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hf u)
  -- Bound ∑_{d: d.fst=u} g(d.snd) ≤ ∑_v g v via image
  have hinj : ∀ d₁ ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u),
      ∀ d₂ ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u),
      d₁.snd = d₂.snd → d₁ = d₂ := by
    intro d₁ hd₁ d₂ hd₂ h
    exact SimpleGraph.Dart.ext d₁ d₂ (Prod.ext
      ((Finset.mem_filter.mp hd₁).2.trans (Finset.mem_filter.mp hd₂).2.symm) h)
  calc ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u), g d.snd
      = ∑ v ∈ (Finset.univ.filter (fun d : G.Dart => d.fst = u)).image (fun d => d.snd), g v := by
          rw [← Finset.sum_image hinj]
      _ ≤ ∑ v : V, g v := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro v _; exact Finset.mem_univ v
          · intro v _ _; exact hg v

/-- **Lebowitz sum bounded by product of correlation sums** (Step 160, GJ §17.5):
For the induced ℤ^d lattice graph on `Λ`,
```
∑_{e ∈ E(G)} (corr(r,u)·corr(s,v) + corr(r,v)·corr(s,u))
  ≤ (∑_j corr(r,j)) · (∑_j corr(s,j))
```

Proof: apply the dart product sum identity (`sum_edgeFinset_sym2_lift_prod_eq_sum_dart`),
then bound the dart sum by the full Cartesian product via the injectivity of
`d ↦ (d.fst, d.snd)` and GKS non-negativity.

Reference: Glimm–Jaffe §17.5. -/
theorem inducedLatticeGraph_leb_sum_le_corr_sum_mul
    {d : ℕ} (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (r s : ↑Λ) :
    let G := inducedGraph (IsingModel.latticeGraph d) Λ
    let p := (⟨J, 0, β⟩ : IsingParams ℝ)
    ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
            IsingModel.correlation G p {r, u} * IsingModel.correlation G p {s, v} +
            IsingModel.correlation G p {r, v} * IsingModel.correlation G p {s, u},
            fun u v => by ring⟩ e
    ≤ (∑ j : ↑Λ, IsingModel.correlation G p {r, j}) *
      (∑ j : ↑Λ, IsingModel.correlation G p {s, j}) := by
  intro G p
  have hf : Ferromagnetic p := ⟨hJ, le_refl 0, hβ⟩
  have hcorr_nn : ∀ (x y : ↑Λ), 0 ≤ IsingModel.correlation G p {x, y} :=
    fun x y => gks_first G p hf _
  rw [SimpleGraph.sum_edgeFinset_sym2_lift_prod_eq_sum_dart]
  exact sum_dart_le_mul_sum G
    (fun u => IsingModel.correlation G p {r, u})
    (fun v => IsingModel.correlation G p {s, v})
    (fun u => hcorr_nn r u)
    (fun v => hcorr_nn s v)

/-- **Lebowitz sum bounded by susceptibilityAlongExhaustion product** (Step 161, GJ §17.5):
`∑_{e∈E(G_n)} leb_n(e) ≤ susceptibilityAlongExhaustion_n(r) · susceptibilityAlongExhaustion_n(s)`.

Proof: apply Step 160 + identify `∑_j corr_n(r,j) = susceptibilityAlongExhaustion_n(r.val)`
via `susceptibility_h_zero` + `susceptibilityAlongExhaustion_of_mem`.

Reference: Glimm–Jaffe §17.5. -/
theorem inducedLatticeGraph_leb_sum_le_susc_along
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (n : ℕ) (r s : ↑(Λ.volume n)) :
    ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, u},
            fun u v => by ring⟩ e
    ≤ susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val n *
      susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val n := by
  classical
  set G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n) with hG
  -- Identify ∑_j corr_n(r,j) = susceptibilityAlongExhaustion n r.val via h=0
  have hsusc_r : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val n
      = ∑ j : ↑(Λ.volume n), IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, j} := by
    rw [susceptibilityAlongExhaustion_of_mem _ _ _ r.2, susceptibilityΛ_apply,
        IsingModel.susceptibility_h_zero]
  have hsusc_s : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val n
      = ∑ j : ↑(Λ.volume n), IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {s, j} := by
    rw [susceptibilityAlongExhaustion_of_mem _ _ _ s.2, susceptibilityΛ_apply,
        IsingModel.susceptibility_h_zero]
  rw [hsusc_r, hsusc_s]
  exact inducedLatticeGraph_leb_sum_le_corr_sum_mul (Λ.volume n) J β hJ hβ r s

/-- **Lebowitz sum bounded by susceptibilityInfinite product** (Step 162, GJ §17.5):
Under `BddAbove` for the susceptibility sequences,
`∑_{e∈E(G_n)} leb_n(e) ≤ susceptibilityInfinite_r · susceptibilityInfinite_s`.

Proof: Step 161 + `le_ciSup` (monotone convergence to the supremum).

Reference: Glimm–Jaffe §17.5. -/
theorem inducedLatticeGraph_leb_sum_le_susceptibilityInfinite
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (n : ℕ) (r s : ↑(Λ.volume n))
    (hbdd_r : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val m)))
    (hbdd_s : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val m))) :
    ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, u},
            fun u v => by ring⟩ e
    ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) r.val *
      susceptibilityInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) s.val := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  -- Step 161 bound
  have h161 := inducedLatticeGraph_leb_sum_le_susc_along Λ J β hJ hβ n r s
  -- susc_along_n ≤ susc_∞ via le_ciSup
  have hr : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val n
      ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val := by
    rw [susceptibilityInfinite_eq_ciSup]; exact le_ciSup hbdd_r n
  have hs : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val n
      ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val := by
    rw [susceptibilityInfinite_eq_ciSup]; exact le_ciSup hbdd_s n
  -- Non-negativity
  have hr_nn : 0 ≤ susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val n :=
    susceptibilityAlongExhaustion_nonneg _ _ _ hf _ _
  have hs_nn : 0 ≤ susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val n :=
    susceptibilityAlongExhaustion_nonneg _ _ _ hf _ _
  exact h161.trans (mul_le_mul hr hs hs_nn (hr_nn.trans hr))

/-! ## Moved: Lebowitz derivative ≤ χ²(Σ²+4d) wrappers

The two wrappers
`inducedLatticeGraph_beta_deriv_le_susc_sq`,
`inducedLatticeGraph_J_deriv_le_susc_sq` now live in
`LatticeMassLebowitzDerivativeSuscSq.lean`. -/


/-! ## Moved: high-temperature Lebowitz / derivative wrappers

The three wrappers
`inducedLatticeGraph_leb_sum_le_susceptibilityInfinite_high_temp`,
`inducedLatticeGraph_beta_deriv_le_susc_sq_high_temp`,
`inducedLatticeGraph_J_deriv_le_susc_sq_high_temp`
now live in `LatticeMassLebowitzDerivativeHighTemp.lean`. -/





end Ambient
end IsingModel
