import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivative
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CorrelationAlongExhaustionDeriv
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagBoundsCorrAlongExMonotone

/-!
# Lebowitz β-derivative bound on `correlationAlongExhaustion` at ℤ^d

This module composes the per-stage Lebowitz β-derivative bound for the induced
lattice graph (`inducedLatticeGraph_beta_deriv_le`, Step 157 in
`LatticeMassLebowitzDerivative.lean`) with the covered-stage
`HasDerivAt` transfer (`hasDerivAt_correlationAlongExhaustion_of_hasDerivAt_inducedGraph`,
PR #3143 in `CorrelationAlongExhaustionDeriv.lean`) to yield the Lebowitz
β-derivative bound on `correlationAlongExhaustion` in the volume coverage
regime.

This is the per-stage real-axis input for Issue #2965 Phase C: the alternative
route to the Lemma 17.5.2 β-derivative increment bound bypassing the CE /
Cauchy decomposition entirely.

References:

* Glimm-Jaffe, *Quantum Physics* (2nd ed.), §17.5, Cor. 4.3.3 (Lebowitz),
  pp. 311-312.
* Issue #2965 (Phase C: real-axis Lebowitz route).
-/

namespace IsingModel
namespace Ambient

variable {d : ℕ}

/-- **Lebowitz β-derivative bound on `correlationAlongExhaustion`** at the
induced lattice subgraph of ℤ^d (Issue #2965 Phase C, real-axis Lebowitz
route).

Given a covered pair `{r, s} ⊆ Λ.volume n`, the β-derivative of the family
`fun β' => correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β'⟩ {r, s} n`
at any `β > 0` exists and is bounded by the standard Lebowitz edge sum on
the induced subgraph plus the uniform `J · 4d` boundary correction:

    ∂_β c_n ≤ J · ∑_{e ∈ E(G_n)} [c_n(r,u)·c_n(s,v) + c_n(r,v)·c_n(s,u)]
            + J · 4d

where `c_n(·, ·) := correlation (inducedGraph (latticeGraph d) (Λ.volume n)) ⟨J,0,β⟩ {·, ·}`.

Composes `inducedLatticeGraph_beta_deriv_le` (Step 157) with
`hasDerivAt_correlationAlongExhaustion_of_hasDerivAt_inducedGraph` (PR #3143). -/
theorem correlationAlongExhaustion_latticeGraph_beta_deriv_le
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (n : ℕ)
    (hr : r ∈ Λ.volume n) (hs : s ∈ Λ.volume n)
    (hrs_sub : ({r, s} : Finset (Fin d → ℤ)) ⊆ Λ.volume n) :
    ∃ dval : ℝ,
      HasDerivAt
        (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s} n) dval β ∧
      dval ≤ J * ∑ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
            Sym2.lift ⟨fun u v =>
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨r, hr⟩ : ↑(Λ.volume n)), u} *
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨s, hs⟩ : ↑(Λ.volume n)), v} +
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨r, hr⟩ : ↑(Λ.volume n)), v} *
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨s, hs⟩ : ↑(Λ.volume n)), u},
              fun u v => by ring⟩ e
          + J * (4 * ↑d) := by
  classical
  have hrs_sub_subtypes :
      (⟨r, hr⟩ : ↑(Λ.volume n)) ≠ ⟨s, hs⟩ := fun heq =>
    hrs (congrArg Subtype.val heq)
  obtain ⟨dval, hd_ind, hbound⟩ :=
    inducedLatticeGraph_beta_deriv_le (Λ.volume n) J β hJ hβ
      (⟨r, hr⟩ : ↑(Λ.volume n)) ⟨s, hs⟩ hrs_sub_subtypes
  -- The induced-graph derivative HasDerivAt lifts to correlationAlongExhaustion
  -- via PR #3143's transfer, using that liftFinset {r, s} hrs_sub = {⟨r, hr⟩, ⟨s, hs⟩}.
  refine ⟨dval, ?_, hbound⟩
  have h_lift :
      Ambient.liftFinset ({r, s} : Finset (Fin d → ℤ)) hrs_sub
        = ({(⟨r, hr⟩ : ↑(Λ.volume n)), ⟨s, hs⟩} : Finset ↑(Λ.volume n)) :=
    Ambient.liftFinset_pair hrs_sub hr hs
  have h_ind' : HasDerivAt
      (fun β' => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β'⟩ : IsingParams ℝ)
        (Ambient.liftFinset ({r, s} : Finset (Fin d → ℤ)) hrs_sub)) dval β := by
    rw [show (fun β' => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β'⟩ : IsingParams ℝ)
        (Ambient.liftFinset ({r, s} : Finset (Fin d → ℤ)) hrs_sub)) =
      (fun β' => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β'⟩ : IsingParams ℝ)
        ({(⟨r, hr⟩ : ↑(Λ.volume n)), ⟨s, hs⟩} : Finset ↑(Λ.volume n)))
      from funext (fun β' => by rw [h_lift])]
    exact hd_ind
  exact hasDerivAt_correlationAlongExhaustion_of_hasDerivAt_inducedGraph
    (IsingModel.latticeGraph d) Λ J 0 ({r, s} : Finset (Fin d → ℤ)) n hrs_sub h_ind'

/-- **Closed-form `deriv`-version of `correlationAlongExhaustion_latticeGraph_beta_deriv_le`**
(Issue #2965 Phase C, real-axis Lebowitz route).

Identical hypotheses to `correlationAlongExhaustion_latticeGraph_beta_deriv_le`, but the
conclusion replaces the `∃ dval, HasDerivAt … dval β ∧ dval ≤ …` form with the closed-form
`deriv (…) β ≤ …`. Obtained by `HasDerivAt.deriv` on the witness produced by the existential
form, so downstream consumers can use the bound without unpacking the existential. -/
theorem correlationAlongExhaustion_latticeGraph_beta_deriv_eq_le
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (n : ℕ)
    (hr : r ∈ Λ.volume n) (hs : s ∈ Λ.volume n)
    (hrs_sub : ({r, s} : Finset (Fin d → ℤ)) ⊆ Λ.volume n) :
    deriv (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s} n) β
      ≤ J * ∑ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
            Sym2.lift ⟨fun u v =>
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨r, hr⟩ : ↑(Λ.volume n)), u} *
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨s, hs⟩ : ↑(Λ.volume n)), v} +
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨r, hr⟩ : ↑(Λ.volume n)), v} *
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨s, hs⟩ : ↑(Λ.volume n)), u},
              fun u v => by ring⟩ e
          + J * (4 * ↑d) := by
  obtain ⟨dval, hdrv, hbound⟩ :=
    correlationAlongExhaustion_latticeGraph_beta_deriv_le Λ J β hJ hβ hrs n hr hs hrs_sub
  rw [hdrv.deriv]
  exact hbound

/-- **β-derivative of `correlationAlongExhaustion` bounded by `J·χ_∞² + J·4d`** (GJ §17.5
Cor. 4.3.3 + Step 162, Issue #2965 Phase C, real-axis Lebowitz route).

Composes `correlationAlongExhaustion_latticeGraph_beta_deriv_eq_le` (deriv-form Lebowitz
bound on `correlationAlongExhaustion`) with `inducedLatticeGraph_leb_sum_le_susceptibilityInfinite`
(Step 162, the Lebowitz edge sum is bounded by the infinite-volume susceptibility product).
Yields the closed-form bound

    ∂_β c_n ≤ J·χ_∞(r)·χ_∞(s) + J·4d

under the `BddAbove` hypotheses on the per-stage susceptibility sequences at `r` and `s`
that Step 162 requires (these hold in particular in the high-temperature region where
`χ_∞` is finite). The right-hand side is uniform in `n`, providing the per-stage
real-axis input for the Phase C convergence-rate argument. -/
theorem correlationAlongExhaustion_latticeGraph_beta_deriv_le_susceptibilityInfinite_sq
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (n : ℕ)
    (hr : r ∈ Λ.volume n) (hs : s ∈ Λ.volume n)
    (hrs_sub : ({r, s} : Finset (Fin d → ℤ)) ⊆ Λ.volume n)
    (hbdd_r : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r m)))
    (hbdd_s : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s m))) :
    deriv (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s} n) β
      ≤ J * (susceptibilityInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) r *
            susceptibilityInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) s)
        + J * (4 * ↑d) := by
  -- Bound the deriv by Lebowitz cross sum + J·4d
  have hleb := correlationAlongExhaustion_latticeGraph_beta_deriv_eq_le
    Λ J β hJ hβ hrs n hr hs hrs_sub
  -- Bound the Lebowitz cross sum by χ_∞(r)·χ_∞(s) (Step 162)
  have hsusc := inducedLatticeGraph_leb_sum_le_susceptibilityInfinite Λ J β hJ hβ n
    (⟨r, hr⟩ : ↑(Λ.volume n)) ⟨s, hs⟩ hbdd_r hbdd_s
  -- Chain: deriv ≤ J·(Lebowitz sum) + J·4d ≤ J·(χ_∞·χ_∞) + J·4d
  have hmul : J * ∑ e ∈ _, _ ≤ J * (_ * _) := mul_le_mul_of_nonneg_left hsusc hJ
  linarith [hleb, hmul]

/-- **β-derivative of `correlationAlongExhaustion` bounded by `J·χ_along² + J·4d`** (GJ §17.5
Cor. 4.3.3, pp. 311–312, + Step 161, Issue #2965 Phase C, real-axis Lebowitz route).

Unconditional susceptibility-product β-derivative bound: drops the `BddAbove` hypotheses of
`…_le_susceptibilityInfinite_sq` by using Step 161
(`inducedLatticeGraph_leb_sum_le_susc_along`) — the per-stage Lebowitz cross sum is bounded
by the *per-stage* susceptibility product, which is unconditionally well-defined:

    ∂_β c_n ≤ J·χ_along_n(r)·χ_along_n(s) + J·4d

(`c_n := correlationAlongExhaustion (latticeGraph d) Λ ⟨J,0,β⟩ {r,s} n`,
`χ_along_n(x) := susceptibilityAlongExhaustion (latticeGraph d) Λ ⟨J,0,β⟩ x n`).

Same hypotheses as the existential form, *without* any boundedness assumption on the
susceptibility sequences. Composes `correlationAlongExhaustion_latticeGraph_beta_deriv_eq_le`
with Step 161 (`inducedLatticeGraph_leb_sum_le_susc_along`). -/
theorem correlationAlongExhaustion_latticeGraph_beta_deriv_le_susceptibilityAlong_sq
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (n : ℕ)
    (hr : r ∈ Λ.volume n) (hs : s ∈ Λ.volume n)
    (hrs_sub : ({r, s} : Finset (Fin d → ℤ)) ⊆ Λ.volume n) :
    deriv (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s} n) β
      ≤ J * (susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) r n *
            susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) s n)
        + J * (4 * ↑d) := by
  have hleb := correlationAlongExhaustion_latticeGraph_beta_deriv_eq_le
    Λ J β hJ hβ hrs n hr hs hrs_sub
  have hsusc := inducedLatticeGraph_leb_sum_le_susc_along Λ J β hJ hβ n
    (⟨r, hr⟩ : ↑(Λ.volume n)) ⟨s, hs⟩
  have hmul : J * ∑ e ∈ _, _ ≤ J * (_ * _) := mul_le_mul_of_nonneg_left hsusc hJ
  linarith [hleb, hmul]

/-! ## J-direction parallel

The J-direction analogues parallel the β-direction theorems above. The same
Lebowitz cross-product sum bounds the J-derivative, with boundary term `β · 4d`
instead of `J · 4d` (cf. `inducedLatticeGraph_J_deriv_le`, Step 218). -/

/-- **J-direction Lebowitz bound on `correlationAlongExhaustion`** at the
induced lattice subgraph of ℤ^d (Issue #2965 Phase C, real-axis Lebowitz route,
J-direction parallel of `correlationAlongExhaustion_latticeGraph_beta_deriv_le`).

Composes `inducedLatticeGraph_J_deriv_le` (Step 218, J-direction Lebowitz on
the induced subgraph) with `hasDerivAt_correlationAlongExhaustion_J_of_hasDerivAt_inducedGraph`
(J-direction `HasDerivAt` transfer) using `liftFinset_pair`. Yields, for
`r ≠ s ∈ Λ.volume n` and `J ≥ 0`, `β > 0`:

    ∂_J c_n ≤ β · ∑_{e ∈ E(G_n)} [c_n(r,u)·c_n(s,v) + c_n(r,v)·c_n(s,u)]
            + β · 4d

with `c_n := correlationAlongExhaustion (latticeGraph d) Λ ⟨J,0,β⟩ {r,s} n`. -/
theorem correlationAlongExhaustion_latticeGraph_J_deriv_le
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (n : ℕ)
    (hr : r ∈ Λ.volume n) (hs : s ∈ Λ.volume n)
    (hrs_sub : ({r, s} : Finset (Fin d → ℤ)) ⊆ Λ.volume n) :
    ∃ dval : ℝ,
      HasDerivAt
        (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J', 0, β⟩ : IsingParams ℝ) {r, s} n) dval J ∧
      dval ≤ β * ∑ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
            Sym2.lift ⟨fun u v =>
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨r, hr⟩ : ↑(Λ.volume n)), u} *
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨s, hs⟩ : ↑(Λ.volume n)), v} +
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨r, hr⟩ : ↑(Λ.volume n)), v} *
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨s, hs⟩ : ↑(Λ.volume n)), u},
              fun u v => by ring⟩ e
          + β * (4 * ↑d) := by
  classical
  have hrs_sub_subtypes :
      (⟨r, hr⟩ : ↑(Λ.volume n)) ≠ ⟨s, hs⟩ := fun heq =>
    hrs (congrArg Subtype.val heq)
  obtain ⟨dval, hd_ind, hbound⟩ :=
    inducedLatticeGraph_J_deriv_le (Λ.volume n) J β hJ hβ
      (⟨r, hr⟩ : ↑(Λ.volume n)) ⟨s, hs⟩ hrs_sub_subtypes
  refine ⟨dval, ?_, hbound⟩
  have h_lift :
      Ambient.liftFinset ({r, s} : Finset (Fin d → ℤ)) hrs_sub
        = ({(⟨r, hr⟩ : ↑(Λ.volume n)), ⟨s, hs⟩} : Finset ↑(Λ.volume n)) :=
    Ambient.liftFinset_pair hrs_sub hr hs
  have h_ind' : HasDerivAt
      (fun J' => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J', 0, β⟩ : IsingParams ℝ)
        (Ambient.liftFinset ({r, s} : Finset (Fin d → ℤ)) hrs_sub)) dval J := by
    rw [show (fun J' => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J', 0, β⟩ : IsingParams ℝ)
        (Ambient.liftFinset ({r, s} : Finset (Fin d → ℤ)) hrs_sub)) =
      (fun J' => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J', 0, β⟩ : IsingParams ℝ)
        ({(⟨r, hr⟩ : ↑(Λ.volume n)), ⟨s, hs⟩} : Finset ↑(Λ.volume n)))
      from funext (fun J' => by rw [h_lift])]
    exact hd_ind
  exact hasDerivAt_correlationAlongExhaustion_J_of_hasDerivAt_inducedGraph
    (IsingModel.latticeGraph d) Λ 0 β ({r, s} : Finset (Fin d → ℤ)) n hrs_sub h_ind'

/-- **Closed-form `deriv`-version of `correlationAlongExhaustion_latticeGraph_J_deriv_le`**
(Issue #2965 Phase C, J-direction parallel). Mirrors
`correlationAlongExhaustion_latticeGraph_beta_deriv_eq_le`: the existential form's `dval`
becomes `deriv (…) J` via `HasDerivAt.deriv`. -/
theorem correlationAlongExhaustion_latticeGraph_J_deriv_eq_le
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (n : ℕ)
    (hr : r ∈ Λ.volume n) (hs : s ∈ Λ.volume n)
    (hrs_sub : ({r, s} : Finset (Fin d → ℤ)) ⊆ Λ.volume n) :
    deriv (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', 0, β⟩ : IsingParams ℝ) {r, s} n) J
      ≤ β * ∑ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
            Sym2.lift ⟨fun u v =>
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨r, hr⟩ : ↑(Λ.volume n)), u} *
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨s, hs⟩ : ↑(Λ.volume n)), v} +
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨r, hr⟩ : ↑(Λ.volume n)), v} *
                IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ)
                  {(⟨s, hs⟩ : ↑(Λ.volume n)), u},
              fun u v => by ring⟩ e
          + β * (4 * ↑d) := by
  obtain ⟨dval, hdrv, hbound⟩ :=
    correlationAlongExhaustion_latticeGraph_J_deriv_le Λ J β hJ hβ hrs n hr hs hrs_sub
  rw [hdrv.deriv]
  exact hbound

/-- **Unconditional J-derivative bound by `β·χ_along² + β·4d`** (Issue #2965 Phase C,
J-direction parallel of `…_beta_deriv_le_susceptibilityAlong_sq`). Composes the J-deriv
form with Step 161. -/
theorem correlationAlongExhaustion_latticeGraph_J_deriv_le_susceptibilityAlong_sq
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (n : ℕ)
    (hr : r ∈ Λ.volume n) (hs : s ∈ Λ.volume n)
    (hrs_sub : ({r, s} : Finset (Fin d → ℤ)) ⊆ Λ.volume n) :
    deriv (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', 0, β⟩ : IsingParams ℝ) {r, s} n) J
      ≤ β * (susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) r n *
            susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) s n)
        + β * (4 * ↑d) := by
  have hleb := correlationAlongExhaustion_latticeGraph_J_deriv_eq_le
    Λ J β hJ hβ hrs n hr hs hrs_sub
  have hsusc := inducedLatticeGraph_leb_sum_le_susc_along Λ J β hJ hβ n
    (⟨r, hr⟩ : ↑(Λ.volume n)) ⟨s, hs⟩
  have hmul : β * ∑ e ∈ _, _ ≤ β * (_ * _) := mul_le_mul_of_nonneg_left hsusc hβ.le
  linarith [hleb, hmul]

/-- **J-derivative of `correlationAlongExhaustion` bounded by `β·χ_∞² + β·4d`** (GJ §17.5
Cor. 4.3.3, pp. 311–312, + Step 162, Issue #2965 Phase C, J-direction parallel of
`…_beta_deriv_le_susceptibilityInfinite_sq`).

Conditional susceptibility-infinite J-derivative bound: requires `BddAbove` of the per-stage
susceptibility sequences at `r`, `s` (Step 162 hypothesis; holds in particular in the
high-temperature region). Gives the infinite-volume susceptibility-product form

    ∂_J c_n ≤ β · χ_∞(r) · χ_∞(s) + β · 4d

(boundary term `β·4d`, matching the J-direction Lebowitz bound).

Composes `correlationAlongExhaustion_latticeGraph_J_deriv_eq_le` with Step 162
(`inducedLatticeGraph_leb_sum_le_susceptibilityInfinite`). -/
theorem correlationAlongExhaustion_latticeGraph_J_deriv_le_susceptibilityInfinite_sq
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (n : ℕ)
    (hr : r ∈ Λ.volume n) (hs : s ∈ Λ.volume n)
    (hrs_sub : ({r, s} : Finset (Fin d → ℤ)) ⊆ Λ.volume n)
    (hbdd_r : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r m)))
    (hbdd_s : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s m))) :
    deriv (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', 0, β⟩ : IsingParams ℝ) {r, s} n) J
      ≤ β * (susceptibilityInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) r *
            susceptibilityInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) s)
        + β * (4 * ↑d) := by
  have hleb := correlationAlongExhaustion_latticeGraph_J_deriv_eq_le
    Λ J β hJ hβ hrs n hr hs hrs_sub
  have hsusc := inducedLatticeGraph_leb_sum_le_susceptibilityInfinite Λ J β hJ hβ n
    (⟨r, hr⟩ : ↑(Λ.volume n)) ⟨s, hs⟩ hbdd_r hbdd_s
  have hmul : β * ∑ e ∈ _, _ ≤ β * (_ * _) := mul_le_mul_of_nonneg_left hsusc hβ.le
  linarith [hleb, hmul]

/-! ## Per-stage β/J-derivative non-negativity (sandwich lower bound)

In the ferromagnetic h=0 regime, the per-stage `correlationAlongExhaustion` is monotone
non-decreasing in both `β` and `J` (`correlationAlongExhaustion_latticeGraph_monotone_{beta,J}`).
Equivalently, its β- and J-derivatives are non-negative. Combined with the upper bounds
above, this gives a **two-sided sandwich** on the per-stage derivative — the more useful
form when only an upper bound on the *magnitude* `|deriv …|` is needed. -/

/-- **β-derivative of `correlationAlongExhaustion` is non-negative** (GJ §17.5 GKS-II,
Issue #2965 Phase C, real-axis Lebowitz route).

In the ferromagnetic h=0 regime, the per-stage `correlationAlongExhaustion` is monotone
non-decreasing in `β` (GKS-II / `correlationAlongExhaustion_latticeGraph_monotone_beta`).
Hence `0 ≤ deriv (β' ↦ correlationAlongExhaustion …) β`. Used together with the upper
bounds above to form a two-sided sandwich:

    0 ≤ deriv (β' ↦ correlationAlongExhaustion …) β ≤ J·χ_along² + J·4d. -/
theorem correlationAlongExhaustion_latticeGraph_beta_deriv_nonneg
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ deriv (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) A n) β := by
  -- The function is monotone on Ioi 0; convert derivWithin to deriv since Ioi 0 is open.
  have hmono : MonotoneOn
      (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) A n) (Set.Ioi 0) :=
    fun β₁ hβ₁ β₂ _ h₁₂ =>
      Ambient.correlationAlongExhaustion_latticeGraph_monotone_beta d Λ hJ (le_refl 0)
        A hβ₁ h₁₂ n
  have hwithin : 0 ≤ derivWithin
      (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) A n) (Set.Ioi 0) β :=
    hmono.derivWithin_nonneg
  rwa [derivWithin_of_isOpen isOpen_Ioi (Set.mem_Ioi.mpr hβ)] at hwithin

/-- **J-derivative of `correlationAlongExhaustion` is non-negative** (GKS-II J-direction,
Issue #2965 Phase C, J-direction parallel of `..._beta_deriv_nonneg`).

In the ferromagnetic h=0 regime, the per-stage `correlationAlongExhaustion` is monotone
non-decreasing in `J` (`correlationAlongExhaustion_latticeGraph_monotone_J`). Hence
`0 ≤ deriv (J' ↦ correlationAlongExhaustion …) J`. -/
theorem correlationAlongExhaustion_latticeGraph_J_deriv_nonneg
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ deriv (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', 0, β⟩ : IsingParams ℝ) A n) J := by
  have hmono : MonotoneOn
      (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', 0, β⟩ : IsingParams ℝ) A n) (Set.Ioi 0) :=
    fun J₁ hJ₁ J₂ _ h₁₂ =>
      Ambient.correlationAlongExhaustion_latticeGraph_monotone_J d Λ (le_refl 0) hβ
        A hJ₁.le h₁₂ n
  have hwithin : 0 ≤ derivWithin
      (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', 0, β⟩ : IsingParams ℝ) A n) (Set.Ioi 0) J :=
    hmono.derivWithin_nonneg
  rwa [derivWithin_of_isOpen isOpen_Ioi (Set.mem_Ioi.mpr hJ)] at hwithin

/-- **Two-sided sandwich for the β-derivative of `correlationAlongExhaustion`** (Issue
#2965 Phase C, real-axis Lebowitz route, full sandwich).

Combines the GKS-II non-negativity (`..._beta_deriv_nonneg`) with the unconditional
susceptibility-product upper bound (`..._beta_deriv_le_susceptibilityAlong_sq`):

    0 ≤ deriv (β' ↦ correlationAlongExhaustion …) β
      ≤ J · χ_along_n(r) · χ_along_n(s) + J · 4d.

Equivalent to `|deriv (…) β| ≤ J·χ_along²+J·4d` in the ferromagnetic h=0 regime, exposing
the per-stage derivative magnitude that downstream consumers typically need. -/
theorem correlationAlongExhaustion_latticeGraph_beta_deriv_sandwich
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (n : ℕ)
    (hr : r ∈ Λ.volume n) (hs : s ∈ Λ.volume n)
    (hrs_sub : ({r, s} : Finset (Fin d → ℤ)) ⊆ Λ.volume n) :
    0 ≤ deriv (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s} n) β
      ∧ deriv (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s} n) β
        ≤ J * (susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) r n *
              susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) s n)
          + J * (4 * ↑d) :=
  ⟨correlationAlongExhaustion_latticeGraph_beta_deriv_nonneg Λ J β hJ hβ
     ({r, s} : Finset (Fin d → ℤ)) n,
   correlationAlongExhaustion_latticeGraph_beta_deriv_le_susceptibilityAlong_sq
     Λ J β hJ hβ hrs n hr hs hrs_sub⟩

/-- **Two-sided sandwich for the J-derivative of `correlationAlongExhaustion`** (Issue
#2965 Phase C, J-direction parallel of the β-direction sandwich).

Combines the J-direction GKS-II non-negativity with the unconditional susceptibility-product
upper bound. -/
theorem correlationAlongExhaustion_latticeGraph_J_deriv_sandwich
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (n : ℕ)
    (hr : r ∈ Λ.volume n) (hs : s ∈ Λ.volume n)
    (hrs_sub : ({r, s} : Finset (Fin d → ℤ)) ⊆ Λ.volume n) :
    0 ≤ deriv (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', 0, β⟩ : IsingParams ℝ) {r, s} n) J
      ∧ deriv (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', 0, β⟩ : IsingParams ℝ) {r, s} n) J
        ≤ β * (susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) r n *
              susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) s n)
          + β * (4 * ↑d) :=
  ⟨correlationAlongExhaustion_latticeGraph_J_deriv_nonneg Λ J β hJ hβ
     ({r, s} : Finset (Fin d → ℤ)) n,
   correlationAlongExhaustion_latticeGraph_J_deriv_le_susceptibilityAlong_sq
     Λ J β hJ.le hβ hrs n hr hs hrs_sub⟩

end Ambient
end IsingModel
