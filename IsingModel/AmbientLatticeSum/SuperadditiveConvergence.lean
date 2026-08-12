import IsingModel.AmbientLatticeSum.InfiniteBounds

/-!
# Fekete convergence of the free-energy density along an exhaustion

The stage sequence `freeEnergyAlongExhaustion G Λ p` takes at a stage `n` the free energy of
the subgraph of `G` induced by the finite volume `Λ.volume n`, and `freeEnergyInfinite G Λ p`
is its `Filter.limsup` along `atTop`. What is proved here is that under hypotheses making
the tower of volumes additive and the logarithm of the partition function super-additive
along it, that `limsup` is an actual limit: the stage sequence tends to
`freeEnergyInfinite G Λ p`.

Three structural hypotheses on the exhaustion `Λ : Exhaustion V` and the parameters
`p : IsingParams ℝ` recur. The stage cardinalities add,
`(Λ.volume (m + n)).card = (Λ.volume m).card + (Λ.volume n).card`. The logarithms of the
stage partition functions are super-additive: the sum of
`log (partitionFunctionΛ G (Λ.volume m) p)` and `log (partitionFunctionΛ G (Λ.volume n) p)`
is at most `log (partitionFunctionΛ G (Λ.volume (m + n)) p)`. And the first stage is
non-degenerate, `(Λ.volume 1).card ≠ 0`. `DisjointTowerHypotheses G Λ p` is a `Prop`-valued
structure whose fields are exactly those three and which carries no further data.

The convergence statement occurs in three shapes, differing only in how an upper bound on
the stage sequence arrives and whether the three structural hypotheses arrive singly or
bundled: as `BddAbove (Set.range (freeEnergyAlongExhaustion G Λ p))` with the three given
singly; as `BoundedEdgeDensity G Λ`, from which that `BddAbove` is obtained, again with the
three given singly; and as `BoundedEdgeDensity G Λ` together with a single
`DisjointTowerHypotheses` record.

No typeclass binder applies to the ambient graph `G : SimpleGraph V` itself, but `G` is not
left unconstrained: the super-additivity hypothesis on `log (partitionFunctionΛ G …)` names
it in every shape, singly or through the bundle, and `BoundedEdgeDensity G Λ` names it in the
two shapes that obtain the upper bound instead of assuming it. The only instance binders
anywhere in the module are `[DecidableEq V]` and the stagewise `Fintype` instance on the edge
set of the induced subgraph; in particular nothing here takes `[Nonempty V]`, and no
statement assumes `Ferromagnetic p` or any sign condition on `p.J`, `p.h` or `p.β`.

Reference: Glimm-Jaffe, *Quantum Physics*, 2nd ed., Springer 1987, §4.6 Proposition 4.6.1,
p. 68, "as `Λ ↑ ∞`, `f_Λ` converges". The proposition is stated there for a lattice field
with a nearest neighbour, translation-invariant, ferromagnetic pair interaction, and is not
proved in that section; the hypotheses above stand in for that framework.
-/

namespace IsingModel

open Ambient

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **GJ §4.6 Prop 4.6.1 (Fekete convergence of free energy density)**:
under a super-additivity hypothesis on `log Z` along the exhaustion and
the cardinality additivity `|Λ_{m+n}| = |Λ_m| + |Λ_n|`,
`freeEnergyAlongExhaustion G Λ p` converges to `freeEnergyInfinite G Λ p`.

Mathematical content: apply `Subadditive.tendsto_lim` (mathlib Fekete)
to the negated sequence `u_n := -log Z_{Λ.volume n}`. Under
`hcard_add` we have `|Λ_n| = n · |Λ_1|`, whence
`freeEnergyAlongExhaustion G Λ p n = -(u_n / n) / |Λ_1|` for `n ≥ 1`.
The Fekete limit `u_n / n → ℓ` translates to
`freeEnergyAlongExhaustion → -ℓ / |Λ_1|`, and
`freeEnergyInfinite_eq_of_tendsto` identifies the limit with
`freeEnergyInfinite`.

Hypotheses:
* `hcard_add`: `|Λ_{m+n}| = |Λ_m| + |Λ_n|` (additive cardinality along the tower).
* `hsuper`: `log Z_{Λ_m} + log Z_{Λ_n} ≤ log Z_{Λ_{m+n}}` (`log Z` super-additive).
* `hbdd`: `freeEnergyAlongExhaustion` bounded above (provided e.g. by
  `freeEnergyAlongExhaustion_le_uniform_upper_bound` under
  `BoundedEdgeDensity`).
* `hcard_one`: `|Λ_1| ≠ 0` (non-degenerate base step).

The hypothesis bundle is the natural formalisation of "disjoint-tower"
exhaustion: on a lattice with translation symmetry, a box-like
exhaustion of a fixed block size satisfies `hcard_add` and `hsuper`
(the latter from `log_partitionFunctionΛ_disjUnion_super_additive`). -/
theorem freeEnergyAlongExhaustion_tendsto_of_superadditive
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hsuper : ∀ m n, Real.log (partitionFunctionΛ G (Λ.volume m) p)
                      + Real.log (partitionFunctionΛ G (Λ.volume n) p)
                      ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p))
    (hbdd : BddAbove (Set.range (freeEnergyAlongExhaustion G Λ p)))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ p) Filter.atTop
      (nhds (freeEnergyInfinite G Λ p)) := by
  set u : ℕ → ℝ := fun n => -Real.log (partitionFunctionΛ G (Λ.volume n) p)
    with hu_def
  -- 1. `u` is subadditive.
  have hsub : Subadditive u := by
    intro m n
    have := hsuper m n
    simp only [hu_def]
    linarith
  -- 2. `(Λ.volume n).card = n * (Λ.volume 1).card`.
  have hcard0 : (Λ.volume 0).card = 0 := by
    have h : (Λ.volume 0).card = (Λ.volume 0).card + (Λ.volume 0).card := by
      have := hcard_add 0 0; simpa using this
    omega
  have hcard_mul : ∀ n, (Λ.volume n).card = n * (Λ.volume 1).card := by
    intro n
    induction n with
    | zero =>
      rw [hcard0, Nat.zero_mul]
    | succ n ih =>
      calc (Λ.volume (n + 1)).card
          = (Λ.volume n).card + (Λ.volume 1).card := hcard_add n 1
        _ = n * (Λ.volume 1).card + (Λ.volume 1).card := by rw [ih]
        _ = (n + 1) * (Λ.volume 1).card := by ring
  -- 3. `(Λ.volume 1).card > 0` as a real number.
  have hcard1_pos : (0 : ℝ) < ((Λ.volume 1).card : ℝ) := by
    have : 0 < (Λ.volume 1).card := Nat.pos_of_ne_zero hcard_one
    exact_mod_cast this
  have hcard1_ne : ((Λ.volume 1).card : ℝ) ≠ 0 := hcard1_pos.ne'
  -- 4. Bound below `u n / n`.
  obtain ⟨C, hC⟩ := hbdd
  have hpos_cardC : 0 ≤ ((Λ.volume 1).card : ℝ) * max C 0 := by
    have hm : 0 ≤ max C 0 := le_max_right _ _
    have hc : 0 ≤ ((Λ.volume 1).card : ℝ) := Nat.cast_nonneg _
    exact mul_nonneg hc hm
  have hbdd_below : BddBelow (Set.range fun n : ℕ => u n / (n : ℝ)) := by
    refine ⟨-((Λ.volume 1).card : ℝ) * max C 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    change -((Λ.volume 1).card : ℝ) * max C 0 ≤ u n / (n : ℝ)
    by_cases hn : n = 0
    · -- At n = 0: u 0 / 0 = 0 ≥ -card_1 * max C 0 since max C 0 ≥ 0.
      subst hn
      rw [Nat.cast_zero, div_zero]
      linarith
    · -- For n ≥ 1: derive `u n / n = -card_1 * freeEnergyAlongExhaustion n`
      -- from `card_n = n * card_1` and the definition of freeEnergyΛ.
      have hn' : 0 < n := Nat.pos_of_ne_zero hn
      have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn'
      have hn_ne : (n : ℝ) ≠ 0 := hn_real.ne'
      have hcardn : ((Λ.volume n).card : ℝ)
          = (n : ℝ) * ((Λ.volume 1).card : ℝ) := by
        exact_mod_cast hcard_mul n
      have hfe_unfold :
          freeEnergyAlongExhaustion G Λ p n
            = (((Λ.volume n).card : ℝ))⁻¹
              * Real.log (partitionFunctionΛ G (Λ.volume n) p) := by
        simp only [freeEnergyAlongExhaustion]
        unfold freeEnergyΛ IsingModel.freeEnergy partitionFunctionΛ
        rw [Fintype.card_coe]
      have hfe_val : freeEnergyAlongExhaustion G Λ p n ≤ C :=
        hC ⟨n, rfl⟩
      have hrel : u n / (n : ℝ)
          = -((Λ.volume 1).card : ℝ) * freeEnergyAlongExhaustion G Λ p n := by
        rw [hfe_unfold, hcardn]
        change -Real.log (partitionFunctionΛ G (Λ.volume n) p) / (n : ℝ)
            = -((Λ.volume 1).card : ℝ)
              * (((n : ℝ) * ((Λ.volume 1).card : ℝ))⁻¹
                * Real.log (partitionFunctionΛ G (Λ.volume n) p))
        field_simp
      rw [hrel]
      have hmax : freeEnergyAlongExhaustion G Λ p n ≤ max C 0 :=
        hfe_val.trans (le_max_left _ _)
      nlinarith
  -- 5. Apply Fekete.
  have htendsto_quot : Filter.Tendsto (fun n => u n / (n : ℝ)) Filter.atTop
      (nhds hsub.lim) :=
    hsub.tendsto_lim hbdd_below
  -- 6. Translate to freeEnergyAlongExhaustion via the ratio relation.
  set L : ℝ := -hsub.lim / ((Λ.volume 1).card : ℝ) with hL_def
  have htendsto_feAE : Filter.Tendsto (freeEnergyAlongExhaustion G Λ p)
      Filter.atTop (nhds L) := by
    have htendsto_target : Filter.Tendsto
        (fun n => -(u n / (n : ℝ)) / ((Λ.volume 1).card : ℝ))
        Filter.atTop (nhds L) := by
      rw [hL_def]
      exact (htendsto_quot.neg).div_const _
    refine htendsto_target.congr' ?_
    refine (Filter.eventually_ge_atTop 1).mono ?_
    intro n hn
    -- For n ≥ 1: freeEnergy_n = -(u n / n) / card_1
    have hn_pos : 0 < n := hn
    have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hn_ne : (n : ℝ) ≠ 0 := hn_real.ne'
    have hcardn : ((Λ.volume n).card : ℝ)
        = (n : ℝ) * ((Λ.volume 1).card : ℝ) := by
      exact_mod_cast hcard_mul n
    have hfe_unfold :
        freeEnergyAlongExhaustion G Λ p n
          = (((Λ.volume n).card : ℝ))⁻¹
            * Real.log (partitionFunctionΛ G (Λ.volume n) p) := by
      simp only [freeEnergyAlongExhaustion]
      unfold freeEnergyΛ IsingModel.freeEnergy partitionFunctionΛ
      rw [Fintype.card_coe]
    rw [hfe_unfold, hcardn]
    change -(u n / (n : ℝ)) / ((Λ.volume 1).card : ℝ)
      = (((n : ℝ) * ((Λ.volume 1).card : ℝ))⁻¹
          * Real.log (partitionFunctionΛ G (Λ.volume n) p))
    simp only [hu_def]
    field_simp
  -- 7. Identify L with freeEnergyInfinite.
  have hL_eq : freeEnergyInfinite G Λ p = L :=
    freeEnergyInfinite_eq_of_tendsto G Λ p htendsto_feAE
  rw [hL_eq]
  exact htendsto_feAE

/-- **GJ §4.6 Prop 4.6.1, disjoint-tower + `BoundedEdgeDensity` form**:
under a super-additivity hypothesis on `log Z` along a disjoint-tower
exhaustion (`hcard_add`, `hsuper`, `hcard_one`) and bounded edge
density along the exhaustion, `freeEnergyAlongExhaustion G Λ p`
converges to `freeEnergyInfinite G Λ p`.

This is a strict relaxation of
`freeEnergyAlongExhaustion_tendsto_of_superadditive`: the explicit
`hbdd : BddAbove (Set.range (freeEnergyAlongExhaustion G Λ p))`
hypothesis is discharged automatically via
`BddAbove_freeEnergyAlongExhaustion_range` under
`BoundedEdgeDensity`.  No other hypothesis is added; in particular
neither this theorem nor `BddAbove_freeEnergyAlongExhaustion_range`
needs `Ferromagnetic p`.

Reference: Glimm–Jaffe, *Quantum Physics*, 2nd ed., Springer 1987,
§4.6 Prop 4.6.1, p. 68. This is a formal weaker variant of the
proposition as stated in GJ: the bundled hypotheses replace the
translation-invariance framework that GJ uses implicitly. -/
theorem freeEnergyAlongExhaustion_tendsto_of_disjoint_tower
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hsuper : ∀ m n, Real.log (partitionFunctionΛ G (Λ.volume m) p)
                      + Real.log (partitionFunctionΛ G (Λ.volume n) p)
                      ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ p) Filter.atTop
      (nhds (freeEnergyInfinite G Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_superadditive G Λ p
    hcard_add hsuper
    (BddAbove_freeEnergyAlongExhaustion_range G Λ p hBED)
    hcard_one

/-- **Bundle of disjoint-tower hypotheses** for `freeEnergyAlongExhaustion`
Fekete convergence (GJ §4.6 Prop 4.6.1 p. 68).

Packages the three exhaustion-structural hypotheses required by
`freeEnergyAlongExhaustion_tendsto_of_disjoint_tower`:

* `card_add`: `|Λ_{m+n}| = |Λ_m| + |Λ_n|` (additive cardinality).
* `super`: `log Z_{Λ_m} + log Z_{Λ_n} ≤ log Z_{Λ_{m+n}}`
  (super-additivity of `log Z` along the tower).
* `card_one`: `|Λ_1| ≠ 0` (non-degenerate base step).

The bundle is indexed by a `SimpleGraph V`, an `Exhaustion V`, and
`IsingParams ℝ`; it does not depend on any probabilistic / ferromagnetic
content — that enters separately through `BoundedEdgeDensity` when
needed.

Concrete constructors for the `J = 0` and `β = 0` slices are provided by
`DisjointTowerHypotheses.of_J_zero` and `DisjointTowerHypotheses.of_beta_zero` in
`AmbientLatticeSum.TrivialSlices`; general callers may supply the three structural fields
directly. -/
structure DisjointTowerHypotheses
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : Prop where
  /-- Additive cardinality along the tower:
  `|Λ_{m+n}| = |Λ_m| + |Λ_n|` for all `m, n`. -/
  card_add : ∀ m n, (Λ.volume (m + n)).card
                      = (Λ.volume m).card + (Λ.volume n).card
  /-- Super-additivity of `log Z` along the tower:
  `log Z_{Λ_m} + log Z_{Λ_n} ≤ log Z_{Λ_{m+n}}`. -/
  super : ∀ m n, Real.log (partitionFunctionΛ G (Λ.volume m) p)
                  + Real.log (partitionFunctionΛ G (Λ.volume n) p)
                  ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p)
  /-- Non-degenerate base step: `|Λ_1| ≠ 0`. -/
  card_one : (Λ.volume 1).card ≠ 0

/-- **Bundled-hypothesis wrapper for Prop 4.6.1 (disjoint-tower +
`BoundedEdgeDensity`)** (GJ §4.6 Prop 4.6.1 p. 68).

Same content as `freeEnergyAlongExhaustion_tendsto_of_disjoint_tower`,
but takes the three structural hypotheses as a single
`DisjointTowerHypotheses` record for API-site convenience. -/
theorem freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (h : DisjointTowerHypotheses G Λ p) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ p) Filter.atTop
      (nhds (freeEnergyInfinite G Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_disjoint_tower G Λ p
    hBED h.card_add h.super h.card_one

end Ambient

end IsingModel
