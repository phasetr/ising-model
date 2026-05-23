import IsingModel.TranslationInvariance.Spontaneous

universe u v

namespace IsingModel

namespace Ambient

/-! ## Translation-invariant exhaustions

An exhaustion whose consecutive volumes differ by a disjoint
translate of the base block `volume 1` gives automatic
cardinality additivity `|Λ.volume (m + n)| = |Λ.volume m| +
|Λ.volume n|`, discharging the first field of
`DisjointTowerHypotheses`.

Deriving the second structural field, `super`, requires
translation-invariance of the Ising Hamiltonian itself and is
left to a subsequent PR. -/

/-- A **translation-invariant exhaustion** is an `Exhaustion V`
whose consecutive volumes differ by a disjoint translate of the
base block. `shift n : T` is the translation vector inserted at
stage `n+1`.

Informally: `Λ.volume 0 = ∅`, then `Λ.volume n` is built up by
successively adjoining disjoint translates of `Λ.volume 1`.
This is the natural structure under which Prop 4.6.1's
`hcard_add` hypothesis becomes automatic.

The field `shift_zero : shift 0 = 0` ensures the `n = 0` case of
`volume_succ` is self-consistent: it forces `volume 1 = volume 1`
(since `volume 0 = ∅` and `vaddFinset 0 (volume 1) = volume 1`
by `vaddFinset_zero`).

This structure concerns only the **exhaustion geometry**. It does
*not* by itself imply translation invariance of the graph edges
or of the Ising Hamiltonian — those are separate conditions.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1,
p. 68. -/
structure TranslationInvariantExhaustion (T : Type u) [AddGroup T]
    (V : Type v) [DecidableEq V] [AddAction T V]
    extends Exhaustion V where
  /-- Translation vector inserted at the `n+1`-th stage. -/
  shift : ℕ → T
  /-- The stage-0 shift is the identity, making the `n = 0` case of
  `volume_succ` self-consistent (together with `volume_zero`). -/
  shift_zero : shift 0 = 0
  /-- `volume 0` is empty — the exhaustion starts from scratch. -/
  volume_zero : volume 0 = ∅
  /-- The `(n+1)`-th volume is the `n`-th volume together with the
  translated base block `shift n +ᵥ volume 1`. -/
  volume_succ : ∀ n,
    volume (n + 1) = volume n ∪ vaddFinset (shift n) (volume 1)
  /-- The translated base block is disjoint from `volume n`. -/
  disjoint_shift : ∀ n,
    Disjoint (volume n) (vaddFinset (shift n) (volume 1))
  /-- `shift` is an additive monoid homomorphism `ℕ → T`:
  `shift (m + n) = shift m + shift n`. This is the structural datum
  that makes the tower "regular" and allows
  `volume (m + n) = volume m ∪ (shift m +ᵥ volume n)`. -/
  shift_add : ∀ m n, shift (m + n) = shift m + shift n

namespace TranslationInvariantExhaustion

variable {T : Type u} [AddGroup T] {V : Type v} [DecidableEq V]
  [AddAction T V]

/-- **Linear cardinality**: `|volume n| = n · |volume 1|` for any
translation-invariant exhaustion.

Proved by induction on `n`, using `volume_succ`,
`disjoint_shift`, and `vaddFinset_card`. -/
theorem volume_card_eq_mul
    (Λ : TranslationInvariantExhaustion T V) (n : ℕ) :
    (Λ.volume n).card = n * (Λ.volume 1).card := by
  induction n with
  | zero =>
    rw [Λ.volume_zero, Finset.card_empty, Nat.zero_mul]
  | succ n ih =>
    rw [Λ.volume_succ n,
        Finset.card_union_of_disjoint (Λ.disjoint_shift n),
        vaddFinset_card, ih]
    ring

/-- **`hcard_add` holds automatically**:
`|volume (m + n)| = |volume m| + |volume n|`. Direct from the
linear-cardinality formula. -/
theorem volume_card_add
    (Λ : TranslationInvariantExhaustion T V) (m n : ℕ) :
    (Λ.volume (m + n)).card = (Λ.volume m).card + (Λ.volume n).card := by
  rw [Λ.volume_card_eq_mul (m + n), Λ.volume_card_eq_mul m,
      Λ.volume_card_eq_mul n]
  ring

/-- **Decomposition of `volume (m + n)` as a union**: under the
additive `shift_add` structural field,
`volume (m + n) = volume m ∪ (shift m +ᵥ volume n)`.

Proof by induction on `n`. The base case uses `volume_zero`,
`vaddFinset_empty`, and `Finset.union_empty`; the inductive step
uses `volume_succ` (twice), `vaddFinset_union`, `vaddFinset_add`,
`shift_add`, and `Finset.union_assoc`. -/
theorem volume_decomposes
    (Λ : TranslationInvariantExhaustion T V) (m n : ℕ) :
    Λ.volume (m + n)
      = Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n) := by
  induction n with
  | zero =>
    rw [Nat.add_zero, Λ.volume_zero, vaddFinset_empty,
        Finset.union_empty]
  | succ n ih =>
    -- LHS: Λ.volume (m + (n + 1)) = Λ.volume (m + n + 1)
    --    = Λ.volume (m + n) ∪ (shift (m+n) +ᵥ Λ.volume 1) [volume_succ]
    -- RHS: Λ.volume m ∪ (shift m +ᵥ Λ.volume (n + 1))
    --    = Λ.volume m ∪ (shift m +ᵥ (Λ.volume n ∪ (shift n +ᵥ Λ.volume 1)))
    --    = Λ.volume m ∪ ((shift m +ᵥ Λ.volume n) ∪
    --                    (shift m +ᵥ (shift n +ᵥ Λ.volume 1)))
    --    = Λ.volume m ∪ ((shift m +ᵥ Λ.volume n) ∪
    --                    ((shift m + shift n) +ᵥ Λ.volume 1))
    --    = Λ.volume m ∪ ((shift m +ᵥ Λ.volume n) ∪
    --                    (shift (m+n) +ᵥ Λ.volume 1)) [shift_add]
    --    = (Λ.volume m ∪ (shift m +ᵥ Λ.volume n)) ∪
    --      (shift (m+n) +ᵥ Λ.volume 1) [union_assoc]
    --    = Λ.volume (m+n) ∪ (shift (m+n) +ᵥ Λ.volume 1) [IH]
    --    = LHS.
    have hstep : m + (n + 1) = (m + n) + 1 := by ring
    rw [hstep, Λ.volume_succ (m + n), Λ.volume_succ n, ih,
        vaddFinset_union, vaddFinset_add, Λ.shift_add m n,
        Finset.union_assoc]

/-- **Disjointness of `volume m` and `shift m +ᵥ volume n`**:
under the `TranslationInvariantExhaustion` structure,
`Disjoint (volume m) (vaddFinset (shift m) (volume n))`.

Proof by induction on `n`. Base case `n = 0` reduces to `Disjoint _ ∅`
(trivial via `Finset.disjoint_empty_right`). Inductive step uses
the decomposition `vaddFinset (shift m) (volume (n+1)) = (shift m +ᵥ
volume n) ∪ (shift(m+n) +ᵥ volume 1)` (via `volume_succ`,
`vaddFinset_union`, `vaddFinset_add`, `shift_add`), the IH, and
`disjoint_shift (m+n)` combined with
`Λ.volume m ⊆ Λ.volume (m+n)` (from `Λ.mono`) to transfer disjointness. -/
theorem disjoint_volume_shift
    (Λ : TranslationInvariantExhaustion T V) (m n : ℕ) :
    Disjoint (Λ.volume m) (vaddFinset (Λ.shift m) (Λ.volume n)) := by
  induction n with
  | zero =>
    rw [Λ.volume_zero, vaddFinset_empty]
    exact Finset.disjoint_empty_right _
  | succ n ih =>
    -- vaddFinset (shift m) (volume (n+1))
    --   = vaddFinset (shift m) (volume n ∪ (shift n +ᵥ volume 1))
    --   = (shift m +ᵥ volume n) ∪ (shift m +ᵥ (shift n +ᵥ volume 1))
    --   = (shift m +ᵥ volume n) ∪ ((shift m + shift n) +ᵥ volume 1)
    --   = (shift m +ᵥ volume n) ∪ (shift (m+n) +ᵥ volume 1)
    rw [Λ.volume_succ n, vaddFinset_union, vaddFinset_add,
        ← Λ.shift_add m n]
    -- Show Disjoint Λ_m ((shift m +ᵥ Λ_n) ∪ (shift(m+n) +ᵥ Λ_1)).
    rw [Finset.disjoint_union_right]
    refine ⟨ih, ?_⟩
    -- Disjoint Λ_m (shift(m+n) +ᵥ Λ_1):
    -- since Λ_m ⊆ Λ_{m+n} (by mono), and disjoint_shift gives
    -- Disjoint Λ_{m+n} (shift(m+n) +ᵥ Λ_1).
    exact (Λ.disjoint_shift (m + n)).mono_left (Λ.mono (Nat.le_add_right m n))

set_option linter.unusedFintypeInType false in
/-- **`hsuper` in union form from translation invariance**: for a
translation-invariant graph `G`, a translation-invariant exhaustion
`Λ` with additive shift, and ferromagnetic parameters,

`log Z_{Λ.volume m} + log Z_{Λ.volume n}
  ≤ log Z_{Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n)}`.

The RHS is, by `volume_decomposes` (step 7),
`log Z_{Λ.volume (m + n)}` — so this is the same statement as the
target `hsuper` field of `DisjointTowerHypotheses`, modulo the
Finset rewrite. Stating it in the union form avoids Fintype-instance
juggling that arises when applying `volume_decomposes` as a rewrite
through the partitionFunction indexed by a Fintype typeclass.

Proof: combine
1. `partitionFunctionΛ_vaddFinset_eq` (PR #237) — translation
   invariance of Z, reduces `log Z_{shift m +ᵥ Λ_n}` to
   `log Z_{Λ_n}`.
2. `log_partitionFunctionΛ_disjUnion_super_additive` — super-
   additivity on disjoint union (ferromagnetic).
3. `disjoint_volume_shift` (step 8) — supplies the disjointness. -/
theorem log_partitionFunctionΛ_super_of_translationInvariant_union
    (Λ : TranslationInvariantExhaustion T V)
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (m n : ℕ)
    [Fintype (inducedGraph G
        (vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet]
    [Fintype (inducedGraph G
        (Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet] :
    Real.log (partitionFunctionΛ G (Λ.volume m) p)
      + Real.log (partitionFunctionΛ G (Λ.volume n) p)
      ≤ Real.log (partitionFunctionΛ G
          (Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n)) p) := by
  have h_translate :
      partitionFunctionΛ G (vaddFinset (Λ.shift m) (Λ.volume n)) p
        = partitionFunctionΛ G (Λ.volume n) p :=
    partitionFunctionΛ_vaddFinset_eq G (Λ.shift m) (Λ.volume n) p
  have h_super := log_partitionFunctionΛ_disjUnion_super_additive
    (G := G) (hd := Λ.disjoint_volume_shift m n) p hf
  rw [h_translate] at h_super
  exact h_super

set_option linter.unusedFintypeInType false in
/-- **`hsuper` in `volume (m + n)` form**: bridges step 9's union
form to the form expected by `DisjointTowerHypotheses.super`.

Proof: apply step 9 (union form), then `partitionFunctionΛ_congr_finset`
with `volume_decomposes` to rewrite the RHS Finset. -/
theorem log_partitionFunctionΛ_super_of_translationInvariant
    (Λ : TranslationInvariantExhaustion T V)
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (m n : ℕ)
    [Fintype (inducedGraph G
        (vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet]
    [Fintype (inducedGraph G
        (Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet] :
    Real.log (partitionFunctionΛ G (Λ.volume m) p)
      + Real.log (partitionFunctionΛ G (Λ.volume n) p)
      ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p) := by
  have h_union := log_partitionFunctionΛ_super_of_translationInvariant_union
    Λ G p hf m n
  have h_eq := partitionFunctionΛ_congr_finset (G := G)
    (Λ.volume_decomposes m n).symm (p := p)
  rw [← h_eq]
  exact h_union

/-- **`DisjointTowerHypotheses` from a `TranslationInvariantExhaustion`
+ hypothesised `hsuper`**: given a translation-invariant exhaustion
(which handles `card_add` via `volume_card_add`) together with
user-supplied super-additivity of `log Z` and non-degeneracy
`(volume 1).card ≠ 0`, the full `DisjointTowerHypotheses` record
follows.

This is the abstract assembly step: the `hsuper` input itself —
`log Z_{volume m} + log Z_{volume n} ≤ log Z_{volume (m + n)}` —
is expected to come from a full translation-invariance proof of
the log partition function in a subsequent PR. Current step
provides the scaffold so that, once `hsuper` is derived, it
plugs directly into `freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1,
p. 68. -/
def disjointTowerHypotheses_of_translationInvariant
    (Λ : TranslationInvariantExhaustion T V)
    (G : SimpleGraph V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hsuper : ∀ m n,
      Real.log (partitionFunctionΛ G (Λ.volume m) p)
        + Real.log (partitionFunctionΛ G (Λ.volume n) p)
        ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    DisjointTowerHypotheses G Λ.toExhaustion p where
  card_add := Λ.volume_card_add
  super := hsuper
  card_one := hcard_one

/-- **Fekete convergence from a `TranslationInvariantExhaustion`**:
given a translation-invariant exhaustion, a bounded-edge-density
hypothesis, user-supplied `log Z` super-additivity `hsuper`, and
non-degenerate base step `hcard_one`, the exhaustion free-energy
density tends (in the sense of `Filter.Tendsto` at `Filter.atTop`)
to the infinite-volume free energy: `freeEnergyAlongExhaustion
G Λ.toExhaustion p` converges to `freeEnergyInfinite G
Λ.toExhaustion p`.

Thin wrapper over
`freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses`
(PR #204) + `disjointTowerHypotheses_of_translationInvariant`
(step 4 / PR #223). `card_add` is supplied automatically by the
exhaustion structure; once `hsuper` is derived from full
translation invariance (subsequent PR), this theorem will become
an unconditional-in-`hsuper` corollary.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1,
p. 68. -/
theorem freeEnergyAlongExhaustion_tendsto_of_translationInvariant
    (Λ : TranslationInvariantExhaustion T V)
    (G : SimpleGraph V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ.toExhaustion)
    (hsuper : ∀ m n,
      Real.log (partitionFunctionΛ G (Λ.volume m) p)
        + Real.log (partitionFunctionΛ G (Λ.volume n) p)
        ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ.toExhaustion p)
      Filter.atTop
      (nhds (freeEnergyInfinite G Λ.toExhaustion p)) :=
  freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses G
    Λ.toExhaustion p hBED
    (disjointTowerHypotheses_of_translationInvariant Λ G p
      hsuper hcard_one)

set_option linter.unusedFintypeInType false in
/-- **Automatic Fekete convergence under full translation
invariance** (GJ §4.6 Prop 4.6.1, p. 68): final step of the
translation scaffolding. Given

* a translation-invariant exhaustion `Λ` (step 3 / PR #222 +
  step 7 / PR #238);
* a translation-invariant graph `G` (step 1 / PR #220);
* ferromagnetic parameters `p` (for the disjoint-union
  super-additivity);
* bounded edge density along `Λ` (discharges `hbdd` via
  PR #203 / `BddAbove_freeEnergyAlongExhaustion_range`);
* auxiliary Fintype instances for the translated and union
  Finsets (required for the `log Z` super-additivity statement);
* `hcard_one`: non-degenerate base block,

the exhaustion free-energy density tends to the infinite-volume
free energy:
`freeEnergyAlongExhaustion G Λ.toExhaustion p` converges to
`freeEnergyInfinite G Λ.toExhaustion p`.

The `hsuper` input of previous steps is now discharged automatically
via `log_partitionFunctionΛ_super_of_translationInvariant`. -/
theorem freeEnergyAlongExhaustion_tendsto_of_translationInvariant_auto
    (Λ : TranslationInvariantExhaustion T V)
    (G : SimpleGraph V) [IsTranslationInvariant T G]
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ m n, Fintype (inducedGraph G
        (vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet]
    [∀ m n, Fintype (inducedGraph G
        (Λ.volume m ∪ vaddFinset (Λ.shift m) (Λ.volume n))).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (hBED : BoundedEdgeDensity G Λ.toExhaustion)
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ.toExhaustion p)
      Filter.atTop
      (nhds (freeEnergyInfinite G Λ.toExhaustion p)) :=
  freeEnergyAlongExhaustion_tendsto_of_translationInvariant Λ G p hBED
    (fun m n =>
      log_partitionFunctionΛ_super_of_translationInvariant Λ G p hf m n)
    hcard_one

end TranslationInvariantExhaustion

end Ambient

end IsingModel
