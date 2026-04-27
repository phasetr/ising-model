import IsingModel.AmbientLattice.Defs

/-!
# Exhaustion framework and along-exhaustion observables

Defines the `Exhaustion` structure (a monotone increasing covering
sequence of finite volumes) and the observables computed along an
exhaustion: `correlationAlongExhaustion`, `freeEnergyAlongExhaustion`,
`partitionFunctionAlongExhaustion`, `magnetizationAlongExhaustion`.

## Definitions

* `IsingModel.Ambient.Exhaustion V` — increasing sequence `Λₙ ↑ V`.
* `IsingModel.Ambient.liftFinset` — embed `A ⊆ Λ` into `Finset ↑Λ`.
* `IsingModel.Ambient.correlationAlongExhaustion` — per-stage correlation.
* `IsingModel.Ambient.freeEnergyAlongExhaustion` — per-stage free energy.
* `IsingModel.Ambient.partitionFunctionAlongExhaustion` — per-stage Z.
* `IsingModel.Ambient.magnetizationAlongExhaustion` — per-stage M.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.6, §5.1.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Thermodynamic limit along exhaustions

An **exhaustion** of the ambient lattice `V` by `G : SimpleGraph V` is
a monotone increasing sequence of finite volumes `Λₙ : ℕ → Finset V`
whose union covers all of `V`.  For each `n`, the finite-volume
correlation `correlationΛ G (Λₙ n) p A` is defined for
`A : Finset (↑(Λₙ n))`.

To speak of convergence of correlations along an exhaustion, we need
to compare correlations across different `Λ`s.  The simplest approach:
fix a finite set `A : Finset V` (subset of the ambient type), and
consider only exhaustions `Λₙ` such that `A ⊆ Λₙ` eventually
(`A ⊆ Λₙ` for all `n ≥ N` for some `N`).

For each such `n`, we can lift `A` to `A' : Finset (↑(Λₙ n))` via the
embedding `A ↪ Λₙ n` and evaluate `correlationΛ G (Λₙ n) p A'`. -/

/-- An exhaustion of `V` by an increasing sequence of finite volumes. -/
structure Exhaustion (V : Type*) where
  /-- The underlying sequence of finite volumes. -/
  volume : ℕ → Finset V
  /-- Monotone: `volume n ⊆ volume m` for `n ≤ m`. -/
  mono : Monotone volume
  /-- Eventually covers any finite set: for any `A : Finset V` there is
  `N` with `A ⊆ volume n` for all `n ≥ N`. -/
  exhaust : ∀ A : Finset V, ∃ N, ∀ n ≥ N, A ⊆ volume n

omit [DecidableEq V] in
/-- For a nonempty ambient type `V`, any exhaustion eventually has
nonempty volumes (`∀ᶠ n in atTop, (Λ.volume n).Nonempty`).

Follows from `Exhaustion.exhaust` applied to a singleton of any
element of `V`. This is the standard hypothesis needed to lift
per-stage statements about `freeEnergyAlongExhaustion` or
`partitionFunctionAlongExhaustion` to `limsup` via filter lemmas. -/
theorem Exhaustion.eventually_volume_nonempty [Nonempty V]
    (Λ : Exhaustion V) :
    ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨N, hN⟩ := Λ.exhaust {v}
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact ⟨v, hN n hn (Finset.mem_singleton_self v)⟩

omit [DecidableEq V] in
/-- For an `Infinite` ambient type `V`, the volume cardinality
`|Λ.volume n|` tends to infinity as `n → ∞`.

Follows from `Exhaustion.exhaust`: any finite set is eventually
contained in some `Λ.volume n`, so `|Λ.volume n|` dominates the
sizes of arbitrarily-large finite subsets (and infinite `V` provides
such subsets of any desired cardinality). -/
theorem Exhaustion.tendsto_card_atTop [Infinite V]
    (Λ : Exhaustion V) :
    Filter.Tendsto (fun n => (Λ.volume n).card) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro M
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq V M
  obtain ⟨N, hN⟩ := Λ.exhaust A
  refine ⟨N, fun n hn => ?_⟩
  have : A ⊆ Λ.volume n := hN n hn
  calc M = A.card := hA.symm
    _ ≤ (Λ.volume n).card := Finset.card_le_card this

/-- Lift a finite set `A ⊆ V` to a finite set in `↑Λ` when `A ⊆ Λ`. -/
noncomputable def liftFinset {Λ : Finset V} (A : Finset V) (hA : A ⊆ Λ) :
    Finset (↑Λ : Type _) :=
  A.attach.image (fun ⟨v, hv⟩ => ⟨v, hA hv⟩)

/-- Membership characterization for `liftFinset`: a subtype element
`x : ↑Λ` lies in `liftFinset A hA` iff its underlying value `x.val`
lies in `A`. -/
theorem mem_liftFinset {Λ : Finset V} {A : Finset V} (hA : A ⊆ Λ)
    (x : (↑Λ : Type _)) :
    x ∈ liftFinset A hA ↔ x.val ∈ A := by
  simp only [liftFinset, Finset.mem_image, Finset.mem_attach, true_and]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨v, hv⟩, hxv⟩
    simpa [← hxv]
  · intro hx
    exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩

/-- **`liftFinset` preserves cardinality**: `(liftFinset A hA).card = A.card`.

`liftFinset` is defined as `A.attach.image` of an explicit subtype
coercion; the coercion is injective, so card is preserved. -/
@[simp]
theorem liftFinset_card {Λ : Finset V} {A : Finset V} (hA : A ⊆ Λ) :
    (liftFinset A hA).card = A.card := by
  have hinj : Function.Injective
      (fun (x : { v // v ∈ A }) =>
        (⟨x.val, hA x.property⟩ : (↑Λ : Type _))) := by
    intro x y heq
    apply Subtype.ext
    exact Subtype.mk.inj heq
  simp only [liftFinset, Finset.card_image_of_injective _ hinj,
    Finset.card_attach]

/-- `liftFinset` commutes with `symmDiff`: if `A, B ⊆ Λ` then
`liftFinset A hA Δ liftFinset B hB = liftFinset (A Δ B) hAB`
(where the subset `A Δ B ⊆ Λ` follows since `A Δ B ⊆ A ∪ B`).

Proof by extensional equality using `mem_liftFinset`. -/
theorem liftFinset_symmDiff {Λ : Finset V} {A B : Finset V}
    (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    liftFinset A hA ∆ liftFinset B hB =
      liftFinset (A ∆ B)
        (fun _ hx => (Finset.mem_symmDiff.mp hx).elim
          (fun h => hA h.1) (fun h => hB h.1)) := by
  ext x
  simp only [Finset.mem_symmDiff, mem_liftFinset]

/-- `liftFinset` commutes with `insert`: if `a ∈ Λ` and `A ⊆ Λ` then
`insert ⟨a, ha⟩ (liftFinset A hA) = liftFinset (insert a A) h_insert`. -/
theorem liftFinset_insert {Λ : Finset V} {A : Finset V} {a : V}
    (ha : a ∈ Λ) (hA : A ⊆ Λ) :
    insert (⟨a, ha⟩ : (↑Λ : Type _)) (liftFinset A hA)
      = liftFinset (insert a A)
          (fun _ hx => (Finset.mem_insert.mp hx).elim
            (fun h => h ▸ ha) (fun h => hA h)) := by
  ext x
  simp only [Finset.mem_insert, mem_liftFinset]
  constructor
  · rintro (rfl | hx)
    · exact Or.inl rfl
    · exact Or.inr hx
  · rintro (rfl | hx)
    · exact Or.inl (Subtype.ext rfl)
    · exact Or.inr hx

/-- `liftFinset` commutes with `sdiff` (set difference): if `A, B ⊆ Λ` then
`liftFinset A hA \ liftFinset B hB = liftFinset (A \ B) h_sdiff`. -/
theorem liftFinset_sdiff {Λ : Finset V} {A B : Finset V}
    (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    liftFinset A hA \ liftFinset B hB
      = liftFinset (A \ B) (fun _ hx => hA (Finset.mem_sdiff.mp hx).1) := by
  ext x
  simp only [Finset.mem_sdiff, mem_liftFinset]

/-- The correlation along an exhaustion, evaluated eventually (from the
first `n` with `A ⊆ volume n`). Returns a function `ℕ → ℝ` which equals
`correlationΛ G (volume n) p (liftFinset A _)` once `A ⊆ volume n`, and
is set arbitrarily (e.g. `0`) before. -/
noncomputable def correlationAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) : ℕ → ℝ :=
  fun n =>
    if h : A ⊆ Λ.volume n then
      correlationΛ G (Λ.volume n) p (liftFinset A h)
    else 0

/-- **Free energy along an exhaustion**: the volume-direction free
energy density sequence $f_n := f_{\Lambda_n}$ whose convergence
Glimm–Jaffe §4.6 Proposition 4.6.1 (pp. 78ff) asserts.

This is the scaffold object; the full convergence theorem (volume
direction, genuine `Λ ↑ V`) requires subadditivity of `log Z`
combined with Fekete's lemma and is deferred to a follow-up PR. -/
noncomputable def freeEnergyAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : ℕ → ℝ :=
  fun n => freeEnergyΛ G (Λ.volume n) p

/-- **Unfolding of `freeEnergyAlongExhaustion`**: by construction, equal
to `freeEnergyΛ` at the `n`-th volume of the exhaustion.  Marked `@[simp]`
(unconditional `rfl`-proved unfolding) for ergonomic downstream use in
the Fekete/subadditivity follow-up. -/
@[simp]
theorem freeEnergyAlongExhaustion_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ p n = freeEnergyΛ G (Λ.volume n) p :=
  rfl


/-- **Partition function along an exhaustion**: the volume-direction
partition function sequence $Z_n := Z_{\Lambda_n}$.  Companion to
`freeEnergyAlongExhaustion` (Glimm–Jaffe §4.6); useful for Prop 4.6.1
∞-vol proofs that decompose `freeEnergy = log Z / |Λ|`. -/
noncomputable def partitionFunctionAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : ℕ → ℝ :=
  fun n => partitionFunctionΛ G (Λ.volume n) p

/-- **Magnetization along an exhaustion** at a fixed ambient site `i : V`:
the stagewise sequence `n ↦ ⟨σ_i⟩` computed on the induced volume
`Λ.volume n`. Once `i ∈ Λ.volume n`, this equals
`correlationΛ G (Λ.volume n) p {liftFinset {i} _}`; before, it is `0`.

Direct specialization of `correlationAlongExhaustion` at `A = {i}`,
matching the single-site magnetization layering at `magnetizationΛ`
(PR #396) and `magnetizationInfinite`. -/
noncomputable def magnetizationAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) : ℕ → ℝ :=
  correlationAlongExhaustion G Λ p {i}

/-- **Unfolding of `partitionFunctionAlongExhaustion`**: by construction
equal to `partitionFunctionΛ` at the `n`-th volume.  Unconditional
`rfl`-proof, marked `@[simp]`. -/
@[simp]
theorem partitionFunctionAlongExhaustion_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ p n
      = partitionFunctionΛ G (Λ.volume n) p :=
  rfl

/-- **Along-exhaustion free energy as `|Λ_n|⁻¹ · log Z_n`** per stage:
`freeEnergyAlongExhaustion G Λ p n = (Fintype.card ↑(Λ.volume n))⁻¹ ·
log (partitionFunctionAlongExhaustion G Λ p n)`. Per-stage
specialization of `freeEnergyΛ_eq_inv_card_mul_log`. -/
theorem freeEnergyAlongExhaustion_eq_inv_card_mul_log
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ p n
      = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion G Λ p n) :=
  freeEnergyΛ_eq_inv_card_mul_log G (Λ.volume n) p

/-- **Along-exhaustion free energy with `(Λ.volume n).card` cast**. -/
theorem freeEnergyAlongExhaustion_eq_inv_Λcard_mul_log
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ p n
      = ((Λ.volume n).card : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion G Λ p n) :=
  freeEnergyΛ_eq_inv_Λcard_mul_log G (Λ.volume n) p

/-- **Positivity along an exhaustion**:
`0 < partitionFunctionAlongExhaustion G Λ p n` for every `n`. -/
theorem partitionFunctionAlongExhaustion_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    0 < partitionFunctionAlongExhaustion G Λ p n :=
  partitionFunctionΛ_pos G (Λ.volume n) p

/-- Unfold `correlationAlongExhaustion` when `A ⊆ Λ.volume n`:
it equals the lifted finite-volume correlation. -/
theorem correlationAlongExhaustion_of_subset
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {A : Finset V} {n : ℕ} (hA : A ⊆ Λ.volume n) :
    correlationAlongExhaustion G Λ p A n
      = correlationΛ G (Λ.volume n) p (liftFinset A hA) := by
  simp only [correlationAlongExhaustion, hA, dite_true]

/-- Unfold `correlationAlongExhaustion` when `A ⊄ Λ.volume n`:
it equals `0`. -/
theorem correlationAlongExhaustion_of_not_subset
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {A : Finset V} {n : ℕ} (hA : ¬ A ⊆ Λ.volume n) :
    correlationAlongExhaustion G Λ p A n = 0 := by
  simp only [correlationAlongExhaustion, hA, dite_false]

/-- For any finite `A`, the correlation along an exhaustion is
eventually equal to the lifted correlation. -/
theorem correlationAlongExhaustion_eventually
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ hA : A ⊆ Λ.volume n,
      correlationAlongExhaustion G Λ p A n =
        correlationΛ G (Λ.volume n) p (liftFinset A hA) := by
  obtain ⟨N, hN⟩ := Λ.exhaust A
  refine ⟨N, fun n hn => ?_⟩
  have hA : A ⊆ Λ.volume n := hN n hn
  refine ⟨hA, ?_⟩
  simp [correlationAlongExhaustion, hA]

/-- The correlation along an exhaustion is bounded in absolute value
by `1` eventually. -/
theorem abs_correlationAlongExhaustion_eventually_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    ∀ᶠ n in Filter.atTop,
      |correlationAlongExhaustion G Λ p A n| ≤ 1 := by
  obtain ⟨N, hN⟩ := correlationAlongExhaustion_eventually G Λ p A
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hA, heq⟩ := hN n hn
  rw [heq]
  exact abs_correlationΛ_le_one G (Λ.volume n) p (liftFinset A hA)

/-- **Pointwise `|correlationAlongExhaustion| ≤ 1`** at every `n : ℕ`,
strengthening the eventual form: either `A ⊆ Λ.volume n` (in which case
the value is the finite-volume `correlationΛ` bounded by `1` in absolute
value) or `A ⊄ Λ.volume n` (the dite branch returns `0`). -/
theorem abs_correlationAlongExhaustion_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) :
    |correlationAlongExhaustion G Λ p A n| ≤ 1 := by
  by_cases hA : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ p hA]
    exact abs_correlationΛ_le_one G (Λ.volume n) p _
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hA, abs_zero]
    exact zero_le_one

/-- **Pointwise `-1 ≤ correlationAlongExhaustion`** at every `n : ℕ`.
Lower side of `abs_correlationAlongExhaustion_le_one`. -/
theorem neg_one_le_correlationAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) :
    -1 ≤ correlationAlongExhaustion G Λ p A n :=
  (abs_le.mp (abs_correlationAlongExhaustion_le_one G Λ p A n)).1

/-- **`correlationAlongExhaustion` is bounded below** (unconditional):
the range of `n ↦ correlationAlongExhaustion G Λ p A n` is bounded below
by `-1` via `neg_one_le_correlationAlongExhaustion`. -/
theorem correlationAlongExhaustion_bddBelow
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    BddBelow (Set.range (correlationAlongExhaustion G Λ p A)) := by
  refine ⟨-1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact neg_one_le_correlationAlongExhaustion G Λ p A n

/-- **Pointwise `correlationAlongExhaustion² ≤ 1`** at every `n : ℕ`. -/
theorem correlationAlongExhaustion_sq_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G Λ p A n ^ 2 ≤ 1 := by
  have h := abs_correlationAlongExhaustion_le_one G Λ p A n
  have : |correlationAlongExhaustion G Λ p A n| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this


end Ambient
end IsingModel
