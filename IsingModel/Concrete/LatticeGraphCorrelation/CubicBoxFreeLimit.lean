import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxExtremalCoincidence
import IsingModel.Inequalities.VolumeMonotonicity

/-!
# Full-box free-boundary infinite-volume limit for the origin observable (GJ §17.1, Issue #4214 §A)

The screened-convention limit existence of PR #4262
(`CubicBoxExtremalCoincidence.lean`) leaves one final piece of Master #4214 item A open: the literal
**full-box free-boundary** (`Λ' = Finset.univ`, no frozen boundary) infinite-volume limit.
This file closes it.

## Headline

`tendsto_gibbsExpectationBC_originObs_free_limit` — at high temperature, for a **monotone** `g`, the
**free-boundary** Gibbs expectation of the origin observable on `cubicBox d n` converges, as
`n → ∞`, to the common extremal value `plusStateExpectation J h β (originLocalObs d g)` (the unique
infinite-volume Gibbs expectation).  Since the free measure (`Λ' = univ`) is independent of the
boundary configuration (`gibbsExpectationBC_boundary_congr`, the `agreesOff univ` hypothesis being
vacuous), this is genuinely the free-boundary thermodynamic limit.

## Method

A two-sided **volume-monotonicity squeeze**, *not* the extremal sandwich (which is vacuous at
`Λ = univ`).  Freezing more sites to `+` raises a monotone-observable expectation
(`gibbsExpectationBC_plus_volume_antitone`, FV Lemma 3.22), and freezing more sites to `−` lowers it
(`gibbsExpectationBC_minus_volume_monotone`, the new `−`-dual, via the spin-flip bridge).  Hence for
every `k`, the free measure on `cubicBox d (k+1)` is bracketed:
```
⟨originObs⟩^{−}_{plusBoxInterior d k (k+1)} ≤ ⟨originObs⟩^{free}_{cubicBox d (k+1)}
                                            ≤ ⟨originObs⟩^{+}_{plusBoxInterior d k (k+1)},
```
and both bounding sequences are exactly the `±`-boundary instances of the PR #4262 limit theorem
(`tendsto_gibbsExpectationBC_originObs_extremal_limit`, which is stated for an *arbitrary* boundary
family `η`), both converging to the common value.  The squeeze plus an index shift gives the
free-boundary limit.

This completes Master #4214 item A: the ℤ^d infinite-volume Gibbs expectation of a local observable
exists at high temperature and is independent of the boundary condition (free, `+`, `−`, or any
sequence), in both the screened and the full-box free-boundary conventions.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306;
Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.4 (Lemmas 3.22–3.23), §6.5;
Georgii, *Gibbs Measures and Phase Transitions*, Ch. 8.
-/

namespace IsingModel

open Finset

/-- **The spin flip is antitone**: `Spin.flip` reverses the order (`down < up`, `flip down = up`,
`flip up = down`). -/
theorem Spin.flip_antitone : Antitone Spin.flip := by
  intro a b hab
  revert hab
  cases a <;> cases b <;> decide

/-- **The configuration flip is antitone**: flipping every spin reverses the product order on
`Config ι`. -/
theorem Config.flip_antitone {ι : Type*} : Antitone (Config.flip : Config ι → Config ι) :=
  fun _ _ h i => Spin.flip_antitone (h i)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Negation linearity of the Gibbs expectation**: `⟨−F⟩^η_Λ = −⟨F⟩^η_Λ` (from
`gibbsExpectationBC_const_mul` with `c = −1`). -/
theorem gibbsExpectationBC_neg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι) (F : Config ι → ℝ) :
    gibbsExpectationBC G β J h Λ η (fun σ => -F σ) = -gibbsExpectationBC G β J h Λ η F := by
  have := gibbsExpectationBC_const_mul G β J h Λ η (-1) F
  simpa using this

/-- **Minus-state volume monotonicity** (the `−`-dual of `gibbsExpectationBC_plus_volume_antitone`,
FV Lemma 3.22): for a ferromagnetic Ising model and a monotone observable, the `−` boundary
expectation **increases as the volume grows**, `Λ₁ ⊆ Λ₂ ⟹ ⟨φ⟩^−_{Λ₁} ≤ ⟨φ⟩^−_{Λ₂}`.

Proof via the global spin-flip bridge `gibbsExpectationBC_minus_eq_plus_neg_h_flip`: both sides
become `+` expectations at field `−h` of `ψ = φ ∘ flip`, antitone (`φ` monotone, `flip` antitone),
so `−ψ` is monotone; applying the `+` volume antitonicity to `−ψ` flips the inequality, and undoing
the negation (`gibbsExpectationBC_neg`) gives the claim. -/
theorem gibbsExpectationBC_minus_volume_monotone (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    {Λ₁ Λ₂ : Finset ι} (hsub : Λ₁ ⊆ Λ₂)
    (φ : Config ι → ℝ) (hφ_mono : Monotone φ) :
    gibbsExpectationBC G β J h Λ₁ (minusConfig ι) φ ≤
      gibbsExpectationBC G β J h Λ₂ (minusConfig ι) φ := by
  rw [gibbsExpectationBC_minus_eq_plus_neg_h_flip G β J h Λ₁ φ,
    gibbsExpectationBC_minus_eq_plus_neg_h_flip G β J h Λ₂ φ]
  have hmono : Monotone (fun σ : Config ι => -(φ σ.flip)) :=
    (hφ_mono.comp_antitone Config.flip_antitone).neg
  have hva := gibbsExpectationBC_plus_volume_antitone (G := G) (β := β) (J := J) (h := -h)
    hβ hJ hsub (fun σ => -(φ σ.flip)) hmono
  rw [gibbsExpectationBC_neg, gibbsExpectationBC_neg] at hva
  linarith

namespace Ambient

open IsingModel.Dobrushin Filter Topology

/-- **Full-box free-boundary infinite-volume limit for the origin observable** (GJ §17.1; ℤ^d
Dobrushin uniqueness, #4214 §A — final piece).

At high temperature (`0 ≤ β`, `0 ≤ J`, `βJ·2d < 1`, `d ≥ 1`) and for a **monotone** `g`
(`g↓ ≤ g↑`), the **free-boundary** (`Λ' = univ`) Gibbs expectation of the origin observable on
`cubicBox d n` converges, as `n → ∞`, to the common extremal value
`plusStateExpectation J h β (originLocalObs d g)` — the unique infinite-volume Gibbs expectation of
the local observable.  The free measure is boundary-condition-independent
(`gibbsExpectationBC_boundary_congr`, `agreesOff univ` vacuous), so the limit holds for every
boundary family `η`.

Proof: volume-monotonicity squeeze.  At `Λ' = univ` the free measure equals both the `+` and `−`
boundary measures (boundary congruence); freezing the shell of an inner box to `+`/`−` brackets it
(`gibbsExpectationBC_{plus_volume_antitone, minus_volume_monotone}`); both bracketing sequences are
the `±` instances of the PR #4262 limit `tendsto_gibbsExpectationBC_originObs_extremal_limit`, both
`→` the common value.  Squeeze and shift the index. -/
theorem tendsto_gibbsExpectationBC_originObs_free_limit (d : ℕ) (hd : 1 ≤ d) {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) {g : Spin → ℝ}
    (hg : g Spin.down ≤ g Spin.up) (η : ∀ n : ℕ, Config (↑(cubicBox d n) : Type _)) :
    Tendsto (fun n : ℕ =>
        gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d n)) β (fun _ => J) h
          Finset.univ (η n) (originObs d g (origin_mem_cubicBox d n)))
      atTop
      (𝓝 (plusStateExpectation J h β (originLocalObs d g)
        (Finset.singleton_subset_iff.mpr (origin_mem_cubicBox d 0)))) := by
  -- Step A: at `Λ' = univ` the free measure equals the `+` and `−` boundary measures.
  have hfree_plus : ∀ n,
      gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d n)) β (fun _ => J) h
          Finset.univ (η n) (originObs d g (origin_mem_cubicBox d n))
        = gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d n)) β (fun _ => J) h
          Finset.univ (plusConfig _) (originObs d g (origin_mem_cubicBox d n)) := fun n =>
    gibbsExpectationBC_boundary_congr _ _ _ _ _ (fun i hi => absurd (Finset.mem_univ i) hi) _
  have hfree_minus : ∀ n,
      gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d n)) β (fun _ => J) h
          Finset.univ (η n) (originObs d g (origin_mem_cubicBox d n))
        = gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d n)) β (fun _ => J) h
          Finset.univ (minusConfig _) (originObs d g (origin_mem_cubicBox d n)) := fun n =>
    gibbsExpectationBC_boundary_congr _ _ _ _ _ (fun i hi => absurd (Finset.mem_univ i) hi) _
  -- Endpoints: the ± instances of the PR #4262 limit, both → the common value.  Convert to clean
  -- `k`-form (the `0 + k` index normalised) by `Tendsto.congr` on the real-valued sequence.
  have hUk : Tendsto (fun k : ℕ =>
      gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (k + 1))) β (fun _ => J) h
        (plusBoxInterior d k (k + 1)) (plusConfig _)
        (originObs d g (origin_mem_cubicBox d (k + 1)))) atTop
      (𝓝 (plusStateExpectation J h β (originLocalObs d g)
        (Finset.singleton_subset_iff.mpr (origin_mem_cubicBox d 0)))) :=
    (tendsto_gibbsExpectationBC_originObs_extremal_limit d hd hβ hJ hα h hg
      (Finset.singleton_subset_iff.mpr (origin_mem_cubicBox d 0)) (fun _ => plusConfig _)).congr
      (fun k => by rw [Nat.zero_add k])
  have hLok : Tendsto (fun k : ℕ =>
      gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (k + 1))) β (fun _ => J) h
        (plusBoxInterior d k (k + 1)) (minusConfig _)
        (originObs d g (origin_mem_cubicBox d (k + 1)))) atTop
      (𝓝 (plusStateExpectation J h β (originLocalObs d g)
        (Finset.singleton_subset_iff.mpr (origin_mem_cubicBox d 0)))) :=
    (tendsto_gibbsExpectationBC_originObs_extremal_limit d hd hβ hJ hα h hg
      (Finset.singleton_subset_iff.mpr (origin_mem_cubicBox d 0)) (fun _ => minusConfig _)).congr
      (fun k => by rw [Nat.zero_add k])
  -- Squeeze `fun k => free (k+1)` between the two coinciding endpoints (all in `k`-form).
  have hsq : Tendsto (fun k : ℕ =>
      gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (k + 1))) β (fun _ => J) h
        Finset.univ (η (k + 1)) (originObs d g (origin_mem_cubicBox d (k + 1)))) atTop
      (𝓝 (plusStateExpectation J h β (originLocalObs d g)
        (Finset.singleton_subset_iff.mpr (origin_mem_cubicBox d 0)))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hLok hUk (fun k => ?_) (fun k => ?_)
    · rw [hfree_minus (k + 1)]
      exact gibbsExpectationBC_minus_volume_monotone
        (inducedGraph (latticeGraph d) (cubicBox d (k + 1)))
        hβ (fun _ => hJ) (Finset.subset_univ (plusBoxInterior d k (k + 1)))
        (originObs d g (origin_mem_cubicBox d (k + 1)))
        (originObs_monotone d hg (origin_mem_cubicBox d (k + 1)))
    · rw [hfree_plus (k + 1)]
      exact gibbsExpectationBC_plus_volume_antitone
        (inducedGraph (latticeGraph d) (cubicBox d (k + 1)))
        hβ (fun _ => hJ) (Finset.subset_univ (plusBoxInterior d k (k + 1)))
        (originObs d g (origin_mem_cubicBox d (k + 1)))
        (originObs_monotone d hg (origin_mem_cubicBox d (k + 1)))
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hsq

end Ambient

end IsingModel
