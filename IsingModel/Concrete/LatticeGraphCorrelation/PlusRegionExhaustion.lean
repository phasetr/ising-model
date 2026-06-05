import IsingModel.Concrete.LatticeGraphCorrelation.PlusRegionCubicConvergence

/-!
# Exhaustion independence of the `+`-state functional (FV §3.4 Theorem 3.17)

The headline of the exhaustion-independence programme (Issue #3581): for **any**
exhaustion `Λ` of `ℤ^d` (`d ≥ 1`), the region `+` expectation
`plusRegionExpectation (Λ.volume k)` of a monotone local observable converges, as
`k → ∞`, to the cubic-exhaustion `+`-state functional `plusStateExpectation` — the
finite-volume `+` measures `μ⁺_{Λ_k}` converge to the same infinite-volume `+` state
regardless of the exhaustion (FV Theorem 3.17).

The proof is a **squeeze**: each volume `Λ.volume k` is sandwiched between two cubic
boxes `cubicBox d (innerRadius k) ⊆ Λ.volume k ⊆ cubicBox d (outerRadius k)`, both
radii tending to `∞`; region antitonicity (FV Lemma 3.22) turns the inclusions into
inequalities, and both cubic bounds converge to `plusStateExpectation`
(`tendsto_regionCubicValue`).

* `cubicBox_subset_iff_le` — strict monotonicity of cubic boxes (`d ≥ 1`).
* `exhaustionOuterRadius` / `_spec` / `_tendsto` — smallest enclosing cubic radius.
* `exhaustionInnerRadius` / `_spec` / `_tendsto` — largest enclosed cubic radius.
* `tendsto_plusRegionExpectation_exhaustion` — the headline convergence.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17 (statement p. 95, proof pp. 102–103).
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

variable {d : ℕ}

/-- **A larger cubic box is not contained in a smaller one** (`d ≥ 1`): for `b < a`,
the box `cubicBox d a` contains a vertex (with one coordinate equal to `a`) outside
`cubicBox d b`. -/
theorem cubicBox_not_subset_of_lt (hd : 0 < d) {a b : ℕ} (hab : b < a) :
    ¬ cubicBox d a ⊆ cubicBox d b := by
  intro hsub
  set i₀ : Fin d := ⟨0, hd⟩
  set p : Fin d → ℤ := Pi.single i₀ (a : ℤ) with hp
  have hpa : p ∈ cubicBox d a := by
    rw [mem_cubicBox]
    intro i
    by_cases hi : i = i₀
    · subst hi; rw [hp, Pi.single_eq_same]; exact ⟨by omega, le_refl _⟩
    · rw [hp, Pi.single_eq_of_ne hi]; exact ⟨by omega, by omega⟩
  have hpb := hsub hpa
  rw [mem_cubicBox] at hpb
  have hi₀ := hpb i₀
  rw [hp, Pi.single_eq_same] at hi₀
  omega

/-- **Cubic-box inclusion is equivalent to radius inequality** (`d ≥ 1`):
`cubicBox d a ⊆ cubicBox d b ↔ a ≤ b`. -/
theorem cubicBox_subset_iff_le (hd : 0 < d) {a b : ℕ} :
    cubicBox d a ⊆ cubicBox d b ↔ a ≤ b := by
  constructor
  · intro hsub
    by_contra hlt
    exact cubicBox_not_subset_of_lt hd (Nat.lt_of_not_le hlt) hsub
  · exact fun hab => cubicBox_mono d hab

/-- **Every finite region sits inside some cubic box**: a direct consequence of
`cubicBox_exhaust`. -/
theorem exists_cubicBox_superset (d : ℕ) (A : Finset (Fin d → ℤ)) :
    ∃ m, A ⊆ cubicBox d m :=
  let ⟨N, hN⟩ := cubicBox_exhaust d A; ⟨N, hN N le_rfl⟩

/-- **Outer cubic radius of an exhaustion stage**: the smallest `m` with
`Λ.volume k ⊆ cubicBox d m`. -/
noncomputable def exhaustionOuterRadius (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (k : ℕ) : ℕ :=
  Nat.find (exists_cubicBox_superset d (Λ.volume k))

/-- **Outer-radius enclosure**: the exhaustion stage sits inside the cubic box at its
outer radius. -/
theorem exhaustionOuterRadius_spec (Λ : Ambient.Exhaustion (Fin d → ℤ)) (k : ℕ) :
    Λ.volume k ⊆ cubicBox d (exhaustionOuterRadius d Λ k) :=
  Nat.find_spec (exists_cubicBox_superset d (Λ.volume k))

/-- **The outer radius tends to infinity** (`d ≥ 1`): as the exhaustion grows, the
smallest enclosing cubic box grows without bound. -/
theorem exhaustionOuterRadius_tendsto (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) :
    Tendsto (exhaustionOuterRadius d Λ) atTop atTop := by
  refine tendsto_atTop_atTop.2 (fun M => ?_)
  obtain ⟨K, hK⟩ := Λ.exhaust (cubicBox d M)
  refine ⟨K, fun k hk => ?_⟩
  exact (cubicBox_subset_iff_le hd).1
    ((hK k hk).trans (exhaustionOuterRadius_spec Λ k))

/-- **Inner cubic radius of an exhaustion stage**: the largest `R ≤ k` with
`cubicBox d R ⊆ Λ.volume k` (or `0` if none). -/
noncomputable def exhaustionInnerRadius (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (k : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun R => cubicBox d R ⊆ Λ.volume k) k

/-- **Inner-radius enclosure** (conditional): given any witness `R ≤ k` with
`cubicBox d R ⊆ Λ.volume k`, the cubic box at the inner radius sits inside the
exhaustion stage. -/
theorem exhaustionInnerRadius_spec {Λ : Ambient.Exhaustion (Fin d → ℤ)} {k R : ℕ}
    (hRk : R ≤ k) (hR : cubicBox d R ⊆ Λ.volume k) :
    cubicBox d (exhaustionInnerRadius d Λ k) ⊆ Λ.volume k := by
  classical
  exact Nat.findGreatest_spec (P := fun R => cubicBox d R ⊆ Λ.volume k) hRk hR

/-- **The inner radius tends to infinity**: as the exhaustion grows, the largest
enclosed cubic box grows without bound. -/
theorem exhaustionInnerRadius_tendsto (Λ : Ambient.Exhaustion (Fin d → ℤ)) :
    Tendsto (exhaustionInnerRadius d Λ) atTop atTop := by
  classical
  refine tendsto_atTop_atTop.2 (fun M => ?_)
  obtain ⟨K, hK⟩ := Λ.exhaust (cubicBox d M)
  refine ⟨max K M, fun k hk => ?_⟩
  exact Nat.le_findGreatest (le_trans (le_max_right K M) hk)
    (hK k (le_trans (le_max_left K M) hk))

/-- **Exhaustion independence of the `+`-state functional** (FV Theorem 3.17, `d ≥ 1`):
for any exhaustion `Λ` of `ℤ^d` and a monotone local observable `O` supported in
`cubicBox d N`, with `O.S ⊆ Λ.volume k` for `k ≥ N₀`, the region `+` expectations
`plusRegionExpectation (Λ.volume (N₀+k))` converge to the cubic-exhaustion `+`-state
functional `plusStateExpectation` as `k → ∞` — independently of the exhaustion.

Proof by squeeze: `cubicBox d (innerRadius) ⊆ Λ.volume ⊆ cubicBox d (outerRadius)`
with both radii `→ ∞`; region antitonicity bounds the volume expectation between the
two cubic values, which both converge to `plusStateExpectation`
(`tendsto_regionCubicValue`). -/
theorem tendsto_plusRegionExpectation_exhaustion (hd : 0 < d) {N : ℕ} {J h β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d N)
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) {N₀ : ℕ}
    (hN₀ : ∀ k, N₀ ≤ k → O.S ⊆ Λ.volume k) :
    Tendsto (fun k => plusRegionExpectation (Λ.volume (N₀ + k)) J h β O
        (hN₀ (N₀ + k) (Nat.le_add_right N₀ k))) atTop
      (nhds (plusStateExpectation J h β (⟨O.S, O.φ⟩ : LocalObservable d) hS)) := by
  -- The shifted index `k ↦ N₀ + k` tends to infinity.
  have hshift : Tendsto (fun k => N₀ + k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left k N₀) tendsto_id
  have houter : Tendsto (fun k => exhaustionOuterRadius d Λ (N₀ + k)) atTop atTop :=
    (exhaustionOuterRadius_tendsto hd Λ).comp hshift
  have hinner : Tendsto (fun k => exhaustionInnerRadius d Λ (N₀ + k)) atTop atTop :=
    (exhaustionInnerRadius_tendsto Λ).comp hshift
  -- Both cubic bounds converge to the `+`-state functional.
  have hlower : Tendsto (fun k => regionCubicValue J h β O hS
      (exhaustionOuterRadius d Λ (N₀ + k))) atTop
      (nhds (plusStateExpectation J h β (⟨O.S, O.φ⟩ : LocalObservable d) hS)) :=
    (tendsto_regionCubicValue (h := h) hβ hJ O hS).comp houter
  have hupper : Tendsto (fun k => regionCubicValue J h β O hS
      (exhaustionInnerRadius d Λ (N₀ + k))) atTop
      (nhds (plusStateExpectation J h β (⟨O.S, O.φ⟩ : LocalObservable d) hS)) :=
    (tendsto_regionCubicValue (h := h) hβ hJ O hS).comp hinner
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · -- lower ≤ mid : `regionCubicValue (outer) ≤ plusRegionExpectation (Λ.volume)`.
    filter_upwards [houter.eventually_ge_atTop N] with k hkN
    rw [regionCubicValue_eq hkN O hS (hS.trans (cubicBox_mono d hkN))]
    exact plusRegionExpectation_antitone (exhaustionOuterRadius_spec Λ (N₀ + k)) hβ hJ O
      (hN₀ (N₀ + k) (Nat.le_add_right N₀ k))
  · -- mid ≤ upper : `plusRegionExpectation (Λ.volume) ≤ regionCubicValue (inner)`.
    obtain ⟨K, hK⟩ := Λ.exhaust (cubicBox d N)
    filter_upwards [hinner.eventually_ge_atTop N, hshift.eventually_ge_atTop K,
      hshift.eventually_ge_atTop N] with k hkN hkK hkN2
    rw [regionCubicValue_eq hkN O hS (hS.trans (cubicBox_mono d hkN))]
    have hwitness : cubicBox d (exhaustionInnerRadius d Λ (N₀ + k)) ⊆ Λ.volume (N₀ + k) :=
      exhaustionInnerRadius_spec hkN2 (hK (N₀ + k) hkK)
    exact plusRegionExpectation_antitone hwitness hβ hJ O (hS.trans (cubicBox_mono d hkN))

end Ambient

end IsingModel
