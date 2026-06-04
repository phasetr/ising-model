import IsingModel.Concrete.LatticeGraphCorrelation.PlusStateTranslationFinal

/-!
# Translation invariance of the cubic-exhaustion `+`-state functional (Issue #3581 PR 4d)

The culmination of the translation-invariance arc: the cubic-exhaustion `+`-state
functional is invariant under lattice translations on a monotone observable,
`μ⁺(τ_a φ) = μ⁺(φ)`, assembled from the interlacing antitone sandwich (#3585), the
recentering covariance (#3586), and the screening connection (#3587), via a limit
squeeze.

* `plusBoxLocalExpectation_screening_eq` — the multi-step ambient independence of
  the `+` local expectation (the inner box only sees the immediate boundary layer).
* `plusStateExpectation_vadd_monotone` — translation invariance for a monotone
  observable.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.4 Theorem 3.17 (statement p. 95, proof pp. 102–103).
-/

namespace IsingModel

namespace Ambient

open Finset Filter Topology

/-- **Multi-step ambient independence of the `+` local expectation**: for
`n + 1 ≤ m`, the `+` local expectation on the ambient `cubicBox d m` equals that on
the immediate ambient `cubicBox d (n+1)` (the inner box only sees the immediate
boundary layer; iterating `plusBoxLocalExpectation_screening_succ`). -/
theorem plusBoxLocalExpectation_screening_eq {d : ℕ} {n m : ℕ} (hnm : n + 1 ≤ m)
    {J h β : ℝ} (O : LocalMonotoneObservable d) (hSn1 : O.S ⊆ cubicBox d (n + 1)) :
    plusBoxLocalExpectation n m J h β O (hSn1.trans (cubicBox_mono d hnm))
      = plusBoxLocalExpectation n (n + 1) J h β O hSn1 := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [← ih]
    exact plusBoxLocalExpectation_screening_succ hnm (cubicBox_mono d (Nat.le_succ m)) O
      (hSn1.trans (cubicBox_mono d hnm))

/-- **Per-stage squeeze inequality**: writing `R = latticeRadius a` and
`n = N + 2R + k`, the cubic `+` local expectation of the translated observable at
inner index `n+R` is below that of `O` at inner index `n`, which is below that of
the translated observable at inner index `n-R` (the interlacing antitone sandwich
#3585 with the recentered middle term #3586/#3587, the bounds at their natural
ambient or reduced by the multi-step screening). -/
theorem plusBoxLocal_vadd_squeeze {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (a : Fin d → ℤ) (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d N) (k : ℕ) :
    plusBoxLocalExpectation (N + 3 * latticeRadius a + k) (N + 3 * latticeRadius a + k + 1)
        J h β (O.vadd a)
        ((O.vadd_support_subset a hS).trans (cubicBox_mono d (by omega)))
      ≤ plusBoxLocalExpectation (N + 2 * latticeRadius a + k) (N + 2 * latticeRadius a + k + 1)
        J h β O (hS.trans (cubicBox_mono d (by omega)))
    ∧ plusBoxLocalExpectation (N + 2 * latticeRadius a + k) (N + 2 * latticeRadius a + k + 1)
        J h β O (hS.trans (cubicBox_mono d (by omega)))
      ≤ plusBoxLocalExpectation (N + latticeRadius a + k) (N + latticeRadius a + k + 1)
        J h β (O.vadd a)
        ((O.vadd_support_subset a hS).trans (cubicBox_mono d (by omega))) := by
  set R := latticeRadius a with hR
  set n := N + 2 * R + k with hn
  have hRn : R ≤ n := by omega
  have hSM : (O.vadd a).S ⊆ cubicBox d (n + 1 + R) :=
    (O.vadd_support_subset a hS).trans (cubicBox_mono d (by omega))
  have hSn1 : O.S ⊆ cubicBox d (n + 1) := hS.trans (cubicBox_mono d (by omega))
  obtain ⟨hl, hr⟩ := gibbsExpectationBC_translatedInner_sandwich (h := h) a hRn hβ hJ
    ((O.vadd a).lift hSM) ((O.vadd a).lift_monotone hSM)
  have hmid : gibbsExpectationBC
        (inducedGraph (IsingModel.latticeGraph d) (cubicBox d (n + 1 + R))) β (fun _ => J) h
        (translatedInner a n (n + 1 + R)) (plusConfig _) ((O.vadd a).lift hSM)
      = plusBoxLocalExpectation n (n + 1) J h β O hSn1 :=
    gibbsExpectationBC_translatedInner_vadd_eq_plusBoxLocal a O hSn1 hSM
  -- the upper bound: ambient `n+1+R` reduced to its natural ambient `(n+R)+1`
  have hUp : gibbsExpectationBC
        (inducedGraph (IsingModel.latticeGraph d) (cubicBox d (n + 1 + R))) β (fun _ => J) h
        (plusBoxInterior d (n + R) (n + 1 + R)) (plusConfig _) ((O.vadd a).lift hSM)
      = plusBoxLocalExpectation (n + R) (n + R + 1) J h β (O.vadd a)
          ((O.vadd_support_subset a hS).trans (cubicBox_mono d (by omega))) := by
    change plusBoxLocalExpectation (n + R) (n + 1 + R) J h β (O.vadd a) hSM = _
    exact plusBoxLocalExpectation_screening_eq (by omega) (O.vadd a)
      ((O.vadd_support_subset a hS).trans (cubicBox_mono d (by omega)))
  -- the lower bound: ambient `n+1+R` reduced to its natural ambient `(n-R)+1`
  have hLo : gibbsExpectationBC
        (inducedGraph (IsingModel.latticeGraph d) (cubicBox d (n + 1 + R))) β (fun _ => J) h
        (plusBoxInterior d (n - R) (n + 1 + R)) (plusConfig _) ((O.vadd a).lift hSM)
      = plusBoxLocalExpectation (n - R) (n - R + 1) J h β (O.vadd a)
          ((O.vadd_support_subset a hS).trans (cubicBox_mono d (by omega))) := by
    change plusBoxLocalExpectation (n - R) (n + 1 + R) J h β (O.vadd a) hSM = _
    exact plusBoxLocalExpectation_screening_eq (by omega) (O.vadd a)
      ((O.vadd_support_subset a hS).trans (cubicBox_mono d (by omega)))
  refine ⟨?_, ?_⟩
  · have := hl
    rw [hmid, hUp] at this
    convert this using 2 <;> omega
  · have := hr
    rw [hmid, hLo] at this
    convert this using 2 <;> omega

/-- **The `+` local expectation only depends on the box indices through their
values**: equal inner/ambient indices give equal expectations (proof-irrelevant in
the support inclusion). -/
theorem plusBoxLocalExpectation_congr {d : ℕ} {n₁ n₂ m₁ m₂ : ℕ} (hn : n₁ = n₂)
    (hm : m₁ = m₂) {J h β : ℝ} (O : LocalMonotoneObservable d)
    (hS₁ : O.S ⊆ cubicBox d m₁) (hS₂ : O.S ⊆ cubicBox d m₂) :
    plusBoxLocalExpectation n₁ m₁ J h β O hS₁ = plusBoxLocalExpectation n₂ m₂ J h β O hS₂ := by
  subst hn; subst hm; rfl

/-- **Translation invariance of the cubic-exhaustion `+`-state functional on a
monotone observable** (FV Theorem 3.17): `μ⁺(τ_a φ) = μ⁺(φ)`.  The per-stage squeeze
`plusBoxLocal_vadd_squeeze` brackets the translated `+` local expectations between
two shifted subsequences of the original, all converging to the same `+`-state
limit; uniqueness of limits gives the equality. -/
theorem plusStateExpectation_vadd_monotone {d N : ℕ} {J h β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (a : Fin d → ℤ) (O : LocalMonotoneObservable d) (hS : O.S ⊆ cubicBox d N) :
    plusStateExpectation J h β (⟨(O.vadd a).S, (O.vadd a).φ⟩ : LocalObservable d)
        (O.vadd_support_subset a hS)
      = plusStateExpectation J h β (⟨O.S, O.φ⟩ : LocalObservable d) hS := by
  set R := latticeRadius a with hR
  have hshift : Tendsto (fun k => 2 * R + k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left k (2 * R)) tendsto_id
  -- base tendsto for `O.vadd a` (start `N+R`) and `O` (start `N`)
  have htOva : Tendsto (fun k => plusBoxLocalExpectation (N + R + k) (N + R + k + 1) J h β
        (O.vadd a) ((O.vadd_support_subset a hS).trans (cubicBox_mono d (by omega)))) atTop
      (nhds (plusStateExpectation J h β (⟨(O.vadd a).S, (O.vadd a).φ⟩ : LocalObservable d)
        (O.vadd_support_subset a hS))) := by
    rw [plusStateExpectation_of_monotone hβ hJ (O.vadd a) (O.vadd_support_subset a hS)]
    exact tendsto_plusBoxLocalObservable_infiniteVolume (h := h) hβ hJ (O.vadd a)
      (O.vadd_support_subset a hS)
  have htO : Tendsto (fun k => plusBoxLocalExpectation (N + k) (N + k + 1) J h β O
        (hS.trans (cubicBox_mono d (by omega)))) atTop
      (nhds (plusStateExpectation J h β (⟨O.S, O.φ⟩ : LocalObservable d) hS)) := by
    rw [plusStateExpectation_of_monotone hβ hJ O hS]
    exact tendsto_plusBoxLocalObservable_infiniteVolume (h := h) hβ hJ O hS
  -- LHS sequence (index `N+3R+k`) and middle sequence (index `N+2R+k`) as shifts
  have htLHS : Tendsto (fun k => plusBoxLocalExpectation (N + 3 * R + k) (N + 3 * R + k + 1)
        J h β (O.vadd a) ((O.vadd_support_subset a hS).trans (cubicBox_mono d (by omega)))) atTop
      (nhds (plusStateExpectation J h β (⟨(O.vadd a).S, (O.vadd a).φ⟩ : LocalObservable d)
        (O.vadd_support_subset a hS))) :=
    (htOva.comp hshift).congr (fun k =>
      plusBoxLocalExpectation_congr (by simp only []; omega) (by simp only []; omega)
        (O.vadd a) _ _)
  have htMid : Tendsto (fun k => plusBoxLocalExpectation (N + 2 * R + k) (N + 2 * R + k + 1)
        J h β O (hS.trans (cubicBox_mono d (by omega)))) atTop
      (nhds (plusStateExpectation J h β (⟨O.S, O.φ⟩ : LocalObservable d) hS)) :=
    (htO.comp hshift).congr (fun k =>
      plusBoxLocalExpectation_congr (by simp only []; omega) (by simp only []; omega) O _ _)
  refine le_antisymm ?_ ?_
  · exact le_of_tendsto_of_tendsto' htLHS htMid
      (fun k => (plusBoxLocal_vadd_squeeze hβ hJ a O hS k).1)
  · exact le_of_tendsto_of_tendsto' htMid htOva
      (fun k => (plusBoxLocal_vadd_squeeze hβ hJ a O hS k).2)

end Ambient

end IsingModel
