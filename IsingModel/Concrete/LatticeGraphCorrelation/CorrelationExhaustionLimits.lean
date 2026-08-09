import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume correlations and the infinite-volume correlation

Concrete `latticeGraph d` statements about the sequence of finite-volume correlations of a
fixed finite subset `A` of `Fin d → ℤ`, lifted into the volumes of an arbitrary
`Ambient.Exhaustion`, for a parameter record satisfying `Ferromagnetic`.

Given an index beyond which `A` is contained in every volume, that shifted sequence is
monotone and bounded above by `1`, hence converges, and its limit is the infinite-volume
correlation of `A`. The containment index is then produced existentially, so that for an
arbitrary `A` the convergence to the infinite-volume correlation holds for some index; that
existential form is stated along an arbitrary exhaustion and at `Ambient.cubicExhaustion d`.
`Ferromagnetic` and the containment hypothesis are the only requirements anywhere here, and
no instance argument is needed.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d shifted correlationΛ sequence is monotone and bounded by 1**
(any-Exhaustion, ferromagnetic). -/
theorem correlationΛ_shifted_monotone_bounded_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Monotone (fun n : ℕ =>
      correlationΛ (IsingModel.latticeGraph d) (Λ.volume (n + N)) p
        (Ambient.liftFinset A (hN (n + N) (Nat.le_add_left N n))))
    ∧ ∀ n : ℕ,
      correlationΛ (IsingModel.latticeGraph d) (Λ.volume (n + N)) p
        (Ambient.liftFinset A (hN (n + N) (Nat.le_add_left N n))) ≤ 1 :=
  correlationΛ_shifted_monotone_bounded (IsingModel.latticeGraph d) Λ p hf hN

/-- **ℤ^d shifted correlationΛ sequence converges** (any-Exhaustion, ferromagnetic). -/
theorem correlationΛ_shifted_tendsto_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    ∃ L : ℝ, Filter.Tendsto
      (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
        (Λ.volume (m + N)) p
        (Ambient.liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds L) :=
  correlationΛ_shifted_tendsto (IsingModel.latticeGraph d) Λ p hf hN

/-- **ℤ^d correlationΛ → correlationInfinite under an explicit subset hypothesis**
(any-Exhaustion). -/
theorem tendsto_correlationΛ_correlationInfinite_of_subset_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Filter.Tendsto
      (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
        (Λ.volume (m + N)) p
        (Ambient.liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds (correlationInfinite (IsingModel.latticeGraph d) Λ p A)) :=
  tendsto_correlationΛ_correlationInfinite_of_subset
    (IsingModel.latticeGraph d) Λ p hf hN

/-- **ℤ^d physical identification: correlationΛ → correlationInfinite**
(any-Exhaustion). -/
theorem tendsto_correlationΛ_correlationInfinite_latticeGraph_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    ∃ N : ℕ, ∃ hN : ∀ n ≥ N, A ⊆ Λ.volume n,
      Filter.Tendsto
        (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
          (Λ.volume (m + N)) p
          (Ambient.liftFinset A (hN (m + N) (Nat.le_add_left N m))))
        Filter.atTop (nhds (correlationInfinite (IsingModel.latticeGraph d)
          Λ p A)) :=
  tendsto_correlationΛ_correlationInfinite (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d physical identification: correlationΛ → correlationInfinite**. -/
theorem tendsto_correlationΛ_correlationInfinite_latticeGraph
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    ∃ N : ℕ, ∃ hN : ∀ n ≥ N, A ⊆ (Ambient.cubicExhaustion d).volume n,
      Filter.Tendsto
        (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume (m + N)) p
          (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
        Filter.atTop (nhds (correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p A)) :=
  tendsto_correlationΛ_correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A

end Ambient
end IsingModel
