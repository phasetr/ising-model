import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDartDivC
import IsingModel.Concrete.LatticeGraphBED.HandshakeIdentity

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1i: cross-sum `/c` reduced to the dart-profile sum (p.312)

Combines the handshake fiber-decomposition identity (`sum_edgeFinset_sym2_lift_prod_eq_sum_dart`)
with the unified per-dart `/c` bound (#4346 `dart_term_div_c_le`) to reduce the c-cancelling
Lebowitz
cross-sum (from #4341 `derivative_profile_cubic_le_infiniteVolume_lebowitz_cancelling`), divided by
`c = ⟨φ_x φ_z⟩`, to a pure **dart-profile sum**:
`(∑_{⟨u,v⟩∈E}[g{x,u}g{z,v}+g{x,v}g{z,u}]) / c
  ≤ 2·(1+(m⁻·d(x,z))^α)·e^{m⁻}·∑_{dt:Dart} s(x,dt.fst)·s(z,dt.snd)`,
where `s(a,b) = 1/(1+(m⁻·d(a,b))^α)`.  The dart-profile sum is then bounded by the m⁻-scaled HLS
convolution (#4336) in the next step.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Cross-sum `/c` reduced to the dart-profile sum** (GJ p.312): for a distinct binding pair
`x ≠ z` (`m⁻(x,z) = globalPseudoMassDist`), the c-cancelling Lebowitz cross-sum divided by
`c = ⟨φ_x φ_z⟩` is bounded by `2·(1+(m⁻·d(x,z))^α)·e^{m⁻}` times the dart-profile sum
`∑_{dt:Dart} (1/(1+(m⁻·d(x,dt.fst))^α))·(1/(1+(m⁻·d(z,dt.snd))^α))`.

Handshake conversion (`sum_edgeFinset_sym2_lift_prod_eq_sum_dart`) turns the edge `Sym2`-sum into a
dart sum; `Finset.sum_div` distributes `/c`; the uniform per-dart `/c` bound (#4346
`dart_term_div_c_le`) applies to every dart; the dart-independent constant
`2·(1+(m⁻·d(x,z))^α)·e^{m⁻}` factors out (`Finset.mul_sum`). -/
theorem cross_sum_div_c_le_dart_profile {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    {n : ℕ} {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hbind : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    (∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} *
              Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} +
            Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} *
              Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val},
          fun u v => by ring⟩ e)
      / Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ≤ 2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            * (latticeDistance d x z : ℝ)) ^ α)
          * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
          * ∑ dt : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Dart,
              (1 / (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
                  * (latticeDistance d x dt.fst.val : ℝ)) ^ α))
                * (1 / (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
                  * (latticeDistance d z dt.snd.val : ℝ)) ^ α)) := by
  classical
  rw [show (∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} *
              Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} +
            Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} *
              Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val},
          fun u v => by ring⟩ e)
      = ∑ dt : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Dart,
          Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, dt.fst.val} *
            Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {z, dt.snd.val}
      from SimpleGraph.sum_edgeFinset_sym2_lift_prod_eq_sum_dart
        (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
        (fun w => Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, w.val})
        (fun w => Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {z, w.val})]
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_le_sum (fun dt _ => ?_)
  exact (dart_term_div_c_le hα hJ_pos hβ hxz dt hbind).trans (le_of_eq (by ring))

end Ambient
end IsingModel
