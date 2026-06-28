import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeDartDivC
import IsingModel.Concrete.LatticeGraphBED.HandshakeIdentity

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV3d: the finite-volume cross-sum `/c` → dart-profile sum (p.312)

The finite-volume analogue of `cross_sum_div_c_le_dart_profile` (#4347).  Combining the handshake
fiber-decomposition identity (`sum_edgeFinset_sym2_lift_prod_eq_sum_dart`) with the unified per-dart
`/c` bound (PR-FV3c `dart_term_div_c_le_finiteRegionFV`) reduces the finite-volume c-cancelling
Lebowitz cross-sum, divided by `c = ⟨φ_x φ_z⟩_{σ,A}`, to a pure **dart-profile sum**:
`(∑_{⟨u,v⟩∈E}[g_A{x,u}g_A{z,v}+g_A{x,v}g_A{z,u}]) / c
  ≤ 2·(1+(m⁻_FV·d(x,z))^α)·e^{m⁻_FV}·∑_{dt:Dart} s(x,dt.fst)·s(z,dt.snd)`
(`s(a,b)=1/(1+(m⁻_FV·d(a,b))^α)`, `g_A{a,b}=⟨φ_a φ_b⟩_{σ,A}`).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Finite-volume cross-sum `/c` reduced to the dart-profile sum** (GJ p.312): for a distinct
in-box binding pair `x ≠ z`, the finite-volume c-cancelling Lebowitz cross-sum divided by
`c = ⟨φ_x φ_z⟩_{σ,A}` is bounded by `2·(1+(m⁻_FV·d(x,z))^α)·e^{m⁻_FV}` times the dart-profile sum.
Handshake (`sum_edgeFinset_sym2_lift_prod_eq_sum_dart`) turns the edge `Sym2`-sum into a dart sum;
`Finset.sum_div` distributes `/c`; the unified per-dart `/c` bound (PR-FV3c) applies to every dart;
the dart-independent constant factors out (`Finset.mul_sum`). -/
theorem cross_sum_div_c_le_dart_profile_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α) {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hxz : x ≠ z) (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n)
    (hbind : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) :
    (∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} n *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} n +
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} n *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val} n,
          fun u v => by ring⟩ e)
      / Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      ≤ 2 * (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
            * (latticeDistance d x z : ℝ)) ^ α)
          * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
          * ∑ dt : (inducedGraph (IsingModel.latticeGraph d)
              ((cubicExhaustion d).volume n)).Dart,
              (1 / (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
                  * (latticeDistance d x dt.fst.val : ℝ)) ^ α))
                * (1 / (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
                  * (latticeDistance d z dt.snd.val : ℝ)) ^ α)) := by
  classical
  rw [show (∑ e ∈ (inducedGraph (IsingModel.latticeGraph d)
          ((cubicExhaustion d).volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} n *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} n +
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} n *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val} n,
          fun u v => by ring⟩ e)
      = ∑ dt : (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n)).Dart,
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, dt.fst.val} n *
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {z, dt.snd.val} n
      from SimpleGraph.sum_edgeFinset_sym2_lift_prod_eq_sum_dart
        (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
        (fun w => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, w.val} n)
        (fun w => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {z, w.val} n)]
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_le_sum (fun dt _ => ?_)
  exact (dart_term_div_c_le_finiteRegionFV hα hJ hβ hA hxz hx hz dt hbind).trans
    (le_of_eq (by ring))

end Ambient
end IsingModel
