import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLS

/-!
# Scope-excluded analytic axiom for the GJ §17.5 sharp HLS constant (Lemma 17.5.2)

This module isolates, as a **clearly-labelled, deliberately-unproven `axiom`**, the single analytic
input of the GJ §17.5 sharp Hardy–Littlewood–Sobolev constant (Theorem 17.5.1 / Lemma 17.5.2) that
is **out of scope** for this lattice-Ising library — exactly the same way
`IsingModel.FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn`
(`ComplexAnalyticity/FunctionTheoryAxioms.lean`) isolates the Vitali–Porter convergence theorem.

The axiom is the **locally-uniform derivative-limit provider** (Montel / Vitali–Porter
normal-families convergence of the finite-stage `β`-derivatives). It belongs to the
**volume-uniform complex cluster-expansion / normal-families** analytic core that GJ §17.5 p. 312
invokes and that is the *same* analytic class master tracker **#4214 item D** (∞-volume two-point
analyticity) discharged only via the `vitaliPorter` axiom. `CEConditionalCapstone.lean:48–61`
records the precise obstruction on the Ising side: the only available concrete complex data
(per-fixed-volume trivial-`Q`, disc radius `r = O(1/|Λ_k|)` shrinking with the volume) forces the
Cauchy Lipschitz constants `C_k → ∞`, so the volume-uniform single-disc input cannot be produced
from current data. Proving it would amount to building a bespoke complex-analysis /
cluster-expansion-convergence library inside a lattice-model project, which is not this project's
responsibility.

This axiom discharges the analytic core of audit gaps **B2 #4269** (volume-uniform complex CE input)
and **B4 #4271** (sharp HLS constant, master #4214 item C); the GJ Lemma 17.5.2 sharp two-sided
sandwich is then completed on top of it in `SharpHLSCapstone.lean`.

**Important — what is NOT axiomatized.** The sharp sandwich's *lower* side needs the **per-pair
profile bound** `pseudoMassG α r (−log(β·J·2d)) ≤ correlationInfinite {x,z}`. This is **not**
axiomatized here, because its unconditional `∀ x ≠ z` form is **false**: as the pair separates,
`correlationInfinite {x,z} → 0` while `pseudoMassFromParamsAtPair → ∞`, so an unconditional
validating-decay axiom would force `latticeMass = ⊤` (the project's own no-go
`not_forall_cubicTanhProfileBound_of_betaJ_pos_high_temp`, B3 #4270, proves exactly this failure for
far pairs). The capstone therefore keeps the per-pair profile bound as an explicit **hypothesis**
(matching the non-sharp uniform sandwich `lemma_17_5_2_high_temp_sandwich_uniform_transfer`) and
discharges the decay via the *proven*
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr`. Only the genuine analytic
normal-families core below is an axiom.

The axiom is (i) the genuine analytic / volume-uniform-complex core, unprovable from current
Ising-side data; (ii) absent from Mathlib; (iii) confined to this module; (iv) documented with its
precise statement and the reason it is out of scope. The Ising-side content that *feeds* the sharp
constant (the real-axis derivative bounds, the HLS convolution constant, the active-range and
pseudo-mass calculus, the per-pair susceptibility ceiling #4277) is in scope and proven in the
usual way.

**Reference:** Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 Theorem 17.5.1 / Lemma 17.5.2,
pp. 311–312.
-/

namespace IsingModel
namespace Ambient

/-- **Scope-excluded axiom — locally-uniform derivative-limit provider for the cubic lattice**
(GJ §17.5 sharp HLS analytic core; audit B2 #4269 / B4 #4271).

States that, for the `d`-dimensional lattice graph along any exhaustion `Λ`, at strictly positive
coupling `J` and a distinct pair `x ≠ z`, the finite-stage `β`-derivatives of the pair correlation
converge **locally uniformly** on the high-temperature interval `Ioo 0 (1/(J·2d))`, i.e.
`Lemma_17_5_2_DerivativeLimitProvider Λ J x z` holds.

This `TendstoLocallyUniformlyOn` statement is the **Montel / Vitali–Porter normal-families core**
of the sharp HLS derivative bound (GJ p. 312). It is the same volume-uniform complex-analyticity
class that master #4214 item D obtained only via the `vitaliPorter` axiom, and
`CEConditionalCapstone.lean:48–61` shows it cannot be produced from the available concrete
complex data (Cauchy constants `C_k → ∞`). It is therefore **out of scope** and isolated here as a
deliberately-unproven axiom (cf. `ComplexAnalyticity/FunctionTheoryAxioms.lean`).

**Reference:** Glimm–Jaffe, 2nd ed., §17.5 pp. 311–312; cf. Issues #4269, #4271, #3054. -/
axiom lemma_17_5_2_derivativeLimitProvider_latticeGraph
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z

end Ambient
end IsingModel
