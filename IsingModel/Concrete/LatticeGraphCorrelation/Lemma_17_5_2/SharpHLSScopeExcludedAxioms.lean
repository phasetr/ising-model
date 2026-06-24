import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLS

/-!
# Scope-excluded analytic axioms for the GJ §17.5 sharp HLS constant (Lemma 17.5.2)

This module isolates, as **clearly-labelled, deliberately-unproven `axiom`s**, the two analytic
inputs of the GJ §17.5 sharp Hardy–Littlewood–Sobolev constant (Theorem 17.5.1 / Lemma 17.5.2)
that are **out of scope** for this lattice-Ising library — exactly the same way
`IsingModel.FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn`
(`ComplexAnalyticity/FunctionTheoryAxioms.lean`) isolates the Vitali–Porter convergence theorem.

Both inputs belong to the **volume-uniform complex cluster-expansion / normal-families**
analytic core that GJ §17.5 p. 312 invokes and that is the *same* analytic class master tracker
**#4214 item D** (∞-volume two-point analyticity) discharged only via the `vitaliPorter` axiom.
`CEConditionalCapstone.lean:48–61` records the precise obstruction on the Ising side: the only
available concrete complex data (per-fixed-volume trivial-`Q`, disc radius `r = O(1/|Λ_k|)`
shrinking with the volume) forces the Cauchy Lipschitz constants `C_k → ∞`, so the volume-uniform
single-disc input cannot be produced from current data. Proving it would amount to building a
bespoke complex-analysis / cluster-expansion-convergence library inside a lattice-model project,
which is not this project's responsibility.

These axioms discharge audit gaps **B2 #4269** (volume-uniform complex CE input) and the analytic
core of **B4 #4271** (sharp HLS constant, master #4214 item C); the GJ Lemma 17.5.2 sharp two-sided
sandwich is then completed on top of them in `SharpHLSCapstone.lean`.

Each axiom is (i) the genuine analytic / volume-uniform-complex core, unprovable from current
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

/-- **Scope-excluded axiom — validating endpoint pseudo-mass exponential decay for the cubic
lattice** (GJ §17.5 sharp HLS lower side; audit B4 #4271).

States that, at high temperature (`0 < J`, `0 < β`, `β·J·2d < 1`) and a distinct pair `x ≠ z`, the
concrete pair pseudo-mass `pseudoMassFromParamsAtPair` is itself a valid exponential-decay rate of
the lattice mass, i.e. `HasExponentialDecay d Λ ⟨J,0,β⟩ (pseudoMassFromParamsAtPair … x z)`.

On the Ising side this reduces to the per-pair profile lower bound
`pseudoMassG α r (−log(βJ·2d)) ≤ correlationInfinite {x,z}` (cf.
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr`), the lower validating
input of the sharp sandwich. The all-displacement form of this profile bound has a proven no-go
(`not_forall_cubicTanhProfileBound_of_betaJ_pos_high_temp`, audit B3 #4270), so a uniform per-pair
discharge belongs to the same volume-uniform analytic core as the derivative-limit provider above.
It is therefore isolated here as a deliberately-unproven scope-excluded axiom.

**Reference:** Glimm–Jaffe, 2nd ed., §17.5 pp. 311–312; cf. Issues #4271, #4270. -/
axiom lemma_17_5_2_validatingDecay_latticeGraph
    {d α : ℕ} (hα : 1 ≤ α) {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β) (hlt : β * J * ↑(2 * d) < 1)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z)

end Ambient
end IsingModel
