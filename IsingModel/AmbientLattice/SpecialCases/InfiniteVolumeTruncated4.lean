import IsingModel.AmbientLattice.TruncatedFunctions.FourPoint

/-!
# Sign of the infinite-volume truncated four-point function at zero external field

Statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`. Every
statement takes `DecidableEq V` and the stagewise `Fintype` instance on the edge set of the
induced subgraph of `Λ.volume n`.

At the zero-field parameter triple `⟨J, 0, β⟩` the infinite-volume truncated four-point
function is nonpositive at four sites `i j k l : V`. The Prop-valued hypotheses are exactly
`Ferromagnetic ⟨J, 0, β⟩` together with the six inequalities making `i`, `j`, `k`, `l`
pairwise distinct.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **ζ ≥ 0 at infinite volume** (GJ §17.7 Thm 17.7.1, infinite-volume
lattice version, at `h = 0`). Explicit alias of
`truncated4Infinite_nonpos_h_zero`: `U₄^∞ ≤ 0` for pairwise-distinct sites at
`h = 0`. -/
theorem zeta_nonneg_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero G Λ J β hf hij hik hil hjk hjl hkl

/-- **Absence of even bound states, infinite-volume lattice form**
(Glimm-Jaffe §17.2, pp. 311-313). Infinite-volume version of
`IsingModel.absence_of_even_bound_states_finite_vol`: `U₄^∞(i,j,k,l) ≤ 0` for
ferromagnetic `⟨J, 0, β⟩` and pairwise-distinct sites. Explicit alias of
`truncated4Infinite_nonpos_h_zero`. -/
theorem absence_of_even_bound_states_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero G Λ J β hf hij hik hil hjk hjl hkl

end Ambient
end IsingModel
