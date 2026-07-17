import IsingModel.AmbientLattice.TruncatedFunctions.FourPoint

/-!
# Infinite-volume `truncated4Infinite` aliases at `h = 0`

Narrow child module for the two §17.7 ambient infinite-volume
aliases of `truncated4Infinite_nonpos_h_zero` extracted from
`InfiniteVolume.lean`:

* `zeta_nonneg_infinite_vol` (GJ §17.7 Thm 17.7.1 critical-exponent
  naming),
* `absence_of_even_bound_states_infinite_vol` (GJ §17.2 pp. 311-313
  named-theorem alias).

Both wrappers state `U₄^∞(i,j,k,l) ≤ 0` for ferromagnetic
`⟨J, 0, β⟩` and pairwise-distinct sites; each is a thin alias of
`truncated4Infinite_nonpos_h_zero`. Theorem names are unchanged
from the former `InfiniteVolume` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Critical exponents at infinite volume (GJ §17.7 Thm 17.7.1) -/

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
