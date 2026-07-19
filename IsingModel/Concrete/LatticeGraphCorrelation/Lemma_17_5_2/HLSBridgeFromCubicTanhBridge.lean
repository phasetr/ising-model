import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanhCore

/-!
# Conditional PseudoMassLatticeDistanceBridge constructor: active range + direct constructor

Final `active`-range provider and the direct `PseudoMassLatticeDistanceBridge`
constructor (Step 119 plan Steps 5.7o, 5.7p): the all-pair active range from
`0 < β·J` via the tanh-power lower bound, and the direct bridge constructor
from bound + active providers.

This is a structural child of `HLSBridgeFromCubicTanh.lean`; see that umbrella
module for the full overview.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-! ## Step 119 plan Step 5.7o: active range from tanh-power lower bound -/

/-- **All-pair active range from `0 < β·J`** (Step 119 plan Step 5.7o).

Direct provider of the `active` field of `PseudoMassLatticeDistanceBridge`:
given `0 < β·J` (strict positivity), `tanh(β·J) > 0`, so
`tanh(β·J)^d(x,z) > 0` for every distinct pair `(x, z)`, and combined with
the existing tanh-power lower bound `tanh(β·J)^d(0, r) ≤ twoPointFunction d r`
(`PathLowerBound.twoPointFunction_ge_tanh_betaJ_pow_dist`) plus translation
invariance and the universal upper bound
`correlationInfinite_latticeGraph_le_one`, yields
`correlationInfinite ∈ Ioo 0 2` for every distinct pair.

Complements Step 5.7n (PR #3185)'s all-pair bound provider, completing the
structural input set for building a concrete `PseudoMassLatticeDistanceBridge`
value directly from concrete analytic inputs (without going through the
conditional `cubicTanhProfileBound` family). -/
theorem correlationInfinite_pair_active_of_betaJ_pos
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 := by
  have hJ : 0 ≤ J := by
    have hJ_pos : 0 < J := (mul_pos_iff_of_pos_left hβ).mp hβJ_pos
    exact hJ_pos.le
  intro x z hxz
  refine ⟨?_, ?_⟩
  · -- Lower bound: 0 < tanh(β·J)^d(x,z) ≤ correlation
    have hzx_ne : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
    have htanh_pos : 0 < Real.tanh (β * J) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr hβJ_pos) (Real.cosh_pos _)
    have hpow_pos : 0 < Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 (z - x) :=
      pow_pos htanh_pos _
    have h_tanh_le_two_pt :=
      twoPointFunction_ge_tanh_betaJ_pow_dist (d := d) (J := J) (β := β)
        hJ hβ hzx_ne
    have htrans :
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
          = twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) (z - x) := by
      rw [correlationInfinite_pair_eq_displacement d hJ hβ x z]
      exact twoPointFunction_apply d _ (z - x)
    rw [htrans]
    exact lt_of_lt_of_le hpow_pos h_tanh_le_two_pt
  · -- Upper bound: correlation ≤ 1 < 2
    have h_le_one := correlationInfinite_latticeGraph_le_one d
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
    linarith

/-! ## Step 119 plan Step 5.7p: direct PseudoMassLatticeDistanceBridge constructor -/

/-- **Direct `PseudoMassLatticeDistanceBridge` constructor from bound + active
providers** (Step 119 plan Step 5.7p).

Convenience structural constructor taking:
- `M_inf : ℝ`, `M_inf_pos : 0 < M_inf` (the rate);
- `hf : Ferromagnetic ⟨J, 0, β⟩`;
- `bound`: the all-pair shape from Step 5.7n (PR #3185);
- `active`: the all-pair shape from Step 5.7o (PR #3186);

and producing a `PseudoMassLatticeDistanceBridge` value directly. This is
the alternative constructor matching the natural shape of the Step 5.7n /
Step 5.7o providers, bypassing the conditional `cubicTanhProfileBound`
family path. -/
def PseudoMassLatticeDistanceBridge_of_bound_active
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ}
    {M_inf : ℝ} (M_inf_pos : 0 < M_inf)
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (bound : ∀ x z : Fin d → ℤ, x ≠ z →
      M_inf * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r)
    (active : ∀ x z : Fin d → ℤ, x ≠ z →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2) :
    PseudoMassLatticeDistanceBridge hα hr d J β where
  M_inf := M_inf
  M_inf_pos := M_inf_pos
  hf := hf
  bound := bound
  active := active

end Ambient
end IsingModel
