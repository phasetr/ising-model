import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint

/-!
# Concrete infinite-volume correlation inequalities on Z^d

Thin concrete wrappers for the GHS and Lebowitz infinite-volume inequalities,
specialized to the cubic lattice and the two-point separation notation.
-/

namespace IsingModel
namespace Ambient

/-! ## Concrete Lebowitz / GHS inequalities on Z^d -/

/-- **GHS `U_3 ≤ 0` on ℤ^d** (Glimm–Jaffe §4.3 Cor 4.3.4): for
ferromagnetic `p` and pairwise distinct `r, s : Fin d → ℤ`
(with both non-zero to ensure distinctness from the anchor `0`),
`truncated3TwoPoint d p r s ≤ 0`.

Direct application of `truncated3Infinite_nonpos` at `i = 0, j = r, k = s`
under the three distinctness hypotheses `0 ≠ r, r ≠ s, 0 ≠ s`. -/
theorem truncated3TwoPoint_nonpos_of_distinct
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {r s : Fin d → ℤ} (hr : (0 : Fin d → ℤ) ≠ r)
    (hrs : r ≠ s) (hs : (0 : Fin d → ℤ) ≠ s) :
    truncated3TwoPoint d p r s ≤ 0 :=
  truncated3Infinite_nonpos (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf hr hrs hs

/-- **Lebowitz `U_4 ≤ 0` on ℤ^d at `h = 0`** (Glimm–Jaffe §4.3 Cor 4.3.3):
for ferromagnetic `⟨J, 0, β⟩` and pairwise distinct `r, s, u : Fin d → ℤ`
(all three non-zero + pairwise distinct),
`truncated4TwoPoint d ⟨J, 0, β⟩ r s u ≤ 0`.

Direct application of `truncated4Infinite_nonpos_h_zero` at
`i = 0, j = r, k = s, l = u`. -/
theorem truncated4TwoPoint_nonpos_h_zero_of_distinct
    (d : ℕ) (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {r s u : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s)
    (hu : (0 : Fin d → ℤ) ≠ u)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) :
    truncated4TwoPoint d ⟨J, 0, β⟩ r s u ≤ 0 :=
  truncated4Infinite_nonpos_h_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hf hr hs hu hrs hru hsu

/-- **GJ §17.3 (17.3.1) lower bound on U₄^∞ on ℤ^d** (Glimm–Jaffe §17.3 p. 308 eq. (17.3.1)):
for ferromagnetic `⟨J, 0, β⟩` and pairwise distinct `r, s, u : Fin d → ℤ`,
`-(corr{0,s}·corr{r,u} + corr{0,u}·corr{r,s}) ≤ truncated4TwoPoint d ⟨J,0,β⟩ r s u`.

Direct application of `truncated4Infinite_ge_neg_pair_correlations` at `i=0, j=r, k=s, l=u`. -/
theorem truncated4TwoPoint_ge_neg_pair_correlations_of_distinct
    (d : ℕ) (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {r s u : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s)
    (hu : (0 : Fin d → ℤ) ≠ u)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) :
    -(correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          ⟨J, 0, β⟩ {0, s} *
        correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          ⟨J, 0, β⟩ {r, u} +
      correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          ⟨J, 0, β⟩ {0, u} *
        correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          ⟨J, 0, β⟩ {r, s})
    ≤ truncated4TwoPoint d ⟨J, 0, β⟩ r s u :=
  truncated4Infinite_ge_neg_pair_correlations (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hf hr hs hu hrs hru hsu

end Ambient
end IsingModel
