import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity

/-!
# Concrete real-complex compatibility / Lee-Yang domain wrappers

Narrow child module for concrete real-complex compatibility,
Lee-Yang-domain non-vanishing, and related restriction wrappers on
`latticeGraph d`. 22 theorems including
`partitionFunction_ofReal_eq_partitionFunctionComplex_latticeGraph`,
`partitionFunctionComplex_mem_slitPlane_of_real_latticeGraph`,
`freeEnergy_ofReal_eq_freeEnergyComplex_latticeGraph`,
`partitionFunctionComplex_eq_normalization_mul_isingEdgePoly_latticeGraph`,
`partitionFunctionComplex_ne_zero_on_leeYangDomain_latticeGraph`,
`partitionFunctionComplex_re_pos_of_leeYangSubdomain_latticeGraph`,
`freeEnergyComplex_analyticAt_h_of_leeYangSubdomain_latticeGraph`,
`partitionFunctionComplex_at_real_pos_latticeGraph`,
`freeEnergyComplex_at_real_latticeGraph`,
`norm_partitionFunctionComplex_at_real_latticeGraph`, and related
real-axis restriction lemmas. The theorem names are unchanged from the
former `Complex` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `partitionFunction` / `partitionFunctionComplex` real-complex
compatibility** (Λ-induced):
`↑(Z G p) = Z_ℂ G ↑p.J ↑p.h ↑p.β`. -/
theorem partitionFunction_ofReal_eq_partitionFunctionComplex_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ((IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ)
      = IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) :=
  IsingModel.partitionFunction_ofReal_eq_partitionFunctionComplex
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `partitionFunctionComplex` in `slitPlane` on the real slice**
(Λ-induced). -/
theorem partitionFunctionComplex_mem_slitPlane_of_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) ∈ Complex.slitPlane :=
  IsingModel.partitionFunctionComplex_mem_slitPlane_of_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `freeEnergy` / `freeEnergyComplex` real-complex compatibility**
(Λ-induced): `↑(f G p) = f_ℂ G ↑p.J ↑p.h ↑p.β`. -/
theorem freeEnergy_ofReal_eq_freeEnergyComplex_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ((IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ)
      = IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) :=
  IsingModel.freeEnergy_ofReal_eq_freeEnergyComplex
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-! #### Lee-Yang domain / subdomain analyticity (GJ §4.6 Thm 4.6.2)

Direct ℤ^d forwarders for the Lee-Yang nonvanishing and free-energy
analyticity package from `IsingModel/ComplexAnalyticity.lean`:
Friedli-Velenik factorisation, Lee-Yang nonvanishing, `Re Z > 0` /
`slitPlane` on the subdomain, `freeEnergyComplex` analyticity on the
subdomain / real slice, and `logDeriv Z / Z` on the entire Lee-Yang
domain. These feed GJ §4.6 Thm 4.6.2 Vitali completion at ℤ^d. -/

/-- **ℤ^d Friedli-Velenik factorisation** (Λ-induced):
`Z_ℂ G (J, h, β) = N(β, J, h, |E|, |ι|) · P_E(leeYangFugacityVec β h)`.
Thin pass-through of
`IsingModel.partitionFunctionComplex_eq_normalization_mul_isingEdgePoly`.
Combined with Lee-Yang nonvanishing of `P_E` this yields
`Z ≠ 0` on the Lee-Yang domain. -/
theorem partitionFunctionComplex_eq_normalization_mul_isingEdgePoly_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) (h : ℂ) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)
      = IsingModel.leeYangNormalization (β : ℂ) (J : ℂ) h
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          (Fintype.card (↑Λ : Type _))
        * (IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (Real.exp (-2 * β * J)))).eval
              (IsingModel.leeYangFugacityVec (β : ℂ) h) :=
  IsingModel.partitionFunctionComplex_eq_normalization_mul_isingEdgePoly
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h

/-- **ℤ^d Lee-Yang nonvanishing on the Lee-Yang domain** (Λ-induced,
ferromagnetic): for `β > 0`, `J > 0`, and `h ∈ leeYangDomain`,
`Z_ℂ G (J, h, β) ≠ 0`. GJ §4.6 Thm 4.6.2 core. Thin pass-through of
`IsingModel.partitionFunctionComplex_ne_zero_on_leeYangDomain`. -/
theorem partitionFunctionComplex_ne_zero_on_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangDomain) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ) ≠ 0 :=
  IsingModel.partitionFunctionComplex_ne_zero_on_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hh

/-- **ℤ^d `Re Z_ℂ > 0` on the Lee-Yang subdomain** (Λ-induced): for
`β > 0` and `h` with `β · |h.im| · |Λ| < π/2`,
`0 < Re(Z_ℂ G (J, h, β))`. Thin pass-through of
`IsingModel.partitionFunctionComplex_re_pos_of_leeYangSubdomain`. -/
theorem partitionFunctionComplex_re_pos_of_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card (↑Λ : Type _) : ℝ) < Real.pi / 2) :
    0 < (IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h (β : ℂ)).re :=
  IsingModel.partitionFunctionComplex_re_pos_of_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J himπ

/-- **ℤ^d `Z_ℂ ∈ slitPlane` on the Lee-Yang subdomain** (Λ-induced):
corollary of the `Re Z > 0` result, feeding `Complex.log` analyticity. -/
theorem partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card (↑Λ : Type _) : ℝ) < Real.pi / 2) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane :=
  IsingModel.partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J himπ

/-- **ℤ^d `freeEnergyComplex` analytic in `h` on the Lee-Yang subdomain**
(Λ-induced). Finite-volume GJ §4.6 Thm 4.6.2 on the subdomain
`β · |Im h| · |Λ| < π/2`. -/
theorem freeEnergyComplex_analyticAt_h_of_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card (↑Λ : Type _) : ℝ) < Real.pi / 2) :
    AnalyticAt ℂ (fun h' => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
      (J : ℂ) h' (β : ℂ)) h :=
  IsingModel.freeEnergyComplex_analyticAt_h_of_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J himπ

/-- **ℤ^d `freeEnergyComplex` `AnalyticOnNhd` on the Lee-Yang subdomain**
(Λ-induced). -/
theorem freeEnergyComplex_analyticOnNhd_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOnNhd ℂ (fun h' => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h' (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_analyticOnNhd_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `freeEnergyComplex` analytic in `h` at real `h₀`** (Λ-induced,
real-slice corollary; no ferromagnetic hypothesis). -/
theorem freeEnergyComplex_analyticAt_h_ofReal_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h₀ β : ℝ) :
    AnalyticAt ℂ (fun h => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ))
      (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_analyticAt_h_ofReal
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h₀ β

/-- **ℤ^d `partitionFunctionComplex` `AnalyticOnNhd` on the Lee-Yang
domain** (Λ-induced): globally entire in `h`. -/
theorem partitionFunctionComplex_analyticOnNhd_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOnNhd ℂ
        (fun h' => IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h' β)
      IsingModel.leeYangDomain :=
  IsingModel.partitionFunctionComplex_analyticOnNhd_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d logarithmic derivative `Z'/Z` analytic on Lee-Yang domain**
(Λ-induced, ferromagnetic `β > 0`, `J > 0`): input to the Morera-based
branch construction of `log Z`. -/
theorem logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    AnalyticOnNhd ℂ (fun h : ℂ =>
        deriv (fun h' => IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h' (β : ℂ)) h
          / IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ))
      IsingModel.leeYangDomain :=
  IsingModel.logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-! #### Real-axis evaluation of the complex partition function / free energy

Direct ℤ^d forwarders for the real-axis evaluation identities of the
complex partition function and free energy. These restate the
real-complex bridge in the form most useful for Vitali convergence
(pointwise values on the real axis via Fekete). -/

/-- **ℤ^d `partitionFunctionComplex` at real `h₀`** (Λ-induced):
`Z_ℂ(J, ↑h₀, β) = ↑(Z G ⟨J, h₀, β⟩)`. -/
theorem partitionFunctionComplex_at_real_pos_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β h₀ : ℝ) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) (h₀ : ℂ) (β : ℂ)
      = ((IsingModel.partitionFunction
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            ⟨J, h₀, β⟩ : ℝ) : ℂ) :=
  IsingModel.partitionFunctionComplex_at_real_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `freeEnergyComplex` at real parameters** (Λ-induced):
`f_ℂ(J, h, β) = ↑(f G ⟨J, h, β⟩)`. -/
theorem freeEnergyComplex_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) (h : ℂ) (β : ℂ)
      = ((IsingModel.freeEnergy
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            ⟨J, h, β⟩ : ℝ) : ℂ) :=
  IsingModel.freeEnergyComplex_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-- **ℤ^d `freeEnergyComplex ↔ freeEnergy` Vitali form** (Λ-induced):
`f_ℂ G ↑p.J ↑p.h ↑p.β = ↑(f G p)`. Thin restatement of
`freeEnergy_ofReal_eq_freeEnergyComplex` in the orientation most useful
for Vitali convergence (RHS is the cast of the real-parameter value). -/
theorem freeEnergyComplex_ofReal_eq_freeEnergy_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)
      = ((IsingModel.freeEnergy
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ) :=
  IsingModel.freeEnergyComplex_ofReal_eq_freeEnergy
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Re Z_ℂ > 0` at real parameters** (Λ-induced):
immediate from positivity of the real `Z`. -/
theorem partitionFunctionComplex_re_pos_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    0 < (IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).re :=
  IsingModel.partitionFunctionComplex_re_pos_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Im Z_ℂ = 0` at real parameters** (Λ-induced). -/
theorem partitionFunctionComplex_im_zero_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).im = 0 :=
  IsingModel.partitionFunctionComplex_im_zero_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Im (log Z_ℂ) = 0` at real parameters** (Λ-induced). -/
theorem log_partitionFunctionComplex_im_zero_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (Complex.log (IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))).im = 0 :=
  IsingModel.log_partitionFunctionComplex_im_zero_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Im f_ℂ = 0` at real parameters** (Λ-induced). -/
theorem freeEnergyComplex_im_zero_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).im = 0 :=
  IsingModel.freeEnergyComplex_im_zero_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Re f_ℂ = f` at real parameters** (Λ-induced). -/
theorem freeEnergyComplex_re_eq_freeEnergy_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).re
      = IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.freeEnergyComplex_re_eq_freeEnergy_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `‖Z_ℂ‖ = Z` at real parameters** (Λ-induced). -/
theorem norm_partitionFunctionComplex_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)‖
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.norm_partitionFunctionComplex_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Z_ℂ` is a positive real at real parameters** (Λ-induced):
explicit witness for `Z_ℂ = ↑x` with `0 < x`. -/
theorem partitionFunctionComplex_is_pos_real_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ∃ x : ℝ, 0 < x ∧ IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) = (x : ℂ) :=
  IsingModel.partitionFunctionComplex_is_pos_real_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

end Ambient

end IsingModel
