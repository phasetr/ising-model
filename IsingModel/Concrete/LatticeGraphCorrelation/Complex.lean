import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity

/-!
# ℤ^d real/complex analyticity wrappers (fixed-Λ)

Direct ℤ^d forwarders for:

* Real analyticity of `partitionFunctionΛ` / `freeEnergyH` / `freeEnergyJ`
  (using `IsingModel/FreeEnergy.lean`).
* Complex analyticity of `partitionFunctionComplex` / `freeEnergyComplex`
  (GJ §4.6 Thm 4.6.2; using `IsingModel/ComplexAnalyticity.lean` and
  `IsingModel/AmbientComplexAnalyticity.lean`).
* Lee–Yang non-vanishing: `partitionFunctionComplex_nonzero_of_leeYang_*`.
* Slit-plane membership and `freeEnergyComplex` log-branch wrappers.
* `isingEdgePoly` / `leeYangFugacityVec` product expansion.

All theorems are thin pass-throughs of the abstract results in
`ComplexAnalyticity.lean` / `AmbientComplexAnalyticity.lean` applied to the
concrete `Ambient.inducedGraph (IsingModel.latticeGraph d) Λ` at a fixed
finite `Λ : Finset (Fin d → ℤ)`.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6, pp. 68–70.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d `partitionFunction` analytic in `h`** at Λ-induced subgraph. -/
theorem partitionFunctionH_analyticAt_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β h₀ : ℝ) :
    AnalyticAt ℝ
      (fun h => partitionFunctionΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩) h₀ :=
  IsingModel.partitionFunctionH_analyticAt
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `freeEnergyH` analytic on `(0, ∞)`** at Λ-induced subgraph. -/
theorem freeEnergyH_analyticOn_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    AnalyticOn ℝ
      (IsingModel.freeEnergyH
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β)
      (Set.Ioi 0) :=
  IsingModel.freeEnergyH_analyticOn
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `partitionFunction` analytic in `J`** at Λ-induced subgraph. -/
theorem partitionFunctionJ_analyticAt_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β J₀ : ℝ) :
    AnalyticAt ℝ
      (fun J => partitionFunctionΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩) J₀ :=
  IsingModel.partitionFunctionJ_analyticAt
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β J₀

/-- **ℤ^d `freeEnergyJ` analytic on `(0, ∞)`** at Λ-induced subgraph. -/
theorem freeEnergyJ_analyticOn_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    AnalyticOn ℝ
      (IsingModel.freeEnergyJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β)
      (Set.Ioi 0) :=
  IsingModel.freeEnergyJ_analyticOn
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-! #### Complex analyticity (GJ §4.6 Thm 4.6.2)

Direct ℤ^d forwarders for the complex-analyticity package in
`IsingModel/ComplexAnalyticity.lean`: per-variable / joint entire
analyticity of `partitionFunctionComplex`, its `slitPlane`-conditioned
`freeEnergyComplex` counterpart, and the real-complex compatibility
identities. -/

/-- **ℤ^d `partitionFunctionComplex` entire in `h`** (Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β h₀ : ℂ) :
    AnalyticAt ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) h₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `partitionFunctionComplex` entire in `J`** (Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β J₀ : ℂ) :
    AnalyticAt ℂ (fun J => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) J₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β J₀

/-- **ℤ^d `partitionFunctionComplex` entire in `β`** (Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β₀ : ℂ) :
    AnalyticAt ℂ (fun β => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) β₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β₀

/-- **ℤ^d `freeEnergyComplex` analytic in `h`** (Λ-induced), on
`{Z ∈ slitPlane}`. -/
theorem freeEnergyComplex_analyticAt_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β h₀ : ℂ)
    (hZ : IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h₀ β
          ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) h₀ :=
  IsingModel.freeEnergyComplex_analyticAt_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀ hZ

/-- **ℤ^d `freeEnergyComplex` analytic in `J`** (Λ-induced), on
`{Z ∈ slitPlane}`. -/
theorem freeEnergyComplex_analyticAt_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β J₀ : ℂ)
    (hZ : IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J₀ h β
          ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun J => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) J₀ :=
  IsingModel.freeEnergyComplex_analyticAt_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β J₀ hZ

/-- **ℤ^d `freeEnergyComplex` analytic in `β`** (Λ-induced), on
`{Z ∈ slitPlane}`. -/
theorem freeEnergyComplex_analyticAt_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β₀ : ℂ)
    (hZ : IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β₀
          ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun β => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) β₀ :=
  IsingModel.freeEnergyComplex_analyticAt_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β₀ hZ

/-- **ℤ^d `partitionFunctionComplex` jointly entire in `(J, h, β)`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (z₀ : ℂ × ℂ × ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) z₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z₀

/-- **ℤ^d `freeEnergyComplex` jointly analytic** (Λ-induced), on
`{Z ∈ slitPlane}`. -/
theorem freeEnergyComplex_analyticAt_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (z₀ : ℂ × ℂ × ℂ)
    (hZ : IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            z₀.1 z₀.2.1 z₀.2.2
          ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) z₀ :=
  IsingModel.freeEnergyComplex_analyticAt_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z₀ hZ

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

/-! #### Continuity, analyticOn, and norm bounds for complex Z / f

Direct ℤ^d forwarders for continuity, universe / Lee-Yang-domain
`AnalyticOn` restatements, and locally-uniform norm bounds on
`partitionFunctionComplex` / `freeEnergyComplex`. These are the
Montel + Vitali inputs for the infinite-volume completion at ℤ^d. -/

/-- **ℤ^d `Continuous` form of `partitionFunctionComplex` in `h`**
(Λ-induced). -/
theorem continuous_partitionFunctionComplex_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    Continuous (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.continuous_partitionFunctionComplex_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Continuous` form of `partitionFunctionComplex` in `J`**
(Λ-induced). -/
theorem continuous_partitionFunctionComplex_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℂ) :
    Continuous (fun J => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.continuous_partitionFunctionComplex_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d `Continuous` form of `partitionFunctionComplex` in `β`**
(Λ-induced). -/
theorem continuous_partitionFunctionComplex_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℂ) :
    Continuous (fun β => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.continuous_partitionFunctionComplex_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h

/-- **ℤ^d joint continuity of `partitionFunctionComplex`** (Λ-induced):
`(J, h, β) : ℂ × ℂ × ℂ ↦ Z_ℂ` is continuous. -/
theorem continuous_partitionFunctionComplex_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Continuous (fun z : ℂ × ℂ × ℂ =>
      IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) :=
  IsingModel.continuous_partitionFunctionComplex_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `partitionFunctionComplex` `AnalyticOnNhd ℂ Set.univ` in `h`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticOnNhd_univ_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOnNhd ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) Set.univ :=
  IsingModel.partitionFunctionComplex_analyticOnNhd_univ_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d joint `AnalyticOnNhd ℂ Set.univ` for `partitionFunctionComplex`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticOnNhd_univ_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      Set.univ :=
  IsingModel.partitionFunctionComplex_analyticOnNhd_univ_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `partitionFunctionComplex` `ContinuousOn` on `leeYangDomain`**
(Λ-induced). -/
theorem partitionFunctionComplex_continuousOn_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    ContinuousOn (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      IsingModel.leeYangDomain :=
  IsingModel.partitionFunctionComplex_continuousOn_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `partitionFunctionComplex` `AnalyticOn` on `leeYangDomain`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticOn_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOn ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      IsingModel.leeYangDomain :=
  IsingModel.partitionFunctionComplex_analyticOn_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `freeEnergyComplex` `AnalyticOn` on `leeYangSubdomain`**
(Λ-induced, ferromagnetic `β > 0`). -/
theorem freeEnergyComplex_analyticOn_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOn ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_analyticOn_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `freeEnergyComplex` `ContinuousOn` on `leeYangSubdomain`**
(Λ-induced, ferromagnetic `β > 0`). -/
theorem freeEnergyComplex_continuousOn_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    ContinuousOn (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_continuousOn_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `freeEnergyComplex` `DifferentiableOn` on `leeYangSubdomain`**
(Λ-induced, ferromagnetic `β > 0`): Vitali-compatible input. -/
theorem freeEnergyComplex_differentiableOn_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    DifferentiableOn ℂ (fun h' => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h' (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_differentiableOn_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `‖Z_ℂ‖ ≤ Z_ℝ(J, Re h, β)`** (Λ-induced): dominate the complex
partition function by its real counterpart at `Re h`. -/
theorem norm_partitionFunctionComplex_le_partitionFunction_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) (h : ℂ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, h.re, β⟩ :=
  IsingModel.norm_partitionFunctionComplex_le_partitionFunction
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h

/-- **ℤ^d trivial upper bound on `‖Z_ℂ‖`** (Λ-induced):
`‖Z_ℂ‖ ≤ 2^|Λ| · exp(|β|·(|J|·|E|_Λ + |Re h|·|Λ|))`. Locally uniform
on compact sets in `h`; input for Montel in the Vitali lift. -/
theorem norm_partitionFunctionComplex_le_trivial_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) (h : ℂ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ Fintype.card (IsingModel.Config (↑Λ : Type _)) *
          Real.exp (|β| *
            (|J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + |h.re| * Fintype.card (↑Λ : Type _))) :=
  IsingModel.norm_partitionFunctionComplex_le_trivial_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h

/-- **ℤ^d `‖Z_ℂ‖` upper bound under `|Re h| ≤ R`** (Λ-induced):
uniform over the strip `|Re h| ≤ R`. -/
theorem norm_partitionFunctionComplex_le_of_re_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) {R : ℝ} {h : ℂ}
    (hh : |h.re| ≤ R) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ Fintype.card (IsingModel.Config (↑Λ : Type _)) *
          Real.exp (|β| *
            (|J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + R * Fintype.card (↑Λ : Type _))) :=
  IsingModel.norm_partitionFunctionComplex_le_of_re_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J hh

/-- **ℤ^d trivial upper bound on `‖f_ℂ‖`** (Λ-induced, nonempty `Λ`):
`‖f_ℂ‖ ≤ |log ‖Z_ℂ‖|/|Λ| + π/|Λ|`. Combined with `BoundedEdgeDensity`
this gives the Vitali uniform-on-compacts bound. -/
theorem norm_freeEnergyComplex_le_trivial_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)] (β J : ℝ) (h : ℂ) :
    ‖IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ |Real.log ‖IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ)‖|
          / (Fintype.card (↑Λ : Type _) : ℝ)
        + Real.pi / (Fintype.card (↑Λ : Type _) : ℝ) :=
  IsingModel.norm_freeEnergyComplex_le_trivial_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h

/-! #### Local `log Z` / `freeEnergyComplex` branch on Lee-Yang domain

Direct ℤ^d forwarders for the `exists_logZ_*` / `exists_freeEnergyComplex_*`
local-branch construction, the `partitionFunctionComplex` non-vanishing
on `leeYangSubdomain` / `leeYangDomain`, and the principal-branch
`freeEnergyComplex` `AnalyticOnNhd` on its analyticity locus. These are
the finite-volume GJ §4.6 Thm 4.6.2 branch-form ingredients at ℤ^d. -/

/-- **ℤ^d `Z_ℂ ≠ 0` on `leeYangSubdomain`** (Λ-induced, ferromagnetic). -/
theorem partitionFunctionComplex_ne_zero_on_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ) ≠ 0 :=
  IsingModel.partitionFunctionComplex_ne_zero_on_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hh

/-- **ℤ^d `Z_ℂ MapsTo ≠ 0` on `leeYangDomain`** (Λ-induced,
ferromagnetic): `Set.MapsTo` restatement of the Lee-Yang
non-vanishing. -/
theorem partitionFunctionComplex_mapsTo_ne_zero_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Set.MapsTo (fun h : ℂ => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      IsingModel.leeYangDomain {z : ℂ | z ≠ 0} :=
  IsingModel.partitionFunctionComplex_mapsTo_ne_zero_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d `freeEnergyComplex` `AnalyticOnNhd` on the principal-branch
`slitPlane` analyticity locus** (Λ-induced). -/
theorem freeEnergyComplex_analyticOnNhd_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOnNhd ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_analyticOnNhd_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `freeEnergy` analyticity locus is open** (Λ-induced). -/
theorem isOpen_freeEnergy_analyticity_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    IsOpen {h : ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_freeEnergy_analyticity_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d local log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic): primitive of `Z'/Z`. -/
theorem exists_logZ_branch_on_ball_of_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
        (deriv (fun h'' => IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h'' (β : ℂ)) z
          / IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ)) z :=
  IsingModel.exists_logZ_branch_on_ball_of_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hsub

/-- **ℤ^d holomorphic log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic): `exp g = Z` on the ball,
`g h₀ = Complex.log(Z h₀)`. -/
theorem exists_logZ_holomorphic_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ,
        (∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ))
      ∧ g h₀ = Complex.log
          (IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h₀ (β : ℂ))
      ∧ ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
            (deriv (fun h'' => IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h'' (β : ℂ)) z
              / IsingModel.partitionFunctionComplex
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                  (J : ℂ) z (β : ℂ)) z :=
  IsingModel.exists_logZ_holomorphic_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d analytic log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic): `AnalyticOnNhd` refinement. -/
theorem exists_logZ_analytic_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ,
        (∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ))
      ∧ g h₀ = Complex.log
          (IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h₀ (β : ℂ))
      ∧ AnalyticOnNhd ℂ g (Metric.ball h₀ r) :=
  IsingModel.exists_logZ_analytic_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d pointwise analytic `log Z` branch at every `h₀ ∈ leeYangDomain`**
(Λ-induced, ferromagnetic). -/
theorem exists_logZ_analyticAt_of_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g h₀
      ∧ Complex.exp (g h₀)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h₀ (β : ℂ)
      ∧ g h₀ = Complex.log
          (IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h₀ (β : ℂ)) :=
  IsingModel.exists_logZ_analyticAt_of_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hmem

/-- **ℤ^d GJ §4.6 Thm 4.6.2 finite-volume (branch form)** (Λ-induced,
nonempty `Λ`, ferromagnetic): at every `h₀ ∈ leeYangDomain` there is an
`AnalyticAt` representative `f` with `exp(|Λ|·f) = Z` and
`f h₀ = freeEnergyComplex …`. -/
theorem exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h₀
      ∧ Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h₀)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h₀ (β : ℂ)
      ∧ f h₀ = IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h₀ (β : ℂ) :=
  IsingModel.exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hmem

/-- **ℤ^d `freeEnergyComplex` local branch `AnalyticOnNhd ball`**
(Λ-induced, nonempty `Λ`, ferromagnetic). -/
theorem exists_freeEnergyComplex_analyticOnNhd_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f z)
            = IsingModel.partitionFunctionComplex
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_freeEnergyComplex_analyticOnNhd_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d `freeEnergyComplex` local branch `DifferentiableOn ball`**
(Λ-induced, nonempty `Λ`, ferromagnetic). -/
theorem exists_freeEnergyComplex_differentiableOn_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        DifferentiableOn ℂ f (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f z)
            = IsingModel.partitionFunctionComplex
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_freeEnergyComplex_differentiableOn_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-! #### slitPlane-locus analyticity + log-branch basepoint evaluation

Direct ℤ^d forwarders for the remaining continuity / differentiable /
analytic-on-slitPlane-locus theorems (h-variable and joint (J, h, β)),
the log-branch basepoint identities, and auxiliary `exists_logZ_*`
ball restatements from `IsingModel/ComplexAnalyticity.lean`. -/

/-- **ℤ^d `Z_ℂ` `ContinuousAt` real `h₀`** (Λ-induced). -/
theorem partitionFunctionComplex_continuousAt_real_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    ContinuousAt (fun h : ℂ => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
      (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.partitionFunctionComplex_continuousAt_real_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` `ContinuousAt` real positive `h₀`** (Λ-induced). -/
theorem freeEnergyComplex_continuousAt_real_pos_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    ContinuousAt (fun h : ℂ => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
      (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_continuousAt_real_pos_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` `AnalyticAt h₀` under `Z h₀ ∈ slitPlane`**
(Λ-induced). -/
theorem analyticAt_freeEnergyComplex_of_slitPlane_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) {h₀ : ℂ}
    (hZ : IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h₀ β
        ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) h₀ :=
  IsingModel.analyticAt_freeEnergyComplex_of_slitPlane_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hZ

/-- **ℤ^d `f_ℂ` `ContinuousOn` slitPlane-locus in `h`** (Λ-induced). -/
theorem freeEnergyComplex_continuousOn_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    ContinuousOn (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_continuousOn_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `f_ℂ` `DifferentiableOn` slitPlane-locus in `h`**
(Λ-induced). -/
theorem freeEnergyComplex_differentiableOn_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    DifferentiableOn ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_differentiableOn_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `f_ℂ` `AnalyticOn` slitPlane-locus in `h`** (Λ-induced). -/
theorem freeEnergyComplex_analyticOn_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOn ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_analyticOn_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `f_ℂ` `AnalyticOnNhd` joint slitPlane-locus** (Λ-induced). -/
theorem freeEnergyComplex_analyticOnNhd_slitPlane_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_analyticOnNhd_slitPlane_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d joint slitPlane-locus is open** (Λ-induced). -/
theorem isOpen_freeEnergy_analyticity_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    IsOpen {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_freeEnergy_analyticity_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `f_ℂ` `ContinuousOn` joint slitPlane-locus** (Λ-induced). -/
theorem freeEnergyComplex_continuousOn_slitPlane_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    ContinuousOn
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_continuousOn_slitPlane_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `f_ℂ` `DifferentiableOn` joint slitPlane-locus** (Λ-induced). -/
theorem freeEnergyComplex_differentiableOn_slitPlane_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    DifferentiableOn ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_differentiableOn_slitPlane_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d log-branch at real basepoint** (Λ-induced):
`Complex.log (Z_ℂ ↑p) = ↑(Real.log (Z_ℝ p))` at real parameters. -/
theorem logZ_branch_at_real_basepoint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    Complex.log (IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = ((Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p)) : ℂ) :=
  IsingModel.logZ_branch_at_real_basepoint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `exp(|Λ| · f_ℂ) = Z_ℝ` at real parameters** (Λ-induced,
nonempty `Λ`). -/
theorem exp_card_mul_freeEnergyComplex_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    (p : IsingParams ℝ) :
    Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) *
        IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℂ) :=
  IsingModel.exp_card_mul_freeEnergyComplex_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d log-branch `AnalyticOnNhd ball`** (Λ-induced, ferromagnetic). -/
theorem exists_logZ_analyticOnNhd_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_logZ_analyticOnNhd_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d log-branch `ContinuousOn ball`** (Λ-induced, ferromagnetic). -/
theorem continuous_logZ_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, ContinuousOn g (Metric.ball h₀ r) ∧
        ∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ) :=
  IsingModel.continuous_logZ_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d log-branch `DifferentiableOn ball`** (Λ-induced,
ferromagnetic). -/
theorem exists_logZ_differentiableOn_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball h₀ r) ∧
        ∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_logZ_differentiableOn_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-! #### Lee-Yang subdomain ⊆ slitPlane locus + real-slice inclusions +
function-restriction identities -/

/-- **ℤ^d `leeYangSubdomain ⊆ slitPlane_locus`** (Λ-induced,
ferromagnetic `β > 0`). -/
theorem leeYangSubdomain_subset_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _)))
      ⊆ {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane} :=
  IsingModel.leeYangSubdomain_subset_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `h ∈ leeYangSubdomain ⇒ Z_ℂ ∈ slitPlane`** (Λ-induced). -/
theorem mem_slitPlane_locus_of_mem_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane :=
  IsingModel.mem_slitPlane_locus_of_mem_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J hh

/-- **ℤ^d `logZ` slitPlane-locus is open** (Λ-induced). -/
theorem isOpen_logZ_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    IsOpen {h : ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_logZ_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d slitPlane-locus open in `(h, β)`** (Λ-induced). -/
theorem isOpen_slitPlane_locus_h_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℂ) :
    IsOpen {z : ℂ × ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J z.1 z.2
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_slitPlane_locus_h_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J

/-- **ℤ^d real `h₀` (cast) is in `slitPlane_locus`** (Λ-induced). -/
theorem real_coe_mem_slitPlane_locus_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    (h₀ : ℂ) ∈ {h : ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ)
        ∈ Complex.slitPlane} :=
  IsingModel.real_coe_mem_slitPlane_locus_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d real-axis (cast) ⊆ `slitPlane_locus`** (Λ-induced). -/
theorem real_axis_in_slitPlane_locus_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    ((fun h₀ : ℝ => (h₀ : ℂ)) '' Set.univ) ⊆
      {h : ℂ | IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ)
          ∈ Complex.slitPlane} :=
  IsingModel.real_axis_in_slitPlane_locus_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d real parameter point in joint slitPlane-locus** (Λ-induced). -/
theorem real_params_in_analyticity_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) ∈
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        z.1 z.2.1 z.2.2 ∈ Complex.slitPlane} :=
  IsingModel.real_params_in_analyticity_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d real parameter point `AnalyticAt` jointly** (Λ-induced). -/
theorem real_params_analyticAt_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    AnalyticAt ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  IsingModel.real_params_analyticAt_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d image of real-parameter cast ⊆ joint slitPlane-locus**
(Λ-induced). -/
theorem real_params_image_subset_analyticity_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    (fun p : IsingParams ℝ => ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)))
        '' Set.univ ⊆
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        z.1 z.2.1 z.2.2 ∈ Complex.slitPlane} :=
  IsingModel.real_params_image_subset_analyticity_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `f_ℂ` `AnalyticAt` at real `h₀` (cast)** (Λ-induced). -/
theorem freeEnergyComplex_analyticAt_h_real_coe_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    AnalyticAt ℂ
      (fun h => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_analyticAt_h_real_coe
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` `DifferentiableAt` at real `h₀` (cast)** (Λ-induced). -/
theorem freeEnergyComplex_differentiableAt_h_real_coe_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    DifferentiableAt ℂ
      (fun h => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_differentiableAt_h_real_coe
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` `ContinuousAt` at real `h₀` (cast)** (Λ-induced). -/
theorem freeEnergyComplex_continuousAt_h_real_coe_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    ContinuousAt
      (fun h => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_continuousAt_h_real_coe
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` restriction to real axis equals `f_ℝ`** (Λ-induced). -/
theorem freeEnergyComplex_restrict_real_axis_eq_freeEnergy_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    (fun h : ℝ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) (h : ℂ) (β : ℂ))
      = fun h : ℝ => ((IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, h, β⟩ : ℝ) : ℂ) :=
  IsingModel.freeEnergyComplex_restrict_real_axis_eq_freeEnergy
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Z_ℂ` restriction to real axis equals `↑Z_ℝ`** (Λ-induced). -/
theorem partitionFunctionComplex_restrict_real_axis_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    (fun h : ℝ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) (h : ℂ) (β : ℂ))
      = fun h : ℝ => ((IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, h, β⟩ : ℝ) : ℂ) :=
  IsingModel.partitionFunctionComplex_restrict_real_axis_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Z_ℂ` restriction to `IsingParams ℝ`-image = `↑Z_ℝ`**
(Λ-induced). -/
theorem partitionFunctionComplex_restrict_joint_real_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    (fun p : IsingParams ℝ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = fun p : IsingParams ℝ => ((IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ) :=
  IsingModel.partitionFunctionComplex_restrict_joint_real_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `f_ℂ` restriction to `IsingParams ℝ`-image = `↑f_ℝ`**
(Λ-induced). -/
theorem freeEnergyComplex_restrict_joint_real_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    (fun p : IsingParams ℝ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = fun p : IsingParams ℝ => ((IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ) :=
  IsingModel.freeEnergyComplex_restrict_joint_real_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-! #### Packaged analyticBranch form + Differentiable ℂ entire +
joint real continuity -/

/-- **ℤ^d GJ §4.6 Thm 4.6.2 finite-volume (symbolic branch-locus form)**
(Λ-induced, nonempty `Λ`, ferromagnetic). -/
theorem leeYangDomain_subset_branch_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ h ∈ IsingModel.leeYangDomain,
      ∃ f : ℂ → ℂ, AnalyticAt ℂ f h ∧
        Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ) :=
  IsingModel.leeYangDomain_subset_branch_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d `freeEnergyComplex` has analytic branch over leeYangDomain**
(Λ-induced, nonempty `Λ`, ferromagnetic): headline form. -/
theorem freeEnergyComplex_exists_analyticBranch_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ h ∈ IsingModel.leeYangDomain, ∃ f : ℂ → ℂ, AnalyticAt ℂ f h ∧
        Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ) :=
  IsingModel.freeEnergyComplex_exists_analyticBranch
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d `freeEnergyComplex` analyticBranch (strong form)**
(Λ-induced, nonempty `Λ`, ferromagnetic): additionally identifies the
branch value at the basepoint with the principal-branch
`freeEnergyComplex`. -/
theorem freeEnergyComplex_exists_analyticBranch_strong_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ h ∈ IsingModel.leeYangDomain, ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h
      ∧ Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ)
      ∧ f h = IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h (β : ℂ) :=
  IsingModel.freeEnergyComplex_exists_analyticBranch_strong
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d GJ §4.6 Thm 4.6.2 finite-volume (`analyticBranch` packaged form
over `leeYangDomain`)** (Λ-induced, nonempty `Λ`, ferromagnetic). -/
theorem analyticBranch_freeEnergyComplex_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ f : ℂ → ℂ,
          AnalyticAt ℂ f h₀
        ∧ Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h₀)
            = IsingModel.partitionFunctionComplex
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (J : ℂ) h₀ (β : ℂ)
        ∧ f h₀ = IsingModel.freeEnergyComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h₀ (β : ℂ) :=
  IsingModel.analyticBranch_freeEnergyComplex_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d packaged `AnalyticOnNhd` on Lee-Yang subdomain** (Λ-induced,
ferromagnetic `β > 0`). -/
theorem freeEnergyComplex_analyticOnNhd_of_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOnNhd ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_analyticOnNhd_of_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `ContinuousOn` joint slitPlane locus (packaged alias)**
(Λ-induced). -/
theorem continuous_freeEnergyComplex_on_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    ContinuousOn
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.continuous_freeEnergyComplex_on_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d joint `ContinuousAt` at real parameters** (Λ-induced). -/
theorem continuousAt_freeEnergyComplex_at_real_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ContinuousAt
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  IsingModel.continuousAt_freeEnergyComplex_at_real_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d joint `DifferentiableAt` at real parameters** (Λ-induced). -/
theorem differentiableAt_freeEnergyComplex_at_real_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    DifferentiableAt ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  IsingModel.differentiableAt_freeEnergyComplex_at_real_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Z_ℂ` entire in `h` (Differentiable ℂ)** (Λ-induced). -/
theorem partitionFunctionComplex_entire_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    Differentiable ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.partitionFunctionComplex_entire_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Z_ℂ` entire in `J` (Differentiable ℂ)** (Λ-induced). -/
theorem partitionFunctionComplex_entire_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℂ) :
    Differentiable ℂ (fun J => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.partitionFunctionComplex_entire_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d `Z_ℂ` entire in `β` (Differentiable ℂ)** (Λ-induced). -/
theorem partitionFunctionComplex_entire_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℂ) :
    Differentiable ℂ (fun β => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.partitionFunctionComplex_entire_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h

/-- **ℤ^d `Z_ℂ` jointly entire on ℂ³ (Differentiable ℂ)**
(Λ-induced). -/
theorem partitionFunctionComplex_entire_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Differentiable ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) :=
  IsingModel.partitionFunctionComplex_entire_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `‖Z_ℂ‖ = Z_ℝ` at real parameters (alias)** (Λ-induced). -/
theorem norm_partitionFunctionComplex_eq_partitionFunction_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)‖
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.norm_partitionFunctionComplex_eq_partitionFunction_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-! #### Friedli-Velenik / Lee-Yang polynomial helpers

Direct ℤ^d forwarders for the remaining Lee-Yang polynomial nonvanishing,
Friedli-Velenik factorisation helpers, `Re(exp(-β·H)) > 0` on the
subdomain, logarithmic branch intermediate step, and non-vanishing
restatement from `IsingModel/ComplexAnalyticity.lean`. Closes ℤ^d
coverage of that module. -/

/-- **ℤ^d Lee-Yang polynomial evaluation is non-zero on the Lee-Yang
domain** (Λ-induced). -/
theorem isingEdgePoly_eval_leeYangFugacityVec_ne_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    {β : ℝ} (hβ : 0 < β) {h : ℂ} (hh : h ∈ IsingModel.leeYangDomain) :
    (IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)).eval
        (IsingModel.leeYangFugacityVec (β : ℂ) h) ≠ 0 :=
  IsingModel.isingEdgePoly_eval_leeYangFugacityVec_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ht₀ ht₁ hβ hh

/-- **ℤ^d Lee-Yang normalisation · polynomial is non-zero on the
Lee-Yang domain** (Λ-induced): the Friedli-Velenik RHS factor is
non-zero. -/
theorem leeYangNormalization_mul_isingEdgePoly_eval_ne_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (J : ℂ) {β : ℝ} (hβ : 0 < β) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangDomain)
    (edgeCount siteCount : ℕ) :
    IsingModel.leeYangNormalization (β : ℂ) J h edgeCount siteCount
        * (IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)).eval
            (IsingModel.leeYangFugacityVec (β : ℂ) h) ≠ 0 :=
  IsingModel.leeYangNormalization_mul_isingEdgePoly_eval_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
    ht₀ ht₁ J hβ hh edgeCount siteCount

/-- **ℤ^d edge-term product factorisation** (Λ-induced):
`∏_e exp(β·J·edgeSpin σ e) = exp(β·J·|E|) · ∏_e edgeWeight … (configToFinset σ)`.
Helper for the Friedli-Velenik factorisation of Z_ℂ. -/
theorem prod_exp_beta_J_edgeSpin_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    ∏ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
        Complex.exp ((β : ℂ) * (J : ℂ) * IsingModel.edgeSpinComplex σ e)
      = Complex.exp ((β : ℂ) * (J : ℂ) *
            ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              : ℂ))
        * ∏ e ∈
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
              IsingModel.edgeWeight (Quot.out e).1 (Quot.out e).2
                (Real.exp (-2 * β * J)) (IsingModel.configToFinset σ) :=
  IsingModel.prod_exp_beta_J_edgeSpin_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J σ

/-- **ℤ^d `isingEdgePoly` evaluated at `configToFinset σ`** (Λ-induced):
product over edges of `edgeWeight`. -/
theorem isingEdgePoly_apply_configToFinset_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (t : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)
        (IsingModel.configToFinset σ)
      = ∏ e ∈
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
            IsingModel.edgeWeight (Quot.out e).1 (Quot.out e).2 t
              (IsingModel.configToFinset σ) :=
  IsingModel.isingEdgePoly_apply_configToFinset
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t σ

/-- **ℤ^d per-configuration Friedli-Velenik factorisation** (Λ-induced):
`exp(-β · H(σ)) = leeYangNormalization · isingEdgePoly · ∏ fugacityVec`. -/
theorem exp_neg_beta_hamiltonian_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) (h : ℂ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    Complex.exp (-(β : ℂ) * IsingModel.hamiltonianComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h σ)
      = IsingModel.leeYangNormalization (β : ℂ) (J : ℂ) h
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          (Fintype.card (↑Λ : Type _))
        * IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (Real.exp (-2 * β * J)))
            (IsingModel.configToFinset σ)
        * ∏ i ∈ IsingModel.configToFinset σ,
            IsingModel.leeYangFugacityVec (β : ℂ) h i :=
  IsingModel.exp_neg_beta_hamiltonian_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h σ

/-- **ℤ^d `Re(exp(-β · H(σ))) > 0` on Lee-Yang subdomain** (Λ-induced):
per-configuration positive-real-part. Helper for
`partitionFunctionComplex_re_pos_of_leeYangSubdomain`. -/
theorem exp_neg_beta_hamiltonian_re_pos_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card (↑Λ : Type _) : ℝ) < Real.pi / 2)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    0 < (Complex.exp (-(β : ℂ) * IsingModel.hamiltonianComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h σ)).re :=
  IsingModel.exp_neg_beta_hamiltonian_re_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J himπ σ

/-- **ℤ^d normalised local log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic). Intermediate between
`exists_logZ_branch_on_ball_of_leeYangDomain_latticeGraph` and
`exists_logZ_holomorphic_branch_on_ball_latticeGraph`. -/
theorem exists_normalised_logZ_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ}
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, g h₀ = Complex.log
        (IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h₀ (β : ℂ))
      ∧ ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
          (deriv (fun h'' => IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h'' (β : ℂ)) z
            / IsingModel.partitionFunctionComplex
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (J : ℂ) z (β : ℂ)) z :=
  IsingModel.exists_normalised_logZ_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hsub

/-- **ℤ^d `Z_ℂ ≠ 0 → Z_ℂ ∈ {z ≠ 0}`** (Λ-induced): non-vanishing
restatement (trivial but useful set-level restatement). -/
theorem partitionFunctionComplex_ne_zero_not_iff_slitPlane_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) (h : ℂ)
    (hne : IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β ≠ 0) :
    IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ ({z : ℂ | z ≠ 0}) :=
  IsingModel.partitionFunctionComplex_ne_zero_not_iff_slitPlane
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h hne

/-- **ℤ^d product-form for `isingEdgePoly` evaluated at `leeYangFugacityVec`**
(Λ-induced): expands `P_E(z(h))` over `Finset ι` subsets. -/
theorem isingEdgePoly_eval_leeYangFugacityVec_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (t : ℝ) (β h : ℂ) :
    (IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)).eval
        (IsingModel.leeYangFugacityVec β h)
      = ∑ X : Finset (↑Λ : Type _),
          ((IsingModel.graphToEdgeList
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t).map
              fun e => IsingModel.edgeWeight e.1 e.2.1 e.2.2 X).prod *
            ∏ _i ∈ X, IsingModel.leeYangFugacity β h :=
  IsingModel.isingEdgePoly_eval_leeYangFugacityVec_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t β h

end Ambient

end IsingModel
