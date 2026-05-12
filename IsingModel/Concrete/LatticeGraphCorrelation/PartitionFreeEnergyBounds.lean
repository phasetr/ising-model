import IsingModel.Concrete.LatticeGraphBED

/-!
# Concrete partition/free-energy lower and upper bound wrappers

Thin `ℤ^d` specializations of partition-function and free-energy bounds,
nonnegativity facts, and infinite-volume bridge statements.  These wrappers keep
downstream imports away from the legacy concrete correlation module when only
order-theoretic or bound facts are needed.
-/

namespace IsingModel

namespace Ambient

/-! ## Lambda-layer partition and free-energy bounds -/

/-- **ℤ^d partitionFunctionΛ ≥ 1** (ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_ge_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    1 ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_one_of_ferromagnetic (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d partitionFunctionΛ ≥ 2^|Λ|** (ferromagnetic, per-Λ). -/
theorem partitionFunctionΛ_latticeGraph_ge_two_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Λ.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_two_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d log partitionFunctionΛ ≥ |Λ|·log 2** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log 2
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d `log Z_Λ ≥ 0`** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    0 ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d `freeEnergyΛ = |↑Λ|⁻¹ · log Z_Λ`**. -/
theorem freeEnergyΛ_latticeGraph_eq_inv_card_mul_log
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = (Fintype.card (↑Λ : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  freeEnergyΛ_eq_inv_card_mul_log (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `freeEnergyΛ = (Λ.card)⁻¹ · log Z_Λ`** (Finset-card form). -/
theorem freeEnergyΛ_latticeGraph_eq_inv_Λcard_mul_log
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = (Λ.card : ℝ)⁻¹
        * Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  freeEnergyΛ_eq_inv_Λcard_mul_log (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `freeEnergyΛ ≥ 0`** (ferromagnetic, nonempty `Λ`). -/
theorem freeEnergyΛ_latticeGraph_nonneg_of_ferromagnetic
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_nonneg_of_ferromagnetic (IsingModel.latticeGraph d) hne p hf

/-- **ℤ^d partitionFunctionΛ ≥ (2 cosh βh)^|Λ|** (sharp, ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_ge_two_cosh_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (2 * Real.cosh (p.β * p.h)) ^ Λ.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_two_cosh_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d sharp log Z_Λ bound**: `|Λ|·log(2 cosh βh) ≤ log Z_Λ` (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two_cosh
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_cosh_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-! ## Along-exhaustion partition and free-energy bounds -/

/-- **ℤ^d `freeEnergyAlongExhaustion = |↑(Λ_n)|⁻¹ · log Z_n`** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_inv_card_mul_log
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_inv_card_mul_log (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d `freeEnergyAlongExhaustion = ((Λ.volume n).card)⁻¹ · log Z_n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_inv_Λcard_mul_log
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = ((Λ.volume n).card : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_inv_Λcard_mul_log
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d `freeEnergyAlongExhaustion ≥ 0`** per stage (ferromagnetic,
nonempty stage, any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_nonneg_of_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {n : ℕ}
    (hne : (Λ.volume n).Nonempty) :
    0 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf hne

/-- **ℤ^d `freeEnergyAlongExhaustion` as `log Z / card`** (any-Exhaustion):
alternate form of `freeEnergyAlongExhaustion_eq_inv_card_mul_log` using the
Fintype-card expression. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_log_div_card
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_log_div_card
    (IsingModel.latticeGraph d) Λ p n

/-! ## Moved: ℤ^d AlongExhaustion partition / log-partition bounds

The 8 ℤ^d `partitionFunctionAlongExhaustion_latticeGraph_*` and
`log_partitionFunctionAlongExhaustion_latticeGraph_*` ferromagnetic
bound wrappers (`ge_one`, `ge_one_general`, `ge_two_pow_card`,
`ge_two_cosh_pow_card`, `nonneg_general`, `nonneg`,
`ge_card_mul_log_two`, `ge_card_mul_log_two_cosh`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyBoundsAlongEx`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Infinite-volume free-energy bridges and BED bounds -/

/-- **ℤ^d freeEnergyInfinite from convergence** (any-Exhaustion): if
`freeEnergyAlongExhaustion` tendsto `L`, then `freeEnergyInfinite = L`. -/
theorem freeEnergyInfinite_latticeGraph_eq_of_tendsto
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {L : ℝ}
    (h : Filter.Tendsto (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      Λ p) Filter.atTop (nhds L)) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p = L :=
  freeEnergyInfinite_eq_of_tendsto (IsingModel.latticeGraph d) Λ p h

/-- **ℤ^d freeEnergyInfinite of eventually constant sequence** (any-Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_of_eventually_const
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion
      (IsingModel.latticeGraph d) Λ p n = c) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p = c :=
  freeEnergyInfinite_of_eventually_const (IsingModel.latticeGraph d) Λ p h

/-- **ℤ^d freeEnergyInfinite from convergence**: if
`freeEnergyAlongExhaustion` tendsto `L`, then `freeEnergyInfinite = L`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_of_tendsto
    (d : ℕ) (p : IsingParams ℝ) {L : ℝ}
    (h : Filter.Tendsto (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p) Filter.atTop (nhds L)) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p = L :=
  freeEnergyInfinite_eq_of_tendsto (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p h

/-- **ℤ^d freeEnergyInfinite of eventually constant sequence**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_of_eventually_const
    (d : ℕ) (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion
      (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p n = c) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p = c :=
  freeEnergyInfinite_of_eventually_const (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p h

/-- **ℤ^d freeEnergyInfinite uniform upper bound via caller-supplied BED**
(any-Exhaustion): `freeEnergyInfinite ≤ log 2 + |β|·(|J|·c + |h|)`. -/
theorem freeEnergyInfinite_latticeGraph_le_uniform_upper_bound
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p
      ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) :=
  freeEnergyInfinite_le_uniform_upper_bound
    (IsingModel.latticeGraph d) Λ p hf hc

/-- **ℤ^d freeEnergyInfinite uniform upper bound via BED**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_le_uniform_upper_bound
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p
      ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  refine freeEnergyInfinite_le_uniform_upper_bound (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d BddAbove range of `freeEnergyAlongExhaustion`** (any-Exhaustion,
caller-supplied BED). -/
theorem BddAbove_freeEnergyAlongExhaustion_latticeGraph_range
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      Λ p)) :=
  BddAbove_freeEnergyAlongExhaustion_range (IsingModel.latticeGraph d) Λ p hBED

/-- **ℤ^d BddAbove range of `freeEnergyAlongExhaustion`**: via BED c=d. -/
theorem BddAbove_freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion
    (d : ℕ) (p : IsingParams ℝ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p)) :=
  BddAbove_freeEnergyAlongExhaustion_range (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p
    (boundedEdgeDensity_latticeGraph_cubicExhaustion d)

/-- **ℤ^d per-stage freeEnergyAlongExhaustion upper bound** using BED c = d. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_le_uniform_upper_bound
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  refine freeEnergyAlongExhaustion_le_uniform_upper_bound
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p
    (c := (d : ℝ)) ?_ n hne
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **Per-stage lower bound on ℤ^d**: `log 2 ≤ freeEnergyAlongExhaustion` for
ferromagnetic + nonempty stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_ge_log_two
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    Real.log 2 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_log_two (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n hne

/-- **Sharp per-stage lower bound on ℤ^d**:
`log(2 cosh(βh)) ≤ freeEnergyAlongExhaustion`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_ge_log_two_cosh
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_log_two_cosh (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n hne

/-- **ℤ^d per-stage `log 2 ≤ f_n`** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_log_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log 2 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_ge_log_two (IsingModel.latticeGraph d) Λ
    hJ hh hβ n hne

/-- **ℤ^d per-stage `log(2 cosh(βh)) ≤ f_n`** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_log_two_cosh
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_ge_log_two_cosh (IsingModel.latticeGraph d) Λ
    hJ hh hβ n hne

/-- **ℤ^d per-stage `0 ≤ f_n`** (ferromagnetic, nonempty stage, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {n : ℕ}
    (hne : (Λ.volume n).Nonempty) :
    0 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf hne

end Ambient

end IsingModel
