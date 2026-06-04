import IsingModel.Inequalities.MonotonicityExtremal

/-!
# Spin-flip bridge between the `−` and `+` boundary states (FV Theorem 3.17)

The global spin-flip involution `σ ↦ σ.flip` (`Config.flip`) maps the `−` boundary
state to the `+` boundary state with the magnetic field reflected `h ↦ −h`.  This
lets the entire `−`-state theory be obtained from the `+`-state theory for free,
rather than mirroring the cubic-box screening machinery.

The chain (inhomogeneous couplings `J`, arbitrary field `h`):

* `interactionEnergyJ_flip` / `hamiltonianJ_neg_h_flip` /
  `boltzmannWeightJ_neg_h_flip` — the Hamiltonian and weight under `h ↦ −h` + flip.
* `agreesOff_minusConfig_flip_iff` — `σ` agrees with `−` off `Λ` iff `σ.flip`
  agrees with `+` off `Λ`.
* `boltzmannWeightBC_minus_eq_plus_neg_h_flip` — the per-configuration `−`/`+`
  weight identity.
* `partitionFunctionBC_minus_eq_plus_neg_h_flip` /
  `gibbsExpectationBC_minus_eq_plus_neg_h_flip` — the partition-function and
  expectation bridges: `⟨F⟩^−_Λ(h) = ⟨F ∘ flip⟩^+_Λ(−h)`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
§3.4 Theorem 3.17 and the global spin-flip symmetry.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **The inhomogeneous interaction energy is flip-invariant**: each edge spin
product is unchanged under the global spin flip (`edgeSpin_flip`). -/
theorem interactionEnergyJ_flip (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : Sym2 ι → ℝ) (σ : Config ι) :
    interactionEnergyJ G J σ.flip = interactionEnergyJ G J σ := by
  unfold interactionEnergyJ
  congr 1
  exact Finset.sum_congr rfl fun e _ => by rw [edgeSpin_flip]

omit [DecidableEq ι] in
/-- **The inhomogeneous Hamiltonian under `h ↦ −h` and spin flip**:
`H_G(σ; J, −h) = H_G(σ.flip; J, h)`.  The `J`-term is flip-invariant; the field
term `−(−h)·∑ s(σ_i) = h·∑ s(σ_i) = −h·∑ s(σ.flip_i)`. -/
theorem hamiltonianJ_neg_h_flip (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : Sym2 ι → ℝ) (h : ℝ) (σ : Config ι) :
    hamiltonianJ G J (-h) σ = hamiltonianJ G J h σ.flip := by
  unfold hamiltonianJ
  rw [interactionEnergyJ_flip]
  congr 1
  unfold externalFieldEnergy Config.flip
  simp only [Spin.sign_flip]
  rw [Finset.sum_neg_distrib]
  ring

omit [DecidableEq ι] in
/-- **The inhomogeneous Boltzmann weight under `h ↦ −h` and spin flip**. -/
theorem boltzmannWeightJ_neg_h_flip (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (σ : Config ι) :
    boltzmannWeightJ G β J (-h) σ = boltzmannWeightJ G β J h σ.flip := by
  unfold boltzmannWeightJ
  rw [hamiltonianJ_neg_h_flip]

omit [Fintype ι] [DecidableEq ι] in
/-- **The flip exchanges the `−` and `+` boundary conditions**: `σ` agrees with the
all-`−` configuration off `Λ` iff `σ.flip` agrees with the all-`+` configuration
off `Λ`. -/
theorem agreesOff_minusConfig_flip_iff (Λ : Finset ι) (σ : Config ι) :
    agreesOff Λ (minusConfig ι) σ ↔ agreesOff Λ (plusConfig ι) σ.flip := by
  constructor <;> intro hag i hi <;> have hi' := hag i hi
  · change (σ i).flip = Spin.up
    rw [show σ i = Spin.down from hi']; rfl
  · change σ i = Spin.down
    revert hi'; change (σ i).flip = Spin.up → σ i = Spin.down
    cases σ i <;> decide

omit [DecidableEq ι] in
/-- **Per-configuration `−`/`+` boundary weight identity**: the `−` boundary weight
at `(h, σ)` equals the `+` boundary weight at `(−h, σ.flip)`. -/
theorem boltzmannWeightBC_minus_eq_plus_neg_h_flip (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (σ : Config ι) :
    boltzmannWeightBC G β J h Λ (minusConfig ι) σ
      = boltzmannWeightBC G β J (-h) Λ (plusConfig ι) σ.flip := by
  classical
  unfold boltzmannWeightBC
  by_cases hag : agreesOff Λ (minusConfig ι) σ
  · rw [Set.indicator_of_mem hag,
      Set.indicator_of_mem ((agreesOff_minusConfig_flip_iff Λ σ).mp hag),
      boltzmannWeightJ_neg_h_flip, Config.flip_flip]
  · rw [Set.indicator_of_notMem hag,
      Set.indicator_of_notMem (fun hc => hag ((agreesOff_minusConfig_flip_iff Λ σ).mpr hc))]

/-- **`−`/`+` partition-function bridge**: `Z^−_Λ(h) = Z^+_Λ(−h)`. -/
theorem partitionFunctionBC_minus_eq_plus_neg_h_flip (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) :
    partitionFunctionBC G β J h Λ (minusConfig ι)
      = partitionFunctionBC G β J (-h) Λ (plusConfig ι) := by
  unfold partitionFunctionBC
  rw [← Equiv.sum_comp
    (⟨Config.flip, Config.flip, Config.flip_flip, Config.flip_flip⟩ : Equiv.Perm (Config ι))
    (fun σ => boltzmannWeightBC G β J (-h) Λ (plusConfig ι) σ)]
  exact Finset.sum_congr rfl fun σ _ => boltzmannWeightBC_minus_eq_plus_neg_h_flip G β J h Λ σ

/-- **`−`/`+` expectation bridge** (the global spin-flip symmetry, FV Thm 3.17):
the `−` boundary expectation of `F` at field `h` equals the `+` boundary
expectation of `F ∘ flip` at field `−h`,
`⟨F⟩^−_Λ(h) = ⟨F ∘ flip⟩^+_Λ(−h)`. -/
theorem gibbsExpectationBC_minus_eq_plus_neg_h_flip (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (F : Config ι → ℝ) :
    gibbsExpectationBC G β J h Λ (minusConfig ι) F
      = gibbsExpectationBC G β J (-h) Λ (plusConfig ι) (fun σ => F σ.flip) := by
  unfold gibbsExpectationBC
  rw [partitionFunctionBC_minus_eq_plus_neg_h_flip]
  congr 1
  rw [← Equiv.sum_comp
    (⟨Config.flip, Config.flip, Config.flip_flip, Config.flip_flip⟩ : Equiv.Perm (Config ι))
    (fun σ => F σ.flip * boltzmannWeightBC G β J (-h) Λ (plusConfig ι) σ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  change F σ * boltzmannWeightBC G β J h Λ (minusConfig ι) σ
      = F σ.flip.flip * boltzmannWeightBC G β J (-h) Λ (plusConfig ι) σ.flip
  rw [Config.flip_flip, boltzmannWeightBC_minus_eq_plus_neg_h_flip]

end IsingModel
