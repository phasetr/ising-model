import IsingModel.Inequalities.GHS

/-!
# Phase transitions: pure and mixed phases

Formalization of concepts from Glimm–Jaffe, §5.1 (pp. 72–74).

## Main results

* `truncated2_le_one` — `0 ≤ ⟨σ_i; σ_j⟩ ≤ 1` for ferromagnetic parameters
* `mixed_phase_truncated2` — the algebraic core of the mixed-phase formula (5.1.5)

## References

* Glimm–Jaffe, *Quantum Physics*, §5.1, pp. 72–74
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Truncated 2-point function bounds

For ferromagnetic parameters, the truncated 2-point function satisfies
`0 ≤ ⟨σ_i; σ_j⟩ ≤ 1` (cf. eq. (5.1.3)).

The lower bound is GKS-II (`truncated2_nonneg` in `GHS.lean`).
The upper bound follows from `⟨σ^A⟩ ≤ 1` and `⟨σ_i⟩ ≥ 0`, `⟨σ_j⟩ ≥ 0`. -/

/-- For ferromagnetic parameters, the truncated 2-point function is at most 1:
`⟨σ_i; σ_j⟩ = ⟨σ_iσ_j⟩ - ⟨σ_i⟩⟨σ_j⟩ ≤ ⟨σ_iσ_j⟩ ≤ 1`. -/
theorem truncated2_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : ι) :
    truncated2 G p i j ≤ 1 := by
  unfold truncated2
  have h1 : correlation G p {i, j} ≤ 1 :=
    le_trans (le_abs_self _) (abs_correlation_le_one G p {i, j})
  have h2 : 0 ≤ correlation G p {i} := gks_first G p hf {i}
  have h3 : 0 ≤ correlation G p {j} := gks_first G p hf {j}
  linarith [mul_nonneg h2 h3]

/-! ## Mixed phase formula (eq. 5.1.5)

For a convex combination `dμ = α dμ₊ + (1-α) dμ₋` of two pure phases
with magnetizations `⟨σ_i⟩₊ = M` and `⟨σ_i⟩₋ = -M`, the mixed-state
magnetization is `⟨σ_i⟩ = M(2α - 1)`.

If the pure phases satisfy the cluster property
`⟨σ_iσ_j⟩₊ → M²` and `⟨σ_iσ_j⟩₋ → M²` as `|i-j| → ∞`,
then `⟨σ_iσ_j⟩ → α M² + (1-α) M² = M²`, so the asymptotic
truncated 2-point function is

`⟨σ_iσ_j⟩_T → M² - M²(2α-1)² = 4α(1-α)M²`.

This vanishes if and only if `α ∈ {0, 1}` (pure phase). -/

/-- **Eq. (5.1.5)** (Glimm–Jaffe, §5.1, p. 73).
The algebraic identity underlying the mixed-phase formula:
`M² - (M(2α-1))² = 4α(1-α)M²`. -/
theorem mixed_phase_truncated2 (M α : ℝ) :
    M ^ 2 - (M * (2 * α - 1)) ^ 2 = 4 * α * (1 - α) * M ^ 2 := by
  ring

/-- The mixed-phase truncated 2-point function vanishes iff the state is pure.
If `0 ≤ α ≤ 1` and `M > 0`, then `4α(1-α)M² = 0` iff `α = 0` or `α = 1`. -/
theorem mixed_phase_pure_iff (M α : ℝ) (hM : M ≠ 0)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    4 * α * (1 - α) * M ^ 2 = 0 ↔ α = 0 ∨ α = 1 := by
  rw [mul_eq_zero, mul_eq_zero, mul_eq_zero]
  constructor
  · intro h
    rcases h with ((h | h) | h) | h
    · linarith
    · exact Or.inl h
    · exact Or.inr (by linarith)
    · exact absurd (pow_eq_zero_iff (n := 2) (by omega) |>.mp h) hM
  · intro h; rcases h with rfl | rfl <;> simp

/-! ## Mean field theory (§5.2)

The mean field picture (Glimm–Jaffe, §5.2) for the Ising model uses
the mean field free energy density

`φ(m) = -½Jzm² - hm + β⁻¹[(1+m)/2 · ln((1+m)/2) + (1-m)/2 · ln((1-m)/2)]`

and the mean field (self-consistency) equation `m = tanh(β(Jzm + h))`.

We formalize the key algebraic properties:
- Symmetry of the mean field free energy at `h = 0`
- The mean field equation `m = tanh(β(Jzm + h))` as the stationarity
  condition of `φ`
- `tanh` is odd: `tanh(-x) = -tanh(x)`, giving `m = 0` as a solution
  when `h = 0` -/

/-- **Mean field free energy density** (Glimm–Jaffe, §5.2, eq. (5.2.3)).
For the Ising model with coordination number `z`, coupling `J`,
external field `h`, and inverse temperature `β`:
`φ(m) = -½Jzm² - hm + β⁻¹ · entropy(m)`
where `entropy(m) = (1+m)/2 · ln((1+m)/2) + (1-m)/2 · ln((1-m)/2)`.

Here we define the interaction part only (without the entropy term),
as the entropy requires `m ∈ (-1, 1)` and logarithms. -/
noncomputable def meanFieldEnergy (J : ℝ) (z : ℕ) (h : ℝ) (m : ℝ) : ℝ :=
  -(1/2) * J * z * m ^ 2 - h * m

/-- The mean field interaction energy is symmetric in `m` when `h = 0`:
`φ(-m) = φ(m)`. -/
theorem meanFieldEnergy_neg (J : ℝ) (z : ℕ) (m : ℝ) :
    meanFieldEnergy J z 0 (-m) = meanFieldEnergy J z 0 m := by
  unfold meanFieldEnergy; ring

/-- The mean field equation `m = tanh(β(Jzm + h))` always has the
trivial solution `m = 0` when `h = 0`, since `tanh(0) = 0`. -/
theorem meanField_zero_solution (β J : ℝ) (z : ℕ) :
    Real.tanh (β * (J * z * 0 + 0)) = 0 := by
  simp [Real.tanh_zero]

/-- `tanh` is an odd function: `tanh(-x) = -tanh(x)`.
This reflects the spin-flip symmetry of the mean field equation at `h = 0`:
if `m*` is a solution, so is `-m*`. -/
theorem tanh_odd (x : ℝ) : Real.tanh (-x) = -Real.tanh x := by
  simp [Real.tanh_neg]

/-! ## Symmetry breaking (§5.3)

Glimm–Jaffe §5.3 discusses symmetry breaking in the context of phase
transitions. The key formalizable content for finite volume:

1. **Z₂ symmetry at h = 0**: already proved as `correlation_odd_vanish`
   in `GHS.lean` — for `h = 0`, odd correlations vanish.

2. **Magnetization as order parameter**: `M = ⟨σ_i⟩` (eq. 5.3.5).

3. **Susceptibility**: `χ = Σ_j ⟨σ_i; σ_j⟩ ≥ 0` (finite-volume sum).
   Non-negativity follows from `truncated2_nonneg`.

4. **Concavity of M(h)**: `d²M/dh² ≤ 0` for `h ≥ 0` follows from
   GHS inequality (Cor. 4.3.4). This is stated conceptually.

References: Glimm–Jaffe, §5.3, pp. 77–80, esp. p. 80. -/

/-- **Magnetization** (order parameter, eq. (5.3.5)):
`M(i) = ⟨σ_i⟩ = correlation G p {i}`. -/
noncomputable def magnetization (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) : ℝ :=
  correlation G p {i}

/-- **Susceptibility** (per site `i`):
`χ(i) = Σ_j ⟨σ_i; σ_j⟩ = Σ_j truncated2(i, j)`.

The susceptibility measures the response of the magnetization to the
external field. It equals `dM/dh` in the thermodynamic limit. -/
noncomputable def susceptibility (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) : ℝ :=
  ∑ j : ι, truncated2 G p i j

/-- The susceptibility is non-negative for ferromagnetic parameters.
Follows from `truncated2_nonneg`: each term `⟨σ_i; σ_j⟩ ≥ 0`. -/
theorem susceptibility_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ι) :
    0 ≤ susceptibility G p i := by
  unfold susceptibility
  exact Finset.sum_nonneg (fun j _ => truncated2_nonneg G p hf i j)

/-- The magnetization vanishes at `h = 0` (Z₂ symmetry, finite volume).
This is the finite-volume counterpart of the statement that the Z₂
symmetry is unbroken in finite volume. Symmetry breaking occurs only
in the infinite volume limit. -/
theorem magnetization_zero_at_h_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    magnetization G ⟨J, 0, β⟩ i = 0 := by
  unfold magnetization
  exact correlation_odd_vanish G J β {i} ⟨0, by simp⟩

/-! ## Free energy convexity and phase transitions (§16.1)

Glimm–Jaffe §16.1 (pp. 280–284) discusses the thermodynamic
characterization of phase transitions.

Key results for the Ising model:
1. `da/dh = ⟨σ_i⟩ = M` (magnetization) — eq. (16.1.8)
2. `d²a/dh² = Σ_j ⟨σ_i; σ_j⟩ = χ ≥ 0` (susceptibility) — eq. (16.1.9)
3. `a(h)` is convex in `h` since `χ ≥ 0`
4. A first-order phase transition occurs at `h₀` iff `M(h)` is
   discontinuous at `h₀`

For finite volume: `f(h)` is real-analytic (`freeEnergyH_analyticOn`),
so there are no phase transitions. Phase transitions appear only in the
infinite volume limit `Λ ↑ Zᵈ`.

The convexity `χ ≥ 0` is already proved as `susceptibility_nonneg`.
The monotonicity `M(h₁) ≤ M(h₂)` for `h₁ ≤ h₂` follows from
`correlation_monotone_h`. -/

/-- **Magnetization monotonicity** (Glimm–Jaffe, §16.1, p. 283).
The magnetization `M(i) = ⟨σ_i⟩` is monotone increasing in `h` on `[0, ∞)`
for ferromagnetic parameters. This is the lattice version of the fact
that `da/dh` is monotone (since `d²a/dh² = χ ≥ 0`). -/
theorem magnetization_monotone_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : ι) :
    MonotoneOn (fun h => magnetization G ⟨J, h, β⟩ i) (Set.Ici 0) := by
  intro h₁ hh₁ h₂ hh₂ hh
  unfold magnetization
  exact correlation_monotone_h G J hJ β hβ {i} hh₁ hh₂ hh

/-! ## Critical exponents (§17.7)

Glimm–Jaffe §17.7 (pp. 314–316) derives bounds on critical exponents
from correlation inequalities. For single-component φ⁴/Ising models:

- `η ≥ 0`: from `⟨σ_iσ_j⟩_T ≥ 0` (GKS-II, already `truncated2_nonneg`)
- `ζ ≥ 0`: from `U₄ ≤ 0` (Cor 4.3.3, already `cor_4_3_3` for h = 0)
- `γ ≥ 1`: from susceptibility bounds (χ monotone, requires more)
- `ν ≥ ½`: from correlation length bounds (requires spectral theory)

The Gaussian (mean field) values are: ν_cl = ½, γ_cl = 1, η_cl = 0, ζ_cl = 0.
Theorem 17.7.1 states each exponent ≥ its classical value. -/

/-- **η ≥ 0** (Glimm–Jaffe, Thm 17.7.1, lattice version).
The critical exponent `η` measures the anomalous dimension:
`⟨σ(0)σ(x)⟩ ~ |x|^{-(d-2+η)}` at the critical point.
The bound `η ≥ 0` follows from `⟨σ_iσ_j⟩_T ≥ 0` (GKS-II).

In finite volume, this is simply `truncated2_nonneg`. -/
theorem eta_nonneg_finite_vol (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : ι) :
    0 ≤ truncated2 G p i j :=
  truncated2_nonneg G p hf i j

/-! ## Correlation length (§17.5)

The correlation length (inverse mass) for the Ising model is defined by
`m(β)⁻¹ = -lim_{|x|→∞} ln⟨σ(0)σ(x)⟩ / |x|`.

For finite volume on a graph G, we define a proxy: the susceptibility
`χ = Σ_j ⟨σ_i; σ_j⟩` serves as a measure of the correlation range.
When `χ → ∞`, the correlation length diverges (critical point).

The monotonicity `χ(β₁) ≤ χ(β₂)` for `β₁ ≤ β₂` follows from:
- `truncated2_nonneg` (each term ≥ 0)
- monotonicity of each `truncated2` in β (from GKS-II + β-monotonicity)

The full correlation length definition and the continuity theorem
(Thm 17.5.1: m(σ) is continuous) require the infinite volume limit
and spectral theory of the transfer matrix. -/

end IsingModel
