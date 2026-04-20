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

/-- **`|magnetization| ≤ 1`** for any parameters and any site `i`.
Direct from `abs_correlation_le_one` at `A = {i}`. -/
theorem abs_magnetization_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) :
    |magnetization G p i| ≤ 1 :=
  abs_correlation_le_one G p {i}

/-- **`magnetization ≤ 1`** unconditionally. Direct from
`correlation_le_one` at `A = {i}`. -/
theorem magnetization_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) :
    magnetization G p i ≤ 1 :=
  correlation_le_one G p {i}

/-- **`-1 ≤ magnetization`** unconditionally. Direct from
`neg_one_le_correlation` at `A = {i}`. -/
theorem neg_one_le_magnetization (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i : ι) :
    -1 ≤ magnetization G p i :=
  neg_one_le_correlation G p {i}

/-- **`0 ≤ magnetization`** for ferromagnetic `p`. Direct from
`gks_first` at `A = {i}` (GKS-I). -/
theorem magnetization_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ι) :
    0 ≤ magnetization G p i :=
  gks_first G p hf {i}

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

/-- **Susceptibility closed form at `J = 0`** (Finset-based): for any
ambient graph `G`, any `h, β`, and any site `i`,

`susceptibility G ⟨0, h, β⟩ i = tanh(β·h) · (1 − tanh(β·h))`.

Caveat: this is the repo-level `susceptibility` built from
`truncated2` which uses the Finset `{i, j}` — at `j = i` this
collapses to `{i}` and yields `⟨σ_i⟩ − ⟨σ_i⟩² = t − t²`, not the
physics `⟨σ_i σ_i⟩ − ⟨σ_i⟩² = 1 − ⟨σ_i⟩²` (which would use
`σ_i² = 1`). Accordingly this formula differs from the physics
response-function identity `dM/dh = β·(1 − t²)` at the diagonal.

Proof: `susceptibility i = ∑_j truncated2 i j`. For `j ≠ i`,
`truncated2_J_zero_of_ne` makes the summand 0. For `j = i`,
`{i, i} = {i}` as Finset, so the term reduces to
`correlation {i} − (correlation {i})² = t − t²` with
`t = tanh(β·h)` (via `correlation_J_zero`). Factor to `t · (1 − t)`.

Complements the trivial-slice sweep of PRs #207-#215, #218-#219.
Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1
(non-interacting `J = 0` slice); §5.1 pp. 76–77 (susceptibility). -/
theorem susceptibility_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i : ι) :
    susceptibility G (⟨0, h, β⟩ : IsingParams ℝ) i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h)) := by
  unfold susceptibility
  rw [Finset.sum_eq_single i]
  · -- Diagonal term at j = i: truncated2 i i = t - t^2
    unfold truncated2
    have hsingleton : ({i, i} : Finset ι) = {i} := by simp
    rw [hsingleton, correlation_J_zero, Finset.card_singleton, pow_one]
    ring
  · -- Off-diagonal: truncated2 i j = 0 for j ≠ i
    intro j _ hji
    exact truncated2_J_zero_of_ne G h β hji.symm
  · -- j ∉ univ is vacuous
    intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **Susceptibility vanishes at `β = 0`**: for any ambient graph
`G`, any `J, h`, and any site `i`, `susceptibility G ⟨J, h, 0⟩ i = 0`.

Proof: every summand in `∑_j truncated2 G ⟨J, h, 0⟩ i j` vanishes
by `truncated2_beta_zero` (PR #208). Companion to
`susceptibility_J_zero`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1
infinite-temperature slice; §5.1 pp. 76–77. -/
theorem susceptibility_beta_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i : ι) :
    susceptibility G (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 := by
  unfold susceptibility
  refine Finset.sum_eq_zero ?_
  intro j _
  exact truncated2_beta_zero G J h i j

/-- The magnetization vanishes at `h = 0` (Z₂ symmetry, finite volume).
This is the finite-volume counterpart of the statement that the Z₂
symmetry is unbroken in finite volume. Symmetry breaking occurs only
in the infinite volume limit. -/
theorem magnetization_zero_at_h_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    magnetization G ⟨J, 0, β⟩ i = 0 := by
  unfold magnetization
  exact correlation_odd_vanish G J β {i} ⟨0, by simp⟩

/-- The magnetization vanishes at `β = 0` (infinite temperature,
finite volume). At `β = 0` the Gibbs measure is uniform and spins
are independent with zero mean (`±1` symmetric distribution), so
every single-site expectation is `0`.

Specialization of `correlation_beta_zero_vanish_of_nonempty_A`
(Inequalities/NonnegCorrelations.lean) at the singleton `{i}`
(automatically nonempty). Finite-volume companion to
`magnetizationInfinite_beta_zero`. -/
theorem magnetization_beta_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i : ι) :
    magnetization G ⟨J, h, 0⟩ i = 0 := by
  unfold magnetization
  exact correlation_beta_zero_vanish_of_nonempty_A G J h {i} ⟨i, by simp⟩

/-- The magnetization at `J = 0` (non-interacting model) has the
closed form `M(i) = tanh(β·h)`.

At `J = 0` the Hamiltonian has no inter-site coupling and the sites
are independent; single-site expectation `⟨σ_i⟩` under an external
field `h` at inverse temperature `β` is the mean of a `±1`-valued
random variable with `P(+1) ∝ exp(βh)` and `P(-1) ∝ exp(-βh)`,
giving `tanh(βh)`.

Specialization of `correlation_J_zero`
(`⟨σ^A⟩ = tanh(βh)^|A|`) at the singleton `{i}`. Finite-volume
companion to `magnetizationInfinite_J_zero` (PR #218). Completes
the three trivial slices of `magnetization`:
`J = 0` (`tanh(βh)`), `β = 0` (`0`), `h = 0` (`0`).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1
(non-interacting `J = 0` slice); §5.1 pp. 76–77 (magnetization). -/
theorem magnetization_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i : ι) :
    magnetization G (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
  unfold magnetization
  rw [correlation_J_zero, Finset.card_singleton, pow_one]

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

/-- **Magnetization β-monotonicity**: for `J, h ≥ 0`, the magnetization
`Mᵢ = ⟨σᵢ⟩` is monotone increasing in `β` on `(0, ∞)`.
Direct specialization of `correlation_monotone_beta` at `A = {i}`. -/
theorem magnetization_monotone_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ι) :
    MonotoneOn (fun β : ℝ => magnetization G ⟨J, h, β⟩ i) (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  unfold magnetization
  exact correlation_monotone_beta G J hJ h hh {i} hβ₁ hβ₂ hβ

/-- **Magnetization β → ∞ convergence**: for `J, h ≥ 0`, the sequence
`n ↦ Mᵢ(J, h, n+1)` converges as `n → ∞`.
Direct specialization of `correlation_convergent_beta` at `A = {i}`. -/
theorem magnetization_convergent_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetization G ⟨J, h, (n + 1 : ℝ)⟩ i)
      Filter.atTop (nhds L) :=
  correlation_convergent_beta G J hJ h hh {i}

/-- **Magnetization h → ∞ convergence**: for `J ≥ 0`, `β > 0`, the sequence
`n ↦ Mᵢ(J, n, β)` converges as `n → ∞`.
Direct specialization of `correlation_convergent_h` at `A = {i}`. -/
theorem magnetization_convergent_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetization G ⟨J, (n : ℝ), β⟩ i)
      Filter.atTop (nhds L) :=
  correlation_convergent_h G J hJ β hβ {i}

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

/-! ## Lattice-growth convergence of §5 quantities

Named corollaries of `correlation_convergent_subgraph` (PR #64) for the
derived quantities of §5: truncated 2-point function, susceptibility,
and total magnetization.  These are all immediate consequences of the
correlation convergence combined with standard mathlib limit operations
(`Tendsto.sub`, `Tendsto.mul`, `tendsto_finset_sum`).

These results are the *existence* of the infinite-volume limits (in our
discretized fixed-finite-ambient subgraph setting); Glimm–Jaffe does not
name these particular convergence results as standalone theorems, though
the infinite-volume limits of the truncated function and susceptibility
are standard objects in §5.1 (p. 73), §5.3 (pp. 77–80).

Note on `magnetization_total_convergent_subgraph`: `Σᵢ⟨σᵢ⟩` is the
*extensive* total, not the per-site density. In the true thermodynamic
limit (infinite ambient lattice) the physically meaningful quantity is
`|Λ|⁻¹ Σᵢ⟨σᵢ⟩`. Since our ambient `|ι|` is fixed and finite, the two
differ only by a fixed multiplicative constant and convergence transfers
trivially between them. -/

-- Note: `magnetization_convergent_subgraph` already exists in
-- `InfiniteVolume.lean` (PR #64), stated on `correlation G p {i}`.
-- Since `magnetization G p i` is definitionally `correlation G p {i}`,
-- that theorem applies directly to the magnetization.

/-- The truncated 2-point function `⟨σᵢ;σⱼ⟩_{Gₙ}` converges along any
increasing subgraph sequence.

Proof: Each of `⟨σᵢσⱼ⟩_{Gₙ}`, `⟨σᵢ⟩_{Gₙ}`, `⟨σⱼ⟩_{Gₙ}` converges by
`correlation_convergent_subgraph`; apply `Tendsto.sub` and `Tendsto.mul`. -/
theorem truncated2_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => truncated2 (Gn n) p i j)
      Filter.atTop (nhds L) := by
  obtain ⟨Lij, hij⟩ := correlation_convergent_subgraph Gn hmono p hf {i, j}
  obtain ⟨Li, hi⟩ := correlation_convergent_subgraph Gn hmono p hf {i}
  obtain ⟨Lj, hj⟩ := correlation_convergent_subgraph Gn hmono p hf {j}
  refine ⟨Lij - Li * Lj, ?_⟩
  exact hij.sub (hi.mul hj)

/-- The susceptibility `χᵢ(Gₙ) = Σⱼ ⟨σᵢ;σⱼ⟩_{Gₙ}` converges along any
increasing subgraph sequence.

Proof: Finite sum of convergent sequences, via `tendsto_finset_sum`. -/
theorem susceptibility_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibility (Gn n) p i)
      Filter.atTop (nhds L) := by
  choose Lj hLj using fun j =>
    truncated2_convergent_subgraph Gn hmono p hf i j
  refine ⟨∑ j : ι, Lj j, ?_⟩
  unfold susceptibility
  exact tendsto_finset_sum _ (fun j _ => hLj j)

/-- The total magnetization `M_tot(Gₙ) = Σᵢ ⟨σᵢ⟩_{Gₙ}` converges along any
increasing subgraph sequence.

Proof: Finite sum of convergent sequences, via `tendsto_finset_sum`. -/
theorem magnetization_total_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => ∑ i : ι, magnetization (Gn n) p i)
      Filter.atTop (nhds L) := by
  choose Li hLi using fun i =>
    correlation_convergent_subgraph Gn hmono p hf {i}
  refine ⟨∑ i : ι, Li i, ?_⟩
  simp only [magnetization]
  exact tendsto_finset_sum _ (fun i _ => hLi i)

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

/-! ## Convergence matrix for §5 derived quantities

Named specializations of `correlation_convergent_*` (J/h/β) and
`Tendsto.sub`/`Tendsto.mul`/`tendsto_finset_sum` for the derived
quantities of §5: magnetization (J), truncated 2-point (J/h/β),
and susceptibility (J/h/β).  The lattice (subgraph) versions are
already above.  These complete the "convergence matrix" for the
physically meaningful §5 quantities. -/

/-- **Magnetization J → ∞ convergence**: for `h ≥ 0`, `β > 0`, the
sequence `n ↦ Mᵢ(n, h, β)` converges.  Specialization of
`correlation_convergent` at `A = {i}`. -/
theorem magnetization_convergent_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetization G ⟨(n : ℝ), h, β⟩ i)
      Filter.atTop (nhds L) :=
  correlation_convergent G h hh β hβ {i}

/-- **Truncated 2-point J → ∞ convergence**: for `h ≥ 0`, `β > 0`, the
sequence `n ↦ ⟨σᵢ;σⱼ⟩_{(n,h,β)}` converges.

Proof: Each of `⟨σᵢσⱼ⟩`, `⟨σᵢ⟩`, `⟨σⱼ⟩` converges by
`correlation_convergent`; apply `Tendsto.sub` and `Tendsto.mul`. -/
theorem truncated2_convergent_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i j : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => truncated2 G ⟨(n : ℝ), h, β⟩ i j)
      Filter.atTop (nhds L) := by
  obtain ⟨Lij, hij⟩ := correlation_convergent G h hh β hβ {i, j}
  obtain ⟨Li, hLi⟩ := correlation_convergent G h hh β hβ {i}
  obtain ⟨Lj, hLj⟩ := correlation_convergent G h hh β hβ {j}
  refine ⟨Lij - Li * Lj, ?_⟩
  exact hij.sub (hLi.mul hLj)

/-- **Truncated 2-point h → ∞ convergence**: for `J ≥ 0`, `β > 0`, the
sequence `n ↦ ⟨σᵢ;σⱼ⟩_{(J,n,β)}` converges. -/
theorem truncated2_convergent_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i j : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => truncated2 G ⟨J, (n : ℝ), β⟩ i j)
      Filter.atTop (nhds L) := by
  obtain ⟨Lij, hij⟩ := correlation_convergent_h G J hJ β hβ {i, j}
  obtain ⟨Li, hLi⟩ := correlation_convergent_h G J hJ β hβ {i}
  obtain ⟨Lj, hLj⟩ := correlation_convergent_h G J hJ β hβ {j}
  refine ⟨Lij - Li * Lj, ?_⟩
  exact hij.sub (hLi.mul hLj)

/-- **Truncated 2-point β → ∞ convergence**: for `J ≥ 0`, `h ≥ 0`, the
sequence `n ↦ ⟨σᵢ;σⱼ⟩_{(J,h,n+1)}` converges. -/
theorem truncated2_convergent_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i j : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => truncated2 G ⟨J, h, (n + 1 : ℝ)⟩ i j)
      Filter.atTop (nhds L) := by
  obtain ⟨Lij, hij⟩ := correlation_convergent_beta G J hJ h hh {i, j}
  obtain ⟨Li, hLi⟩ := correlation_convergent_beta G J hJ h hh {i}
  obtain ⟨Lj, hLj⟩ := correlation_convergent_beta G J hJ h hh {j}
  refine ⟨Lij - Li * Lj, ?_⟩
  exact hij.sub (hLi.mul hLj)

/-- **Susceptibility J → ∞ convergence**: for `h ≥ 0`, `β > 0`, the
sequence `n ↦ χᵢ(n, h, β)` converges.  Proof: finite sum of convergent
via `tendsto_finset_sum`. -/
theorem susceptibility_convergent_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibility G ⟨(n : ℝ), h, β⟩ i)
      Filter.atTop (nhds L) := by
  choose Lj hLj using fun j => truncated2_convergent_J G h hh β hβ i j
  refine ⟨∑ j : ι, Lj j, ?_⟩
  unfold susceptibility
  exact tendsto_finset_sum _ (fun j _ => hLj j)

/-- **Susceptibility h → ∞ convergence**: for `J ≥ 0`, `β > 0`, the
sequence `n ↦ χᵢ(J, n, β)` converges. -/
theorem susceptibility_convergent_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibility G ⟨J, (n : ℝ), β⟩ i)
      Filter.atTop (nhds L) := by
  choose Lj hLj using fun j => truncated2_convergent_h G J hJ β hβ i j
  refine ⟨∑ j : ι, Lj j, ?_⟩
  unfold susceptibility
  exact tendsto_finset_sum _ (fun j _ => hLj j)

/-- **Susceptibility β → ∞ convergence**: for `J ≥ 0`, `h ≥ 0`, the
sequence `n ↦ χᵢ(J, h, n+1)` converges. -/
theorem susceptibility_convergent_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibility G ⟨J, h, (n + 1 : ℝ)⟩ i)
      Filter.atTop (nhds L) := by
  choose Lj hLj using fun j => truncated2_convergent_beta G J hJ h hh i j
  refine ⟨∑ j : ι, Lj j, ?_⟩
  unfold susceptibility
  exact tendsto_finset_sum _ (fun j _ => hLj j)

end IsingModel
