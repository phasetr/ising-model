import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDecayLatticeDistance
import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDistanceDecay
import IsingModel.Inequalities.GHS.Truncated3Contraction
import IsingModel.FieldDerivative.Truncated2Antitone
import IsingModel.Conditioning.CorrelationRates.Ferromagnetic
import IsingModel.LatticeExpSum

/-!
# Finite-volume, field-uniform summable majorant for the ∂/∂h site-sum (GJ Thm 17.6.1)

Brick 2 toward the `h`-derivative of the connected two-point function on `ℤ^d`
(tracking issue #4413), the static analytic input behind Glimm--Jaffe
Theorem 17.6.1 (*Quantum Physics*, 2nd ed., p. 313).  The field derivative
is the site-sum `∂/∂h ⟨σ_i; σ_j⟩ = β · ∑_k U₃(i, j, k)`, where the
*off-diagonal* terms (`k ≠ i, j`) are Ursell three-point functions
`truncated3(i, j, k)`, but the two *diagonal* terms `k = i` and `k = j` are
**not** three-point functions: they equal `-2 · corr(m) · truncated2(i, j)`
(see `Truncated2Antitone.lean`).  This file only builds the summable majorant
for the off-diagonal part `∑_{k ≠ i, j} |truncated3(i, j, k)|`, independent of
both the field `h ≥ 0` and the finite volume `Λ`; the two diagonal terms are
handled separately by the downstream §17.6.1 assembly.  The majorant is built
by pure composition of existing pieces:

* **(2a)** a per-term exponential bound
  `truncated2 ⟨J,h,β⟩ i j ≤ exp(m) · exp(-m · d_{ℓ¹}(i,j))`,
  `m = simonLiebRate β J d`, *uniform in `h ≥ 0` and in `Λ`*.  This uses GHS
  field-antitonicity (`truncated2_antitoneOn_h_of_ne`) to reduce to `h = 0`,
  the `Z₂` singleton collapse `correlation_high_temp_h_zero_at_singleton`, and
  the volume-uniform `h = 0` decay
  `correlation_inducedLatticeGraph_le_pow_latticeDistance`, converted to
  exponential form via `betaJ_two_d_pow_eq_exp_neg_simonLiebRate_mul`.
* **(2b)** summability of the majorant term
  `∑_k exp(m) · exp(-m · d_{ℓ¹}(x,k)) < ∞` via `summable_exp_neg_dist`.
* **(2c)** the composed finite-box bound
  `∑_{k ≠ i,j} |truncated3(i,j,k)| ≤ M(i) + M(j)` with `M` a finite tsum
  independent of `Λ` and `h`, via brick 1 `abs_truncated3_le`, (2a), and
  `Finset.sum_le_tsum`.

This is a **static** pointwise-plus-summable bound: no infinite-volume object
appears (everything lives on the finite induced graph `inducedGraph`), and it
does **not** touch the equicontinuity / derivative-limit wall (a separate,
later brick).  The reachability of the box is carried as a `Preconnected`
hypothesis, matching the convention of `IsingModel/PeierlsInfinite.lean`; the
general-`d` cubic-box connectivity discharge is a separate assembly brick.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Theorem 17.6.1 (p. 313);
  §4.3, Cor. 4.3.4 (GHS inequality), Cor. 4.3.3 (GKS-II).
* Fernández--Fröhlich--Sokal, *Random Walks, Critical Phenomena, and
  Triviality* (1992), Ch 12 (Simon--Lieb decay).
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **(2a) Per-term field- and volume-uniform exponential bound** (GJ Thm 17.6.1,
p. 313): on the finite induced subgraph `inducedGraph (latticeGraph d) Λ`, for a
ferromagnetic field `⟨J, h, β⟩` with `h ≥ 0`, high temperature
`0 < β J · 2d ≤ 1`, and reachable distinct sites `i ≠ j`,
`⟨σ_i; σ_j⟩_{⟨J,h,β⟩} ≤ exp(m) · exp(-m · d_{ℓ¹}(i,j))` with
`m = simonLiebRate β J d`.

Both the prefactor `exp(m)` and the rate `m` are **independent of `h` and of
`Λ`**, which is the whole point of the majorant.  Proof: GHS field-antitonicity
(`truncated2_antitoneOn_h_of_ne`) reduces `h ≥ 0` to `h = 0`, where the
singletons vanish by `Z₂` symmetry (`correlation_high_temp_h_zero_at_singleton`)
so `⟨σ_i; σ_j⟩ = ⟨σ_iσ_j⟩`; the volume-uniform `h = 0` Simon--Lieb decay
(`correlation_inducedLatticeGraph_le_pow_latticeDistance`) gives
`≤ (β J·2d)^{d_{ℓ¹}(i,j)-1}`, rewritten in exponential form via
`betaJ_two_d_pow_eq_exp_neg_simonLiebRate_mul`. -/
theorem truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J h : ℝ} (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ))
    (hβJ2d_pos : 0 < β * J * (2 * (d : ℝ))) (hβJ2d_le : β * J * (2 * (d : ℝ)) ≤ 1)
    {i j : ↑Λ} (hij : i ≠ j)
    (hreach : (inducedGraph (IsingModel.latticeGraph d) Λ).Reachable i j) :
    truncated2 (inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β⟩ : IsingParams ℝ) i j
      ≤ Real.exp (simonLiebRate β J d)
        * Real.exp (-(simonLiebRate β J d)
            * (latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ) : ℝ)) := by
  have hf0 : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) :=
    ⟨hf.hJ, le_refl 0, hf.hβ⟩
  -- GHS field-antitonicity: `h ≥ 0 ⟹ τ₂(h) ≤ τ₂(0)`.
  have hanti := truncated2_antitoneOn_h_of_ne
    (inducedGraph (IsingModel.latticeGraph d) Λ) J hf.hJ β hf.hβ hij
  have h_le : truncated2 (inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β⟩ : IsingParams ℝ) i j
      ≤ truncated2 (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j :=
    hanti Set.self_mem_Ici (Set.mem_Ici.mpr hf.hh) hf.hh
  -- `Z₂` singleton collapse at `h = 0`: `τ₂(0) = ⟨σ_iσ_j⟩`.
  have h_collapse : truncated2 (inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j
      = correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} := by
    unfold truncated2
    rw [correlation_high_temp_h_zero_at_singleton
        (inducedGraph (IsingModel.latticeGraph d) Λ) J β i,
      correlation_high_temp_h_zero_at_singleton
        (inducedGraph (IsingModel.latticeGraph d) Λ) J β j]
    ring
  -- Positivity of the induced-graph distance from reachability of distinct sites.
  have hdist : 0 < (inducedGraph (IsingModel.latticeGraph d) Λ).dist i j := by
    rcases Nat.eq_zero_or_pos
      ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j) with h0 | hpos
    · rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable] at h0
      rcases h0 with h | h
      · exact absurd h hij
      · exact absurd hreach h
    · exact hpos
  -- Volume-uniform `h = 0` power decay.
  have hdecay := correlation_inducedLatticeGraph_le_pow_latticeDistance d Λ hf0 hβJ2d_le hdist
  -- `latticeDistance ≥ 1` for distinct sites (needed for the `Nat.cast_sub`).
  have hN1 : 1 ≤ latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ) := by
    have hne : (i : Fin d → ℤ) ≠ (j : Fin d → ℤ) := fun h => hij (Subtype.ext h)
    exact Nat.one_le_iff_ne_zero.mpr
      (fun h0 => hne ((latticeDistance_eq_zero_iff d _ _).mp h0))
  -- pow → exp, with the arc identity `(βJ2d)^{N-1} = exp(m)·exp(-m·N)`.
  have hpow := betaJ_two_d_pow_eq_exp_neg_simonLiebRate_mul hβJ2d_pos
    (latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ) - 1)
  have hcast : ((latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ) - 1 : ℕ) : ℝ)
      = (latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ) : ℝ) - 1 := by
    rw [Nat.cast_sub hN1]; simp
  have harc : Real.exp (-(simonLiebRate β J d)
        * ((latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ) - 1 : ℕ) : ℝ))
      = Real.exp (simonLiebRate β J d)
        * Real.exp (-(simonLiebRate β J d)
            * (latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ) : ℝ)) := by
    rw [hcast, ← Real.exp_add]
    congr 1
    ring
  calc truncated2 (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j
      ≤ correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} := h_collapse ▸ h_le
    _ ≤ (β * J * (2 * (d : ℝ)))
          ^ (latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ) - 1) := hdecay
    _ = Real.exp (-(simonLiebRate β J d)
          * ((latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ) - 1 : ℕ) : ℝ)) := hpow
    _ = Real.exp (simonLiebRate β J d)
          * Real.exp (-(simonLiebRate β J d)
              * (latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ) : ℝ)) := harc

/-- **(2b) Summability of the majorant term** (GJ Thm 17.6.1 prerequisite): for
a positive Simon--Lieb rate `m = simonLiebRate β J d`, the lattice function
`k ↦ exp(m) · exp(-m · d_{ℓ¹}(x,k))` is summable over `ℤ^d`.  Its total mass
`M(x) = ∑_k exp(m) · exp(-m · d_{ℓ¹}(x,k))` is the finite, `Λ`- and
`h`-independent majorant consumed by (2c).  Direct `.mul_left` of the discrete
exponential summability `summable_exp_neg_dist`. -/
theorem summable_truncated2FiniteVolumeMajorant
    {d : ℕ} {β J : ℝ} (hm : 0 < simonLiebRate β J d) (x : Fin d → ℤ) :
    Summable (fun k : Fin d → ℤ =>
      Real.exp (simonLiebRate β J d)
        * Real.exp (-(simonLiebRate β J d) * (latticeDistance d x k : ℝ))) :=
  (summable_exp_neg_dist hm d x).mul_left (Real.exp (simonLiebRate β J d))

/-- **Finite subtype site-sum bounded by the majorant tsum**: for a positive
Simon--Lieb rate and any finset `S` of box sites, the finite sum of the
majorant term over `S` (indexed through the inclusion `↑Λ ↪ ℤ^d`) is bounded by
the full-lattice tsum `M(a)`.  The inclusion `Subtype.val` is injective, so the
sum reindexes to a subset sum of the lattice tsum; each term is non-negative and
the family is summable by `summable_truncated2FiniteVolumeMajorant`, whence
`Finset.sum_le_tsum` applies. -/
private lemma sum_majorant_subtype_le_tsum
    {d : ℕ} (Λ : Finset (Fin d → ℤ)) {β J : ℝ} (hm : 0 < simonLiebRate β J d)
    (a : Fin d → ℤ) (S : Finset ↑Λ) :
    ∑ k ∈ S, Real.exp (simonLiebRate β J d)
        * Real.exp (-(simonLiebRate β J d)
            * (latticeDistance d a (k : Fin d → ℤ) : ℝ))
      ≤ ∑' x : Fin d → ℤ, Real.exp (simonLiebRate β J d)
          * Real.exp (-(simonLiebRate β J d) * (latticeDistance d a x : ℝ)) := by
  have hInj : Set.InjOn (Subtype.val : ↑Λ → (Fin d → ℤ)) ↑S :=
    fun x _ y _ h => Subtype.ext h
  have himg : ∑ x ∈ S.image (Subtype.val : ↑Λ → (Fin d → ℤ)),
        Real.exp (simonLiebRate β J d)
          * Real.exp (-(simonLiebRate β J d) * (latticeDistance d a x : ℝ))
      = ∑ k ∈ S, Real.exp (simonLiebRate β J d)
          * Real.exp (-(simonLiebRate β J d)
              * (latticeDistance d a (k : Fin d → ℤ) : ℝ)) :=
    Finset.sum_image hInj
  rw [← himg]
  exact Summable.sum_le_tsum _ (fun x _ => by positivity)
    (summable_truncated2FiniteVolumeMajorant hm a)

/-- **(2c) Composed finite-box, field- and volume-uniform majorant** (GJ
Thm 17.6.1, p. 313): on a `Preconnected` finite induced subgraph
`inducedGraph (latticeGraph d) Λ`, for a ferromagnetic field `⟨J, h, β⟩` with
`h ≥ 0`, strict high temperature `0 < β J · 2d < 1`, and distinct sites
`i ≠ j`, the ∂/∂h site-sum of Ursell three-point functions is bounded by a
finite tsum `M(i) + M(j)` that is **independent of `Λ` and of `h`**:
`∑_{k ≠ i,j} |truncated3(i,j,k)| ≤ M(i) + M(j)`,
`M(x) = ∑_k exp(m) · exp(-m · d_{ℓ¹}(x,k))`, `m = simonLiebRate β J d`.

Proof: brick 1 `abs_truncated3_le` gives `|U₃(i,j,k)| ≤ τ₂(i,k) + τ₂(j,k)`;
(2a) bounds each `τ₂(a,k) ≤ exp(m)·exp(-m·d(a,k))` (reachability from
`Preconnected`); `Finset.sum_add_distrib` splits the two site-sums, each
dominated by its tsum via `sum_majorant_subtype_le_tsum`. -/
theorem sum_abs_truncated3_le_finiteVolumeMajorant
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J h : ℝ} (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ))
    (hβJ2d_pos : 0 < β * J * (2 * (d : ℝ))) (hβJ2d_lt : β * J * (2 * (d : ℝ)) < 1)
    (hconn : (inducedGraph (IsingModel.latticeGraph d) Λ).Preconnected)
    {i j : ↑Λ} (hij : i ≠ j) :
    ∑ k ∈ Finset.univ.filter (fun k : ↑Λ => k ≠ i ∧ k ≠ j),
        |truncated3 (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j k|
      ≤ (∑' x : Fin d → ℤ, Real.exp (simonLiebRate β J d)
            * Real.exp (-(simonLiebRate β J d)
                * (latticeDistance d (i : Fin d → ℤ) x : ℝ)))
        + (∑' x : Fin d → ℤ, Real.exp (simonLiebRate β J d)
            * Real.exp (-(simonLiebRate β J d)
                * (latticeDistance d (j : Fin d → ℤ) x : ℝ))) := by
  have hβJ2d_le : β * J * (2 * (d : ℝ)) ≤ 1 := hβJ2d_lt.le
  have hm : 0 < simonLiebRate β J d := simonLiebRate_pos hβJ2d_pos hβJ2d_lt
  -- Pointwise majorisation of each Ursell term by a sum of two exponentials.
  have hstep : ∑ k ∈ Finset.univ.filter (fun k : ↑Λ => k ≠ i ∧ k ≠ j),
        |truncated3 (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j k|
      ≤ ∑ k ∈ Finset.univ.filter (fun k : ↑Λ => k ≠ i ∧ k ≠ j),
          (Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d (i : Fin d → ℤ) (k : Fin d → ℤ) : ℝ))
            + Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d (j : Fin d → ℤ) (k : Fin d → ℤ) : ℝ))) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_filter] at hk
    have hki : i ≠ k := hk.2.1.symm
    have hkj : j ≠ k := hk.2.2.symm
    have hbrick := abs_truncated3_le (inducedGraph (IsingModel.latticeGraph d) Λ)
      (⟨J, h, β⟩ : IsingParams ℝ) hf hij hkj hki
    have hik := truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg
      d Λ hf hβJ2d_pos hβJ2d_le hki (hconn i k)
    have hjk := truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg
      d Λ hf hβJ2d_pos hβJ2d_le hkj (hconn j k)
    linarith
  refine hstep.trans ?_
  rw [Finset.sum_add_distrib]
  exact add_le_add
    (sum_majorant_subtype_le_tsum Λ hm (i : Fin d → ℤ) _)
    (sum_majorant_subtype_le_tsum Λ hm (j : Fin d → ℤ) _)

/-- **Semi-truncated 2-block field- and volume-uniform summable majorant** (GJ
Thm 17.6.1, p. 313, `|B| = 2`): on a `Preconnected` finite induced subgraph
`inducedGraph (latticeGraph d) Λ`, for a ferromagnetic field `⟨J, h, β⟩` with
`h ≥ 0`, strict high temperature `0 < β J · 2d < 1`, and distinct sites
`i ≠ j`, the `∂/∂h` site-sum of the pair semi-truncated susceptibility
`⟨σ_iσ_j; σ_l⟩ = ⟨σ_iσ_jσ_l⟩ − ⟨σ_iσ_j⟩⟨σ_l⟩` is bounded by a finite tsum
`M(i) + M(j)` **independent of `Λ` and of `h`**:
`∑_{l ≠ i,j} ⟨σ_iσ_j; σ_l⟩ ≤ M(i) + M(j)`,
`M(x) = ∑_l exp(m) · exp(-m · d_{ℓ¹}(x,l))`, `m = simonLiebRate β J d`.

Since `∂/∂h ⟨σ_iσ_j⟩_Λ = β ∑_l ⟨σ_iσ_j; σ_l⟩_Λ`, this is the uniform Lipschitz
(equi-Lipschitz-of-moments) bound `0 ≤ ∂/∂h ⟨σ_iσ_j⟩_Λ ≤ β (M(i) + M(j))` feeding
the Dini / uniform-tail step of the `∂/∂h` capstone of GJ Theorem 17.6.1.

Proof: the pair semi-truncated bound `semiTruncated_pair_le` gives
`⟨σ_iσ_j; σ_l⟩ ≤ τ₂(i,l) + τ₂(j,l)`; (2a) bounds each
`τ₂(a,l) ≤ exp(m)·exp(-m·d(a,l))` (reachability from `Preconnected`);
`Finset.sum_add_distrib` splits the two site-sums, each dominated by its tsum via
`sum_majorant_subtype_le_tsum`. -/
theorem sum_semiTruncated_pair_le_finiteVolumeMajorant
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J h : ℝ} (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ))
    (hβJ2d_pos : 0 < β * J * (2 * (d : ℝ))) (hβJ2d_lt : β * J * (2 * (d : ℝ)) < 1)
    (hconn : (inducedGraph (IsingModel.latticeGraph d) Λ).Preconnected)
    {i j : ↑Λ} (hij : i ≠ j) :
    ∑ l ∈ Finset.univ.filter (fun l : ↑Λ => l ≠ i ∧ l ≠ j),
        (correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i, j, l}
          - correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i, j}
            * correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                (⟨J, h, β⟩ : IsingParams ℝ) {l})
      ≤ (∑' x : Fin d → ℤ, Real.exp (simonLiebRate β J d)
            * Real.exp (-(simonLiebRate β J d)
                * (latticeDistance d (i : Fin d → ℤ) x : ℝ)))
        + (∑' x : Fin d → ℤ, Real.exp (simonLiebRate β J d)
            * Real.exp (-(simonLiebRate β J d)
                * (latticeDistance d (j : Fin d → ℤ) x : ℝ))) := by
  have hβJ2d_le : β * J * (2 * (d : ℝ)) ≤ 1 := hβJ2d_lt.le
  have hm : 0 < simonLiebRate β J d := simonLiebRate_pos hβJ2d_pos hβJ2d_lt
  -- Pointwise majorisation of each semi-truncated term by a sum of two exponentials.
  have hstep : ∑ l ∈ Finset.univ.filter (fun l : ↑Λ => l ≠ i ∧ l ≠ j),
        (correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i, j, l}
          - correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i, j}
            * correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                (⟨J, h, β⟩ : IsingParams ℝ) {l})
      ≤ ∑ l ∈ Finset.univ.filter (fun l : ↑Λ => l ≠ i ∧ l ≠ j),
          (Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d (i : Fin d → ℤ) (l : Fin d → ℤ) : ℝ))
            + Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d (j : Fin d → ℤ) (l : Fin d → ℤ) : ℝ))) := by
    apply Finset.sum_le_sum
    intro l hl
    rw [Finset.mem_filter] at hl
    have hil : i ≠ l := hl.2.1.symm
    have hjl : j ≠ l := hl.2.2.symm
    have hpair := semiTruncated_pair_le (inducedGraph (IsingModel.latticeGraph d) Λ)
      (⟨J, h, β⟩ : IsingParams ℝ) hf hij hil hjl
    have hik := truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg
      d Λ hf hβJ2d_pos hβJ2d_le hil (hconn i l)
    have hjk := truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg
      d Λ hf hβJ2d_pos hβJ2d_le hjl (hconn j l)
    linarith
  refine hstep.trans ?_
  rw [Finset.sum_add_distrib]
  exact add_le_add
    (sum_majorant_subtype_le_tsum Λ hm (i : Fin d → ℤ) _)
    (sum_majorant_subtype_le_tsum Λ hm (j : Fin d → ℤ) _)

end Ambient

end IsingModel
