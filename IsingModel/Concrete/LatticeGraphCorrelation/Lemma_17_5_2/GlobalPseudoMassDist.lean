import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMass
import IsingModel.AmbientLattice.CorrelationInfinite.Bounds
import IsingModel.AmbientLattice.TruncatedFunctions.TwoPoint

/-!
# GJ §17.5 Lemma 17.5.2 — faithful lower bound `m⁻(σ) ≤ m(σ)` (distance form)

This module supplies the **faithful, unconditional lower bound** of Glimm--Jaffe
§17.5 Lemma 17.5.2: the system pseudo-mass `m⁻(σ)` is dominated by the lattice
mass `m(σ) = latticeMass`.

The sibling module `GlobalPseudoMass.lean` builds the system pseudo-mass from the
per-pair pseudo-mass `pseudoMassFromParamsAtPair`, which uses a **single fixed**
profile radius `r` for *every* pair.  That fixed-`r` object is *not* the book's
inverse correlation length: the book's `m⁻(x, y, σ)` solves the pseudo-mass
equation with the per-pair distance `r = |x − y|`.  In fact the fixed-`r`
inequality `globalPseudoMass ≤ latticeMass` is **false** (the per-pair mass
blows up as `r → 0⁺` while the lattice mass stays finite).

The faithful fix, implemented here, is a **distance-parametrized** per-pair
pseudo-mass `pseudoMassFromParamsAtPairDist`, where each pair `(x, z)` uses
`r = latticeDistance d x z` (the ℓ¹ lattice distance).  Its lower envelope
`globalPseudoMassDist` then satisfies the book's
`ENNReal.ofReal (m⁻(σ)) ≤ latticeMass` **unconditionally** (only the ferromagnetic
sign condition `0 ≤ J` and `0 < β` are needed), via the book's existential
near-optimal-pair argument: the negation of `HasExponentialDecay` at a rate `R`
just above the lattice mass supplies a single pair `(i, j)` whose correlation
exceeds `2·exp(−R·dist)`, and aligning the profile radius with that same `dist`
forces the per-pair pseudo-mass below `R`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set Real

/-- **Distance-parametrized per-pair pseudo-mass** `m⁻(x, z, σ)` of
Glimm--Jaffe §17.5: the pseudo-mass associated to the infinite-volume two-point
correlation `⟨σ_x σ_z⟩^∞ = correlationInfinite (latticeGraph d) Λ p {x, z}`,
using the book's per-pair profile radius `r = latticeDistance d x z` (the ℓ¹
lattice distance).

For a distinct pair `x ≠ z` the lattice distance is positive
(`latticeDistance_eq_zero_iff`), so the radius hypothesis `0 < r` of
`pseudoMassExt` is met; the value is the totalized `pseudoMassExt` (which is
`pseudoMass` on the active window `Ioo 0 2` and `0` otherwise).  On the diagonal
`x = z` the convention returns `0`.

Unlike `pseudoMassFromParamsAtPair`, the radius here varies with the pair, which
is exactly what is needed to express the inverse correlation length faithfully.

References: Glimm--Jaffe §17.5, p.~311. -/
noncomputable def pseudoMassFromParamsAtPairDist {α d : ℕ} (hα : 1 ≤ α)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (x z : Fin d → ℤ) : ℝ :=
  if hxz : x ≠ z then
    pseudoMassExt hα
      (show (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) from by
        exact_mod_cast Nat.pos_of_ne_zero
          (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h)))
      (Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z})
  else 0

/-- **`pseudoMassFromParamsAtPairDist` is non-negative**: both the active branch
(`pseudoMassExt_nonneg`) and the diagonal fallback `0` are non-negative. -/
theorem pseudoMassFromParamsAtPairDist_nonneg {α d : ℕ} (hα : 1 ≤ α)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    0 ≤ pseudoMassFromParamsAtPairDist hα Λ p x z := by
  unfold pseudoMassFromParamsAtPairDist
  by_cases hxz : x ≠ z
  · rw [dif_pos hxz]
    exact pseudoMassExt_nonneg hα _ _
  · rw [dif_neg hxz]

/-- **Defining equation of `pseudoMassFromParamsAtPairDist` on a distinct pair**:
for `x ≠ z` (with `0 < r := latticeDistance d x z`), the distance-parametrized
per-pair pseudo-mass equals the totalized `pseudoMassExt` of the two-point
correlation at radius `r`.  Proof irrelevance identifies the radius positivity
proof packaged in the definition with any chosen `hpos`. -/
theorem pseudoMassFromParamsAtPairDist_of_ne {α d : ℕ} (hα : 1 ≤ α)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hpos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ)) :
    pseudoMassFromParamsAtPairDist hα Λ p x z
      = pseudoMassExt hα hpos
          (Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}) := by
  unfold pseudoMassFromParamsAtPairDist
  rw [dif_pos hxz]

/-- **Value set of the distance-parametrized system pseudo-mass**: the set of
per-pair pseudo-masses `pseudoMassFromParamsAtPairDist … x z` ranging over all
*active* distinct pairs `(x, z)`.  The system pseudo-mass is its infimum.

References: Glimm--Jaffe §17.5, p.~311. -/
def globalPseudoMassDistSet {α d : ℕ} (hα : 1 ≤ α)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) : Set ℝ :=
  {m | ∃ x z : Fin d → ℤ,
    ActivePseudoMassPair Λ p x z ∧
      m = pseudoMassFromParamsAtPairDist hα Λ p x z}

/-- **Distance-parametrized system (global) pseudo-mass** `m⁻(σ)` of
Glimm--Jaffe §17.5: the lower envelope (infimum over active distinct pairs) of
the distance-parametrized per-pair pseudo-masses.

This is the faithful inverse correlation length: each contributing pair uses its
own ℓ¹ distance as profile radius, so the infimum captures the genuine
asymptotic decay rate rather than a fixed-radius artefact.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
noncomputable def globalPseudoMassDist {α d : ℕ} (hα : 1 ≤ α)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) : ℝ :=
  sInf (globalPseudoMassDistSet hα Λ p)

/-- **The distance-parametrized value set is bounded below by `0`**: every
per-pair pseudo-mass is non-negative (`pseudoMassFromParamsAtPairDist_nonneg`),
so the defining infimum is well posed. -/
theorem globalPseudoMassDistSet_bddBelow {α d : ℕ} (hα : 1 ≤ α)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) :
    BddBelow (globalPseudoMassDistSet hα Λ p) := by
  refine ⟨0, ?_⟩
  rintro m ⟨x, z, _, rfl⟩
  exact pseudoMassFromParamsAtPairDist_nonneg hα Λ p x z

/-- **The distance-parametrized system pseudo-mass is non-negative**: it is the
infimum of a set of non-negative reals. -/
theorem globalPseudoMassDist_nonneg {α d : ℕ} (hα : 1 ≤ α)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) :
    0 ≤ globalPseudoMassDist hα Λ p := by
  unfold globalPseudoMassDist
  refine Real.sInf_nonneg ?_
  rintro m ⟨x, z, _, rfl⟩
  exact pseudoMassFromParamsAtPairDist_nonneg hα Λ p x z

/-- **Distance-parametrized system pseudo-mass is a lower envelope**: for any
active distinct pair `(x, z)`, the system pseudo-mass `m⁻(σ)` is bounded above by
the per-pair pseudo-mass `pseudoMassFromParamsAtPairDist … x z`.

This is the global-to-pair comparison `m⁻(σ) ≤ m⁻(x, z, σ)`, proved by `csInf_le`
against the bounded-below value set.

References: Glimm--Jaffe §17.5, p.~311. -/
theorem globalPseudoMassDist_le_of_active {α d : ℕ} (hα : 1 ≤ α)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {x z : Fin d → ℤ}
    (hxz : ActivePseudoMassPair Λ p x z) :
    globalPseudoMassDist hα Λ p ≤ pseudoMassFromParamsAtPairDist hα Λ p x z :=
  csInf_le (globalPseudoMassDistSet_bddBelow hα Λ p) ⟨x, z, hxz, rfl⟩

set_option maxHeartbeats 1200000 in
-- The proof unifies the heavy `correlationInfinite (latticeGraph d) Λ … {i, j}`
-- terms (with their synthesized `Fintype edgeSet` instances) across the
-- `HasExponentialDecay` negation, the active-pair window, and the pseudo-mass
-- inversion, so the default heartbeat budget is exceeded.
/-- **GJ §17.5 Lemma 17.5.2 faithful lower bound `m⁻(σ) ≤ m(σ)` (unconditional)**:
the distance-parametrized system pseudo-mass is dominated by the lattice mass at
the zero-field ferromagnetic parameter `⟨J, 0, β⟩`.

This is the book's inequality `m⁻(σ) ≤ m(σ)`, carried only by the ferromagnetic
sign hypotheses `0 ≤ J`, `0 < β`.  The proof is the book's existential
near-optimal-pair argument:

* if `latticeMass = ⊤` the bound is trivial;
* otherwise, for any real rate `R` strictly above `latticeMass.toReal`, the
  lattice-mass lower bound `latticeMass_ge_of_HasExponentialDecay` forces
  `¬ HasExponentialDecay d Λ ⟨J,0,β⟩ R`; unfolding the negation at constant
  `C = 2` yields a pair `(i, j)` with
  `2·exp(−R·dist) < ⟨σ_i σ_j⟩^∞` (using `truncated2Infinite_h_zero` and
  `correlationInfinite_nonneg`).  This pair is active, and aligning the profile
  radius with `dist` gives `pseudoMassG α dist R ≤ 2·exp(−R·dist) < ⟨σ_i σ_j⟩^∞`,
  hence (`pseudoMass_le_iff_pseudoMassG_le`) the per-pair pseudo-mass is `≤ R`;
  the lower envelope then gives `globalPseudoMassDist ≤ R`.  Squeezing `R` down to
  `latticeMass.toReal` closes the bound.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem globalPseudoMassDist_le_latticeMass {α d : ℕ} (hα : 1 ≤ α)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    ENNReal.ofReal (globalPseudoMassDist hα Λ (⟨J, 0, β⟩ : IsingParams ℝ))
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  -- Ferromagnetic data at the zero-field slice.
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  -- The key step: every rate `R` above the lattice mass dominates `m⁻(σ)`.
  have key : ∀ R : ℝ,
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) < ENNReal.ofReal R →
        globalPseudoMassDist hα Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤ R := by
    intro R hMR
    have hRpos : 0 < R :=
      ENNReal.ofReal_pos.mp (lt_of_le_of_lt (zero_le _) hMR)
    -- No exponential decay at rate `R`, else `R ≤ latticeMass`.
    have hnd : ¬ HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) R := by
      intro hdec
      exact absurd (latticeMass_ge_of_HasExponentialDecay hRpos.le hdec)
        (not_le.mpr hMR)
    unfold HasExponentialDecay at hnd
    push Not at hnd
    obtain ⟨i, j, hij, hgt0⟩ := hnd 2 (by norm_num)
    -- `hgt0 : 2 * exp (-R * dist) < |truncated2Infinite … i j|`.
    rw [truncated2Infinite_h_zero] at hgt0
    have hcorr_nn :
        0 ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
      correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ _ hf _
    -- `hgt : 2 * exp (-R * dist) < ⟨σ_i σ_j⟩^∞`.
    have hgt :
        2 * Real.exp (-R * (IsingModel.latticeDistance d i j : ℝ))
          < Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
      lt_of_lt_of_le hgt0 (le_of_eq (abs_of_nonneg hcorr_nn))
    have h2exp_pos :
        0 < 2 * Real.exp (-R * (IsingModel.latticeDistance d i j : ℝ)) := by
      positivity
    have hc_pos :
        0 < Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} := h2exp_pos.trans hgt
    have hc_lt2 :
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} < 2 :=
      correlationInfinite_lt_two (IsingModel.latticeGraph d) Λ _ _
    have hc_mem :
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} ∈ Set.Ioo (0 : ℝ) 2 :=
      ⟨hc_pos, hc_lt2⟩
    have hactive : ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j :=
      ⟨hij, hc_mem⟩
    -- Distance positivity.
    have hdist_pos : (0 : ℝ) < (IsingModel.latticeDistance d i j : ℝ) := by
      have hne : IsingModel.latticeDistance d i j ≠ 0 :=
        fun h => hij ((IsingModel.latticeDistance_eq_zero_iff d i j).mp h)
      exact_mod_cast Nat.pos_of_ne_zero hne
    -- Profile bound with the matching radius `dist`.
    have hG :
        pseudoMassG α (IsingModel.latticeDistance d i j : ℝ) R
          ≤ 2 * Real.exp (-(R * (IsingModel.latticeDistance d i j : ℝ))) :=
      pseudoMassG_le_two_mul_exp α hRpos.le hdist_pos
    have hexp_eq :
        -(R * (IsingModel.latticeDistance d i j : ℝ))
          = -R * (IsingModel.latticeDistance d i j : ℝ) := by ring
    rw [hexp_eq] at hG
    have hGlt :
        pseudoMassG α (IsingModel.latticeDistance d i j : ℝ) R
          < Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} := lt_of_le_of_lt hG hgt
    -- Invert the profile to bound the per-pair pseudo-mass by `R`.
    have hpm_le : pseudoMass hα hdist_pos hc_mem ≤ R :=
      (pseudoMass_le_iff_pseudoMassG_le hα hdist_pos hc_mem hRpos.le).mpr hGlt.le
    calc
      globalPseudoMassDist hα Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          ≤ pseudoMassFromParamsAtPairDist hα Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) i j :=
            globalPseudoMassDist_le_of_active hα Λ _ hactive
      _ = pseudoMass hα hdist_pos hc_mem := by
            rw [pseudoMassFromParamsAtPairDist_of_ne hα Λ _ hij hdist_pos,
              pseudoMassExt_of_mem hα hdist_pos hc_mem]
      _ ≤ R := hpm_le
  -- Combine `key` with the ENNReal squeeze.
  by_cases htop : latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) = ⊤
  · rw [htop]; exact le_top
  · rw [← ENNReal.ofReal_toReal htop]
    refine ENNReal.ofReal_le_ofReal ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨R, hR1, hR2⟩ := exists_between hcon
    have hMR : latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) < ENNReal.ofReal R := by
      rw [ENNReal.lt_ofReal_iff_toReal_lt htop]
      exact hR1
    exact absurd (key R hMR) (not_le.mpr hR2)

end Ambient
end IsingModel
