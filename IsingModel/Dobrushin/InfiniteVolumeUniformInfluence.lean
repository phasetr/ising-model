import IsingModel.Dobrushin.ResolventDecay
import IsingModel.Conditioning.InduceDistanceTransfer
import IsingModel.Concrete.LatticeSphereCard
import IsingModel.ClusterExpansion.MayerTsumPerSiteAmbient
import IsingModel.PolyDecay
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Volume-uniform Dobrushin resolvent tails on cubic lattice volumes

This file records the card-free, distance-stratified tail estimate needed to lift the
finite Dobrushin comparison machinery to cubic-lattice infinite-volume limits. The key
point is that the finite-volume sum is stratified by ambient lattice distance and each
sphere is bounded by the surface-growth estimate `2 * (2r + 1)^(d - 1)`, so the result
has no factor depending on `|Λ|`.

References: Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace Dobrushin

open Finset Filter
open scoped Topology

/-! ## Tail series -/

/-- The `r`-th distance-stratum summand for the uniform Dobrushin resolvent tail. -/
noncomputable def resolventTailSummand (d : ℕ) (α : ℝ) (r : ℕ) : ℝ :=
  (2 * (2 * r + 1) ^ (d - 1) : ℝ) * α ^ r * (1 - α)⁻¹

/-- The shifted volume-uniform Dobrushin resolvent tail starting at distance `R`. -/
noncomputable def resolventTail (d : ℕ) (α : ℝ) (R : ℕ) : ℝ :=
  ∑' k : ℕ, resolventTailSummand d α (k + R)

/-- The tail summand is nonnegative for `0 ≤ α < 1`. -/
theorem resolventTailSummand_nonneg {d : ℕ} {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) (r : ℕ) : 0 ≤ resolventTailSummand d α r := by
  unfold resolventTailSummand
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hα0 r))
    (inv_nonneg.mpr (by linarith))

/-- The shifted polynomial-geometric series with `(k+1)^p` is summable for `0 ≤ α < 1`. -/
private theorem summable_succ_pow_mul_geometric_of_nonneg_lt_one (p : ℕ) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ p) * α ^ k) := by
  have hnorm : ‖α‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hα0]
  by_cases hαzero : α = 0
  · subst hαzero
    have hsingle : Summable (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) :=
      (hasSum_single 0 (fun k hk => by simp [hk])).summable
    refine hsingle.congr ?_
    intro k
    by_cases hk : k = 0
    · subst hk
      simp
    · simp [hk]
  · have hshift :
        Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ p) * α ^ (k + 1)) :=
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ p * α ^ n) 1).mpr
        (summable_pow_mul_geometric_of_norm_lt_one p hnorm)
    refine (hshift.mul_left α⁻¹).congr ?_
    intro k
    rw [pow_succ']
    field_simp [hαzero]

/-- The lattice surface-growth polynomial is bounded by a shifted monomial. -/
private theorem lattice_surface_polynomial_le_shifted_monomial (p k : ℕ) :
    (2 * (2 * k + 1) ^ p : ℝ) ≤
      (2 : ℝ) * (3 : ℝ) ^ p * (((k + 1 : ℕ) : ℝ) ^ p) := by
  have hbase : 2 * k + 1 ≤ 3 * (k + 1) := by omega
  have hpow : (2 * k + 1) ^ p ≤ (3 * (k + 1)) ^ p :=
    Nat.pow_le_pow_left hbase p
  calc
    (2 * (2 * k + 1) ^ p : ℝ)
        ≤ (2 * (3 * (k + 1)) ^ p : ℕ) := by
          exact_mod_cast Nat.mul_le_mul_left 2 hpow
    _ = (2 : ℝ) * (3 : ℝ) ^ p * (((k + 1 : ℕ) : ℝ) ^ p) := by
      push_cast
      rw [mul_pow]
      ring

/-- The volume-uniform resolvent-tail summand is summable for `0 ≤ α < 1`. -/
theorem resolventTailSummand_summable (d : ℕ) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) : Summable (resolventTailSummand d α) := by
  have hsucc := summable_succ_pow_mul_geometric_of_nonneg_lt_one (d - 1) hα0 hα1
  have hmajor :
      Summable (fun k : ℕ =>
        ((2 : ℝ) * (3 : ℝ) ^ (d - 1) * (1 - α)⁻¹)
          * ((((k + 1 : ℕ) : ℝ) ^ (d - 1)) * α ^ k)) :=
    hsucc.mul_left ((2 : ℝ) * (3 : ℝ) ^ (d - 1) * (1 - α)⁻¹)
  refine Summable.of_nonneg_of_le
    (fun k => resolventTailSummand_nonneg hα0 hα1 k) ?_ hmajor
  intro k
  have hpoly := lattice_surface_polynomial_le_shifted_monomial (d - 1) k
  have hpow_nonneg : 0 ≤ α ^ k := pow_nonneg hα0 k
  have hinv_nonneg : 0 ≤ (1 - α)⁻¹ := inv_nonneg.mpr (by linarith)
  calc
    resolventTailSummand d α k
        = (2 * (2 * k + 1) ^ (d - 1) : ℝ) * α ^ k * (1 - α)⁻¹ := rfl
    _ ≤ ((2 : ℝ) * (3 : ℝ) ^ (d - 1)
          * (((k + 1 : ℕ) : ℝ) ^ (d - 1)))
          * α ^ k * (1 - α)⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpoly hpow_nonneg) hinv_nonneg
    _ =
        ((2 : ℝ) * (3 : ℝ) ^ (d - 1) * (1 - α)⁻¹)
          * ((((k + 1 : ℕ) : ℝ) ^ (d - 1)) * α ^ k) := by
        ring

/-- The volume-uniform resolvent tail tends to zero as the starting radius tends to infinity. -/
theorem tendsto_resolventTail_atTop (d : ℕ) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) : Tendsto (resolventTail d α) atTop (𝓝 0) := by
  have _hsumm := resolventTailSummand_summable d hα0 hα1
  simpa [resolventTail] using
    (_root_.tendsto_sum_nat_add (fun r : ℕ => resolventTailSummand d α r))

/-! ## Finite far-set embedding into the shifted tail -/

/-- A finite set of radii all at least `R` is bounded by the shifted tail. -/
private theorem sum_far_radii_le_resolventTail (d R : ℕ) {α : ℝ} {T : Finset ℕ}
    (hT : ∀ r ∈ T, R ≤ r) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hsumm : Summable (resolventTailSummand d α)) :
    ∑ r ∈ T, resolventTailSummand d α r ≤ resolventTail d α R := by
  classical
  let K : Finset ℕ := T.image (fun r => r - R)
  have hinj : ∀ a ∈ T, ∀ b ∈ T, a - R = b - R → a = b := by
    intro a ha b hb hab
    have haR := hT a ha
    have hbR := hT b hb
    omega
  have hsum_image :
      ∑ k ∈ K, resolventTailSummand d α (k + R)
        = ∑ r ∈ T, resolventTailSummand d α ((r - R) + R) := by
    dsimp [K]
    rw [Finset.sum_image]
    exact hinj
  have hsum_eq :
      ∑ r ∈ T, resolventTailSummand d α r
        = ∑ k ∈ K, resolventTailSummand d α (k + R) := by
    calc
      ∑ r ∈ T, resolventTailSummand d α r
          = ∑ r ∈ T, resolventTailSummand d α ((r - R) + R) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              rw [Nat.sub_add_cancel (hT r hr)]
      _ = ∑ k ∈ K, resolventTailSummand d α (k + R) := hsum_image.symm
  rw [hsum_eq, resolventTail]
  have hshift : Summable (fun k : ℕ => resolventTailSummand d α (k + R)) :=
    (summable_nat_add_iff (f := resolventTailSummand d α) R).mpr hsumm
  exact hshift.sum_le_tsum K
    (fun k _ => resolventTailSummand_nonneg hα0 hα1 (k + R))

/-- A distance fiber in a finite volume injects into the ambient lattice sphere by translation. -/
private theorem latticeDistance_fiber_card_le_sphere (d r : ℕ)
    {Λ : Finset (Fin d → ℤ)} (x₀ : ↑Λ) (S : Finset ↑Λ) :
    (S.filter fun y => latticeDistance d x₀.val y.val = r).card
      ≤ (Ambient.latticeSphere d r).card := by
  classical
  let e : ↑Λ ↪ (Fin d → ℤ) :=
    { toFun := fun y => y.val - x₀.val
      inj' := by
        intro y z hsub
        apply Subtype.ext
        funext i
        have hi := congrFun hsub i
        dsimp at hi
        linarith }
  have hsubset : (S.filter fun y => latticeDistance d x₀.val y.val = r).map e
      ⊆ Ambient.latticeSphere d r := by
    intro v hv
    rw [Finset.mem_map] at hv
    rcases hv with ⟨y, hy, hyv⟩
    have hdist : latticeDistance d x₀.val y.val = r := (Finset.mem_filter.mp hy).2
    rw [← hyv, Ambient.mem_latticeSphere]
    simpa [e, latticeDistance_translate_eq d x₀.val y.val] using hdist
  calc
    (S.filter fun y => latticeDistance d x₀.val y.val = r).card
        = ((S.filter fun y => latticeDistance d x₀.val y.val = r).map e).card := by
            rw [Finset.card_map]
    _ ≤ (Ambient.latticeSphere d r).card := Finset.card_le_card hsubset

/-- The Dobrushin coefficient of an induced cubic-lattice volume is bounded by `2d*tanh(βJ)`. -/
private theorem isingDobrushinCoeff_induced_latticeGraph_le_uniform (d : ℕ)
    (Λ : Finset (Fin d → ℤ)) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    isingDobrushinCoeff (Ambient.inducedGraph (latticeGraph d) Λ) β J
      ≤ (2 * (d : ℝ)) * Real.tanh (β * J) := by
  have hdeg := induced_latticeGraph_maxDegree_le d Λ
  rw [isingDobrushinCoeff]
  have htanh : 0 ≤ Real.tanh (β * J) := real_tanh_nonneg hβJ
  calc
    ((Ambient.inducedGraph (latticeGraph d) Λ).maxDegree : ℝ) * Real.tanh (β * J)
        ≤ ((2 * d : ℕ) : ℝ) * Real.tanh (β * J) := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg) htanh
    _ = (2 * (d : ℝ)) * Real.tanh (β * J) := by
        norm_num

/-- The uniform high-temperature hypothesis implies the induced-volume condition. -/
private theorem induced_latticeGraph_high_temp_of_uniform (d : ℕ)
    (Λ : Finset (Fin d → ℤ)) {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hα : β * J * (2 * (d : ℝ)) < 1) :
    β * J * (Ambient.inducedGraph (latticeGraph d) Λ).maxDegree < 1 := by
  have hdeg := induced_latticeGraph_maxDegree_le d Λ
  calc
    β * J * ((Ambient.inducedGraph (latticeGraph d) Λ).maxDegree : ℝ)
        ≤ β * J * ((2 * d : ℕ) : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg) hβJ
    _ = β * J * (2 * (d : ℝ)) := by
        norm_num
    _ < 1 := hα

/-- The far-field resolvent bound for any finite graph with lattice-distance control. -/
private theorem dobrushinResolvent_farSum_le_resolventTail_of_distance_control (d : ℕ)
    {Λ : Finset (Fin d → ℤ)} [Fintype ↑Λ] (G : SimpleGraph ↑Λ)
    [DecidableRel G.Adj] {β J : ℝ} (hd : 1 ≤ d) (hβJ : 0 ≤ β * J)
    (hα : β * J * (2 * (d : ℝ)) < 1) (hΔ : β * J * G.maxDegree < 1)
    (hcoeff_uniform : isingDobrushinCoeff G β J ≤
      (2 * (d : ℝ)) * Real.tanh (β * J))
    (hdist_le : ∀ {a b : ↑Λ}, G.Reachable a b →
      latticeDistance d a.val b.val ≤ G.dist a b)
    (x₀ : ↑Λ) (S : Finset ↑Λ) (R : ℕ)
    (hfar : ∀ y ∈ S, R ≤ latticeDistance d x₀.val y.val) :
    ∑ y ∈ S, dobrushinResolvent G β J x₀ y
      ≤ resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) R := by
  classical
  let α : ℝ := (2 * (d : ℝ)) * Real.tanh (β * J)
  let size : ↑Λ → ℕ := fun y => latticeDistance d x₀.val y.val
  have hα0 : 0 ≤ α := by
    dsimp [α]
    exact mul_nonneg (by positivity) (real_tanh_nonneg hβJ)
  have hα_le_beta : α ≤ β * J * (2 * (d : ℝ)) := by
    dsimp [α]
    have htanh := tanh_le_self hβJ
    have hnonneg : 0 ≤ 2 * (d : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left htanh hnonneg]
  have hα1 : α < 1 := lt_of_le_of_lt hα_le_beta hα
  have hsumm : Summable (resolventTailSummand d α) :=
    resolventTailSummand_summable d hα0 hα1
  have hcoeff_nonneg : 0 ≤ isingDobrushinCoeff G β J :=
    isingDobrushinCoeff_nonneg G hβJ
  have hcoeff_le : isingDobrushinCoeff G β J ≤ α := by
    simpa [α] using hcoeff_uniform
  have hres_le_lattice :
      ∀ y : ↑Λ,
        dobrushinResolvent G β J x₀ y
          ≤ α ^ (latticeDistance d x₀.val y.val) * (1 - α)⁻¹ := by
    intro y
    by_cases hreach : G.Reachable x₀ y
    · have hR := dobrushinResolvent_le_pow_dist G hβJ hΔ x₀ y
      have hpow_coeff :
          isingDobrushinCoeff G β J ^ G.dist x₀ y ≤ α ^ G.dist x₀ y :=
        pow_le_pow_left₀ hcoeff_nonneg hcoeff_le _
      have hinv : (1 - isingDobrushinCoeff G β J)⁻¹ ≤ (1 - α)⁻¹ := by
        have hposα : 0 < 1 - α := by linarith
        have hle : 1 - α ≤ 1 - isingDobrushinCoeff G β J := by linarith
        have hposc : 0 < 1 - isingDobrushinCoeff G β J :=
          lt_of_lt_of_le hposα hle
        exact (inv_le_inv₀ hposc hposα).mpr hle
      have hlat : latticeDistance d x₀.val y.val ≤ G.dist x₀ y := hdist_le hreach
      have hpow_dist : α ^ G.dist x₀ y ≤ α ^ latticeDistance d x₀.val y.val :=
        pow_le_pow_of_le_one hα0 hα1.le hlat
      calc
        dobrushinResolvent G β J x₀ y
            ≤ isingDobrushinCoeff G β J ^ G.dist x₀ y
                * (1 - isingDobrushinCoeff G β J)⁻¹ := hR
        _ ≤ α ^ G.dist x₀ y * (1 - α)⁻¹ := by
            exact mul_le_mul hpow_coeff hinv (inv_nonneg.mpr (by linarith))
              (pow_nonneg hα0 _)
        _ ≤ α ^ latticeDistance d x₀.val y.val * (1 - α)⁻¹ :=
            mul_le_mul_of_nonneg_right hpow_dist (inv_nonneg.mpr (by linarith))
    · rw [dobrushinResolvent_eq_zero_of_not_reachable G β J hreach]
      exact mul_nonneg (pow_nonneg hα0 _) (inv_nonneg.mpr (by linarith))
  let T : Finset ℕ := S.image size
  have hmaps : ∀ y ∈ S, size y ∈ T := by
    intro y hy
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hdecomp :
      ∑ y ∈ S, dobrushinResolvent G β J x₀ y
        = ∑ r ∈ T,
            ∑ y ∈ S.filter (fun y => size y = r), dobrushinResolvent G β J x₀ y := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun y => dobrushinResolvent G β J x₀ y)]
  have hfiber :
      ∀ r ∈ T,
        (∑ y ∈ S.filter (fun y => size y = r), dobrushinResolvent G β J x₀ y)
          ≤ resolventTailSummand d α r := by
    intro r _hr
    have hpoint :
        ∀ y ∈ S.filter (fun y => size y = r),
          dobrushinResolvent G β J x₀ y ≤ α ^ r * (1 - α)⁻¹ := by
      intro y hy
      have hdist : size y = r := (Finset.mem_filter.mp hy).2
      simpa [size, hdist] using hres_le_lattice y
    have hconst_nonneg : 0 ≤ α ^ r * (1 - α)⁻¹ :=
      mul_nonneg (pow_nonneg hα0 r) (inv_nonneg.mpr (by linarith))
    have hcard_nat :
        (S.filter (fun y => size y = r)).card ≤ 2 * (2 * r + 1) ^ (d - 1) := by
      change (S.filter fun y => latticeDistance d x₀.val y.val = r).card
        ≤ 2 * (2 * r + 1) ^ (d - 1)
      exact le_trans (latticeDistance_fiber_card_le_sphere d r x₀ S)
        (Ambient.latticeSphere_card_le' d r hd)
    have hcard_real :
        ((S.filter (fun y => size y = r)).card : ℝ)
          ≤ ((2 * (2 * r + 1) ^ (d - 1) : ℕ) : ℝ) := by
      exact_mod_cast hcard_nat
    calc
      ∑ y ∈ S.filter (fun y => size y = r), dobrushinResolvent G β J x₀ y
          ≤ ∑ y ∈ S.filter (fun y => size y = r), α ^ r * (1 - α)⁻¹ :=
          Finset.sum_le_sum hpoint
      _ = ((S.filter (fun y => size y = r)).card : ℝ)
            * (α ^ r * (1 - α)⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 * (2 * r + 1) ^ (d - 1) : ℕ) : ℝ)
            * (α ^ r * (1 - α)⁻¹) := by
          exact mul_le_mul_of_nonneg_right hcard_real hconst_nonneg
      _ = (2 * (2 * r + 1) ^ (d - 1) : ℝ) * (α ^ r * (1 - α)⁻¹) := by
          norm_num
      _ = resolventTailSummand d α r := by
          unfold resolventTailSummand
          ring
  have hTfar : ∀ r ∈ T, R ≤ r := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨y, hy, rfl⟩
    exact hfar y hy
  calc
    ∑ y ∈ S, dobrushinResolvent G β J x₀ y
        = ∑ r ∈ T,
          ∑ y ∈ S.filter (fun y => size y = r), dobrushinResolvent G β J x₀ y := hdecomp
    _ ≤ ∑ r ∈ T, resolventTailSummand d α r := Finset.sum_le_sum hfiber
    _ ≤ resolventTail d α R :=
        sum_far_radii_le_resolventTail d R hTfar hα0 hα1 hsumm
    _ = resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) R := by rfl

/-! ## Headline estimate -/

/-- **Card-free volume-uniform far-field resolvent bound on finite cubic-lattice volumes.**

For the induced graph `GΛ = Ambient.inducedGraph (latticeGraph d) Λ`, the sum of Dobrushin
resolvent entries from `x₀` to any finite set `S` lying at ambient lattice distance at least
`R` is bounded by the shifted surface-growth tail with `α = 2d * tanh(βJ)`. The bound is
uniform in the volume `Λ` and contains no `Fintype.card ↑Λ` or `S.card` factor. -/
theorem dobrushinResolvent_farSum_le_resolventTail (d : ℕ) {Λ : Finset (Fin d → ℤ)}
    {β J : ℝ} (hd : 1 ≤ d) (hβJ : 0 ≤ β * J)
    (hα : β * J * (2 * (d : ℝ)) < 1) (x₀ : ↑Λ) (S : Finset ↑Λ) (R : ℕ)
    (hfar : ∀ y ∈ S, R ≤ latticeDistance d x₀.val y.val) :
    ∑ y ∈ S, dobrushinResolvent (Ambient.inducedGraph (latticeGraph d) Λ) β J x₀ y
      ≤ resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) R := by
  have hΔ_induced := induced_latticeGraph_high_temp_of_uniform d Λ hβJ hα
  have hcoeff_induced := isingDobrushinCoeff_induced_latticeGraph_le_uniform d Λ hβJ
  exact dobrushinResolvent_farSum_le_resolventTail_of_distance_control
    d (Ambient.inducedGraph (latticeGraph d) Λ) hd hβJ hα hΔ_induced hcoeff_induced
    (fun {_a _b} hreach => latticeDistance_le_induce_dist hreach) x₀ S R hfar

end Dobrushin

end IsingModel
