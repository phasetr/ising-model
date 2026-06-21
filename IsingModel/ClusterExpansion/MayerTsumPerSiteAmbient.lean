import IsingModel.ClusterExpansion.MayerTsumPerSite
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.Concrete.CubicExhaustion

/-!
# Volume-uniform (per-site) Mayer bound on ambient / induced-graph / ℤ^d settings (GJ §18.5)

Lifts the abstract volume-uniform per-site Kotecky--Preiss Mayer-expansion bound
`tsum_abs_mayerExpansionTerm_succ_div_card_le` (#4137) to the concrete settings used for
the thermodynamic limit:

* the induced subgraph `Ambient.inducedGraph G Λ` on an arbitrary finite volume `Λ`;
* the per-stage induced graph `Ambient.inducedGraph G (Λ.volume n)` along an exhaustion;
* the lattice graph `latticeGraph d` induced on a cubic box, where the maximum degree is
  bounded uniformly by `2 d` (`induced_latticeGraph_maxDegree_le`), yielding a **genuinely
  volume-uniform** per-site bound `latticeGraph_kp_tsum_per_site_le` whose right-hand side
  `kpBound (2 d) t` is independent of the volume `Λ`.

The ℤ^d-uniform bound uses the monotonicity of the Kotecky--Preiss constant `kpBound Δ t` in
`r = Δ²e|t|` on the KP region (`kpBound_r_mono_of_le` / `kpBound_mono_of_degree_le`), together
with the downward-closure of the KP region in `r` (`kpRegion_downward_closed`).

* `induced_latticeGraph_maxDegree_le`
* `induced_kp_tsum_per_site_le`
* `induced_kp_tsum_per_site_alongExhaustion_le`
* `kpBound`, `kpBound_r_mono_of_le`, `kpBound_mono_of_degree_le`
* `latticeGraph_kp_tsum_per_site_le`
* `latticeGraph_kp_tsum_per_site_cubicExhaustion_le`

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

/-- **The Kotecky--Preiss per-site bound constant** `kpBound Δ t`.  With `r = Δ²e|t|` and
`ρ = 4r/(1−r)²`, this is `((1−r)(1−ρ))⁻¹`, the volume-uniform right-hand side of the
per-site Mayer-expansion bound for a graph of maximum degree `Δ`. -/
noncomputable def kpBound (Δ : ℕ) (t : ℝ) : ℝ :=
  ((1 - (Δ : ℝ) ^ 2 * (Real.exp 1 * |t|))
      * (1 - 4 * ((Δ : ℝ) ^ 2 * (Real.exp 1 * |t|))
            / (1 - (Δ : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2))⁻¹

/-- **Max-degree bound for the induced lattice graph**: the maximum degree of
`Ambient.inducedGraph (latticeGraph d) Λ` is at most `2 d`.  Combines the per-vertex bound
`inducedLatticeGraph_degree_le` with `SimpleGraph.maxDegree_le_of_forall_degree_le`. -/
theorem induced_latticeGraph_maxDegree_le (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).maxDegree ≤ 2 * d :=
  SimpleGraph.maxDegree_le_of_forall_degree_le _ (2 * d)
    (Ambient.inducedLatticeGraph_degree_le d Λ)

/-- **Induced-graph per-site Mayer bound** (arbitrary finite volume `Λ`).  Direct instantiation
of the abstract `tsum_abs_mayerExpansionTerm_succ_div_card_le` (#4137) with the induced subgraph
`Ambient.inducedGraph G Λ`. -/
theorem induced_kp_tsum_per_site_le {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (Λ : Finset V)
    [DecidableRel (Ambient.inducedGraph G Λ).Adj]
    [Fintype (Ambient.inducedGraph G Λ).edgeSet] [Nonempty (↑Λ : Type _)] {t : ℝ}
    (hkp : ((Ambient.inducedGraph G Λ).maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ : 4 * (((Ambient.inducedGraph G Λ).maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - ((Ambient.inducedGraph G Λ).maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    (∑' n : ℕ, |mayerExpansionTerm (Ambient.inducedGraph G Λ) (n + 1) t|)
        / (Fintype.card (↑Λ : Type _) : ℝ)
      ≤ ((1 - ((Ambient.inducedGraph G Λ).maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
          * (1 - 4 * (((Ambient.inducedGraph G Λ).maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
                / (1 - ((Ambient.inducedGraph G Λ).maxDegree : ℝ) ^ 2
                    * (Real.exp 1 * |t|)) ^ 2))⁻¹ :=
  tsum_abs_mayerExpansionTerm_succ_div_card_le (Ambient.inducedGraph G Λ) hkp hρ

/-- **Along-exhaustion induced-graph per-site Mayer bound**.  The induced-graph per-site bound
`induced_kp_tsum_per_site_le` specialised to the `n`-th stage `Λ.volume n` of an exhaustion. -/
theorem induced_kp_tsum_per_site_alongExhaustion_le {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (Λ : Ambient.Exhaustion V) (n : ℕ)
    [DecidableRel (Ambient.inducedGraph G (Λ.volume n)).Adj]
    [Fintype (Ambient.inducedGraph G (Λ.volume n)).edgeSet]
    [Nonempty (↑(Λ.volume n) : Type _)] {t : ℝ}
    (hkp : ((Ambient.inducedGraph G (Λ.volume n)).maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ : 4 * (((Ambient.inducedGraph G (Λ.volume n)).maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - ((Ambient.inducedGraph G (Λ.volume n)).maxDegree : ℝ) ^ 2
            * (Real.exp 1 * |t|)) ^ 2 < 1) :
    (∑' k : ℕ, |mayerExpansionTerm (Ambient.inducedGraph G (Λ.volume n)) (k + 1) t|)
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
      ≤ ((1 - ((Ambient.inducedGraph G (Λ.volume n)).maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
          * (1 - 4 * (((Ambient.inducedGraph G (Λ.volume n)).maxDegree : ℝ) ^ 2
                * (Real.exp 1 * |t|))
                / (1 - ((Ambient.inducedGraph G (Λ.volume n)).maxDegree : ℝ) ^ 2
                    * (Real.exp 1 * |t|)) ^ 2))⁻¹ :=
  tsum_abs_mayerExpansionTerm_succ_div_card_le (Ambient.inducedGraph G (Λ.volume n)) hkp hρ

/-- **Monotonicity of the ratio `4r/(1−r)²`** on `0 ≤ r < 1`.  If `0 ≤ r₁ ≤ r₂` and both
`1−r₁, 1−r₂` are positive, then `4r₁/(1−r₁)² ≤ 4r₂/(1−r₂)²`.  Proof via the
cross-multiplied form `div_le_div_iff₀` and `nlinarith`. -/
private theorem ratio_mono {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ ≤ r₂)
    (hq1 : (0 : ℝ) < 1 - r₁) (hq2 : (0 : ℝ) < 1 - r₂) :
    4 * r₁ / (1 - r₁) ^ 2 ≤ 4 * r₂ / (1 - r₂) ^ 2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (r₂ - r₁), mul_nonneg h0 (le_of_lt hq2), mul_pos hq1 hq2]

/-- **Downward closure of the Kotecky--Preiss region in `r`**: if `0 ≤ r₁ ≤ r₂`, `r₂ < 1`,
and `4r₂/(1−r₂)² < 1`, then `r₁ < 1` and `4r₁/(1−r₁)² < 1`.  The KP region in the variable
`r = Δ²e|t|` is downward closed: a smaller `r` (smaller maximum degree) still satisfies
both conditions. -/
theorem kpRegion_downward_closed {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ ≤ r₂)
    (hr2 : r₂ < 1) (hρ2 : 4 * r₂ / (1 - r₂) ^ 2 < 1) :
    r₁ < 1 ∧ 4 * r₁ / (1 - r₁) ^ 2 < 1 := by
  have hr1 : r₁ < 1 := lt_of_le_of_lt h12 hr2
  refine ⟨hr1, ?_⟩
  have hq1 : (0 : ℝ) < 1 - r₁ := by linarith
  have hq2 : (0 : ℝ) < 1 - r₂ := by linarith
  -- `4r₁/(1−r₁)² ≤ 4r₂/(1−r₂)²` by monotonicity, then `< 1`.
  refine lt_of_le_of_lt ?_ hρ2
  exact ratio_mono h0 h12 hq1 hq2

/-- **Monotonicity of `kpBound` in `r`** (Kotecky--Preiss region).  If `0 ≤ r₁ ≤ r₂`, both
lie in the KP region (`r₂ < 1` and `4r₂/(1−r₂)² < 1`), then the per-site constant — written
in the `r`-variable form `((1−r)(1−4r/(1−r)²))⁻¹` — is monotone increasing: larger at `r₂`.

Proof skeleton: `1−r` is positive and decreasing, `4r/(1−r)²` is increasing, so the product
`(1−r)(1−4r/(1−r)²)` is positive and decreasing, hence its inverse is increasing
(`inv_le_inv_of_le`). -/
theorem kpBound_r_mono_of_le {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ ≤ r₂)
    (hr2 : r₂ < 1) (hρ2 : 4 * r₂ / (1 - r₂) ^ 2 < 1) :
    ((1 - r₁) * (1 - 4 * r₁ / (1 - r₁) ^ 2))⁻¹
      ≤ ((1 - r₂) * (1 - 4 * r₂ / (1 - r₂) ^ 2))⁻¹ := by
  obtain ⟨hr1, hρ1⟩ := kpRegion_downward_closed h0 h12 hr2 hρ2
  have hq1 : (0 : ℝ) < 1 - r₁ := by linarith
  have hq2 : (0 : ℝ) < 1 - r₂ := by linarith
  have hρ1pos : (0 : ℝ) < 1 - 4 * r₁ / (1 - r₁) ^ 2 := by linarith
  have hρ2pos : (0 : ℝ) < 1 - 4 * r₂ / (1 - r₂) ^ 2 := by linarith
  -- denominator at `r₂` is positive and ≤ denominator at `r₁`.
  have hprod2pos : (0 : ℝ) < (1 - r₂) * (1 - 4 * r₂ / (1 - r₂) ^ 2) :=
    mul_pos hq2 hρ2pos
  -- `4r₁/(1−r₁)² ≤ 4r₂/(1−r₂)²` so `1−...` is decreasing.
  have hρmono : 4 * r₁ / (1 - r₁) ^ 2 ≤ 4 * r₂ / (1 - r₂) ^ 2 :=
    ratio_mono h0 h12 hq1 hq2
  have hdenmono : (1 - r₂) * (1 - 4 * r₂ / (1 - r₂) ^ 2)
      ≤ (1 - r₁) * (1 - 4 * r₁ / (1 - r₁) ^ 2) := by
    apply mul_le_mul
    · linarith
    · linarith
    · linarith
    · linarith
  -- inverse reverses the inequality on positive denominators.
  exact inv_anti₀ hprod2pos hdenmono

/-- **Monotonicity of `kpBound` in the maximum degree**.  If `Δ₁ ≤ Δ₂` and both `Δ₁²e|t|`
and `Δ₂²e|t|` lie in the Kotecky--Preiss region (it suffices to assume it for `Δ₂`, since the
region is downward closed in `r`), then `kpBound Δ₁ t ≤ kpBound Δ₂ t`. -/
theorem kpBound_mono_of_degree_le {Δ₁ Δ₂ : ℕ} (hΔ : Δ₁ ≤ Δ₂) (t : ℝ)
    (hr2 : (Δ₂ : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ2 : 4 * ((Δ₂ : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - (Δ₂ : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    kpBound Δ₁ t ≤ kpBound Δ₂ t := by
  set r₁ : ℝ := (Δ₁ : ℝ) ^ 2 * (Real.exp 1 * |t|) with hr1def
  set r₂ : ℝ := (Δ₂ : ℝ) ^ 2 * (Real.exp 1 * |t|) with hr2def
  have he : (0 : ℝ) ≤ Real.exp 1 * |t| := by positivity
  have h0 : 0 ≤ r₁ := by rw [hr1def]; positivity
  have h12 : r₁ ≤ r₂ := by
    rw [hr1def, hr2def]
    have hcast : (Δ₁ : ℝ) ≤ (Δ₂ : ℝ) := by exact_mod_cast hΔ
    have : (Δ₁ : ℝ) ^ 2 ≤ (Δ₂ : ℝ) ^ 2 := by gcongr
    exact mul_le_mul_of_nonneg_right this he
  simpa only [kpBound, hr1def, hr2def] using kpBound_r_mono_of_le h0 h12 hr2 hρ2

/-- **ℤ^d-uniform per-site Mayer bound** (headline).  For the lattice graph `latticeGraph d`
induced on a cubic box `Λ`, with `(2d)²e|t|` in the Kotecky--Preiss region, the per-site total
absolute Mayer expansion sum is bounded by `kpBound (2 d) t`, a constant **independent of the
volume** `Λ`.

The actual maximum degree of the induced lattice graph is at most `2 d`
(`induced_latticeGraph_maxDegree_le`); the bound at the actual maximum degree
(`induced_kp_tsum_per_site_le`) is then dominated by the bound at `2 d` via
`kpBound_mono_of_degree_le`, and the actual-maximum-degree KP hypotheses are discharged from
the `2 d` ones by `kpRegion_downward_closed`. -/
theorem latticeGraph_kp_tsum_per_site_le (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)] {t : ℝ}
    (hkp2d : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ2d : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    (∑' n : ℕ,
          |mayerExpansionTerm (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (n + 1) t|)
        / (Fintype.card (↑Λ : Type _) : ℝ)
      ≤ kpBound (2 * d) t := by
  set G := Ambient.inducedGraph (IsingModel.latticeGraph d) Λ with hG
  have hΔ : G.maxDegree ≤ 2 * d := induced_latticeGraph_maxDegree_le d Λ
  have he : (0 : ℝ) ≤ Real.exp 1 * |t| := by positivity
  -- `r = maxDegree²e|t| ≤ (2d)²e|t|`.
  have h12 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)
      ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|) := by
    apply mul_le_mul_of_nonneg_right _ he
    have hcast : (G.maxDegree : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast hΔ
    gcongr
  have h0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) := by positivity
  -- discharge the actual-maxDegree KP hypotheses from the `2d` ones.
  obtain ⟨hkp, hρ⟩ := kpRegion_downward_closed h0 h12 hkp2d hρ2d
  -- apply the induced-graph per-site bound at the actual maximum degree.
  have hmain := induced_kp_tsum_per_site_le (IsingModel.latticeGraph d) Λ hkp hρ
  refine hmain.trans ?_
  -- and dominate by the `2d` constant via degree monotonicity.
  exact kpBound_mono_of_degree_le hΔ t hkp2d hρ2d

/-- **ℤ^d-uniform per-site Mayer bound along the cubic exhaustion**.  The headline
`latticeGraph_kp_tsum_per_site_le` specialised to the `n`-th stage of `Ambient.cubicExhaustion d`,
giving a per-site Mayer bound `kpBound (2 d) t` uniform over all stages `n`. -/
theorem latticeGraph_kp_tsum_per_site_cubicExhaustion_le (d : ℕ) (n : ℕ)
    [Nonempty (↑((Ambient.cubicExhaustion d).volume n) : Type _)] {t : ℝ}
    (hkp2d : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ2d : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    (∑' k : ℕ, |mayerExpansionTerm
          (Ambient.inducedGraph (IsingModel.latticeGraph d)
            ((Ambient.cubicExhaustion d).volume n)) (k + 1) t|)
        / (Fintype.card (↑((Ambient.cubicExhaustion d).volume n) : Type _) : ℝ)
      ≤ kpBound (2 * d) t :=
  latticeGraph_kp_tsum_per_site_le d ((Ambient.cubicExhaustion d).volume n) hkp2d hρ2d

end IsingModel
