import IsingModel.Peierls.ConnectedDroplet

/-!
# Connected-droplet `+`-boundary Peierls bound (FV §3.7.2)

The `+`-boundary spontaneous-magnetization Peierls bound, with the contour sum restricted
to **connected** droplets:

`⟨1_{σ_i=-1}⟩⁺_B ≤ ∑_{S ∋ i, S∩B=∅, S connected} exp(-2βJ·|cut S|)`.

The connected refinement (witnessed by `downComponent`) is what makes the contour sum
volume-independently countable, towards `m*(β)>0` (Issue #3631). The probabilistic core
(the flip involution / Peierls ratio) is unchanged from `spontaneous_magnetization_plus`;
only the witnessing set and the index filter become connected.

* `spontaneous_magnetization_plus_connected` — the connected-droplet bound.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, Lemma 3.37, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- **Connected-droplet `+`-boundary Peierls bound** (FV §3.7.2): the `+`-state probability
that `σ_i = -1` is bounded by the sum of Peierls weights over **connected** droplets `S`
containing `i` and disjoint from the boundary `B`. The connected component of `i` in the
down-spins (`downComponent`) witnesses the bound. -/
theorem spontaneous_magnetization_plus_connected (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (B : Finset ι) (i : ι) :
    plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => if σ i = Spin.down then 1 else 0) ≤
    ∑ S ∈ Finset.univ.filter
        (fun S : Finset ι => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S),
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
  have hZ := plusPartitionFunction_pos' G ⟨J, 0, β⟩ B
  unfold plusGibbsExpectation
  -- Step 1: connected-droplet indicator bound (downComponent witnesses)
  have hind : ∀ σ ∈ plusConfigs B,
      (if σ i = Spin.down then (1 : ℝ) else 0) ≤
      ∑ S ∈ Finset.univ.filter
          (fun S : Finset ι => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S),
        if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 := by
    intro σ hσ
    simp only [plusConfigs, Finset.mem_filter] at hσ
    have hnn : ∀ S ∈ Finset.univ.filter
        (fun S : Finset ι => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S),
        (0 : ℝ) ≤ if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 :=
      fun S _ => by by_cases h : cutEdges G S ⊆ phaseBoundary G σ <;> simp [h]
    by_cases hi : σ i = Spin.down
    · rw [if_pos hi]
      have hdisj : Disjoint (downComponent G σ i) B :=
        (downSpins_disjoint_boundary σ B hσ.2).mono_left (downComponent_subset_downSpins hi)
      have hmem : downComponent G σ i ∈ Finset.univ.filter
          (fun S : Finset ι => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, self_mem_downComponent G σ i, hdisj,
          isConnectedDroplet_downComponent G σ i⟩
      calc (1 : ℝ)
          = if cutEdges G (downComponent G σ i) ⊆ phaseBoundary G σ then 1 else 0 :=
            (if_pos (cutEdges_downComponent_subset_phaseBoundary hi)).symm
        _ ≤ _ := Finset.single_le_sum hnn hmem
    · rw [if_neg hi]; exact Finset.sum_nonneg hnn
  -- Step 2: multiply by weight and swap sums
  have hnum : ∑ σ ∈ plusConfigs B,
      (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ ≤
    ∑ S ∈ Finset.univ.filter
        (fun S : Finset ι => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S),
      ∑ σ ∈ plusConfigs B,
        (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ := by
    calc ∑ σ ∈ plusConfigs B,
          (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ
        ≤ ∑ σ ∈ plusConfigs B,
            (∑ S ∈ Finset.univ.filter
                (fun S => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S),
              if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
            boltzmannWeight G ⟨J, 0, β⟩ σ :=
          Finset.sum_le_sum fun σ hσ => mul_le_mul_of_nonneg_right (hind σ hσ)
            (boltzmannWeight_pos G ⟨J, 0, β⟩ σ).le
      _ = ∑ σ ∈ plusConfigs B,
            ∑ S ∈ Finset.univ.filter
                (fun S => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S),
              (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
              boltzmannWeight G ⟨J, 0, β⟩ σ := by
          exact Finset.sum_congr rfl fun σ _ => by rw [Finset.sum_mul]
      _ = _ := Finset.sum_comm
  -- Step 3: per-droplet Peierls bound (flip involution, S ∩ B = ∅)
  have hpeierls : ∀ S ∈ Finset.univ.filter
      (fun S : Finset ι => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S),
      (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
        (∑ σ ∈ plusConfigs B,
          (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ) ≤
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have hSB : Disjoint S B := hS.2.1
    have hfactor : ∀ σ ∈ plusConfigs B,
        (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ ≤
        Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
          boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ) := by
      intro σ _
      by_cases hsub : cutEdges G S ⊆ phaseBoundary G σ
      · simp only [if_pos hsub, one_mul]
        exact le_of_eq (boltzmannWeight_flipSet_ratio G J β S σ hsub)
      · simp only [if_neg hsub, zero_mul]
        exact mul_nonneg (Real.exp_nonneg _) (boltzmannWeight_pos G ⟨J, 0, β⟩ _).le
    have hflip_bc : ∀ σ ∈ plusConfigs B, Config.flipSet S σ ∈ plusConfigs B := by
      intro σ hσ
      simp only [plusConfigs, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      intro b hb
      simp only [Config.flipSet]
      rw [if_neg (Finset.disjoint_left.mp hSB · hb)]
      exact hσ b hb
    calc (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          (∑ σ ∈ plusConfigs B,
            (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
            boltzmannWeight G ⟨J, 0, β⟩ σ)
        ≤ (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
            (∑ σ ∈ plusConfigs B,
              Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
              boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ hσ => hfactor σ hσ)
            (inv_nonneg.mpr hZ.le)
      _ = (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
            (Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
              ∑ σ ∈ plusConfigs B,
                boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ)) := by
          congr 1; rw [Finset.mul_sum]
      _ ≤ (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
            (Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
              plusPartitionFunction G ⟨J, 0, β⟩ B) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hZ.le)
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          unfold plusPartitionFunction
          have hsub : (plusConfigs B).image (Config.flipSet S) ⊆ plusConfigs B :=
            Finset.image_subset_iff.mpr hflip_bc
          calc ∑ σ ∈ plusConfigs B, boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ)
              = ∑ σ ∈ (plusConfigs B).image (Config.flipSet S),
                  boltzmannWeight G ⟨J, 0, β⟩ σ := by
                rw [Finset.sum_image fun σ₁ _ σ₂ _ h => Config.flipSet_injective S h]
            _ ≤ ∑ σ ∈ plusConfigs B, boltzmannWeight G ⟨J, 0, β⟩ σ :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub
                  (fun σ _ _ => (boltzmannWeight_pos G ⟨J, 0, β⟩ σ).le)
      _ = Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by field_simp [hZ.ne']
  -- Assemble
  calc (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
        (∑ σ ∈ plusConfigs B,
          (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ)
      ≤ (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          (∑ S ∈ Finset.univ.filter
              (fun S => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S),
            ∑ σ ∈ plusConfigs B,
              (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
              boltzmannWeight G ⟨J, 0, β⟩ σ) :=
        mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hZ.le)
    _ = ∑ S ∈ Finset.univ.filter
          (fun S => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S),
          (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          (∑ σ ∈ plusConfigs B,
            (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
            boltzmannWeight G ⟨J, 0, β⟩ σ) := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum hpeierls

end IsingModel
