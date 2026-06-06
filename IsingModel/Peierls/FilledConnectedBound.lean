import IsingModel.Peierls.FilledRegionConnected
import IsingModel.Peierls.FilledRegion

/-!
# The filled-connected Peierls bound (FV §3.7.2)

The `+`-boundary Peierls bound restricted to **connected, filled** droplets: the witnessing
droplet is the *filled* down-spin component `filledRegion (downComponent σ i) g`, which is
connected (`isConnectedDroplet_filledRegion`) and filled (`isFilled_filledRegion`), with boundary
in the phase boundary. Restricting to filled droplets makes each contour a *single* edge-connected
curve, the form needed for the volume-independent count.

The ground vertex `g` is taken on the (connected) boundary `B`; for a `+`-configuration `B` is all
up-spins, so it lies in the outside component of the down-droplet, giving `Disjoint F B`.

* `spontaneous_magnetization_plus_filled_connected` — the filled-droplet bound.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, Lemma 3.37, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- **Filled-connected `+`-boundary Peierls bound** (FV §3.7.2): the `+`-state probability that
`σ_i = -1` is bounded by the sum of Peierls weights over **connected, filled** droplets `S ∋ i`
disjoint from the boundary `B`. The witness is the filled down-spin component, connected and
filled, whose boundary is a single contour. -/
theorem spontaneous_magnetization_plus_filled_connected (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (hconn : G.Preconnected) (J β : ℝ) (B : Finset ι) (i g : ι)
    (hBconn : IsConnectedDroplet G B) (hgB : g ∈ B) :
    plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => if σ i = Spin.down then 1 else 0) ≤
    ∑ S ∈ Finset.univ.filter
        (fun S : Finset ι => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S ∧ IsFilled G g S),
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
  have hZ := plusPartitionFunction_pos' G ⟨J, 0, β⟩ B
  unfold plusGibbsExpectation
  -- Step 1: filled-connected indicator bound (filled down-component witnesses)
  have hind : ∀ σ ∈ plusConfigs B,
      (if σ i = Spin.down then (1 : ℝ) else 0) ≤
      ∑ S ∈ Finset.univ.filter
          (fun S : Finset ι =>
            i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S ∧ IsFilled G g S),
        if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 := by
    intro σ hσ
    simp only [plusConfigs, Finset.mem_filter] at hσ
    have hnn : ∀ S ∈ Finset.univ.filter
        (fun S : Finset ι =>
          i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S ∧ IsFilled G g S),
        (0 : ℝ) ≤ if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 :=
      fun S _ => by by_cases h : cutEdges G S ⊆ phaseBoundary G σ <;> simp [h]
    by_cases hi : σ i = Spin.down
    · rw [if_pos hi]
      -- `g ∉ downComponent`: `g ∈ B` is an up-spin, the down-component is down-spins
      have hgnotS : g ∉ downComponent G σ i := by
        intro hgd
        have hd : σ g = Spin.down := (mem_downSpins σ g).mp (downComponent_subset_downSpins hi hgd)
        rw [hσ.2 g hgB] at hd; exact absurd hd (by decide)
      -- `B ⊆ outside` (connected, anchored at `g`, avoids the down-component)
      have hBout : ∀ b ∈ B, b ∈ outsideComponent G (downComponent G σ i) g := by
        intro b hb
        rw [mem_outsideComponent]
        refine reachableWithin_mono ?_ (hBconn g hgB b hb)
        intro x hx
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, fun hxd => ?_⟩
        have hd : σ x = Spin.down := (mem_downSpins σ x).mp (downComponent_subset_downSpins hi hxd)
        rw [hσ.2 x hx] at hd; exact absurd hd (by decide)
      have hdisjFB : Disjoint (filledRegion G (downComponent G σ i) g) B := by
        rw [Finset.disjoint_left]
        intro a haF hab
        exact (mem_filledRegion.mp haF) (hBout a hab)
      have hFmem : filledRegion G (downComponent G σ i) g ∈ Finset.univ.filter
          (fun S : Finset ι =>
            i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S ∧ IsFilled G g S) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          self_mem_filledRegion σ i hgnotS, hdisjFB,
          isConnectedDroplet_filledRegion hconn ⟨i, self_mem_downComponent G σ i⟩
            (isConnectedDroplet_downComponent G σ i) hgnotS,
          isFilled_filledRegion hgnotS⟩
      calc (1 : ℝ)
          = if cutEdges G (filledRegion G (downComponent G σ i) g) ⊆ phaseBoundary G σ then 1
              else 0 :=
            (if_pos (cutEdges_filledRegion_downComponent_subset_phaseBoundary hi hgnotS)).symm
        _ ≤ _ := Finset.single_le_sum hnn hFmem
    · rw [if_neg hi]; exact Finset.sum_nonneg hnn
  -- Step 2: multiply by weight and swap sums
  have hnum : ∑ σ ∈ plusConfigs B,
      (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ ≤
    ∑ S ∈ Finset.univ.filter
        (fun S : Finset ι =>
          i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S ∧ IsFilled G g S),
      ∑ σ ∈ plusConfigs B,
        (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ := by
    calc ∑ σ ∈ plusConfigs B,
          (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ
        ≤ ∑ σ ∈ plusConfigs B,
            (∑ S ∈ Finset.univ.filter
                (fun S => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S ∧ IsFilled G g S),
              if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
            boltzmannWeight G ⟨J, 0, β⟩ σ :=
          Finset.sum_le_sum fun σ hσ => mul_le_mul_of_nonneg_right (hind σ hσ)
            (boltzmannWeight_pos G ⟨J, 0, β⟩ σ).le
      _ = ∑ σ ∈ plusConfigs B,
            ∑ S ∈ Finset.univ.filter
                (fun S => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S ∧ IsFilled G g S),
              (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
              boltzmannWeight G ⟨J, 0, β⟩ σ :=
          Finset.sum_congr rfl fun σ _ => by rw [Finset.sum_mul]
      _ = _ := Finset.sum_comm
  -- Step 3: per-droplet Peierls bound (flip involution, S ∩ B = ∅)
  have hpeierls : ∀ S ∈ Finset.univ.filter
      (fun S : Finset ι => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S ∧ IsFilled G g S),
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
              (fun S => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S ∧ IsFilled G g S),
            ∑ σ ∈ plusConfigs B,
              (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
              boltzmannWeight G ⟨J, 0, β⟩ σ) :=
        mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hZ.le)
    _ = ∑ S ∈ Finset.univ.filter
          (fun S => i ∈ S ∧ Disjoint S B ∧ IsConnectedDroplet G S ∧ IsFilled G g S),
          (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          (∑ σ ∈ plusConfigs B,
            (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
            boltzmannWeight G ⟨J, 0, β⟩ σ) := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum hpeierls

end IsingModel
