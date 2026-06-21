import IsingModel.Hamiltonian
import IsingModel.Dobrushin.SingleSiteInfluence

/-!
# Single-site Hamiltonian decomposition (GJ §17.1 / Dobrushin uniqueness)

Toward the lattice single-site conditional Gibbs distribution (and thence the single-site Dobrushin
influence matrix), this file computes the Ising Hamiltonian under updating a single site `x` to `up`
versus `down`, the rest fixed to `η`. Only the edges incident to `x` and the field term at `x`
change, giving
`H(η[x↦up]) − H(η[x↦down]) = −2·(J·∑_{y∼x} sign(η_y) + h)` — twice the local field at `x`.

* `sign_up` / `sign_down` — the `±1` spin-sign values.
* `externalFieldEnergy_update_up_sub_down` — the single-site field-energy gap `−2h`.
* `interactionEnergy_update_up_sub_down` — the single-site interaction-energy gap
  `−2·J·∑_{y∼x} sign(η_y)`.
* `hamiltonian_update_up_sub_down` — the total single-site energy gap `−2·(J·neighbour-sum + h)`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1.
-/

namespace IsingModel

namespace Dobrushin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The spin sign of `up` is `1`**. -/
theorem sign_up : Spin.sign ℝ Spin.up = 1 := by simp [Spin.sign, Spin.toSign]

/-- **The spin sign of `down` is `−1`**. -/
theorem sign_down : Spin.sign ℝ Spin.down = -1 := by simp [Spin.sign, Spin.toSign]

/-- **The single-site field-energy gap**: updating site `x` from `down` to `up` (rest fixed to `η`)
changes the external-field energy by `−2h`, since only site `x`'s field term changes. -/
theorem externalFieldEnergy_update_up_sub_down (h : ℝ) (x : ι) (η : Config ι) :
    externalFieldEnergy h (Function.update η x Spin.up)
      - externalFieldEnergy h (Function.update η x Spin.down) = -2 * h := by
  unfold externalFieldEnergy
  have hsplit : ∀ s : Spin, ∑ i, Spin.sign ℝ ((Function.update η x s) i)
      = Spin.sign ℝ s + ∑ i ∈ Finset.univ.erase x, Spin.sign ℝ (η i) := by
    intro s
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ x), Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hsplit, hsplit, sign_up, sign_down]
  ring

omit [Fintype ι] in
/-- **`edgeSpin` is unchanged by a single-site update away from the edge**: if `x ∉ e`, updating the
configuration at `x` does not change the per-edge spin product on `e`. -/
theorem edgeSpin_update_of_not_mem {x : ι} {s : Spin} {e : Sym2 ι} (he : x ∉ e) (η : Config ι) :
    edgeSpin (K := ℝ) (Function.update η x s) e = edgeSpin (K := ℝ) η e := by
  induction e with
  | h a b =>
    have ha : a ≠ x := fun h => he (h ▸ Sym2.mem_mk_left a b)
    have hb : b ≠ x := fun h => he (h ▸ Sym2.mem_mk_right a b)
    simp only [edgeSpin, Sym2.lift_mk, Function.update_of_ne ha, Function.update_of_ne hb]

/-- **The single-site interaction-energy gap**: updating site `x` from `down` to `up` (rest fixed to
`η`) changes the interaction energy by `−2·J·∑_{y∼x} sign(η_y)`, since only the edges incident to
`x` change, each contributing `2·sign(η_y)` to the per-edge spin sum. -/
theorem interactionEnergy_update_up_sub_down (G : SimpleGraph ι) [Fintype G.edgeSet]
    [DecidableRel G.Adj] (J : ℝ) (x : ι) (η : Config ι) :
    interactionEnergy G J (Function.update η x Spin.up)
      - interactionEnergy G J (Function.update η x Spin.down)
      = -2 * J * ∑ y ∈ G.neighborFinset x, Spin.sign ℝ (η y) := by
  classical
  unfold interactionEnergy
  have hkey : ∑ e ∈ G.edgeFinset,
      (edgeSpin (K := ℝ) (Function.update η x Spin.up) e
        - edgeSpin (K := ℝ) (Function.update η x Spin.down) e)
      = 2 * ∑ y ∈ G.neighborFinset x, Spin.sign ℝ (η y) := by
    rw [← Finset.sum_filter_add_sum_filter_not G.edgeFinset (fun e => x ∈ e)]
    have hnot : ∑ e ∈ G.edgeFinset.filter (fun e => ¬ x ∈ e),
        (edgeSpin (K := ℝ) (Function.update η x Spin.up) e
          - edgeSpin (K := ℝ) (Function.update η x Spin.down) e) = 0 := by
      refine Finset.sum_eq_zero fun e he => ?_
      have hxe : x ∉ e := (Finset.mem_filter.mp he).2
      rw [edgeSpin_update_of_not_mem hxe, edgeSpin_update_of_not_mem hxe, sub_self]
    rw [hnot, add_zero, Finset.mul_sum]
    refine Finset.sum_bij' (fun e he => Sym2.Mem.other (Finset.mem_filter.mp he).2)
      (fun y hy => s(x, y)) ?_ ?_ ?_ ?_ ?_
    · -- forward into neighborFinset
      intro e he
      have hx : x ∈ e := (Finset.mem_filter.mp he).2
      rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_edgeSet, Sym2.other_spec hx]
      exact (G.mem_edgeFinset.mp (Finset.mem_filter.mp he).1)
    · -- backward into the incident-edge filter
      intro y hy
      refine Finset.mem_filter.mpr ⟨G.mem_edgeFinset.mpr ?_, Sym2.mem_mk_left x y⟩
      exact (SimpleGraph.mem_neighborFinset _ _ _).mp hy
    · -- left inverse: `s(x, other e) = e`
      intro e he
      exact Sym2.other_spec (Finset.mem_filter.mp he).2
    · -- right inverse: `other (s(x, y)) = y`
      intro y hy
      have hadj : G.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
      have hspec : s(x, Sym2.Mem.other (Sym2.mem_mk_left x y)) = s(x, y) :=
        Sym2.other_spec (Sym2.mem_mk_left x y)
      rw [Sym2.eq_iff] at hspec
      rcases hspec with ⟨_, h⟩ | ⟨hxy, _⟩
      · exact h
      · exact absurd hxy hadj.ne
    · -- value: `edgeSpin↑ e − edgeSpin↓ e = 2·sign(η (other e))`
      intro e he
      have hx : x ∈ e := (Finset.mem_filter.mp he).2
      set y := Sym2.Mem.other hx with hydef
      have hspec : s(x, y) = e := Sym2.other_spec hx
      have hyx : y ≠ x := by
        have hedge := G.mem_edgeFinset.mp (Finset.mem_filter.mp he).1
        rw [← hspec, SimpleGraph.mem_edgeSet] at hedge
        exact hedge.ne'
      have hup : edgeSpin (K := ℝ) (Function.update η x Spin.up) e = Spin.sign ℝ (η y) := by
        conv_lhs => rw [← hspec]
        simp [edgeSpin, Function.update_self, Function.update_of_ne hyx, sign_up]
      have hdn : edgeSpin (K := ℝ) (Function.update η x Spin.down) e
          = -Spin.sign ℝ (η y) := by
        conv_lhs => rw [← hspec]
        simp [edgeSpin, Function.update_self, Function.update_of_ne hyx, sign_down]
      rw [hup, hdn]; ring
  rw [← mul_sub, ← Finset.sum_sub_distrib, hkey]
  ring

/-- **The single-site Hamiltonian gap**: `H(η[x↦up]) − H(η[x↦down]) = −2·(J·∑_{y∼x} sign(η_y) + h)`,
twice the local field at `x`. -/
theorem hamiltonian_update_up_sub_down (G : SimpleGraph ι) [Fintype G.edgeSet]
    [DecidableRel G.Adj] (p : IsingParams ℝ) (x : ι) (η : Config ι) :
    hamiltonian G p (Function.update η x Spin.up)
      - hamiltonian G p (Function.update η x Spin.down)
      = -2 * (p.J * (∑ y ∈ G.neighborFinset x, Spin.sign ℝ (η y)) + p.h) := by
  unfold hamiltonian
  rw [show (interactionEnergy G p.J (Function.update η x Spin.up)
        + externalFieldEnergy p.h (Function.update η x Spin.up))
      - (interactionEnergy G p.J (Function.update η x Spin.down)
        + externalFieldEnergy p.h (Function.update η x Spin.down))
      = (interactionEnergy G p.J (Function.update η x Spin.up)
        - interactionEnergy G p.J (Function.update η x Spin.down))
        + (externalFieldEnergy p.h (Function.update η x Spin.up)
          - externalFieldEnergy p.h (Function.update η x Spin.down)) by ring,
    interactionEnergy_update_up_sub_down, externalFieldEnergy_update_up_sub_down]
  ring

end Dobrushin

end IsingModel
