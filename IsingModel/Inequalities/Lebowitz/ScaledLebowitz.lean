import IsingModel.Inequalities.Lebowitz.WeightedSystem
import IsingModel.Inequalities.Lebowitz.Theorem431
import IsingModel.CouplingDerivative

/-!
# The Lebowitz machinery for the scaled (non-uniform) couplings

The scaled model (`CouplingDerivative.lean`) has per-edge couplings
`K_e = s·J` on a distinguished edge set `E₀ ⊆ E` and `K_e = J` elsewhere;
for `s ≥ 0` all per-edge couplings are non-negative. This file instantiates
the abstract-weight duplicate-variable layer (`WeightedSystem.lean`) for the
scaled Boltzmann weight: the fourfold scaled weight is the exponential of a
ferromagnetic sum of joint u-monomials with the per-edge coefficient
`scaledQuadCoeff` (the `−β(1−s)J` correction on `E₀` combines with the base
coupling `βJ` and never appears with a negative sign), so it has
non-negative u-moments and the whole `t`/`q` bracket chain applies.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, Theorem 4.3.1 and
  Corollaries 4.3.2–4.3.3, pp. 59–61
-/

namespace IsingModel

namespace Lebowitz

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The per-edge coefficient of the scaled fourfold exponent: `β·s·J/4` on
the distinguished edges, `β·J/4` elsewhere. -/
noncomputable def scaledQuadCoeff (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ)
    (s : ℝ) (e : Sym2 ι) : ℝ :=
  if e ∈ E₀ then p.β * (s * p.J) / 4 else p.β * p.J / 4

omit [Fintype ι] in
/-- The scaled per-edge coefficient is non-negative for ferromagnetic
parameters and `s ≥ 0`. -/
theorem scaledQuadCoeff_nonneg (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (s : ℝ) (hs : 0 ≤ s) (e : Sym2 ι) :
    0 ≤ scaledQuadCoeff E₀ p s e := by
  unfold scaledQuadCoeff
  have hβ := hf.hβ
  have hJ := hf.hJ
  split_ifs <;> positivity

omit [DecidableEq ι] [Fintype ι] in
/-- **Per-edge Hadamard correction identity**: the `−β(1−s)J`-weighted
four-copy edge-spin sum is the `Fin 4`-sum of u-edge quantities with
coefficient `−β(1−s)J/4`. -/
theorem correction_sum_eq_uEdge (p : IsingParams ℝ) (s : ℝ) (e : Sym2 ι)
    (v : QuadConfig ι) :
    ∑ r : Fin 4, -p.β * (1 - s) * p.J / 4 * uEdge r e v
      = -p.β * (1 - s) * p.J *
        (edgeSpin (K := ℝ) v.1 e + edgeSpin (K := ℝ) v.2.1 e +
          edgeSpin (K := ℝ) v.2.2.1 e + edgeSpin (K := ℝ) v.2.2.2 e) := by
  induction e using Sym2.ind with
  | _ i j =>
    rw [Fin.sum_univ_four]
    unfold uEdge edgeSpin
    simp only [Sym2.lift_mk]
    unfold uSite₁ uSite₂ uSite₃ uSite₄ u₁ u₂ u₃ u₄ siteQuadAt s₁ s₂ s₃ s₄
    ring

/-- **The scaled fourfold exponent identity** (the scaled (4.3.5)): the
fourfold scaled weight is the exponential of the `scaledQuadCoeff`-weighted
u-edge sum times the field exponential. -/
theorem wQuadWeight_scaled_eq_exp (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀ : E₀ ⊆ G.edgeFinset) (p : IsingParams ℝ)
    (s : ℝ) (v : QuadConfig ι) :
    wQuadWeight (scaledBoltzmannWeight G E₀ p s) v
      = Real.exp (∑ er ∈ G.edgeFinset ×ˢ (Finset.univ : Finset (Fin 4)),
          scaledQuadCoeff E₀ p s er.1 * uEdge er.2 er.1 v) *
        Real.exp (∑ i, p.β * p.h * uSite₁ i v) := by
  have hquad : wQuadWeight (scaledBoltzmannWeight G E₀ p s) v
      = quadWeight G p v *
        Real.exp (∑ er ∈ E₀ ×ˢ (Finset.univ : Finset (Fin 4)),
          -p.β * (1 - s) * p.J / 4 * uEdge er.2 er.1 v) := by
    have hcorr : ∑ er ∈ E₀ ×ˢ (Finset.univ : Finset (Fin 4)),
        -p.β * (1 - s) * p.J / 4 * uEdge er.2 er.1 v
        = (-p.β * (1 - s) * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) v.1 e) +
          (-p.β * (1 - s) * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) v.2.1 e) +
          (-p.β * (1 - s) * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) v.2.2.1 e) +
          -p.β * (1 - s) * p.J * ∑ e ∈ E₀, edgeSpin (K := ℝ) v.2.2.2 e := by
      rw [Finset.sum_product]
      rw [Finset.sum_congr rfl fun e _ => correction_sum_eq_uEdge p s e v]
      simp only [← Finset.mul_sum]
      rw [show (∑ e ∈ E₀, (edgeSpin (K := ℝ) v.1 e + edgeSpin (K := ℝ) v.2.1 e +
          edgeSpin (K := ℝ) v.2.2.1 e + edgeSpin (K := ℝ) v.2.2.2 e))
          = (∑ e ∈ E₀, edgeSpin (K := ℝ) v.1 e) +
            (∑ e ∈ E₀, edgeSpin (K := ℝ) v.2.1 e) +
            (∑ e ∈ E₀, edgeSpin (K := ℝ) v.2.2.1 e) +
            ∑ e ∈ E₀, edgeSpin (K := ℝ) v.2.2.2 e from by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib]]
      ring
    rw [hcorr]
    unfold wQuadWeight scaledBoltzmannWeight quadWeight
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  rw [hquad, quadWeight_eq_exp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have hext : ∑ er ∈ E₀ ×ˢ (Finset.univ : Finset (Fin 4)),
      -p.β * (1 - s) * p.J / 4 * uEdge er.2 er.1 v
      = ∑ er ∈ G.edgeFinset ×ˢ (Finset.univ : Finset (Fin 4)),
          (if er.1 ∈ E₀ then -p.β * (1 - s) * p.J / 4 else 0) *
            uEdge er.2 er.1 v := by
    have h1 : ∑ er ∈ E₀ ×ˢ (Finset.univ : Finset (Fin 4)),
        -p.β * (1 - s) * p.J / 4 * uEdge er.2 er.1 v
        = ∑ er ∈ E₀ ×ˢ (Finset.univ : Finset (Fin 4)),
            (if er.1 ∈ E₀ then -p.β * (1 - s) * p.J / 4 else 0) *
              uEdge er.2 er.1 v :=
      Finset.sum_congr rfl fun er her => by
        rw [if_pos (Finset.mem_product.1 her).1]
    rw [h1]
    exact Finset.sum_subset
      (Finset.product_subset_product hE₀ (Finset.Subset.refl _))
      (fun er _ hnot => by
        have h2 : er.1 ∉ E₀ := fun hmem => hnot
          (Finset.mem_product.2 ⟨hmem, Finset.mem_univ _⟩)
        rw [if_neg h2, zero_mul])
  rw [hext]
  have hcomb : ∑ er ∈ G.edgeFinset ×ˢ (Finset.univ : Finset (Fin 4)),
      p.β * p.J / 4 * uEdge er.2 er.1 v +
      ∑ er ∈ G.edgeFinset ×ˢ (Finset.univ : Finset (Fin 4)),
        (if er.1 ∈ E₀ then -p.β * (1 - s) * p.J / 4 else 0) *
          uEdge er.2 er.1 v
      = ∑ er ∈ G.edgeFinset ×ˢ (Finset.univ : Finset (Fin 4)),
          scaledQuadCoeff E₀ p s er.1 * uEdge er.2 er.1 v := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun er _ => ?_
    unfold scaledQuadCoeff
    split_ifs <;> ring
  linarith [hcomb]

/-- **The scaled fourfold weight has non-negative u-moments** (ferromagnetic
parameters, `s ≥ 0`): the scaled Theorem 4.3.1 input. -/
theorem hasNonnegUMoments_wQuadWeight_scaled (G : SimpleGraph ι)
    [Fintype G.edgeSet] (E₀ : Finset (Sym2 ι)) (hE₀ : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (s : ℝ) (hs : 0 ≤ s) :
    HasNonnegUMoments (wQuadWeight (scaledBoltzmannWeight G E₀ p s)) := by
  have hKsite : 0 ≤ p.β * p.h := mul_nonneg hf.hβ.le hf.hh
  have hrw : wQuadWeight (scaledBoltzmannWeight G E₀ p s)
      = fun v => Real.exp (∑ er ∈ G.edgeFinset ×ˢ (Finset.univ : Finset (Fin 4)),
            scaledQuadCoeff E₀ p s er.1 * uEdge er.2 er.1 v) *
          (Real.exp (∑ i, p.β * p.h * uSite₁ i v) * (fun _ => (1 : ℝ)) v) := by
    funext v
    rw [wQuadWeight_scaled_eq_exp G E₀ hE₀]
    ring
  rw [hrw]
  refine hasNonnegUMoments_exp_sum_mul _ _ ?_
    (hasNonnegUMoments_exp_sum_mul _ _ ?_ hasNonnegUMoments_one)
  · rintro ⟨e, r⟩ her
    have he : e ∈ G.edgeFinset := (Finset.mem_product.mp her).1
    suffices h : ∃ (K : ℝ) (k₀ l₀ m₀ n₀ : ι → ℕ), 0 ≤ K ∧
        ∀ v, scaledQuadCoeff E₀ p s e * uEdge r e v
          = K * uMonomial k₀ l₀ m₀ n₀ v from h
    induction e using Sym2.ind with
    | _ i j =>
      have hadj : G.Adj i j := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      obtain ⟨k₀, l₀, m₀, n₀, heq⟩ := uEdge_eq_uMonomial hadj.ne r
      exact ⟨scaledQuadCoeff E₀ p s s(i, j), k₀, l₀, m₀, n₀,
        scaledQuadCoeff_nonneg E₀ p hf s hs _, fun v => by rw [heq v]⟩
  · intro i _
    exact ⟨p.β * p.h, _, _, _, _, hKsite, fun v => by
      rw [uMonomial_single₁ i v]⟩

end Lebowitz

end IsingModel
