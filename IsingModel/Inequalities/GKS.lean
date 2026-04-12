import IsingModel.Inequalities.NonnegCorrelations

/-!
# GKS (Griffiths) inequalities

The first and second Griffiths inequalities for the ferromagnetic Ising model.

References:
- Glimm–Jaffe, *Quantum Physics*, Theorem 4.1.1 (GKS-I)
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, Theorem 3.49 (GKS-I/II)
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Numerator of the Gibbs expectation -/

/-- The unnormalized expectation (numerator): `∑_σ F(σ) · exp(-β H(σ))`. -/
noncomputable def numerator (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ) : ℝ :=
  ∑ σ : Config ι, F σ * boltzmannWeight G p σ

/-- The Gibbs expectation equals `Z⁻¹ · numerator`. -/
theorem gibbsExpectation_eq_div (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ) :
    gibbsExpectation G p F = (partitionFunction G p)⁻¹ * numerator G p F := by
  unfold gibbsExpectation numerator
  rfl

/-- If the numerator is non-negative, then the Gibbs expectation is non-negative. -/
theorem gibbsExpectation_nonneg_of_numerator_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ)
    (hnum : 0 ≤ numerator G p F) :
    0 ≤ gibbsExpectation G p F := by
  rw [gibbsExpectation_eq_div]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt (partitionFunction_pos G p))) hnum

/-! ## Boltzmann weight HNC -/

/-- The Boltzmann weight has non-negative correlations for ferromagnetic parameters.
Proved by showing `boltzmannWeight = ∏ exp(K_e · edgeSpin) * ∏ exp(K_i · sign)`
and applying `hasNonnegCorrelations_edge_site_product`. -/
theorem boltzmannWeight_hasNonnegCorrelations (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    HasNonnegCorrelations (boltzmannWeight G p) := by
  -- boltzmannWeight = ∏_e exp(βJ edgeSpin) * ∏_i exp(βh sign)
  -- Apply hasNonnegCorrelations_edge_site_product with K_e = βJ, K_i = βh
  intro S
  have h := hasNonnegCorrelations_edge_site_product G
    (fun _ => p.β * p.J) (fun _ => p.β * p.h)
    (fun _ _ => mul_nonneg hf.hβ.le hf.hJ)
    (fun _ => mul_nonneg hf.hβ.le hf.hh) S
  -- h : HNC for ∏ exp(βJ edgeSpin) * ∏ exp(βh sign)
  -- Show this equals boltzmannWeight
  have hbw : ∀ σ : Config ι, boltzmannWeight G p σ =
      (∏ e ∈ G.edgeFinset, Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) *
      (∏ i : ι, Real.exp (p.β * p.h * Spin.sign ℝ (σ i))) := by
    intro σ
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    rw [show -p.β * (-(p.J) * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e +
        -(p.h) * ∑ i : ι, Spin.sign ℝ (σ i)) =
      (∑ e ∈ G.edgeFinset, p.β * p.J * edgeSpin (K := ℝ) σ e) +
      (∑ i : ι, p.β * p.h * Spin.sign ℝ (σ i)) from by
        simp only [← Finset.mul_sum]; ring]
    rw [Real.exp_add, Real.exp_sum, Real.exp_sum]
  simp_rw [hbw]
  exact h

/-- The numerator of `⟨σ^A⟩` is non-negative for ferromagnetic parameters. -/
theorem gks_numerator_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset ι) :
    0 ≤ numerator G p (spinProduct A) :=
  boltzmannWeight_hasNonnegCorrelations G p hf A

/-! ## GKS-I: main theorem -/

/-- **First Griffiths inequality (GKS-I)**: For a ferromagnetic Ising model
(`J ≥ 0`, `h ≥ 0`, `β > 0`), all correlation functions are non-negative:
`⟨σ^A⟩ ≥ 0` for any subset `A`. -/
theorem gks_first (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset ι) :
    0 ≤ correlation G p A := by
  unfold correlation
  exact gibbsExpectation_nonneg_of_numerator_nonneg G p _ (gks_numerator_nonneg G p hf A)

/-! ## General coupling GKS-I -/

/-! ## GKS-II: second Griffiths inequality -/

/-- The duplicate variable sum: `Σ_{ω,ω'} ω^A(ω^B - ω'^B) w(ω)w(ω')`.
Equals `Z² (⟨σ^{AΔB}⟩ - ⟨σ^A⟩⟨σ^B⟩)` after unfolding. -/
private noncomputable def duplicateSum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A B : Finset ι) : ℝ :=
  ∑ ω : Config ι, ∑ ω' : Config ι,
    spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
    boltzmannWeight G p ω * boltzmannWeight G p ω'

/-- The duplicate sum equals `Z²(corr(AΔB) - corr(A)·corr(B))`. -/
private theorem duplicateSum_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A B : Finset ι) :
    duplicateSum G p A B =
    (partitionFunction G p) ^ 2 *
      (correlation G p (symmDiff A B) - correlation G p A * correlation G p B) := by
  have hZ := partitionFunction_ne_zero G p
  unfold duplicateSum correlation gibbsExpectation
  -- LHS = Σ_ω Σ_ω' σ^A(σ^B - σ'^B) w w'
  --     = Σ_ω σ^A σ^B w · Z - Σ_ω σ^A w · Σ_ω' σ'^B w'
  --     = Z · Σ σ^{AΔB} w - (Σ σ^A w)(Σ σ^B w)
  -- RHS = Z² · (Z⁻¹ Σ σ^{AΔB} w - Z⁻¹ Σ σ^A w · Z⁻¹ Σ σ^B w)
  --     = Z · Σ σ^{AΔB} w - (Σ σ^A w)(Σ σ^B w)
  -- Rewrite σ^A · σ^B = σ^{AΔB} in the LHS
  have hmul : ∀ ω : Config ι, spinProduct A ω * spinProduct B ω =
      spinProduct (symmDiff A B) ω := fun ω => spinProduct_mul A B ω
  -- Expand: LHS = Σ_ω (σ^{AΔB}_ω · Z - (Σ σ^A w)(σ^B_ω)) · w_ω ... complicated
  -- Strategy: rewrite both sides to the same expression and use ring/field_simp
  rw [sq]
  have hZne := partitionFunction_ne_zero G p
  field_simp
  -- Expand double sum: Σ_ω Σ_{ω'} f(ω)(g(ω)-g(ω')) w(ω) w(ω')
  -- = Σ_ω f(ω)g(ω)w(ω) · Σ_{ω'} w(ω') - Σ_ω f(ω)w(ω) · Σ_{ω'} g(ω')w(ω')
  have step1 : ∀ ω : Config ι,
      ∑ ω' : Config ι, spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
        boltzmannWeight G p ω * boltzmannWeight G p ω' =
      spinProduct A ω * spinProduct B ω * boltzmannWeight G p ω *
        ∑ ω', boltzmannWeight G p ω' -
      spinProduct A ω * boltzmannWeight G p ω *
        ∑ ω', spinProduct B ω' * boltzmannWeight G p ω' := by
    intro ω
    simp_rw [show ∀ ω' : Config ι,
        spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
        boltzmannWeight G p ω * boltzmannWeight G p ω' =
        spinProduct A ω * spinProduct B ω * boltzmannWeight G p ω *
        boltzmannWeight G p ω' -
        spinProduct A ω * boltzmannWeight G p ω *
        (spinProduct B ω' * boltzmannWeight G p ω')
      from fun ω' => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp_rw [step1, Finset.sum_sub_distrib, hmul]
  unfold partitionFunction
  simp_rw [← Finset.sum_mul]
  ring

/-- The modified weight for the duplicate variable proof.
For fixed `t : Config ι`, this is `exp(Σ_C K_C(1 + t^C) ω^C)` where
the sum runs over edges (K = βJ, C = {i,j}) and sites (K = βh, C = {i}).
The factor `(1 + t^C)` doubles or zeroes each coupling. -/
private noncomputable def modifiedWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (t ω : Config ι) : ℝ :=
  (∏ e ∈ G.edgeFinset, Real.exp (p.β * p.J * (1 + edgeSpin (K := ℝ) t e) *
      edgeSpin (K := ℝ) ω e)) *
  (∏ i : ι, Real.exp (p.β * p.h * (1 + Spin.sign ℝ (t i)) * Spin.sign ℝ (ω i)))

/-- The variable-changed form of the duplicate sum.
`Σ_t (1 - t^B) · Σ_ω ω^{AΔB} · modifiedWeight(t, ω)` -/
private noncomputable def duplicateSumChanged (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A B : Finset ι) : ℝ :=
  ∑ t : Config ι, (1 - spinProduct B t) *
    ∑ ω : Config ι, spinProduct (symmDiff A B) ω * modifiedWeight G p t ω

/-- The duplicate sum equals its variable-changed form.
Change of variables: ω' ↦ t where t_i = ω_i · ω'_i (Spin.mul).
Reference: Friedli–Velenik, pp. 127–128. -/
private theorem duplicateSum_eq_changed (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A B : Finset ι) :
    duplicateSum G p A B = duplicateSumChanged G p A B := by
  unfold duplicateSum duplicateSumChanged
  -- For each fixed ω, define bijection on Config: ω' ↦ t where t_i = Spin.mul (ω i) (ω' i)
  -- Step 1: Transform each inner sum and rewrite summand
  have hinner : ∀ ω : Config ι,
      ∑ ω', spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
        boltzmannWeight G p ω * boltzmannWeight G p ω' =
      ∑ t, (1 - spinProduct B t) *
        (spinProduct (symmDiff A B) ω * modifiedWeight G p t ω) := by
    intro ω
    -- Change variables: ω' ↦ t = fun i => Spin.mul (ω i) (ω' i)
    let φ : Config ι → Config ι := fun ω' i => Spin.mul (ω i) (ω' i)
    have hφ_inv : Function.Involutive φ := fun t => by ext i; simp [φ, Spin.mul_mul_cancel]
    rw [(Fintype.sum_bijective φ hφ_inv.bijective _ _ fun t => rfl).symm]
    apply Finset.sum_congr rfl; intro t _
    -- spinProduct B (φ t) = spinProduct B ω * spinProduct B t
    have hspB : spinProduct B (φ t) = spinProduct B ω * spinProduct B t := by
      unfold spinProduct
      simp_rw [show ∀ i, (↑((φ t i).toSign) : ℝ) =
        ↑(ω i).toSign * ↑(t i).toSign from fun i => by simp [φ, Spin.toSign_mul]]
      rw [Finset.prod_mul_distrib]
    rw [hspB]
    have hw : boltzmannWeight G p ω * boltzmannWeight G p (φ t) =
        modifiedWeight G p t ω := by
      -- w(ω) * w(φ t) = modifiedWeight(t, ω)
      -- Both sides are exp(...). Show the exponents are equal.
      unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy modifiedWeight
      rw [← Real.exp_add]
      -- Use: edgeSpin(φ t, e) = edgeSpin(ω,e) * edgeSpin(t,e)
      -- and: sign(φ t, i) = sign(ω i) * sign(t i)
      have hes : ∀ e, edgeSpin (K := ℝ) (φ t) e =
          edgeSpin (K := ℝ) ω e * edgeSpin (K := ℝ) t e := by
        intro e; refine Sym2.ind (fun i j => ?_) e
        simp [edgeSpin, Sym2.lift_mk, φ, Spin.sign, Spin.toSign_mul]; ring
      have hss : ∀ i, Spin.sign ℝ ((φ t) i) = Spin.sign ℝ (ω i) * Spin.sign ℝ (t i) := by
        intro i; simp [φ, Spin.sign, Spin.toSign_mul]
      simp_rw [hes, hss]
      -- After simp_rw: both sides have Σ_e and Σ_i with matching summands
      -- LHS: -β(-J Σ ω^e - h Σ ω_i) + -β(-J Σ (ω^e · t^e) - h Σ (ω_i · t_i))
      -- RHS: Σ_e βJ(1+t^e)ω^e + Σ_i βh(1+t_i)ω_i
      -- These are equal: βJω^e + βJω^e·t^e = βJ(1+t^e)ω^e
      -- Both sides are exp(something) or products of exp.
      -- Convert RHS from ∏ exp to exp(Σ) and show exponents match.
      rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
      congr 1
      -- Goal after simp_rw hes, hss and exp manipulations:
      -- -(β * Σ_e -(J*ω^e)) - β * Σ_i -(h*ω_i) - β * Σ_e -(J*ω^e*t^e) - β * Σ_i -(h*ω_i*t_i)
      -- = (Σ_e βJ*t^e*ω^e + βJ*ω^e) + (Σ_i βh*t_i*ω_i + βh*ω_i)
      -- Use Finset.mul_sum to pull β*J inside sums, combine, then ring per term
      simp only [Finset.mul_sum]
      -- Exponent identity: βJ·ω^e + βJ·ω^e·t^e = βJ(1+t^e)ω^e (per term)
      have : -p.β * (∑ i ∈ G.edgeFinset, -p.J * edgeSpin (K := ℝ) ω i +
          ∑ i, -p.h * Spin.sign ℝ (ω i)) +
        -p.β * (∑ i ∈ G.edgeFinset, -p.J * (edgeSpin (K := ℝ) ω i * edgeSpin (K := ℝ) t i) +
          ∑ i, -p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i))) =
        ∑ e ∈ G.edgeFinset, p.β * p.J * (1 + edgeSpin (K := ℝ) t e) * edgeSpin (K := ℝ) ω e +
        ∑ i, p.β * p.h * (1 + Spin.sign ℝ (t i)) * Spin.sign ℝ (ω i) := by
        simp only [mul_add, Finset.mul_sum]
        have h1 : ∀ e ∈ G.edgeFinset,
            -p.β * (-p.J * edgeSpin (K := ℝ) ω e) +
            -p.β * (-p.J * (edgeSpin (K := ℝ) ω e * edgeSpin (K := ℝ) t e)) =
            p.β * p.J * (1 + edgeSpin (K := ℝ) t e) * edgeSpin (K := ℝ) ω e :=
          fun _ _ => by ring
        have h2 : ∀ i ∈ (Finset.univ : Finset ι),
            -p.β * (-p.h * Spin.sign ℝ (ω i)) +
            -p.β * (-p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i))) =
            p.β * p.h * (1 + Spin.sign ℝ (t i)) * Spin.sign ℝ (ω i) :=
          fun _ _ => by ring
        rw [show (∑ i ∈ G.edgeFinset, -p.β * (-p.J * edgeSpin (K := ℝ) ω i)) +
            (∑ i, -p.β * (-p.h * Spin.sign ℝ (ω i))) +
            ((∑ i ∈ G.edgeFinset, -p.β * (-p.J * (edgeSpin (K := ℝ) ω i * edgeSpin (K := ℝ) t i))) +
            (∑ i, -p.β * (-p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i))))) =
          (∑ i ∈ G.edgeFinset, (-p.β * (-p.J * edgeSpin (K := ℝ) ω i) +
            -p.β * (-p.J * (edgeSpin (K := ℝ) ω i * edgeSpin (K := ℝ) t i)))) +
          (∑ i, (-p.β * (-p.h * Spin.sign ℝ (ω i)) +
            -p.β * (-p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i)))))
          from by
            have e1 : ∑ i ∈ G.edgeFinset, (-p.β * (-p.J * edgeSpin (K := ℝ) ω i) +
                -p.β * (-p.J * (edgeSpin (K := ℝ) ω i * edgeSpin (K := ℝ) t i))) =
              ∑ i ∈ G.edgeFinset, -p.β * (-p.J * edgeSpin (K := ℝ) ω i) +
              ∑ i ∈ G.edgeFinset, -p.β * (-p.J * (edgeSpin (K := ℝ) ω i * edgeSpin (K := ℝ) t i)) :=
              Finset.sum_add_distrib
            have e2 : ∑ i : ι, (-p.β * (-p.h * Spin.sign ℝ (ω i)) +
                -p.β * (-p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i)))) =
              ∑ i, -p.β * (-p.h * Spin.sign ℝ (ω i)) +
              ∑ i, -p.β * (-p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i))) :=
              Finset.sum_add_distrib
            linarith]
        rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
      exact this
    rw [show spinProduct A ω * (spinProduct B ω - spinProduct B ω * spinProduct B t) *
        boltzmannWeight G p ω * boltzmannWeight G p (φ t) =
      spinProduct A ω * spinProduct B ω * (1 - spinProduct B t) *
        (boltzmannWeight G p ω * boltzmannWeight G p (φ t)) from by ring,
      hw, spinProduct_mul A B ω]; ring
  simp_rw [hinner]
  -- Step 2: Swap sums Σ_ω Σ_t → Σ_t Σ_ω
  rw [Finset.sum_comm]
  -- Step 3: Factor out (1 - t^B)
  apply Finset.sum_congr rfl; intro t _
  rw [← Finset.mul_sum]

/-- The modified weight has non-negative correlations for each fixed `t`.
Same proof structure as `bwFactored_hasNonnegCorrelations` but with
modified couplings `K_C(1 + t^C) ≥ 0`. -/
private theorem modifiedWeight_nonneg_corr (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (t : Config ι) :
    HasNonnegCorrelations (modifiedWeight G p t) := by
  unfold modifiedWeight
  exact hasNonnegCorrelations_edge_site_product G
    (fun e => p.β * p.J * (1 + edgeSpin (K := ℝ) t e))
    (fun i => p.β * p.h * (1 + Spin.sign ℝ (t i)))
    (fun e _ => by
      apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
      have := edgeSpin_sq t e
      have : (edgeSpin (K := ℝ) t e - 1) * (edgeSpin (K := ℝ) t e + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h <;> linarith)
    (fun i => by
      apply mul_nonneg (mul_nonneg hf.hβ.le hf.hh)
      have := Spin.sign_sq (K := ℝ) (t i)
      have : (Spin.sign ℝ (t i) - 1) * (Spin.sign ℝ (t i) + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h <;> linarith)

/-- The variable-changed duplicate sum is non-negative: each term has `(1-t^B) ≥ 0`
times an HNC inner sum. -/
private theorem duplicateSumChanged_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A B : Finset ι) :
    0 ≤ duplicateSumChanged G p A B := by
  unfold duplicateSumChanged
  apply Finset.sum_nonneg
  intro t _
  apply mul_nonneg (one_sub_spinProduct_nonneg B t)
  exact modifiedWeight_nonneg_corr G p hf t (symmDiff A B)

/-- The duplicate sum is non-negative, by variable change and term-wise non-negativity. -/
private theorem duplicateSum_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A B : Finset ι) :
    0 ≤ duplicateSum G p A B := by
  rw [duplicateSum_eq_changed]
  exact duplicateSumChanged_nonneg G p hf A B

/-- **Second Griffiths inequality (GKS-II)**: For a ferromagnetic Ising model
(`J ≥ 0`, `h ≥ 0`, `β > 0`), correlations are monotone:
`⟨σ^A σ^B⟩ ≥ ⟨σ^A⟩⟨σ^B⟩` for any subsets `A, B`.

Reference: Friedli–Velenik, Theorem 3.49 (3.55), pp. 127–128. -/
theorem gks_second (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A B : Finset ι) :
    correlation G p A * correlation G p B ≤ correlation G p (symmDiff A B) := by
  have hZ := partitionFunction_pos G p
  have hZ2 : (0 : ℝ) < partitionFunction G p ^ 2 := pow_pos hZ 2
  have hdup := duplicateSum_nonneg G p hf A B
  rw [duplicateSum_eq] at hdup
  -- hdup : 0 ≤ Z² * (corr(AΔB) - corr(A)*corr(B))
  -- Since Z² > 0, corr(AΔB) - corr(A)*corr(B) ≥ 0
  have hsub : 0 ≤ correlation G p (symmDiff A B) - correlation G p A * correlation G p B :=
    nonneg_of_mul_nonneg_right hdup hZ2
  linarith

end IsingModel
