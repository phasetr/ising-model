import IsingModel.AmbientComplexAnalyticity.ClosedBallPatches.GlobalBranchEndpoint

/-!
# Real-axis identification of the global branch (GJ §4.6 Thm 4.6.2)

On the positive real axis the global stage branch agrees with the principal finite-volume
free energy *exactly*: along the real segment from the anchor, the imaginary part of the
branch is continuous, takes values in the discrete set `(2π/N)·ℤ` (exponential identity with
a positive real partition function), and vanishes at the anchor — hence it vanishes
identically by the intermediate value theorem, and the real logarithm is unique. With the
field-uniform disjoint-tower hypotheses, the subsequential compact-target patch is then
identified with the infinite-volume free energy along the whole positive real axis.

* `eq_zero_of_continuousOn_int_multiples` — discrete-valued continuous interpolation.
* `globalBranchStage_real_eq` — exact real-axis agreement `g_m(x) = F_m(x)`.
* `..._posReal_globalBranch_holomorphicExtension_realAxis_of_isCompact` — the compact patch
  with real-axis identification `g = f_∞(β, J, ·)` on `U ∩ ℝ₊`.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel

namespace Ambient

open Metric Real

variable {V : Type*} [DecidableEq V]

/-- **Discrete-valued continuous interpolation**: a continuous function on `[0, 1]` taking
values in the integer multiples of a positive constant and vanishing at `0` vanishes at `1`
(intermediate value theorem against the half-multiple). -/
theorem eq_zero_of_continuousOn_int_multiples {φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hcont : ContinuousOn φ (Set.Icc 0 1))
    (hval : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ k : ℤ, φ t = c * k)
    (h0 : φ 0 = 0) : φ 1 = 0 := by
  by_contra hne
  obtain ⟨k1, hk1⟩ := hval 1 (by norm_num)
  have hk1ne : (k1 : ℝ) ≠ 0 := by
    intro h
    exact hne (by rw [hk1, h, mul_zero])
  have half_not : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t ≠ c / 2 ∧ φ t ≠ -(c / 2) := by
    intro t ht
    obtain ⟨k, hk⟩ := hval t ht
    constructor
    · intro h
      rw [hk] at h
      have h2 : (2 * k : ℝ) = 1 := by field_simp at h ⊢; linarith
      have h2' : ((2 * k : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
      have := Int.cast_injective h2'
      omega
    · intro h
      rw [hk] at h
      have h2 : (2 * k : ℝ) = -1 := by field_simp at h ⊢; linarith
      have h2' : ((2 * k : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by push_cast; linarith
      have := Int.cast_injective h2'
      omega
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- `φ 1 ≤ -c < -(c/2) < 0 = φ 0`
    have hk1neg : k1 < 0 := by
      by_contra hge
      push Not at hge
      have hge' : (0 : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast hge
      nlinarith [hk1, hneg]
    have hk1le : k1 ≤ -1 := by omega
    have hk1le' : (k1 : ℝ) ≤ -1 := by exact_mod_cast hk1le
    have hφ1le : φ 1 ≤ -c := by
      rw [hk1]
      nlinarith
    have hmem : -(c / 2) ∈ Set.Icc (φ 1) (φ 0) := by
      rw [h0]
      constructor <;> linarith
    obtain ⟨t, ht, hφt⟩ := intermediate_value_Icc' zero_le_one hcont hmem
    exact (half_not t ht).2 hφt
  · -- `φ 0 = 0 < c/2 < c ≤ φ 1`
    have hk1pos : 0 < k1 := by
      by_contra hle
      push Not at hle
      have hle' : (k1 : ℝ) ≤ 0 := by exact_mod_cast hle
      nlinarith [hk1, hpos]
    have hk1ge : 1 ≤ k1 := by omega
    have hk1ge' : (1 : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast hk1ge
    have hφ1ge : c ≤ φ 1 := by
      rw [hk1]
      nlinarith
    have hmem : c / 2 ∈ Set.Icc (φ 0) (φ 1) := by
      rw [h0]
      constructor <;> linarith
    obtain ⟨t, ht, hφt⟩ := intermediate_value_Icc zero_le_one hcont hmem
    exact (half_not t ht).1 hφt

/-- **Exact real-axis agreement of the global branch**: with a positive real anchor, the
global stage branch at every positive real field equals the principal finite-volume free
energy. The imaginary part along the real segment is continuous, `(2π/N)·ℤ`-valued
(exponential identity with positive real `Z`), and vanishes at the anchor, hence vanishes;
the real exponential is injective. -/
theorem globalBranchStage_real_eq (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {b x : ℝ} (hb : 0 < b) (hx : 0 < x) (m : ℕ) :
    globalBranchStage G Λ (J : ℂ) (β : ℂ) (b : ℂ) m (x : ℂ)
      = freeEnergyComplexAlongExhaustion G Λ (J : ℂ) (x : ℂ) (β : ℂ) m := by
  classical
  have hbdom : (b : ℂ) ∈ IsingModel.leeYangDomain :=
    IsingModel.real_pos_mem_leeYangDomain hb
  set N : ℝ := (Fintype.card (↑(Λ.volume m) : Type _) : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast Fintype.card_pos
  -- the real segment stays positive, hence in the domain
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (1 - t) * b + t * x := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · simp [← h0]; linarith
    · nlinarith [ht.2, hb, hx]
  have hsegC : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (b : ℂ) + (t : ℂ) * ((x : ℂ) - (b : ℂ)) = (((1 - t) * b + t * x : ℝ) : ℂ) := by
    intro t _
    push_cast
    ring
  have hsegdom : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (b : ℂ) + (t : ℂ) * ((x : ℂ) - (b : ℂ)) ∈ IsingModel.leeYangDomain := by
    intro t ht
    rw [hsegC t ht]
    exact IsingModel.real_pos_mem_leeYangDomain (hseg t ht)
  -- the imaginary part along the segment
  set g : ℂ → ℂ := globalBranchStage G Λ (J : ℂ) (β : ℂ) (b : ℂ) m with hg
  set φ : ℝ → ℝ := fun t => (g ((b : ℂ) + (t : ℂ) * ((x : ℂ) - (b : ℂ)))).im with hφ
  have hcont : ContinuousOn φ (Set.Icc 0 1) := by
    have hganal := analyticOnNhd_globalBranchStage G Λ hβ hJ m hbdom
    have hgc : ContinuousOn g IsingModel.leeYangDomain := hganal.continuousOn
    have hpath : Continuous fun t : ℝ => (b : ℂ) + (t : ℂ) * ((x : ℂ) - (b : ℂ)) := by
      fun_prop
    exact Complex.continuous_im.comp_continuousOn
      (hgc.comp hpath.continuousOn fun t ht => hsegdom t ht)
  -- discreteness from the exponential identity with positive real `Z`
  have hval : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ k : ℤ, φ t = (2 * π / N) * k := by
    intro t ht
    set z : ℂ := (b : ℂ) + (t : ℂ) * ((x : ℂ) - (b : ℂ)) with hz
    have hzdom : z ∈ IsingModel.leeYangDomain := hsegdom t ht
    have hexp := exp_card_mul_globalBranchStage G Λ hβ hJ m hbdom hzdom
    -- the partition function at the positive real point is positive real
    set y : ℝ := (1 - t) * b + t * x with hy
    have hzy : z = ((y : ℝ) : ℂ) := hsegC t ht
    have hZreal : partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) z (β : ℂ) m
        = ((partitionFunctionAlongExhaustion G Λ ⟨J, y, β⟩ m : ℝ) : ℂ) := by
      rw [hzy]
      exact partitionFunctionComplexAlongExhaustion_at_real_eq_ofReal G Λ ⟨J, y, β⟩ m
    have hZpos : 0 < partitionFunctionAlongExhaustion G Λ ⟨J, y, β⟩ m :=
      IsingModel.partitionFunction_pos _ _
    set w : ℂ := (Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * g z with hw
    have hwexp : Complex.exp w = ((partitionFunctionAlongExhaustion G Λ ⟨J, y, β⟩ m : ℝ) : ℂ) := by
      rw [hw, hexp, hZreal]
    have him : Real.exp w.re * Real.sin w.im = 0 := by
      have := congrArg Complex.im hwexp
      rwa [Complex.exp_im, Complex.ofReal_im] at this
    have hre : Real.exp w.re * Real.cos w.im
        = partitionFunctionAlongExhaustion G Λ ⟨J, y, β⟩ m := by
      have := congrArg Complex.re hwexp
      rwa [Complex.exp_re, Complex.ofReal_re] at this
    have hsin : Real.sin w.im = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact absurd h (Real.exp_ne_zero _)
      · exact h
    have hcos : 0 < Real.cos w.im := by
      by_contra hle
      push Not at hle
      have : Real.exp w.re * Real.cos w.im ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hle
      linarith [hZpos, hre ▸ this]
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
    -- `cos (kπ) > 0` forces `k` even
    have hcosval : Real.cos w.im = (-1 : ℝ) ^ k := by
      rw [← hk]
      exact Real.cos_int_mul_pi k
    have hkeven : Even k := by
      by_contra hodd
      rw [Int.not_even_iff_odd] at hodd
      rw [hcosval, hodd.neg_one_zpow] at hcos
      linarith
    obtain ⟨k', hk'⟩ := hkeven
    -- `w.im = N * φ t`
    have hwim : w.im = N * φ t := by
      rw [hw, hφ, hN]
      rw [Complex.mul_im]
      have h1 : ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ)).im = 0 := by simp
      have h2 : ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ)).re
          = (Fintype.card (↑(Λ.volume m) : Type _) : ℝ) := by simp
      rw [h1, h2, hz]
      ring
    refine ⟨k', ?_⟩
    have hπpos := Real.pi_pos
    have : N * φ t = (2 * k') * π := by
      rw [← hwim, ← hk, hk']
      push_cast
      ring
    field_simp
    nlinarith [this]
  -- the anchor value is real
  have h0 : φ 0 = 0 := by
    rw [hφ]
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    rw [hg, globalBranchStage_base]
    have := freeEnergyComplexAlongExhaustion_at_real_eq_ofReal G Λ ⟨J, b, β⟩ m
    rw [this]
    exact Complex.ofReal_im _
  -- the imaginary part vanishes at `x`
  have hzero : φ 1 = 0 := by
    refine eq_zero_of_continuousOn_int_multiples ?_ hcont hval h0
    have hπpos := Real.pi_pos
    positivity
  have hxim : (g (x : ℂ)).im = 0 := by
    have h1 : φ 1 = (g (x : ℂ)).im := by
      rw [hφ]
      norm_num
    rw [← h1]
    exact hzero
  -- both sides are real logarithms of the same positive real number
  have hxdom : (x : ℂ) ∈ IsingModel.leeYangDomain :=
    IsingModel.real_pos_mem_leeYangDomain hx
  have hexpx := exp_card_mul_globalBranchStage G Λ hβ hJ m hbdom hxdom
  have hZx : partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) (x : ℂ) (β : ℂ) m
      = ((partitionFunctionAlongExhaustion G Λ ⟨J, x, β⟩ m : ℝ) : ℂ) :=
    partitionFunctionComplexAlongExhaustion_at_real_eq_ofReal G Λ ⟨J, x, β⟩ m
  have hZxpos : 0 < partitionFunctionAlongExhaustion G Λ ⟨J, x, β⟩ m :=
    IsingModel.partitionFunction_pos _ _
  have hFx := freeEnergyComplexAlongExhaustion_at_real_eq_ofReal G Λ ⟨J, x, β⟩ m
  have hFim : (freeEnergyComplexAlongExhaustion G Λ (J : ℂ) (x : ℂ) (β : ℂ) m).im = 0 := by
    rw [hFx]
    exact Complex.ofReal_im _
  -- `exp(N·F) = Z` from the principal-logarithm identity
  have hNne : ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZne : partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) (x : ℂ) (β : ℂ) m ≠ 0 := by
    rw [hZx]
    exact_mod_cast ne_of_gt hZxpos
  have hexpF : Complex.exp
      ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) *
        freeEnergyComplexAlongExhaustion G Λ (J : ℂ) (x : ℂ) (β : ℂ) m)
      = partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) (x : ℂ) (β : ℂ) m := by
    rw [freeEnergyComplexAlongExhaustion]
    simp only [freeEnergyComplex]
    rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
    exact Complex.exp_log hZne
  -- compare the two real logarithms
  set w₁ : ℂ := (Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * g (x : ℂ) with hw₁
  set w₂ : ℂ := (Fintype.card (↑(Λ.volume m) : Type _) : ℂ) *
    freeEnergyComplexAlongExhaustion G Λ (J : ℂ) (x : ℂ) (β : ℂ) m with hw₂
  have hcard_im : ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ)).im = 0 := by simp
  have hw₁im : w₁.im = 0 := by
    rw [hw₁, Complex.mul_im, hcard_im, hxim]
    ring
  have hw₂im : w₂.im = 0 := by
    rw [hw₂, Complex.mul_im, hcard_im, hFim]
    ring
  have hexpeq : Complex.exp w₁ = Complex.exp w₂ := by
    rw [hw₁, hw₂, hexpF]
    exact hexpx
  -- real exponential injectivity
  have hre : w₁.re = w₂.re := by
    have h1 : Complex.exp w₁ = ((Real.exp w₁.re : ℝ) : ℂ) := by
      rw [← Complex.re_add_im w₁, hw₁im]
      simp [← Complex.ofReal_exp]
    have h2 : Complex.exp w₂ = ((Real.exp w₂.re : ℝ) : ℂ) := by
      rw [← Complex.re_add_im w₂, hw₂im]
      simp [← Complex.ofReal_exp]
    have := h1.symm.trans (hexpeq.trans h2)
    have hcast : Real.exp w₁.re = Real.exp w₂.re := by exact_mod_cast this
    exact Real.exp_injective hcast
  have hw_eq : w₁ = w₂ := Complex.ext hre (hw₁im.trans hw₂im.symm)
  rw [hw₁, hw₂] at hw_eq
  exact mul_left_cancel₀ hNne hw_eq

/-- **Subsequential compact-target patch with real-axis identification**: under the
field-uniform disjoint-tower hypotheses, the patch of the unconditional endpoint agrees with
the infinite-volume free energy at *every* positive real field in the open neighbourhood —
the subsequenced global branches there are exactly the principal finite-volume free energies
(`globalBranchStage_real_eq`), which converge by the real Fekete theorem. -/
theorem
    freeEnergyComplexAlongExhaustion_posReal_globalBranch_holomorphicExtension_realAxis_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hd' : ∀ x : ℝ, 0 < x → DisjointTowerHypotheses G Λ ⟨p.J, x, p.β⟩)
    (hβ : 0 < p.β) (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ U ⊆ IsingModel.leeYangDomain ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ g : ℂ → ℂ,
          DifferentiableOn ℂ g U ∧
          (∀ z ∈ U, Filter.Tendsto
            (fun m => globalBranchStage G Λ (p.J : ℂ) (p.β : ℂ) (p.h : ℂ) (σ m) z)
            Filter.atTop (nhds (g z))) ∧
          ∀ x : ℝ, 0 < x → (x : ℂ) ∈ U →
            g (x : ℂ) = ((freeEnergyInfinite G Λ ⟨p.J, x, p.β⟩ : ℝ) : ℂ) := by
  obtain ⟨U, hUo, hKU, hUdom, σ, hσ, g, hgd, hgconv, _hgval⟩ :=
    freeEnergyComplexAlongExhaustion_posReal_globalBranch_holomorphicExtension_of_isCompact
      G Λ p hBED hd hβ hJ hK hKsub hpK
  refine ⟨U, hUo, hKU, hUdom, σ, hσ, g, hgd, hgconv, ?_⟩
  intro x hx hxU
  have hph : 0 < p.h := by
    have hmem := hKsub hpK
    have : |((p.h : ℂ)).im| < ((p.h : ℂ)).re := hmem
    simpa using this
  have hconv := hgconv (x : ℂ) hxU
  have hseq : ∀ m, globalBranchStage G Λ (p.J : ℂ) (p.β : ℂ) (p.h : ℂ) (σ m) (x : ℂ)
      = ((freeEnergyAlongExhaustion G Λ ⟨p.J, x, p.β⟩ (σ m) : ℝ) : ℂ) := by
    intro m
    rw [globalBranchStage_real_eq G Λ hβ hJ hph hx (σ m)]
    exact freeEnergyComplexAlongExhaustion_at_real_eq_ofReal G Λ ⟨p.J, x, p.β⟩ (σ m)
  have hreal : Filter.Tendsto
      (fun m => freeEnergyAlongExhaustion G Λ ⟨p.J, x, p.β⟩ (σ m))
      Filter.atTop (nhds (freeEnergyInfinite G Λ ⟨p.J, x, p.β⟩)) :=
    (freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses G Λ _ hBED
      (hd' x hx)).comp hσ.tendsto_atTop
  have hcast : Filter.Tendsto
      (fun m => ((freeEnergyAlongExhaustion G Λ ⟨p.J, x, p.β⟩ (σ m) : ℝ) : ℂ))
      Filter.atTop (nhds ((freeEnergyInfinite G Λ ⟨p.J, x, p.β⟩ : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hreal
  have hconv' : Filter.Tendsto
      (fun m => ((freeEnergyAlongExhaustion G Λ ⟨p.J, x, p.β⟩ (σ m) : ℝ) : ℂ))
      Filter.atTop (nhds (g (x : ℂ))) := by
    refine Filter.Tendsto.congr (fun m => hseq m) hconv
  exact tendsto_nhds_unique hconv' hcast

end Ambient

end IsingModel
