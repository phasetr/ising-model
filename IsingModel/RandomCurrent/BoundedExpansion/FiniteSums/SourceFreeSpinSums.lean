import IsingModel.RandomCurrent.BoundedExpansion.FiniteSums.DegreeProducts

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Spin sum of the spin-edge product at fixed current**: at
fixed current `n`,
`∑_σ ∏_e (e.toFinset.prod σ.toSign) ^ n e = 2^|Λ|` if
`degreeAt n` is even at every vertex (i.e. `n` is source-free),
else `0`. Direct consequence of `prod_pow_spin_degreeAt` and
`Config.sum_prod_toSign_pow_real`; the per-current spin-sum step
of the random-current expansion (FV §3.7). -/
theorem Config.sum_prod_spin_pow_degreeAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    (∑ σ : ↑Λ → Spin, ∏ e : (inducedGraph G Λ).edgeSet,
        ((e : Sym2 ↑Λ).toFinset.prod
          (fun v => ((σ v).toSign : ℝ))) ^ n e)
      = if (∀ v : ↑Λ, Even (n.degreeAt G Λ v))
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  simp_rw [← Config.prod_pow_spin_degreeAt G Λ _ n]
  exact Config.sum_prod_toSign_pow_real (k := n.degreeAt G Λ)

omit [DecidableEq V] in
/-- **Even `degreeAt` everywhere ↔ source-free**: a current `n`
is source-free iff its total incident degree is even at every
vertex. Bridges the degree-side condition (output of
`Config.sum_prod_spin_pow_degreeAt`) with the parity-side
characterisation (`isSourceFree_iff`). -/
theorem Current.even_degreeAt_iff_isSourceFree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    (∀ v : ↑Λ, Even (n.degreeAt G Λ v)) ↔ n.IsSourceFree G Λ := by
  rw [Current.isSourceFree_iff]
  refine forall_congr' (fun v => ?_)
  rw [Current.parity_eq_degreeAt, ZMod.natCast_eq_zero_iff,
    ← even_iff_two_dvd]

omit [DecidableEq V] in
/-- **Spin sum at fixed current — source-free form**: at fixed
current `n`, the spin sum of the spin-edge product equals
`2^|Λ|` if `n` is source-free, else `0`. Combines
`Config.sum_prod_spin_pow_degreeAt` with
`Current.even_degreeAt_iff_isSourceFree` to produce the per-current
spin-sum identity in its final form (FV §3.7, eq. (3.45)). -/
theorem Config.sum_prod_spin_pow_degreeAt_isSourceFree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) [Decidable (n.IsSourceFree G Λ)] :
    (∑ σ : ↑Λ → Spin, ∏ e : (inducedGraph G Λ).edgeSet,
        ((e : Sym2 ↑Λ).toFinset.prod
          (fun v => ((σ v).toSign : ℝ))) ^ n e)
      = if n.IsSourceFree G Λ
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  rw [Config.sum_prod_spin_pow_degreeAt]
  exact if_congr (Current.even_degreeAt_iff_isSourceFree G Λ n) rfl rfl


end Ambient
end IsingModel
