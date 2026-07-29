import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG

/-!
# Magnetization and correlation forwarders at ℤ^d

ℤ^d forwarders for:

1. **Magnetization / truncated-2 convergence** — `{J,h,β} → ∞`
   convergence and subgraph-monotone convergence from
   `PhaseTransition.lean`.
2. **Site-level magnetization wrappers (GJ §5.3, pp. 77–80)** — bounds,
   vanishing slices, monotonicity.

The susceptibility / η family (with `truncated2_h_zero_latticeGraph`)
moved to the narrow child `MagnetizationSusceptibility.lean`
(PR #2004); the `HasNonnegCorrelations` / GKS / FKG family moved to
the narrow child `MagnetizationGksFkg.lean` (PR #2003).

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.4, §5.3, §17.7.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Moved: convergent wrappers

The 9 ℤ^d `magnetization_convergent_{J,h,beta}_latticeGraph`,
`truncated2_convergent_{J,h,beta,subgraph}_latticeGraph`,
`susceptibility_convergent_subgraph_latticeGraph`, and
`magnetization_total_convergent_subgraph_latticeGraph` wrappers
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationConvergent`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: susceptibility + η wrappers

The 11 ℤ^d `susceptibility_*_latticeGraph` and
`eta_nonneg_finite_vol_latticeGraph` wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationSusceptibility`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: site-level magnetization wrappers (GJ §5.3, pp. 77-80)

The 11 ℤ^d site-level magnetization wrappers
(`magnetization_apply_latticeGraph`,
`{abs_,,neg_one_le_,sq_le_one_,}magnetization_le_one_latticeGraph`,
`magnetization_nonneg_latticeGraph`,
`magnetization_{zero_at_h_zero,beta_zero,J_zero}_latticeGraph`,
`magnetization_{monotone_h,monotone_beta}_latticeGraph`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationSiteLevel`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: HNC / GKS / FKG wrappers

The 8 ℤ^d `hasNonnegCorrelations_*_latticeGraph` /
`gks_*_latticeGraph` / `boltzmannWeight_*_latticeGraph` /
`fkg_ising_latticeGraph` wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationGksFkg`.
The earlier import path is preserved by re-importing the new child.
-/


end Ambient
end IsingModel
