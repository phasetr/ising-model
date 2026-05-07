import IsingModel.AmbientLattice.SpecialCases.Legacy

/-!
# Ambient-lattice special cases umbrella

This module is intentionally a thin re-export. The legacy monolithic body lives
in `IsingModel.AmbientLattice.SpecialCases.Legacy`. Non-analytic free-energy
special cases live in `IsingModel.AmbientLattice.SpecialCases.FreeEnergy`, and
lightweight infinite-volume aliases live in
`IsingModel.AmbientLattice.SpecialCases.InfiniteVolume`. New narrow APIs should
be added in dedicated child modules and re-exported here only when they belong
to the public ambient special-cases surface.
-/
