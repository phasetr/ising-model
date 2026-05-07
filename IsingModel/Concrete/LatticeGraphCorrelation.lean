import IsingModel.Concrete.LatticeGraphCorrelation.Legacy

/-!
# Concrete correlation umbrella for the ℤ^d Ising model

This module is intentionally a thin re-export. The legacy monolithic
implementation lives in `IsingModel.Concrete.LatticeGraphCorrelation.Legacy`;
new narrow APIs should be added in dedicated child modules and re-exported
here only when they belong to the public concrete correlation surface.
-/
