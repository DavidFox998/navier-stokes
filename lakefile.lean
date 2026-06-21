import Lake
open Lake DSL

package «navier-stokes» where
  name := "navier-stokes"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

lean_lib Towers where
  roots := #[`Towers.NS.EnergyIneq,
             `Towers.NS.EnergyV2,
             `Towers.NS.Divergence,
             `Towers.NS.Wall300_Scaffold]
