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
             `Towers.NS.Wall300_Scaffold,
             `Towers.NS.NSStokesAdjoint,
             `Towers.NS.NSNonlinearTerm,
             `Towers.NS.NSClayCombinator,
             `Towers.NS.NSAubinLionsDecomp,
             `Towers.NS.NSCanonicalSurfaces,
             `Towers.NS.NSGate2Decomp,
             `Towers.NS.NSGate3Decomp,
             `Towers.NS.NSKPBridge,
             `Towers.NS.NSLittlewoodPaley,
             `Towers.NS.NSLPKPCertificate,
             `Towers.NS.NSCollection,
             `Towers.NS.NSPhase105BlowupConcentration,
             `Towers.NS.NSPhase106CarlemanHeat,
             `Towers.NS.NSPhase107CarlemanDrift,
             `Towers.NS.NSPhase108LimitPass,
             `Towers.NS.NSPhase97aSobolevC2alphaClose,
             'Towers.NS.NSPhase97bH4EnergyClose]
