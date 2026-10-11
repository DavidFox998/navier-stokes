import Lake
open Lake DSL

package «navier-stokes» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

lean_lib Towers where
  roots := #[
    `Towers.NS.Wall266_Bogovskii,
    `Towers.NS.Wall266_Maximal,
    `Towers.NS.Wall266_CZDecomp,
    `Towers.NS.EnergyIneq,
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
    `Towers.NS.NSPhase97bH4EnergyClose,
    `Towers.NS.NSPhase97c120CellLinftyClose,
    `Towers.NS.NSPhase97dNoStationaryL3Close,
    -- Wall266 analytic proofs. `lake build` of the library must typecheck these;
    -- they are not reached by the Phase 97 roots above.
    `Towers.NS.Wall266_TrilinearForm,
    `Towers.NS.Wall266_H4L4,
    `Towers.NS.Wall266_L2Extension,
    -- Import closure of those three modules. Explicit `roots` are exact
    -- modules, so an imported local file is typechecked only if it is also a root.
    `Towers.YM.Wall260_ClayReduction,
    `Towers.YM.Wall261_H4Defect,
    `Towers.YM.Wall263_CoxeterSpectral,
    `Towers.YM.Wall264_H4Vertices,
    `Towers.NS.NSWeakSolutionClay,
    `Towers.NS.NSPhase104SmoothApprox]
