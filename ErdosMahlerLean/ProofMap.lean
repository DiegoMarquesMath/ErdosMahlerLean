import ErdosMahlerLean.Proposition21
import ErdosMahlerLean.ProportionalPowerPairs
import ErdosMahlerLean.BlockRank
import ErdosMahlerLean.BlockCoordinates
import ErdosMahlerLean.BlockAssignments
import ErdosMahlerLean.ProductCorrespondence
import ErdosMahlerLean.Blocks
import ErdosMahlerLean.Localization
import ErdosMahlerLean.External.Inputs

import ErdosMahlerLean.ShortArc
import ErdosMahlerLean.RotationBlocks
import ErdosMahlerLean.RotationDiscrepancy
import ErdosMahlerLean.CircularDiscrepancy
import ErdosMahlerLean.ReturnCount
import ErdosMahlerLean.RationalRank
import ErdosMahlerLean.Matveev
import ErdosMahlerLean.ExceptionalHeights
import ErdosMahlerLean.ReturnProductData
import ErdosMahlerLean.ProportionalPairs

import ErdosMahlerLean.FixedSeparation
import ErdosMahlerLean.HeightContraction
import ErdosMahlerLean.RationalFibers
import ErdosMahlerLean.RankTransfer
import ErdosMahlerLean.RationalHeight
import ErdosMahlerLean.SmallDenominators
import ErdosMahlerLean.DyadicShells
import ErdosMahlerLean.SmallDenominatorRange

/-!
# Proposition 2.1 — complete conditional formalization

`ErdosMahlerLean.proposition21` proves the exact target `Proposition21` from
four explicitly sourced published-theorem interfaces. Every intermediate
manuscript estimate is proved internally. See docs/STATUS.md for the exact
statement, complete declaration inventory, axiom audit, and external boundary.
-/
