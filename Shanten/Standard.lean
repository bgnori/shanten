import Shanten.Specification

namespace Shanten

/-- The counters carried by the standard-form dynamic program. -/
structure StandardSearchState where
  tileIndex : Nat
  melds : Nat
  taatsu : Nat
  hasPair : Bool
  deriving DecidableEq, Repr

/-- A standard-form target before the fixed melds are added. -/
def standardTarget (pair : Tile) (melds : List Meld) : Multiset Tile :=
  pairTiles pair + meldsTiles melds

/-- The number of copies of each tile still required by a target. -/
def targetDeficit (hand : Hand) (target : Multiset Tile) : Nat :=
  ∑ tile : Tile, (target.count tile - hand.counts tile)

/-- A target has the required number of concealed melds for a hand. -/
def HasStandardMeldCount (hand : Hand) (melds : List Meld) : Prop :=
  melds.length + hand.fixedMelds = 4

/-- A target is a valid standard-form completion for the standing tiles. -/
def IsStandardTarget
    (hand : Hand) (pair : Tile) (melds : List Meld) : Prop :=
  HasStandardMeldCount hand melds ∧
    ∀ tile, hand.counts tile ≤
      (standardTarget pair melds).count tile

/-- The number of additional tiles needed to realize a standard target. -/
def standardTargetDistance
    (hand : Hand) (pair : Tile) (melds : List Meld) : Nat :=
  targetDeficit hand (standardTarget pair melds)

end Shanten
