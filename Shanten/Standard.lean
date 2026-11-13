import Shanten.Specification

namespace Shanten

/-- The counters carried by the standard-form dynamic program. -/
structure StandardSearchState where
  tileIndex : Nat
  used : Multiset Tile
  melds : Nat
  taatsu : Nat
  hasPair : Bool
  deriving DecidableEq

/-- One branch of the standard-form decomposition search. -/
inductive StandardChoice
  | skip
  | pair (tile : Tile)
  | taatsu (tiles : Multiset Tile)
  | meld (meld : Meld)
  deriving DecidableEq

def choiceTiles : StandardChoice → Multiset Tile
  | .skip => 0
  | .pair tile => pairTiles tile
  | .taatsu tiles => tiles
  | .meld meld => meldTiles meld

def choiceUsesMeld : StandardChoice → Bool
  | .meld _ => true
  | _ => false

def choiceUsesPair : StandardChoice → Bool
  | .pair _ => true
  | _ => false

def choiceUsesTaatsu : StandardChoice → Bool
  | .taatsu _ => true
  | _ => false

def ValidStandardChoice
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice) : Prop :=
  (∀ tile, (state.used + choiceTiles choice).count tile ≤ hand.counts tile) ∧
  state.melds + (if choiceUsesMeld choice = true then 1 else 0) ≤ 4 ∧
  state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0) ≤ 4 ∧
  (state.hasPair = true ∨ choiceUsesPair choice = true)

def applyStandardChoice
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice)
    (_ : ValidStandardChoice hand state choice) : StandardSearchState :=
  { state with
    used := state.used + choiceTiles choice
    melds := state.melds + (if choiceUsesMeld choice = true then 1 else 0)
    taatsu := state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0)
    hasPair := state.hasPair || choiceUsesPair choice }

lemma applyStandardChoice_used_subset
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice)
    (hvalid : ValidStandardChoice hand state choice) :
    ∀ tile,
      (applyStandardChoice hand state choice hvalid).used.count tile ≤
        hand.counts tile := by
  intro tile
  exact hvalid.1 tile

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
