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

inductive Taatsu
  | pair (tile : Tile)
  | sequence (suit : Suit) (start : Fin 8)
  deriving DecidableEq, Fintype

def taatsuTiles : Taatsu → Multiset Tile
  | .pair tile => pairTiles tile
  | .sequence suit start =>
      Multiset.ofList
        [ Tile.suited suit ⟨start.val, by omega⟩
        , Tile.suited suit ⟨start.val + 1, by omega⟩ ]

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
  (state.hasPair = true ∨ choiceUsesPair choice = false)

def applyStandardChoice
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice)
    (_ : ValidStandardChoice hand state choice) : StandardSearchState :=
  { state with
    tileIndex := state.tileIndex + 1
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

def allStandardChoices : Finset StandardChoice :=
  insert .skip
    (Finset.univ.image StandardChoice.pair ∪
      Finset.univ.image StandardChoice.meld ∪
      Finset.univ.image (fun taatsu =>
        StandardChoice.taatsu (taatsuTiles taatsu)))

def NextStandardState
    (hand : Hand) (state next : StandardSearchState) : Prop :=
  ∃ choice, choice ∈ allStandardChoices ∧
    ∃ hvalid : ValidStandardChoice hand state choice,
      next = applyStandardChoice hand state choice hvalid

lemma nextStandardState_used_subset
    (hand : Hand) (state next : StandardSearchState)
    (hnext : NextStandardState hand state next) :
    ∀ tile, next.used.count tile ≤ hand.counts tile := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  exact applyStandardChoice_used_subset hand state choice hvalid

lemma nextStandardState_tileIndex
    (hand : Hand) (state next : StandardSearchState)
    (hnext : NextStandardState hand state next) :
    state.tileIndex < next.tileIndex := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  simp [applyStandardChoice]

def initialStandardState : StandardSearchState :=
  { tileIndex := 0
    used := 0
    melds := 0
    taatsu := 0
    hasPair := false }

/-- States reachable after exactly `fuel` decomposition choices. -/
def reachableWithin
    (hand : Hand) : Nat → StandardSearchState → Prop
  | 0, state => state = initialStandardState
  | fuel + 1, state =>
      ∃ previous,
        reachableWithin hand fuel previous ∧
          NextStandardState hand previous state

def IsStandardSearchComplete
    (hand : Hand) (state : StandardSearchState) : Prop :=
  state.melds + hand.fixedMelds = 4 ∧ state.hasPair = true

/-- The DP query: a complete standard decomposition is reachable in `fuel` choices. -/
def StandardSearch
    (hand : Hand) (fuel : Nat) : Prop :=
  ∃ state, reachableWithin hand fuel state ∧
    IsStandardSearchComplete hand state

lemma reachableWithin_zero_iff
    (hand : Hand) (state : StandardSearchState) :
    reachableWithin hand 0 state ↔ state = initialStandardState := by
  rfl

lemma reachableWithin_succ_iff
    (hand : Hand) (fuel : Nat) (state : StandardSearchState) :
    reachableWithin hand (fuel + 1) state ↔
      ∃ previous,
        reachableWithin hand fuel previous ∧
          NextStandardState hand previous state := by
  rfl

lemma reachableWithin_used_subset
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin hand fuel state) :
    ∀ tile, state.used.count tile ≤ hand.counts tile := by
  induction fuel generalizing state with
  | zero =>
      intro tile
      subst state
      simp [initialStandardState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      intro tile
      exact nextStandardState_used_subset hand previous state hnext tile

lemma standardSearch_complete_iff
    (hand : Hand) (fuel : Nat) :
    StandardSearch hand fuel ↔
      ∃ state, reachableWithin hand fuel state ∧
        state.melds + hand.fixedMelds = 4 ∧
        state.hasPair = true := by
  rfl

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
