import Mathlib

/-!
Declarative shanten specification.

The completion predicates for the three hand shapes are supplied separately;
this file defines the meaning of their shanten values, not an algorithm for
deciding completion or finding a value.
-/

namespace Shanten

/-- The three numbered suits. -/
inductive Suit
  | man
  | pin
  | sou
  deriving DecidableEq, Fintype

/-- A normalized tile kind (the three red fives are merged into their fives). -/
inductive Tile
  | suited (suit : Suit) (rank : Fin 9)
  | honor (rank : Fin 7)
  deriving DecidableEq, Fintype

/-- A standing hand represented by its count of each tile kind. -/
abbrev TileCounts := Tile → Nat

/-- The standing tiles and the number of fixed melds. -/
structure Hand where
  counts : TileCounts
  fixedMelds : Nat

/-- A concealed set: either a triplet or a suited sequence. -/
inductive Meld
  | triplet (tile : Tile)
  | sequence (suit : Suit) (start : Fin 7)

/-- The tile multiset represented by one concealed meld. -/
def meldTiles : Meld → Multiset Tile
  | .triplet tile => Multiset.replicate 3 tile
  | .sequence suit start =>
      Multiset.ofList
        [ Tile.suited suit ⟨start.val, by omega⟩
        , Tile.suited suit ⟨start.val + 1, by omega⟩
        , Tile.suited suit ⟨start.val + 2, by omega⟩
        ]

/-- The combined tiles represented by a list of concealed melds. -/
def meldsTiles (melds : List Meld) : Multiset Tile :=
  melds.foldr (fun meld rest => meldTiles meld + rest) 0

/-- A standing hand has exactly the multiplicities of the given tile multiset. -/
def HasTiles (hand : Hand) (tiles : Multiset Tile) : Prop :=
  ∀ tile, hand.counts tile = tiles.count tile

/-- The tile multiset of one pair. -/
def pairTiles (tile : Tile) : Multiset Tile :=
  Multiset.replicate 2 tile

/-- All 13 terminal and honor tile kinds. -/
def orphanKinds : Finset Tile :=
  Finset.univ.filter fun tile =>
    match tile with
    | .suited _ rank => rank.val = 0 ∨ rank.val = 8
    | .honor _ => True

/-- The multiset containing one of each terminal and honor tile kind. -/
def orphanTiles : Multiset Tile :=
  Multiset.ofList orphanKinds.toList

/-- The structural hand shapes whose shanten values are considered. -/
inductive Shape
  | standard
  | sevenPairs
  | thirteenOrphans
  deriving DecidableEq

/-- The two special shapes are applicable only when the hand has no fixed melds. -/
def Applicable (shape : Shape) (hand : Hand) : Prop :=
  match shape with
  | .standard => True
  | .sevenPairs | .thirteenOrphans => hand.fixedMelds = 0

/--
A complete hand of the selected shape. A standard hand has a pair and enough
concealed melds to make four sets together with its fixed melds. The special
shapes use their usual pair-based tile structures.
-/
def Complete : Shape → Hand → Prop
  | .standard, hand =>
      ∃ pair melds,
        melds.length + hand.fixedMelds = 4 ∧
        HasTiles hand (pairTiles pair + meldsTiles melds)
  | .sevenPairs, hand =>
      hand.fixedMelds = 0 ∧
        ∃ pairs : Finset Tile,
          pairs.card = 7 ∧
          HasTiles hand
            (pairs.toList.foldr (fun tile rest => pairTiles tile + rest) 0)
  | .thirteenOrphans, hand =>
      hand.fixedMelds = 0 ∧
        ∃ pair, pair ∈ orphanKinds ∧
          HasTiles hand (orphanTiles + Multiset.replicate 1 pair)

/--
One improvement step either draws one tile or exchanges one standing tile for
a different kind. The number of fixed melds is unchanged.
-/
def HandStep (before after : Hand) : Prop :=
  before.fixedMelds = after.fixedMelds ∧
    ((∃ drawn, ∀ tile,
        after.counts tile =
          before.counts tile + (if tile = drawn then 1 else 0)) ∨
      (∃ discarded drawn, discarded ≠ drawn ∧ before.counts discarded > 0 ∧
        ∀ tile,
          after.counts tile + (if tile = discarded then 1 else 0) =
            before.counts tile + (if tile = drawn then 1 else 0)))

/-- Reaching a complete hand in exactly `distance` improvement steps. -/
inductive ReachesCompletion (complete : Shape → Hand → Prop) (shape : Shape) :
    Hand → Nat → Prop
  | done {hand} : complete shape hand → ReachesCompletion complete shape hand 0
  | step {hand next distance} :
      HandStep hand next →
      ReachesCompletion complete shape next distance →
      ReachesCompletion complete shape hand (distance + 1)

/--
`value` is the shanten number for `shape` when it is the least improvement
distance to a completion, minus one. Thus distance zero is `-1` (complete)
and distance one is `0` (tenpai).

`complete` is a structural predicate for the selected winning shape. It must
describe the intended complete hands; it is deliberately not implemented by a
search or calculator here.
-/
def IsShapeShanten (hand : Hand) (shape : Shape) (value : Int) : Prop :=
  Applicable shape hand ∧
    ∃ distance : Nat,
      (distance : Int) = value + 1 ∧
      ReachesCompletion Complete shape hand distance ∧
      ∀ smaller : Nat, smaller < distance →
        ¬ ReachesCompletion Complete shape hand smaller

/--
The overall shanten value is the least value among the applicable shapes.
Inapplicable special shapes do not participate in this minimum.
-/
def IsOverallShanten (hand : Hand) (value : Int) : Prop :=
  (∃ shape : Shape, IsShapeShanten hand shape value) ∧
    ∀ shape : Shape, ∀ otherValue : Int,
      IsShapeShanten hand shape otherValue →
        value ≤ otherValue

end Shanten
