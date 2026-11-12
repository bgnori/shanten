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
  deriving DecidableEq

instance : Fintype Suit where
  elems := {.man, .pin, .sou}
  complete := by
    intro suit
    cases suit <;> simp

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
noncomputable def orphanKinds : Finset Tile :=
  by
    classical
    exact Finset.univ.filter fun tile =>
      match tile with
      | .suited _ rank => rank.val = 0 ∨ rank.val = 8
      | .honor _ => True

/-- The multiset containing one of each terminal and honor tile kind. -/
noncomputable def orphanTiles : Multiset Tile :=
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
There is at most one shanten value for a given hand shape.
-/
theorem isShapeShanten_unique
    (h₁ : IsShapeShanten hand shape value₁)
    (h₂ : IsShapeShanten hand shape value₂) :
    value₁ = value₂ := by
  rcases h₁ with ⟨_, distance₁, hvalue₁, hreaches₁, hminimal₁⟩
  rcases h₂ with ⟨_, distance₂, hvalue₂, hreaches₂, hminimal₂⟩
  have hdistance : distance₁ = distance₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h₁₂ | h₂₁
    · exact hminimal₂ distance₁ h₁₂ hreaches₁
    · exact hminimal₁ distance₂ h₂₁ hreaches₂
  omega

/- A missing value means that the shape is not a candidate for this hand. -/
noncomputable def ShapeShanten (hand : Hand) (shape : Shape) : Option Int :=
  by
    classical
    exact if h : ∃ value : Int, IsShapeShanten hand shape value then
      some (Classical.choose h)
    else
      none

theorem shapeShanten_eq_some_iff :
    ShapeShanten hand shape = some value ↔
      IsShapeShanten hand shape value := by
  classical
  unfold ShapeShanten
  split
  next h =>
    constructor
    · intro heq
      have hvalue : Classical.choose h = value := Option.some.inj heq
      exact hvalue ▸ Classical.choose_spec h
    · intro hvalue
      exact congrArg some (isShapeShanten_unique (Classical.choose_spec h) hvalue)
  next h =>
    constructor
    · simp
    · intro hvalue
      exact False.elim (h ⟨value, hvalue⟩)

def minOption : Option Int → Option Int → Option Int
  | none, other => other
  | other, none => other
  | some value₁, some value₂ => some (min value₁ value₂)

/--
The overall shanten value is the least value among the shapes that have a
finite value. Shapes with no value are omitted from the minimum.
-/
noncomputable def OverallShanten (hand : Hand) : Option Int :=
  minOption
    (ShapeShanten hand .standard)
    (minOption
      (ShapeShanten hand .sevenPairs)
      (ShapeShanten hand .thirteenOrphans))

/--
Relational characterization of `OverallShanten`. This is retained for proofs
that reason about a particular finite value rather than the `Option` API.
-/
def IsOverallShanten (hand : Hand) (value : Int) : Prop :=
  OverallShanten hand = some value

/-- The number of standing tiles in a hand. -/
def tileCount (hand : Hand) : Nat :=
  ∑ tile, hand.counts tile

/-- A concealed hand containing exactly thirteen standing tiles. -/
def IsThirteenTileHand (hand : Hand) : Prop :=
  hand.fixedMelds = 0 ∧ tileCount hand = 13

/--
The maximum shanten number of a thirteen-tile hand is at most six.  For the
seven-pairs argument, the relevant witness is a completion reachable in
distance seven: six exchanges create six pairs, and one final draw creates
the seventh pair.  Since shanten is distance minus one, this gives `6`.

This is the combinatorial bound for the three hand shapes specified above.
Its proof is intentionally left as an interface theorem: the definitions in
this file specify completion and shanten, but do not implement the finite
enumeration needed to establish the bound.
-/
theorem maxShanten13
    (h13 : IsThirteenTileHand hand)
    (value : Int)
    (hvalue : IsOverallShanten hand value) :
    value ≤ 6 := by
  sorry

end Shanten
