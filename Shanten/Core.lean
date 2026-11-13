import Mathlib

namespace Shanten

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

/-- The thirteen orphan kinds, written explicitly for computable calculations. -/
def kokushiKinds : Finset Tile :=
  { Tile.suited .man ⟨0, by omega⟩
  , Tile.suited .man ⟨8, by omega⟩
  , Tile.suited .pin ⟨0, by omega⟩
  , Tile.suited .pin ⟨8, by omega⟩
  , Tile.suited .sou ⟨0, by omega⟩
  , Tile.suited .sou ⟨8, by omega⟩
  , Tile.honor ⟨0, by omega⟩
  , Tile.honor ⟨1, by omega⟩
  , Tile.honor ⟨2, by omega⟩
  , Tile.honor ⟨3, by omega⟩
  , Tile.honor ⟨4, by omega⟩
  , Tile.honor ⟨5, by omega⟩
  , Tile.honor ⟨6, by omega⟩ }

/-- The number of orphan kinds occurring in a hand. -/
def kokushiDistinctCount (hand : Hand) : Nat :=
  (kokushiKinds.filter fun tile => 0 < hand.counts tile).card

/-- The number of orphan kinds occurring at least twice. -/
def kokushiPairCount (hand : Hand) : Nat :=
  (kokushiKinds.filter fun tile => 2 ≤ hand.counts tile).card

/-- The closed-form shanten value for the thirteen-orphans shape. -/
def kokushiShanten (hand : Hand) : Int :=
  13 - (kokushiDistinctCount hand : Int) -
    if 0 < kokushiPairCount hand then 1 else 0

/-- The example with six middle manzu, six middle pinzu, and one 3-sou. -/
def kokushiWorstCase : Hand :=
  { counts := fun tile =>
      if tile ∈ ({ Tile.suited .man ⟨1, by omega⟩
          , Tile.suited .man ⟨2, by omega⟩
          , Tile.suited .man ⟨3, by omega⟩
          , Tile.suited .man ⟨4, by omega⟩
          , Tile.suited .man ⟨5, by omega⟩
          , Tile.suited .man ⟨6, by omega⟩
          , Tile.suited .pin ⟨1, by omega⟩
          , Tile.suited .pin ⟨2, by omega⟩
          , Tile.suited .pin ⟨3, by omega⟩
          , Tile.suited .pin ⟨4, by omega⟩
          , Tile.suited .pin ⟨5, by omega⟩
          , Tile.suited .pin ⟨6, by omega⟩
          , Tile.suited .sou ⟨2, by omega⟩ } : Finset Tile) then 1 else 0
    fixedMelds := 0 }

def ValidCounts (hand : Hand) : Prop :=
  ∀ tile, hand.counts tile ≤ 4
/-- The number of standing tiles in a hand. -/
def tileCount (hand : Hand) : Nat :=
  ∑ tile, hand.counts tile

/-- The number of tile kinds occurring at least twice in a hand. -/
def pairCount (hand : Hand) : Nat :=
  (Finset.univ.filter fun tile => 2 ≤ hand.counts tile).card

/-- The number of distinct tile kinds occurring in a hand. -/
def distinctTileCount (hand : Hand) : Nat :=
  (Finset.univ.filter fun tile => 0 < hand.counts tile).card

def presentTiles (hand : Hand) : Finset Tile :=
  Finset.univ.filter fun tile => 0 < hand.counts tile

lemma distinctTileCount_eq_presentTiles_card (hand : Hand) :
    distinctTileCount hand = (presentTiles hand).card := by
  rfl

lemma exists_missing_tile_kind
    (hand : Hand) (hdistinct : distinctTileCount hand < 7) :
    ∃ tile, hand.counts tile = 0 := by
  by_contra hmissing
  push Not at hmissing
  have hpresent : presentTiles hand = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro tile
    simp only [presentTiles, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.pos_of_ne_zero (hmissing tile)
  have hcard : 7 ≤ Fintype.card Tile := by native_decide
  have : 7 ≤ distinctTileCount hand := by
    rw [distinctTileCount_eq_presentTiles_card, hpresent]
    simpa using hcard
  omega

lemma tileCount_le_two_mul_distinctTileCount
    (hand : Hand) (hsmall : ∀ tile, hand.counts tile ≤ 2) :
    tileCount hand ≤ 2 * distinctTileCount hand := by
  have hpoint :
      ∀ tile, hand.counts tile ≤
        if 0 < hand.counts tile then 2 else 0 := by
    intro tile
    by_cases hpositive : 0 < hand.counts tile
    · simp [hpositive]
      exact hsmall tile
    · simp [hpositive, Nat.not_lt.mp hpositive, hsmall tile]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun tile _ => hpoint tile)
  calc
    tileCount hand ≤
        ∑ tile : Tile, (if 0 < hand.counts tile then 2 else 0) := hsum
    _ = 2 * distinctTileCount hand := by
      rw [← Finset.sum_filter (s := Finset.univ)
        (p := fun tile => 0 < hand.counts tile) (f := fun _ => 2)]
      simp [distinctTileCount, Nat.mul_comm]

lemma exists_surplus_tile_kind
    (hand : Hand) (hcount : tileCount hand = 13)
    (hdistinct : distinctTileCount hand < 7) :
    ∃ tile, 3 ≤ hand.counts tile := by
  by_contra hsurplus
  push Not at hsurplus
  have hsmall : ∀ tile, hand.counts tile ≤ 2 := by
    intro tile
    have hnot := hsurplus tile
    omega
  have hbound := tileCount_le_two_mul_distinctTileCount hand hsmall
  omega

/-- A concealed hand from the four-copy deck containing exactly thirteen tiles. -/
def IsThirteenTileHand (hand : Hand) : Prop :=
 hand.fixedMelds = 0 ∧
   tileCount hand = 13 ∧
   ValidCounts hand


end Shanten
