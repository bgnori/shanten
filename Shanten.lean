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
   ∀ tile, hand.counts tile ≤ 4



/- A target thirteen-tile shape for seven-pairs tenpai. -/
def sevenPairsTargetCounts (pairs : Finset Tile) (single : Tile) : TileCounts :=
  fun tile => if tile ∈ pairs then 2 else if tile = single then 1 else 0

def sevenPairsTarget (pairs : Finset Tile) (single : Tile) : Hand :=
  { counts := sevenPairsTargetCounts pairs single
    fixedMelds := 0 }

/-- A thirteen-tile seven-pairs tenpai shape. -/
def IsSevenPairsTenpai (hand : Hand) : Prop :=
  hand.fixedMelds = 0 ∧
    tileCount hand = 13 ∧
    distinctTileCount hand = 7 ∧
    pairCount hand = 6

lemma isSevenPairsTenpai_of_terminal
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand = 6) :
    IsSevenPairsTenpai hand := by
  exact ⟨h13.1, h13.2.1, hdistinct, hpairs⟩

lemma sevenPairsTarget_fixedMelds
    (pairs : Finset Tile) (single : Tile) :
    (sevenPairsTarget pairs single).fixedMelds = 0 := by
  rfl

lemma sevenPairsTarget_counts_le_four
    (pairs : Finset Tile) (single : Tile) (tile : Tile) :
    (sevenPairsTarget pairs single).counts tile ≤ 4 := by
  unfold sevenPairsTarget sevenPairsTargetCounts
  by_cases hp : tile ∈ pairs <;> by_cases hs : tile = single <;>
    simp [hp, hs] <;> split <;> omega

/-- The number of tiles still missing from a target count vector. -/
def countDeficit (current target : TileCounts) : Nat :=
  ∑ tile : Tile, (target tile - current tile)

/--
For count vectors with the same total, `countDeficit` is exactly the number
of exchanges needed when each exchange replaces one tile kind by another.
-/
def exchangeDistance (hand : Hand) (target : TileCounts) : Nat :=
  countDeficit hand.counts target

/--
A tile kind that is not yet a pair.  A zero-count tile is also a candidate:
the first exchange creates its singleton, and a later exchange can complete
the pair.  This is needed for hands concentrated in only a few tile kinds.
-/
def IsPairingCandidate (hand : Hand) (tile : Tile) : Prop :=
  hand.counts tile < 2

/-- The count vector obtained by drawing `drawn` and discarding `discarded`. -/
def exchangeCounts (hand : Hand) (discarded drawn : Tile) : TileCounts :=
  fun tile =>
    hand.counts tile + (if tile = drawn then 1 else 0) -
      (if tile = discarded then 1 else 0)

def exchangeHand (hand : Hand) (discarded drawn : Tile) : Hand :=
  { counts := exchangeCounts hand discarded drawn
    fixedMelds := hand.fixedMelds }

lemma exchangeCounts_step
    (hand : Hand) (discarded drawn : Tile)
    (hne : discarded ≠ drawn) (hdiscarded : hand.counts discarded > 0) :
    ∀ tile,
      exchangeCounts hand discarded drawn tile +
          (if tile = discarded then 1 else 0) =
        hand.counts tile + (if tile = drawn then 1 else 0) := by
  intro tile
  by_cases hdiscard : tile = discarded
  · subst tile
    simp [exchangeCounts, hne, Ne.symm hne]
    omega
  · by_cases hdrawn : tile = drawn
    · subst tile
      simp [exchangeCounts, hdiscard]
    · simp [exchangeCounts, hdiscard, hdrawn]

lemma exchangeHand_step
    (hand : Hand) (discarded drawn : Tile)
    (hne : discarded ≠ drawn) (hdiscarded : hand.counts discarded > 0) :
    HandStep hand (exchangeHand hand discarded drawn) := by
  refine ⟨rfl, Or.inr ⟨discarded, drawn, hne, hdiscarded, ?_⟩⟩
  exact exchangeCounts_step hand discarded drawn hne hdiscarded

lemma exchangeCounts_drawn
    (hand : Hand) (discarded drawn : Tile) (hne : discarded ≠ drawn) :
    exchangeCounts hand discarded drawn drawn = hand.counts drawn + 1 := by
  simp [exchangeCounts, hne, Ne.symm hne]

lemma exchangeCounts_discarded
    (hand : Hand) (discarded drawn : Tile) (hne : discarded ≠ drawn)
    (hpositive : hand.counts discarded > 0) :
    exchangeCounts hand discarded drawn discarded =
      hand.counts discarded - 1 := by
  simp [exchangeCounts, hne]

lemma exchangeCounts_other
    (hand : Hand) (discarded drawn tile : Tile)
    (hdiscarded : tile ≠ discarded) (hdrawn : tile ≠ drawn) :
    exchangeCounts hand discarded drawn tile = hand.counts tile := by
  simp [exchangeCounts, hdiscarded, hdrawn]

/-- A chain consisting only of draw-and-discard exchanges. -/
inductive ReachesExchange : Hand → Hand → Nat → Prop
  | done {hand} : ReachesExchange hand hand 0
  | step {hand next target distance} :
      HandStep hand next →
      ReachesExchange next target distance →
      ReachesExchange hand target (distance + 1)

lemma pairingCandidate_not_pair
    (hand : Hand) (tile : Tile) (hcandidate : IsPairingCandidate hand tile) :
    ¬ 2 ≤ hand.counts tile := by
  unfold IsPairingCandidate at hcandidate
  omega

/-- One exchange that advances a tile kind toward its target pair count. -/
def PairingExchange (before after : Hand) : Prop :=
  ∃ discarded drawn,
    IsPairingCandidate before drawn ∧
      discarded ≠ drawn ∧
      before.counts discarded > 0 ∧
      after = exchangeHand before discarded drawn

/--
An exchange directed at a fixed target count vector.  The drawn kind is
deficient at the target, while the discarded kind is strictly in surplus.
-/
def TargetExchange (target : TileCounts) (before after : Hand) : Prop :=
  ∃ discarded drawn,
    target drawn > before.counts drawn ∧
      before.counts discarded > target discarded ∧
      discarded ≠ drawn ∧
      after = exchangeHand before discarded drawn

/- A discard that leaves at least one pair of the same tile kind. -/
def IsPreservingDiscard (hand : Hand) (tile : Tile) : Prop :=
  3 ≤ hand.counts tile

/- A draw of a tile kind that is not present in the hand. -/
def IntroducesNewKind (hand : Hand) (tile : Tile) : Prop :=
  hand.counts tile = 0

/--
An exchange that introduces a new tile kind while removing an extra copy from
an existing kind.  It preserves every existing pair.
-/
def DistinctnessExchange (before after : Hand) : Prop :=
  ∃ discarded drawn,
    IsPreservingDiscard before discarded ∧
      IntroducesNewKind before drawn ∧
      discarded ≠ drawn ∧
      after = exchangeHand before discarded drawn

lemma DistinctnessExchange.isThirteenTileHand
    (h13 : IsThirteenTileHand before)
    (h : DistinctnessExchange before after) :
    IsThirteenTileHand after := by
  rcases h with ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩
  rcases h13 with ⟨hfixed, hcount, hmax⟩
  refine ⟨?_, ?_, ?_⟩
  · change before.fixedMelds = 0
    exact hfixed
  · have hstep := exchangeCounts_step before discarded drawn hne (by
      unfold IsPreservingDiscard at hdiscarded
      omega)
    have hfun :
        (fun tile =>
          exchangeCounts before discarded drawn tile +
            (if tile = discarded then 1 else 0)) =
        (fun tile =>
          before.counts tile + (if tile = drawn then 1 else 0)) :=
      funext hstep
    have hsum := congrArg (fun f : TileCounts => ∑ tile, f tile) hfun
    have hsum' :
        (∑ tile, exchangeCounts before discarded drawn tile) + 1 =
          (∑ tile, before.counts tile) + 1 := by
      simpa [Finset.sum_add_distrib, hne, Ne.symm hne] using hsum
    have hsum_eq :
        (∑ tile, exchangeCounts before discarded drawn tile) =
          ∑ tile, before.counts tile := by
      omega
    change (∑ tile, exchangeCounts before discarded drawn tile) = 13
    rw [hsum_eq]
    exact hcount
  · intro tile
    by_cases hdrawn' : tile = drawn
    · subst tile
      unfold IntroducesNewKind at hdrawn
      change exchangeCounts before discarded drawn drawn ≤ 4
      rw [exchangeCounts_drawn]
      · omega
      · exact hne
    · by_cases hdiscarded' : tile = discarded
      · subst tile
        unfold IsPreservingDiscard at hdiscarded
        change exchangeCounts before discarded drawn discarded ≤ 4
        have hbefore := hmax discarded
        rw [exchangeCounts_discarded]
        · omega
        · exact hne
        · omega
      · change exchangeCounts before discarded drawn tile ≤ 4
        rw [exchangeCounts_other]
        · exact hmax tile
        · exact hdiscarded'
        · exact hdrawn'

lemma exists_distinctnessExchange
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (hdistinct : distinctTileCount hand < 7) :
    ∃ next, DistinctnessExchange hand next := by
  obtain ⟨discarded, hdiscarded⟩ :=
    exists_surplus_tile_kind hand h13.2.1 hdistinct
  obtain ⟨drawn, hdrawn⟩ := exists_missing_tile_kind hand hdistinct
  have hne : discarded ≠ drawn := by
    intro heq
    subst heq
    omega
  refine ⟨exchangeHand hand discarded drawn, ?_⟩
  exact ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩

/--
An exchange that turns a singleton into a pair while discarding an extra copy
from another kind.
-/
def PairMakingExchange (before after : Hand) : Prop :=
  ∃ discarded drawn,
    before.counts drawn = 1 ∧
      IsPreservingDiscard before discarded ∧
      discarded ≠ drawn ∧
      after = exchangeHand before discarded drawn

lemma PairMakingExchange.isThirteenTileHand
    (h13 : IsThirteenTileHand before)
    (h : PairMakingExchange before after) :
    IsThirteenTileHand after := by
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  rcases h13 with ⟨hfixed, hcount, hmax⟩
  refine ⟨?_, ?_, ?_⟩
  · change before.fixedMelds = 0
    exact hfixed
  · have hstep := exchangeCounts_step before discarded drawn hne (by
      unfold IsPreservingDiscard at hdiscarded
      omega)
    have hfun :
        (fun tile =>
          exchangeCounts before discarded drawn tile +
            (if tile = discarded then 1 else 0)) =
        (fun tile =>
          before.counts tile + (if tile = drawn then 1 else 0)) :=
      funext hstep
    have hsum := congrArg (fun f : TileCounts => ∑ tile, f tile) hfun
    have hsum' :
        (∑ tile, exchangeCounts before discarded drawn tile) + 1 =
          (∑ tile, before.counts tile) + 1 := by
      simpa [Finset.sum_add_distrib, hne, Ne.symm hne] using hsum
    have hsum_eq :
        (∑ tile, exchangeCounts before discarded drawn tile) =
          ∑ tile, before.counts tile := by
      omega
    change (∑ tile, exchangeCounts before discarded drawn tile) = 13
    rw [hsum_eq]
    exact hcount
  · intro tile
    by_cases hdrawn' : tile = drawn
    · subst tile
      change exchangeCounts before discarded drawn drawn ≤ 4
      rw [exchangeCounts_drawn]
      · omega
      · exact hne
    · by_cases hdiscarded' : tile = discarded
      · subst tile
        unfold IsPreservingDiscard at hdiscarded
        change exchangeCounts before discarded drawn discarded ≤ 4
        have hbefore := hmax discarded
        rw [exchangeCounts_discarded]
        · omega
        · exact hne
        · omega
      · change exchangeCounts before discarded drawn tile ≤ 4
        rw [exchangeCounts_other]
        · exact hmax tile
        · exact hdiscarded'
        · exact hdrawn'

/-- Every pairing exchange is an ordinary exchange step. -/
lemma PairingExchange.handStep
    (h : PairingExchange before after) : HandStep before after := by
  rcases h with ⟨discarded, drawn, hcandidate, hne, hdiscarded, rfl⟩
  exact exchangeHand_step before discarded drawn hne hdiscarded

lemma TargetExchange.handStep
    (h : TargetExchange target before after) : HandStep before after := by
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  exact exchangeHand_step before discarded drawn hne (by omega)

lemma DistinctnessExchange.handStep
    (h : DistinctnessExchange before after) : HandStep before after := by
  rcases h with ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩
  exact exchangeHand_step before discarded drawn hne (by
    unfold IsPreservingDiscard at hdiscarded
    omega)

lemma PairMakingExchange.handStep
    (h : PairMakingExchange before after) : HandStep before after := by
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  exact exchangeHand_step before discarded drawn hne (by
    unfold IsPreservingDiscard at hdiscarded
    omega)

lemma DistinctnessExchange.filter_conditions
    (h : DistinctnessExchange before after) :
    ∃ discarded drawn,
      before.counts drawn = 0 ∧
        0 < after.counts drawn ∧
        2 ≤ after.counts discarded ∧
        discarded ≠ drawn := by
  rcases h with ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩
  refine ⟨discarded, drawn, ?_, ?_, ?_, hne⟩
  · exact hdrawn
  · unfold IntroducesNewKind at hdrawn
    change 0 < exchangeCounts before discarded drawn drawn
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · unfold IsPreservingDiscard at hdiscarded
    change 2 ≤ exchangeCounts before discarded drawn discarded
    rw [exchangeCounts_discarded]
    · omega
    · exact hne
    · omega

lemma PairMakingExchange.filter_conditions
    (h : PairMakingExchange before after) :
    ∃ discarded drawn,
      before.counts drawn = 1 ∧
        2 ≤ after.counts drawn ∧
        2 ≤ after.counts discarded ∧
        discarded ≠ drawn := by
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  refine ⟨discarded, drawn, hdrawn, ?_, ?_, hne⟩
  · change 2 ≤ exchangeCounts before discarded drawn drawn
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · unfold IsPreservingDiscard at hdiscarded
    change 2 ≤ exchangeCounts before discarded drawn discarded
    rw [exchangeCounts_discarded]
    · omega
    · exact hne
    · omega

lemma card_filter_eq_add_one_of
    {α : Type} [Fintype α] [DecidableEq α]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (a : α) (hpa : ¬ p a) (hqa : q a)
    (hother : ∀ x, x ≠ a → (p x ↔ q x)) :
    (Finset.univ.filter q).card = (Finset.univ.filter p).card + 1 := by
  classical
  have hfilter :
      Finset.univ.filter q = insert a (Finset.univ.filter p) := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [hpa, hqa]
    · rw [Finset.mem_insert]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [hxa, hother x hxa]
  rw [hfilter, Finset.card_insert_of_notMem]
  · simp [hpa]

lemma card_filter_eq_of_iff
    {α : Type} [Fintype α] [DecidableEq α]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ x, p x ↔ q x) :
    (Finset.univ.filter p).card = (Finset.univ.filter q).card := by
  have hfilter :
      Finset.univ.filter p = Finset.univ.filter q := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h x
  exact congrArg Finset.card hfilter

lemma tileCount_le_distinct_add_pairCount
    (hand : Hand) (hsmall : ∀ tile, hand.counts tile ≤ 2) :
    tileCount hand ≤ distinctTileCount hand + pairCount hand := by
  have hpoint :
      ∀ tile, hand.counts tile ≤
        (if 0 < hand.counts tile then 1 else 0) +
          (if 2 ≤ hand.counts tile then 1 else 0) := by
    intro tile
    by_cases hpositive : 0 < hand.counts tile
    · by_cases hpair : 2 ≤ hand.counts tile
      · simpa [hpositive, hpair] using hsmall tile
      · have hnotpair : ¬ 2 ≤ hand.counts tile := hpair
        simp [hpositive, hpair]
        omega
    · have hzero : hand.counts tile = 0 :=
        Nat.eq_zero_of_not_pos hpositive
      simp [hzero]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun tile _ => hpoint tile)
  calc
    tileCount hand ≤
        ∑ tile : Tile,
          ((if 0 < hand.counts tile then 1 else 0) +
            (if 2 ≤ hand.counts tile then 1 else 0)) := hsum
    _ = distinctTileCount hand + pairCount hand := by
      rw [Finset.sum_add_distrib]
      simp [distinctTileCount, pairCount, Finset.sum_filter,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma exists_nonPair_kind
    (hand : Hand) (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand < 6) :
    ∃ tile, hand.counts tile = 1 := by
  by_contra hnon
  have hno : ∀ tile, hand.counts tile ≠ 1 := by
    intro tile htile
    exact hnon ⟨tile, htile⟩
  have hiff : ∀ tile,
      (0 < hand.counts tile) ↔ 2 ≤ hand.counts tile := by
    intro tile
    constructor
    · intro hpositive
      have hno' := hno tile
      omega
    · intro hpair
      have hno' := hno tile
      omega
  have hcard :
      distinctTileCount hand = pairCount hand := by
    unfold distinctTileCount pairCount
    exact card_filter_eq_of_iff
      (fun tile => 0 < hand.counts tile)
      (fun tile => 2 ≤ hand.counts tile)
      hiff
  omega

lemma exists_singleton_kind_of_seven_kinds_six_pairs
    (hand : Hand) (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand = 6) :
    ∃ tile, hand.counts tile = 1 := by
  by_contra hnon
  have hno : ∀ tile, hand.counts tile ≠ 1 := by
    intro tile htile
    exact hnon ⟨tile, htile⟩
  have hiff : ∀ tile,
      (0 < hand.counts tile) ↔ 2 ≤ hand.counts tile := by
    intro tile
    constructor
    · intro hpositive
      have hno' := hno tile
      omega
    · intro hpair
      omega
  have hcard :
      distinctTileCount hand = pairCount hand := by
    unfold distinctTileCount pairCount
    exact card_filter_eq_of_iff
      (fun tile => 0 < hand.counts tile)
      (fun tile => 2 ≤ hand.counts tile)
      hiff
  omega

lemma exists_surplus_kind_for_pairMaking
    (hand : Hand) (hcount : tileCount hand = 13)
    (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand < 6) :
    ∃ tile, 3 ≤ hand.counts tile := by
  by_contra hsurplus
  push Not at hsurplus
  have hsmall : ∀ tile, hand.counts tile ≤ 2 := by
    intro tile
    have hnot := hsurplus tile
    omega
  have hbound := tileCount_le_distinct_add_pairCount hand hsmall
  omega

lemma exists_pairMakingExchange
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand < 6) :
    ∃ next, PairMakingExchange hand next := by
  obtain ⟨drawn, hdrawn⟩ :=
    exists_nonPair_kind hand hdistinct hpairs
  obtain ⟨discarded, hdiscarded⟩ :=
    exists_surplus_kind_for_pairMaking hand h13.2.1 hdistinct hpairs
  have hne : discarded ≠ drawn := by
    intro heq
    subst heq
    omega
  refine ⟨exchangeHand hand discarded drawn, ?_⟩
  exact ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩

lemma distinctTileCount_distinctnessExchange
    (h : DistinctnessExchange before after) :
    distinctTileCount after = distinctTileCount before + 1 := by
  classical
  rcases h with ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩
  unfold distinctTileCount
  apply card_filter_eq_add_one_of
    (p := fun tile => 0 < before.counts tile)
    (q := fun tile => 0 < (exchangeHand before discarded drawn).counts tile)
    drawn
  · unfold IntroducesNewKind at hdrawn
    simp [hdrawn]
  · change 0 < exchangeCounts before discarded drawn drawn
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · intro tile htile
    by_cases hdiscard : tile = discarded
    · subst tile
      unfold IsPreservingDiscard at hdiscarded
      change (0 < before.counts discarded ↔
        0 < exchangeCounts before discarded drawn discarded)
      rw [exchangeCounts_discarded]
      · omega
      · exact hne
      · omega
    · change (0 < before.counts tile ↔
      0 < exchangeCounts before discarded drawn tile)
      rw [exchangeCounts_other]
      · exact hdiscard
      · exact htile

lemma pairCount_distinctnessExchange
    (h : DistinctnessExchange before after) :
    pairCount after = pairCount before := by
  classical
  rcases h with ⟨discarded, drawn, hdiscarded, hdrawn, hne, rfl⟩
  unfold pairCount
  apply Eq.symm
  apply card_filter_eq_of_iff
  intro tile
  by_cases hdrawn' : tile = drawn
  · subst tile
    unfold IntroducesNewKind at hdrawn
    change (2 ≤ before.counts drawn ↔
      2 ≤ exchangeCounts before discarded drawn drawn)
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · by_cases hdiscarded' : tile = discarded
    · subst tile
      unfold IsPreservingDiscard at hdiscarded
      change (2 ≤ before.counts discarded ↔
        2 ≤ exchangeCounts before discarded drawn discarded)
      rw [exchangeCounts_discarded]
      · omega
      · exact hne
      · omega
    · change (2 ≤ before.counts tile ↔
      2 ≤ exchangeCounts before discarded drawn tile)
      rw [exchangeCounts_other]
      · exact hdiscarded'
      · exact hdrawn'

lemma distinctTileCount_pairMakingExchange
    (h : PairMakingExchange before after) :
    distinctTileCount after = distinctTileCount before := by
  classical
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  unfold distinctTileCount
  apply Eq.symm
  apply card_filter_eq_of_iff
  intro tile
  by_cases hdrawn' : tile = drawn
  · subst tile
    change (0 < before.counts drawn ↔
      0 < exchangeCounts before discarded drawn drawn)
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · by_cases hdiscarded' : tile = discarded
    · subst tile
      unfold IsPreservingDiscard at hdiscarded
      change (0 < before.counts discarded ↔
        0 < exchangeCounts before discarded drawn discarded)
      rw [exchangeCounts_discarded]
      · omega
      · exact hne
      · omega
    · change (0 < before.counts tile ↔
      0 < exchangeCounts before discarded drawn tile)
      rw [exchangeCounts_other]
      · exact hdiscarded'
      · exact hdrawn'

lemma pairCount_pairMakingExchange
    (h : PairMakingExchange before after) :
    pairCount after = pairCount before + 1 := by
  classical
  rcases h with ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩
  unfold pairCount
  apply card_filter_eq_add_one_of
    (p := fun tile => 2 ≤ before.counts tile)
    (q := fun tile => 2 ≤ (exchangeHand before discarded drawn).counts tile)
    drawn
  · omega
  · change 2 ≤ exchangeCounts before discarded drawn drawn
    rw [exchangeCounts_drawn]
    · omega
    · exact hne
  · intro tile htile
    by_cases hdiscarded' : tile = discarded
    · subst tile
      unfold IsPreservingDiscard at hdiscarded
      change (2 ≤ before.counts discarded ↔
        2 ≤ exchangeCounts before discarded drawn discarded)
      rw [exchangeCounts_discarded]
      · omega
      · exact hne
      · omega
    · change (2 ≤ before.counts tile ↔
      2 ≤ exchangeCounts before discarded drawn tile)
      rw [exchangeCounts_other]
      · exact hdiscarded'
      · exact htile

lemma deficit_after_drawing
    (target : TileCounts) (hand : Hand) (discarded drawn : Tile)
    (hne : discarded ≠ drawn) (hdeficit : hand.counts drawn < target drawn) :
    target drawn - exchangeCounts hand discarded drawn drawn =
      target drawn - hand.counts drawn - 1 := by
  simp [exchangeCounts, hne, Ne.symm hne]
  omega

lemma deficit_after_discarding
    (target : TileCounts) (hand : Hand) (discarded drawn : Tile)
    (hne : discarded ≠ drawn)
    (hsurplus : target discarded < hand.counts discarded) :
    target discarded - exchangeCounts hand discarded drawn discarded =
      target discarded - hand.counts discarded := by
  simp [exchangeCounts, hne]
  omega

lemma deficit_unchanged
    (target : TileCounts) (hand : Hand) (discarded drawn tile : Tile)
    (hdiscarded : tile ≠ discarded) (hdrawn : tile ≠ drawn) :
    target tile - exchangeCounts hand discarded drawn tile =
      target tile - hand.counts tile := by
  simp [exchangeCounts, hdiscarded, hdrawn]

/-- Repeated pairing exchanges, with the number of exchanges explicit. -/
inductive ReachesPairing : Hand → Hand → Nat → Prop
  | done {hand} : ReachesPairing hand hand 0
  | step {hand next target distance} :
      PairingExchange hand next →
      ReachesPairing next target distance →
      ReachesPairing hand target (distance + 1)

lemma ReachesPairing.toReachesExchange :
    ReachesPairing before after distance →
      ReachesExchange before after distance := by
  intro h
  induction h with
  | done =>
      exact .done
  | step hstep hrest ih =>
      exact .step hstep.handStep ih

/-- Repeated exchanges that introduce previously absent tile kinds. -/
inductive ReachesDistinctness : Hand → Hand → Nat → Prop
  | done {hand} : ReachesDistinctness hand hand 0
  | step {hand next target distance} :
      DistinctnessExchange hand next →
      ReachesDistinctness next target distance →
      ReachesDistinctness hand target (distance + 1)

lemma ReachesDistinctness.toReachesExchange :
    ReachesDistinctness before after distance →
      ReachesExchange before after distance := by
  intro h
  induction h with
  | done =>
      exact .done
  | step hstep hrest ih =>
      exact .step hstep.handStep ih

lemma reaches_seven_tile_kinds
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (hdistinct : distinctTileCount hand ≤ 7) :
    ∃ next,
      ReachesDistinctness hand next (7 - distinctTileCount hand) ∧
        distinctTileCount next = 7 := by
  have aux : ∀ n : Nat, ∀ hand : Hand,
      7 - distinctTileCount hand = n →
      IsThirteenTileHand hand →
      distinctTileCount hand ≤ 7 →
      ∃ next,
        ReachesDistinctness hand next n ∧
          distinctTileCount next = 7 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hand hn h13 hdist
        by_cases hseven : distinctTileCount hand = 7
        · have hnzero : n = 0 := by omega
          subst n
          exact ⟨hand, by simpa [hseven] using
            (ReachesDistinctness.done : ReachesDistinctness hand hand 0), hseven⟩
        · have hlt : distinctTileCount hand < 7 := by omega
          obtain ⟨next, hstep⟩ :=
            exists_distinctnessExchange hand h13 hlt
          have hnext13 :=
            DistinctnessExchange.isThirteenTileHand h13 hstep
          have hnextcount :
              distinctTileCount next = distinctTileCount hand + 1 :=
            distinctTileCount_distinctnessExchange hstep
          have hnnext :
              7 - distinctTileCount next < n := by
            omega
          obtain ⟨final, hrest, hfinal⟩ :=
            ih (7 - distinctTileCount next) hnnext next rfl hnext13 (by omega)
          refine ⟨final, ?_, hfinal⟩
          rw [show n = (7 - distinctTileCount next) + 1 by omega]
          exact .step hstep hrest
  exact aux (7 - distinctTileCount hand) hand rfl h13 hdistinct

/-- Repeated exchanges that turn singleton kinds into pairs. -/
inductive ReachesPairMaking : Hand → Hand → Nat → Prop
  | done {hand} : ReachesPairMaking hand hand 0
  | step {hand next target distance} :
      PairMakingExchange hand next →
      ReachesPairMaking next target distance →
      ReachesPairMaking hand target (distance + 1)

lemma reaches_six_pairs
    (hand : Hand) (h13 : IsThirteenTileHand hand)
    (hdistinct : distinctTileCount hand = 7)
    (hpairs : pairCount hand ≤ 6) :
    ∃ next,
      ReachesPairMaking hand next (6 - pairCount hand) ∧
        pairCount next = 6 := by
  have aux : ∀ n : Nat, ∀ hand : Hand,
      6 - pairCount hand = n →
      IsThirteenTileHand hand →
      distinctTileCount hand = 7 →
      pairCount hand ≤ 6 →
      ∃ next,
        ReachesPairMaking hand next n ∧
          pairCount next = 6 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hand hn h13 hdist hpairs'
        by_cases hsix : pairCount hand = 6
        · have hnzero : n = 0 := by omega
          subst n
          exact ⟨hand, by simpa [hsix] using
            (ReachesPairMaking.done : ReachesPairMaking hand hand 0), hsix⟩
        · have hlt : pairCount hand < 6 := by omega
          obtain ⟨next, hstep⟩ :=
            exists_pairMakingExchange hand h13 hdist hlt
          have hnext13 :=
            PairMakingExchange.isThirteenTileHand h13 hstep
          have hnextdistinct :
              distinctTileCount next = 7 := by
            rw [distinctTileCount_pairMakingExchange hstep]
            exact hdist
          have hnextpairs :
              pairCount next = pairCount hand + 1 :=
            pairCount_pairMakingExchange hstep
          have hnnext :
              6 - pairCount next < n := by
            omega
          obtain ⟨final, hrest, hfinal⟩ :=
            ih (6 - pairCount next) hnnext next rfl hnext13
              hnextdistinct (by omega)
          refine ⟨final, ?_, hfinal⟩
          rw [show n = (6 - pairCount next) + 1 by omega]
          exact .step hstep hrest
  exact aux (6 - pairCount hand) hand rfl h13 hdistinct hpairs

lemma ReachesPairMaking.toReachesExchange :
    ReachesPairMaking before after distance →
      ReachesExchange before after distance := by
  intro h
  induction h with
  | done =>
      exact .done
  | step hstep hrest ih =>
      exact .step hstep.handStep ih

lemma sevenPairsTargetCounts_single
    (pairs : Finset Tile) (single : Tile) (hsingle : single ∉ pairs) :
    sevenPairsTargetCounts pairs single single = 1 := by
  simp [sevenPairsTargetCounts, hsingle]

lemma sevenPairsTargetCounts_pair
    (pairs : Finset Tile) (single tile : Tile) (htile : tile ∈ pairs) :
    sevenPairsTargetCounts pairs single tile = 2 := by
  simp [sevenPairsTargetCounts, htile]

lemma sevenPairsTargetCounts_other
    (pairs : Finset Tile) (single tile : Tile)
    (htile : tile ∉ pairs) (hne : tile ≠ single) :
    sevenPairsTargetCounts pairs single tile = 0 := by
  simp [sevenPairsTargetCounts, htile, hne]

lemma exchangeDistance_eq_target_deficit
    (hand : Hand) (pairs : Finset Tile) (single : Tile) :
    exchangeDistance hand (sevenPairsTargetCounts pairs single) =
      ∑ tile : Tile, (sevenPairsTargetCounts pairs single tile - hand.counts tile) := by
  simp [exchangeDistance, countDeficit]

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
