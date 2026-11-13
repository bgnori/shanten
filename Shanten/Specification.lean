import Shanten.Core

namespace Shanten

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

/-- Every normalized tile kind occurs at most four times. -/
def Complete : Shape → Hand → Prop
  | .standard, hand =>
      ValidCounts hand ∧
        ∃ pair melds,
          melds.length + hand.fixedMelds = 4 ∧
          HasTiles hand (pairTiles pair + meldsTiles melds)
  | .sevenPairs, hand =>
      ValidCounts hand ∧
        hand.fixedMelds = 0 ∧
          ∃ pairs : Finset Tile,
            pairs.card = 7 ∧
            HasTiles hand
              (pairs.toList.foldr (fun tile rest => pairTiles tile + rest) 0)
  | .thirteenOrphans, hand =>
      ValidCounts hand ∧
        hand.fixedMelds = 0 ∧
          ∃ pair, pair ∈ orphanKinds ∧
            HasTiles hand (orphanTiles + Multiset.replicate 1 pair)

/--
One improvement step either draws one tile or exchanges one standing tile for
a different kind. The number of fixed melds is unchanged.
-/
def HandStep (before after : Hand) : Prop :=
  before.fixedMelds = after.fixedMelds ∧
    ((∃ drawn, ValidCounts after ∧ ∀ tile,
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


end Shanten
