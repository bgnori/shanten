import Shanten.SevenPairs

namespace Shanten

lemma reaches_sevenPairs_completion
    (hand : Hand) (h13 : IsThirteenTileHand hand) :
    ∃ distance : Nat, distance ≤ 7 ∧
      ReachesCompletion Complete .sevenPairs hand distance := by
  have hdistinct_le : distinctTileCount hand ≤ 13 := by
    have hcount := h13.2.1
    have hpoint : ∀ tile, (if 0 < hand.counts tile then 1 else 0) ≤
        hand.counts tile := by
      intro tile
      by_cases hpositive : 0 < hand.counts tile <;> simp [hpositive] <;>
        omega
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun tile _ => hpoint tile)
    have hbound : distinctTileCount hand ≤ tileCount hand := by
      calc
        distinctTileCount hand =
            ∑ tile : Tile, (if 0 < hand.counts tile then 1 else 0) := by
              simp [distinctTileCount, Finset.sum_filter]
        _ ≤ tileCount hand := hsum
    omega
  have hpairs : pairCount hand ≤ 6 :=
    pairCount_le_six_of_thirteen hand h13
  by_cases hsmall : distinctTileCount hand ≤ 7
  · obtain ⟨middle, hdistinctness, hmiddleDistinct⟩ :=
      reaches_seven_tile_kinds hand h13 hsmall
    have hmiddle13 :=
      ReachesDistinctness.isThirteenTileHand hdistinctness h13
    have hmiddlePairsEq : pairCount middle = pairCount hand :=
      ReachesDistinctness.pairCount hdistinctness rfl
    have hmiddlePairs : pairCount middle ≤ 6 :=
      pairCount_le_six_of_thirteen middle hmiddle13
    obtain ⟨final, hpairing, hfinalPairs⟩ :=
      reaches_six_pairs middle hmiddle13 hmiddleDistinct hmiddlePairs
    have hfinal13 :=
      ReachesPairMaking.isThirteenTileHand hpairing hmiddle13
    have hfinalDistinct :=
      ReachesPairMaking.distinctTileCount hpairing hmiddleDistinct
    have hfinalTenpai :=
      isSevenPairsTenpai_of_terminal final hfinal13 hfinalDistinct
        (by simpa using hfinalPairs)
    have hdraw := reachesCompletion_of_sevenPairsTenpai final hfinal13
      hfinalTenpai
    have hexchanges :=
      ReachesDistinctness.toReachesExchange hdistinctness
    have hpexchanges :=
      ReachesPairMaking.toReachesExchange hpairing
    have hcombined := ReachesExchange.append hexchanges hpexchanges
    have hcombined' := ReachesExchange.toReachesCompletion hcombined hdraw
    have hlower := seven_le_distinct_add_pairCount_of_thirteen hand h13
    have hlower' : 7 ≤ distinctTileCount hand + pairCount middle := by
      omega
    refine ⟨_, ?_, hcombined'⟩
    omega
  · have hlarge : 7 ≤ distinctTileCount hand := by omega
    by_cases hpairslt : pairCount hand < 6
    · obtain ⟨protectedTiles, hcard, hprotected⟩ :=
        exists_protectedTiles hand hlarge hpairslt
      obtain ⟨final, hpairing, hfinalPairs⟩ :=
        reaches_six_pairs_protected_of_card protectedTiles hand h13
          hcard hprotected hpairs
      have hfinal13 :=
        ReachesProtectedPairMaking.isThirteenTileHand hpairing h13
      have hfinalProtected :=
        ReachesProtectedPairMaking.protectedInvariant hpairing hprotected
      have hfinalDistinct : distinctTileCount final = 7 := by
        have hge : 7 ≤ distinctTileCount final := by
          have hsubset :
              protectedTiles ⊆
                Finset.univ.filter (fun tile => 0 < final.counts tile) := by
            intro tile htile
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hfinalProtected.1 tile htile
          have := Finset.card_le_card hsubset
          simpa [distinctTileCount, hcard] using this
        have hle : distinctTileCount final ≤ 7 := by
          have hbound := distinct_add_pairCount_le_tileCount final
          have hcount := hfinal13.2.1
          rw [hfinalPairs] at hbound
          omega
        omega
      have hfinalTenpai :=
        isSevenPairsTenpai_of_terminal final hfinal13 hfinalDistinct
          (by simpa using hfinalPairs)
      have hdraw := reachesCompletion_of_sevenPairsTenpai final hfinal13
        hfinalTenpai
      have hpexchanges :=
        ReachesProtectedPairMaking.toReachesExchange hpairing
      have hcombined' := ReachesExchange.toReachesCompletion hpexchanges hdraw
      refine ⟨_, ?_, hcombined'⟩
      omega
    · have hpairsEq : pairCount hand = 6 := by omega
      have hdistinctEq : distinctTileCount hand = 7 := by
        have hbound := distinct_add_pairCount_le_tileCount hand
        have hcount := h13.2.1
        rw [hpairsEq] at hbound
        omega
      obtain ⟨final, hpairing, hfinalPairs⟩ :=
        reaches_six_pairs hand h13 hdistinctEq (by omega)
      have hfinal13 :=
        ReachesPairMaking.isThirteenTileHand hpairing h13
      have hfinalDistinct : distinctTileCount final = 7 := by
        exact ReachesPairMaking.distinctTileCount hpairing hdistinctEq
      have hfinalTenpai :=
        isSevenPairsTenpai_of_terminal final hfinal13 hfinalDistinct
          (by simpa using hfinalPairs)
      have hdraw := reachesCompletion_of_sevenPairsTenpai final hfinal13
        hfinalTenpai
      have hpexchanges :=
        ReachesPairMaking.toReachesExchange hpairing
      have hcombined' := ReachesExchange.toReachesCompletion hpexchanges hdraw
      refine ⟨1, by omega, ?_⟩
      convert hcombined' using 1 <;> omega

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
theorem overallShanten_le_six_of_thirteenTileHand
    (h13 : IsThirteenTileHand hand)
    (value : Int)
    (hvalue : IsOverallShanten hand value) :
    value ≤ 6 := by
  classical
  obtain ⟨bound, hbound, hreachable⟩ :=
    reaches_sevenPairs_completion hand h13
  let reachable : Nat → Prop :=
    fun distance => ReachesCompletion Complete .sevenPairs hand distance
  have hexists : ∃ distance, reachable distance :=
    ⟨bound, hreachable⟩
  let distance := Nat.find hexists
  have hdistance : reachable distance :=
    Nat.find_spec hexists
  have hminimal : ∀ smaller, smaller < distance → ¬ reachable smaller := by
    intro smaller hsmaller
    exact Nat.find_min hexists hsmaller
  have hdistance_le : distance ≤ 7 := by
    exact le_trans
      (Nat.find_min' hexists (show reachable bound from hreachable)) hbound
  have hshape :
      IsShapeShanten hand .sevenPairs ((distance : Int) - 1) := by
    refine ⟨h13.1, distance, ?_, hdistance, ?_⟩
    · omega
    · intro smaller hsmaller
      exact hminimal smaller hsmaller
  have hseven :
      ShapeShanten hand .sevenPairs = some ((distance : Int) - 1) :=
    (shapeShanten_eq_some_iff).2 hshape
  have hvalue' : OverallShanten hand = some value := hvalue
  unfold OverallShanten at hvalue'
  cases hstandard : ShapeShanten hand .standard <;>
    cases hthirteen : ShapeShanten hand .thirteenOrphans <;>
    simp [hseven, hstandard, hthirteen, minOption] at hvalue'
  case none.none =>
    omega
  case none.some =>
    have hle : value ≤ (distance : Int) - 1 := by
      rw [← hvalue']
      exact min_le_left _ _
    omega
  case some.none =>
    have hle : value ≤ (distance : Int) - 1 := by
      rw [← hvalue']
      exact min_le_right _ _
    omega
  case some.some =>
    have hle : value ≤ (distance : Int) - 1 := by
      rw [← hvalue']
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    omega

/--
If a shape has a completion reachable in at most seven steps, then its
shape-specific shanten value is at most six.  This is the common bound used
by the three hand-shape arguments below; it does not use any comparison
between the three shapes.
-/
theorem shapeShanten_le_six_of_completion_bound
    (happlicable : Applicable shape hand)
    (hbound : ∃ distance : Nat, distance ≤ 7 ∧
      ReachesCompletion Complete shape hand distance)
    (value : Int)
    (hvalue : IsShapeShanten hand shape value) :
    value ≤ 6 := by
  classical
  obtain ⟨bound, hbound', hreachable⟩ := hbound
  let reachable : Nat → Prop :=
    fun distance => ReachesCompletion Complete shape hand distance
  have hexists : ∃ distance, reachable distance :=
    ⟨bound, hreachable⟩
  let distance := Nat.find hexists
  have hdistance : reachable distance :=
    Nat.find_spec hexists
  have hminimal : ∀ smaller, smaller < distance → ¬ reachable smaller := by
    intro smaller hsmaller
    exact Nat.find_min hexists (by simpa [distance] using hsmaller)
  have hdistance_le : distance ≤ 7 := by
    exact le_trans
      (Nat.find_min' hexists (show reachable bound from hreachable)) hbound'
  have hshape :
      IsShapeShanten hand shape ((distance : Int) - 1) := by
    refine ⟨happlicable, distance, by omega, hdistance, ?_⟩
    intro smaller hsmaller hsmall
    exact hminimal smaller hsmaller hsmall
  have heq :
      value = (distance : Int) - 1 :=
    isShapeShanten_unique hvalue hshape
  omega

/-- The seven-pairs component of the thirteen-tile upper bound. -/
theorem sevenPairsShanten_le_six_of_completion_bound
    (h13 : IsThirteenTileHand hand)
    (value : Int)
    (hvalue : IsShapeShanten hand .sevenPairs value) :
    value ≤ 6 := by
  apply shapeShanten_le_six_of_completion_bound
    (show Applicable .sevenPairs hand from h13.1)
    (reaches_sevenPairs_completion hand h13) value hvalue

/-- The standard-form component of the thirteen-tile upper bound. -/
theorem standardShanten_le_six_of_completion_bound
    (happlicable : Applicable .standard hand)
    (hbound : ∃ distance : Nat, distance ≤ 7 ∧
      ReachesCompletion Complete .standard hand distance)
    (value : Int)
    (hvalue : IsShapeShanten hand .standard value) :
    value ≤ 6 := by
  apply shapeShanten_le_six_of_completion_bound
    happlicable hbound value hvalue

/-- The thirteen-orphans component of the thirteen-tile upper bound. -/
theorem thirteenOrphansShanten_le_six_of_completion_bound
    (happlicable : Applicable .thirteenOrphans hand)
    (hbound : ∃ distance : Nat, distance ≤ 7 ∧
      ReachesCompletion Complete .thirteenOrphans hand distance)
    (value : Int)
    (hvalue : IsShapeShanten hand .thirteenOrphans value) :
    value ≤ 6 := by
  apply shapeShanten_le_six_of_completion_bound
    happlicable hbound value hvalue

/-- No hand can exceed thirteen shanten for the thirteen-orphans shape. -/
theorem kokushiShanten_le_thirteen (hand : Hand) :
    kokushiShanten hand ≤ 13 := by
  unfold kokushiShanten
  split <;> omega

/-- The middle-tile example has the maximum thirteen-orphans shanten value. -/
theorem kokushiWorstCase_shanten :
    kokushiShanten kokushiWorstCase = 13 := by
  native_decide

end Shanten
