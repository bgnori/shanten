import Shanten.Specification
import Shanten.SevenPairs

namespace Shanten

inductive Taatsu
  | pair (tile : Tile)
  | sequence (suit : Suit) (start : Fin 8)
  deriving DecidableEq, Fintype

/-- The counters carried by the standard-form dynamic program. -/
structure StandardSearchState where
  tileIndex : Nat
  used : Multiset Tile
  pair : Option Tile
  meldHistory : List Meld
  taatsuHistory : List Taatsu
  melds : Nat
  taatsu : Nat
  deriving DecidableEq

/-- One branch of the standard-form decomposition search. -/
inductive StandardChoice
  | skip
  | pair (tile : Tile)
  | taatsu (taatsu : Taatsu)
  | meld (meld : Meld)
  deriving DecidableEq

def taatsuTiles : Taatsu → Multiset Tile
  | .pair tile => pairTiles tile
  | .sequence suit start =>
      Multiset.ofList
        [ Tile.suited suit ⟨start.val, by omega⟩
        , Tile.suited suit ⟨start.val + 1, by omega⟩ ]

def choiceTiles : StandardChoice → Multiset Tile
  | .skip => 0
  | .pair tile => pairTiles tile
  | .taatsu taatsu => taatsuTiles taatsu
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
  (state.pair.isNone ∨ choiceUsesPair choice = false)

def applyStandardChoice
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice)
    (_ : ValidStandardChoice hand state choice) : StandardSearchState :=
  { state with
    tileIndex := state.tileIndex + 1
    used := state.used + choiceTiles choice
    pair := match choice with
      | .pair tile => some tile
      | _ => state.pair
    meldHistory := match choice with
      | .meld meld => meld :: state.meldHistory
      | _ => state.meldHistory
    taatsuHistory := match choice with
      | .taatsu taatsu => taatsu :: state.taatsuHistory
      | _ => state.taatsuHistory
    melds := state.melds + (if choiceUsesMeld choice = true then 1 else 0)
    taatsu := state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0)
    }

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
        StandardChoice.taatsu taatsu))

def choicesForTile (tile : Tile) : Finset StandardChoice :=
  allStandardChoices.filter
    (fun choice => choice = .skip ∨ tile ∈ choiceTiles choice)

def NextStandardState
    (hand : Hand) (state next : StandardSearchState) : Prop :=
  ∃ choice, choice ∈ allStandardChoices ∧
    ∃ hvalid : ValidStandardChoice hand state choice,
      next = applyStandardChoice hand state choice hvalid

def NextStandardStateAt
    (hand : Hand) (tile : Tile) (state next : StandardSearchState) : Prop :=
  ∃ choice, choice ∈ choicesForTile tile ∧
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

lemma nextStandardStateAt_used_subset
    (hand : Hand) (tile : Tile) (state next : StandardSearchState)
    (hnext : NextStandardStateAt hand tile state next) :
    ∀ tile', next.used.count tile' ≤ hand.counts tile' := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  exact applyStandardChoice_used_subset hand state choice hvalid

lemma nextStandardStateAt_tileIndex
    (hand : Hand) (tile : Tile) (state next : StandardSearchState)
    (hnext : NextStandardStateAt hand tile state next) :
    state.tileIndex < next.tileIndex := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  simp [applyStandardChoice]

def initialStandardState : StandardSearchState :=
  { tileIndex := 0
    used := 0
    pair := none
    meldHistory := []
    taatsuHistory := []
    melds := 0
    taatsu := 0 }

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
  state.melds + hand.fixedMelds = 4 ∧ state.pair.isSome

/-- The DP query: a complete standard decomposition is reachable in `fuel` choices. -/
def StandardSearch
    (hand : Hand) (fuel : Nat) : Prop :=
  ∃ state, reachableWithin hand fuel state ∧
    IsStandardSearchComplete hand state

def pairHistoryTiles (pair : Option Tile) : Multiset Tile :=
  pair.elim 0 pairTiles

def taatsuHistoryTiles : List Taatsu → Multiset Tile
  | [] => 0
  | taatsu :: taatsus => taatsuTiles taatsu + taatsuHistoryTiles taatsus

def stateHistoryTiles (state : StandardSearchState) : Multiset Tile :=
  pairHistoryTiles state.pair +
    meldsTiles state.meldHistory.reverse +
    taatsuHistoryTiles state.taatsuHistory.reverse

lemma taatsuHistoryTiles_append_single (history : List Taatsu) (taatsu : Taatsu) :
    taatsuHistoryTiles (history ++ [taatsu]) =
      taatsuHistoryTiles history + taatsuTiles taatsu := by
  induction history with
  | nil => simp [taatsuHistoryTiles]
  | cons head tail ih =>
      simp [taatsuHistoryTiles, ih, Multiset.add_assoc]

lemma meldsTiles_append_single (history : List Meld) (meld : Meld) :
    meldsTiles (history ++ [meld]) =
      meldsTiles history + meldTiles meld := by
  have aux : ∀ (items : List Meld) (acc : Multiset Tile),
      List.foldr (fun item rest => meldTiles item + rest) acc items =
        List.foldr (fun item rest => meldTiles item + rest) 0 items + acc := by
    intro items
    induction items with
    | nil =>
        intro acc
        simp
    | cons head tail ih =>
        intro acc
        simp only [List.foldr]
        rw [ih]
        ac_rfl
  simpa [meldsTiles, List.foldr_append] using aux history (meldTiles meld)

lemma applyStandardChoice_used_eq_historyTiles
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice)
    (hvalid : ValidStandardChoice hand state choice)
    (hstate : state.used = stateHistoryTiles state) :
    (applyStandardChoice hand state choice hvalid).used =
      stateHistoryTiles (applyStandardChoice hand state choice hvalid) := by
  cases choice with
  | skip =>
      simpa [applyStandardChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles] using hstate
  | pair tile =>
      have hpair : state.pair.isNone := by
        simpa [choiceUsesPair] using hvalid.2.2.2
      cases hstatePair : state.pair with
      | none =>
          simp only [applyStandardChoice]
          change state.used + pairTiles tile = _
          rw [hstate]
          simp [applyStandardChoice, stateHistoryTiles, pairHistoryTiles,
            taatsuHistoryTiles, choiceTiles, hstatePair]
          ac_rfl
      | some oldPair =>
          simp [hstatePair] at hpair
  | taatsu taatsu =>
      simp only [applyStandardChoice]
      change state.used + taatsuTiles taatsu = _
      rw [hstate]
      simp [applyStandardChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles, List.reverse_cons,
        taatsuHistoryTiles_append_single]
      ac_rfl
  | meld meld =>
      simp only [applyStandardChoice]
      change state.used + meldTiles meld = _
      rw [hstate]
      simp [applyStandardChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles, List.reverse_cons,
        meldsTiles_append_single]
      ac_rfl

lemma reachableWithin_used_eq_historyTiles
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.used = stateHistoryTiles state := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyStandardChoice_used_eq_historyTiles
        hand previous choice hvalid (ih previous hprevious)

lemma applyStandardChoice_melds_eq_history_length
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice)
    (hvalid : ValidStandardChoice hand state choice)
    (hstate : state.melds = state.meldHistory.length) :
    (applyStandardChoice hand state choice hvalid).melds =
      (applyStandardChoice hand state choice hvalid).meldHistory.length := by
  cases choice <;> simp [applyStandardChoice, hstate, choiceUsesMeld]

lemma reachableWithin_melds_eq_history_length
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.melds = state.meldHistory.length := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyStandardChoice_melds_eq_history_length
        hand previous choice hvalid (ih previous hprevious)

lemma applyStandardChoice_taatsu_eq_history_length
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice)
    (hvalid : ValidStandardChoice hand state choice)
    (hstate : state.taatsu = state.taatsuHistory.length) :
    (applyStandardChoice hand state choice hvalid).taatsu =
      (applyStandardChoice hand state choice hvalid).taatsuHistory.length := by
  cases choice <;> simp [applyStandardChoice, hstate, choiceUsesTaatsu]

lemma reachableWithin_taatsu_eq_history_length
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.taatsu = state.taatsuHistory.length := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyStandardChoice_taatsu_eq_history_length
        hand previous choice hvalid (ih previous hprevious)

/-- States reached from a given state while processing tile kinds in order. -/
def reachableOnTilesFrom
    (hand : Hand) : List Tile → StandardSearchState →
      StandardSearchState → Prop
  | [], start, state => state = start
  | tile :: tiles, start, state =>
      ∃ middle,
        NextStandardStateAt hand tile start middle ∧
          reachableOnTilesFrom hand tiles middle state

/-- States reached while processing a prescribed sequence of tile kinds. -/
def reachableOnTiles
    (hand : Hand) (tiles : List Tile) (state : StandardSearchState) : Prop :=
  reachableOnTilesFrom hand tiles initialStandardState state

def StandardSearchOnTiles
    (hand : Hand) (tiles : List Tile) : Prop :=
  ∃ state, reachableOnTiles hand tiles state ∧
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
        state.pair.isSome := by
  rfl

def standardTileAt (index : Fin 34) : Tile :=
  match index with
  | ⟨value, hvalue⟩ =>
        if hsuited : value < 27 then
          let suit :=
            if hman : value < 9 then Suit.man
            else if hpin : value < 18 then Suit.pin
            else Suit.sou
          Tile.suited suit ⟨value % 9, by omega⟩
        else
          Tile.honor ⟨value - 27, by omega⟩

def standardTileOrder : List Tile :=
  (List.finRange 34).map standardTileAt

def StandardSearchOnTileOrder (hand : Hand) : Prop :=
  StandardSearchOnTiles hand standardTileOrder

lemma standardTileOrder_length :
    standardTileOrder.length = 34 := by
  simp [standardTileOrder]

lemma tile_mem_standardTileOrder :
    ∀ tile : Tile, tile ∈ standardTileOrder := by
  native_decide

/-- A standard-form target before the fixed melds are added. -/
def standardTarget (pair : Tile) (melds : List Meld) : Multiset Tile :=
  pairTiles pair + meldsTiles melds

def standardTargetWithTaatsu
    (pair : Tile) (melds : List Meld) (taatsus : List Taatsu) : Multiset Tile :=
  standardTarget pair melds + taatsuHistoryTiles taatsus

def standardTargetWithTaatsuOfState
    (state : StandardSearchState) : Option (Multiset Tile) :=
  state.pair.map fun pair =>
    standardTargetWithTaatsu pair state.meldHistory.reverse
      state.taatsuHistory.reverse

lemma standardTargetWithTaatsuOfState_eq_some_iff
    (state : StandardSearchState) (target : Multiset Tile) :
    standardTargetWithTaatsuOfState state = some target ↔
      ∃ pair, state.pair = some pair ∧
        target = standardTargetWithTaatsu pair state.meldHistory.reverse
          state.taatsuHistory.reverse := by
  constructor
  · intro htarget
    cases hpair : state.pair with
    | none =>
        simp [standardTargetWithTaatsuOfState, hpair] at htarget
    | some pair =>
        refine ⟨pair, rfl, ?_⟩
        simpa [standardTargetWithTaatsuOfState, hpair] using htarget.symm
  · rintro ⟨pair, hpair, rfl⟩
    rw [standardTargetWithTaatsuOfState, hpair]
    rfl

lemma standardTargetWithTaatsuOfState_eq_stateHistoryTiles
    (state : StandardSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    standardTargetWithTaatsu pair state.meldHistory.reverse
        state.taatsuHistory.reverse =
      stateHistoryTiles state := by
  simp [standardTargetWithTaatsu, standardTarget, stateHistoryTiles,
    pairHistoryTiles, hpair, Multiset.add_assoc]

lemma standardTargetWithTaatsu_count_le_hand
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (standardTargetWithTaatsu pair state.meldHistory.reverse
        state.taatsuHistory.reverse).count tile ≤ hand.counts tile := by
  intro tile
  rw [standardTargetWithTaatsuOfState_eq_stateHistoryTiles state pair hpair]
  rw [← reachableWithin_used_eq_historyTiles hand fuel state hreachable]
  exact reachableWithin_used_subset hand fuel state hreachable tile

lemma standardTargetExchange_handStep
    (target : TileCounts) (before : Hand) (discarded drawn : Tile)
    (hdrawn : target drawn > before.counts drawn)
    (hdiscarded : before.counts discarded > target discarded)
    (hne : discarded ≠ drawn) :
    HandStep before (exchangeHand before discarded drawn) := by
  apply TargetExchange.handStep
  exact ⟨discarded, drawn, hdrawn, hdiscarded, hne, rfl⟩

lemma reachesExchange_of_targetExchange
    (target : TileCounts) (before : Hand) (discarded drawn : Tile)
    (hdrawn : target drawn > before.counts drawn)
    (hdiscarded : before.counts discarded > target discarded)
    (hne : discarded ≠ drawn)
    (hrest :
      ReachesExchange (exchangeHand before discarded drawn) after distance) :
    ReachesExchange before after (distance + 1) := by
  apply ReachesExchange.step
    (standardTargetExchange_handStep target before discarded drawn
      hdrawn hdiscarded hne)
  exact hrest

lemma exchangeHand_fixedMelds
    (before : Hand) (discarded drawn : Tile) :
    (exchangeHand before discarded drawn).fixedMelds = before.fixedMelds := by
  rfl

def standardTargetOfState
    (state : StandardSearchState) : Option (Multiset Tile) :=
  state.pair.map fun pair =>
    standardTarget pair state.meldHistory.reverse

lemma standardTargetOfState_eq_some_iff
    (state : StandardSearchState) (target : Multiset Tile) :
    standardTargetOfState state = some target ↔
      ∃ pair, state.pair = some pair ∧
        target = standardTarget pair state.meldHistory.reverse := by
  constructor
  · intro htarget
    cases hpair : state.pair with
    | none =>
        simp [standardTargetOfState, hpair] at htarget
    | some pair =>
        refine ⟨pair, rfl, ?_⟩
        simpa [standardTargetOfState, hpair] using htarget.symm
  · rintro ⟨pair, hpair, rfl⟩
    rw [standardTargetOfState, hpair]
    rfl

/-- The number of copies of each tile still required by a target. -/
def targetDeficit (hand : Hand) (target : Multiset Tile) : Nat :=
  ∑ tile : Tile, (target.count tile - hand.counts tile)

lemma countDeficit_exchange
    (target : TileCounts) (before : Hand) (discarded drawn : Tile)
    (hdrawn : target drawn > before.counts drawn)
    (hdiscarded : before.counts discarded > target discarded)
    (hne : discarded ≠ drawn) :
    countDeficit (exchangeHand before discarded drawn).counts target =
      countDeficit before.counts target - 1 := by
  let deficit : Tile → Nat := fun tile => target tile - before.counts tile
  let afterDeficit : Tile → Nat :=
    fun tile => target tile - (exchangeHand before discarded drawn).counts tile
  have hdrawn' :
      afterDeficit drawn = deficit drawn - 1 := by
    change target drawn - exchangeCounts before discarded drawn drawn =
      target drawn - before.counts drawn - 1
    exact deficit_after_drawing target before discarded drawn hne hdrawn
  have hdiscarded' :
      afterDeficit discarded = deficit discarded := by
    change target discarded - exchangeCounts before discarded drawn discarded =
      target discarded - before.counts discarded
    exact deficit_after_discarding target before discarded drawn hne hdiscarded
  have hother (tile : Tile) (htileDiscarded : tile ≠ discarded)
      (htileDrawn : tile ≠ drawn) :
      afterDeficit tile = deficit tile := by
    change target tile - exchangeCounts before discarded drawn tile =
      target tile - before.counts tile
    exact deficit_unchanged target before discarded drawn tile
      htileDiscarded htileDrawn
  have hdiscarded_zero : deficit discarded = 0 := by
    dsimp [deficit]
    omega
  have hdrawn_deficit :
      deficit drawn = target drawn - before.counts drawn := by
    rfl
  have hsum :
      (∑ tile : Tile, afterDeficit tile) =
        (∑ tile : Tile, deficit tile) - 1 := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset Tile)
      afterDeficit (Finset.mem_univ drawn)]
    rw [← Finset.sum_erase_add (Finset.univ.erase drawn)
      afterDeficit (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ discarded⟩)]
    rw [← Finset.sum_erase_add (Finset.univ : Finset Tile)
      deficit (Finset.mem_univ drawn)]
    rw [← Finset.sum_erase_add (Finset.univ.erase drawn)
      deficit (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ discarded⟩)]
    have hrest :
        (∑ tile ∈ (Finset.univ.erase drawn).erase discarded, afterDeficit tile) =
          ∑ tile ∈ (Finset.univ.erase drawn).erase discarded, deficit tile := by
      apply Finset.sum_congr rfl
      intro tile htile
      exact hother tile
        (Finset.mem_erase.mp htile).1
        (Finset.mem_erase.mp (Finset.mem_erase.mp htile).2).1
    rw [hrest, hdiscarded', hdrawn', hdiscarded_zero]
    rw [hdrawn_deficit]
    omega
  change (∑ tile : Tile, afterDeficit tile) =
    (∑ tile : Tile, deficit tile) - 1
  exact hsum

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

lemma standardTarget_count_le_stateHistoryTiles
    (state : StandardSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (standardTarget pair state.meldHistory.reverse).count tile ≤
        (stateHistoryTiles state).count tile := by
  intro tile
  simp [standardTarget, stateHistoryTiles, pairHistoryTiles, hpair,
    Multiset.count_add]

lemma standardTarget_count_le_used
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (standardTarget pair state.meldHistory.reverse).count tile ≤
        state.used.count tile := by
  intro tile
  rw [reachableWithin_used_eq_historyTiles hand fuel state hreachable]
  exact standardTarget_count_le_stateHistoryTiles state pair hpair tile

lemma standardTarget_count_le_hand
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (standardTarget pair state.meldHistory.reverse).count tile ≤
        hand.counts tile := by
  intro tile
  exact le_trans
    (standardTarget_count_le_used hand fuel state hreachable pair hpair tile)
    (reachableWithin_used_subset hand fuel state hreachable tile)

lemma standardTarget_hasMeldCount_of_complete
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcomplete : IsStandardSearchComplete hand state) :
    HasStandardMeldCount hand state.meldHistory.reverse := by
  have hlength := reachableWithin_melds_eq_history_length
    hand fuel state hreachable
  rcases hcomplete with ⟨hmelds, _⟩
  unfold HasStandardMeldCount
  simpa [List.length_reverse, hlength] using hmelds

lemma standardTargetOfState_exists_of_complete
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcomplete : IsStandardSearchComplete hand state) :
    ∃ target, standardTargetOfState state = some target ∧
      HasStandardMeldCount hand state.meldHistory.reverse := by
  cases hpair : state.pair with
  | none =>
      exfalso
      simpa [hpair] using hcomplete.2
  | some pair =>
      refine ⟨standardTarget pair state.meldHistory.reverse, ?_, ?_⟩
      · rw [standardTargetOfState, hpair]
        rfl
      · exact standardTarget_hasMeldCount_of_complete
          hand fuel state hreachable hcomplete

end Shanten
