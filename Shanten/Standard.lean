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

def taatsuCompletionTile : Taatsu → Tile
  | .pair tile => tile
  | .sequence suit start =>
      if hstart : start.val ≤ 6 then
        Tile.suited suit ⟨start.val + 2, by omega⟩
      else
        Tile.suited suit ⟨start.val - 1, by omega⟩

def taatsuCompletionMeld : Taatsu → Meld
  | .pair tile => .triplet tile
  | .sequence suit start =>
      .sequence suit
        ⟨if hstart : start.val ≤ 6 then start.val else start.val - 1, by
          by_cases h : start.val ≤ 6 <;> simp [h] <;> omega⟩

lemma taatsuTiles_add_completionTile
    (taatsu : Taatsu) :
    taatsuTiles taatsu + Multiset.replicate 1 (taatsuCompletionTile taatsu) =
      meldTiles (taatsuCompletionMeld taatsu) := by
  cases taatsu with
  | pair tile =>
      simp [taatsuTiles, taatsuCompletionTile, taatsuCompletionMeld,
        pairTiles, meldTiles, Multiset.replicate_succ]
  | sequence suit start =>
      by_cases hstart : start.val ≤ 6
      · simp only [taatsuTiles, taatsuCompletionTile, taatsuCompletionMeld,
          meldTiles, dif_pos hstart]
        change Multiset.ofList
            [ Tile.suited suit ⟨start.val, by omega⟩
            , Tile.suited suit ⟨start.val + 1, by omega⟩ ] +
            Multiset.ofList [Tile.suited suit ⟨start.val + 2, by omega⟩] =
          Multiset.ofList
            [ Tile.suited suit ⟨start.val, by omega⟩
            , Tile.suited suit ⟨start.val + 1, by omega⟩
            , Tile.suited suit ⟨start.val + 2, by omega⟩ ]
        rw [Multiset.coe_add]
        rfl
      · have hstart' : start.val = 7 := by omega
        simp only [taatsuTiles, taatsuCompletionTile, taatsuCompletionMeld,
          meldTiles, dif_neg hstart, hstart', dif_neg (by omega)]
        change Multiset.ofList
            [ Tile.suited suit ⟨7, by omega⟩
            , Tile.suited suit ⟨8, by omega⟩ ] +
            Multiset.ofList [Tile.suited suit ⟨6, by omega⟩] =
          Multiset.ofList
            [ Tile.suited suit ⟨6, by omega⟩
            , Tile.suited suit ⟨7, by omega⟩
            , Tile.suited suit ⟨8, by omega⟩ ]
        rw [Multiset.coe_add]
        apply Multiset.coe_eq_coe.mpr
        exact
          (List.Perm.cons _ (List.Perm.swap _ _ [])).trans
            (List.Perm.swap _ _ _).symm

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

lemma validStandardChoice_of
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice)
    (hused :
      ∀ tile, (state.used + choiceTiles choice).count tile ≤ hand.counts tile)
    (hmelds :
      state.melds + (if choiceUsesMeld choice = true then 1 else 0) ≤ 4)
    (htaatsu :
      state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0) ≤ 4)
    (hpair : state.pair.isNone ∨ choiceUsesPair choice = false) :
    ValidStandardChoice hand state choice :=
  ⟨hused, hmelds, htaatsu, hpair⟩

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

lemma standardChoice_mem_all
    (choice : StandardChoice) :
    choice ∈ allStandardChoices := by
  cases choice with
  | skip =>
      simp [allStandardChoices]
  | pair tile =>
      simp [allStandardChoices]
  | taatsu taatsu =>
      simp [allStandardChoices]
  | meld meld =>
      simp [allStandardChoices]

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

/-- A DP state containing four meld-or-taatsu blocks and one pair. -/
def IsStandardBlockSearchComplete
    (hand : Hand) (state : StandardSearchState) : Prop :=
  state.melds + state.taatsu + hand.fixedMelds = 4 ∧ state.pair.isSome

/-- The DP query: a complete standard decomposition is reachable in `fuel` choices. -/
def StandardSearch
    (hand : Hand) (fuel : Nat) : Prop :=
  ∃ state, reachableWithin hand fuel state ∧
    IsStandardSearchComplete hand state

/-- The DP query using the four-block criterion. -/
def StandardBlockSearch
    (hand : Hand) (fuel : Nat) : Prop :=
  ∃ state, reachableWithin hand fuel state ∧
    IsStandardBlockSearchComplete hand state

def pairHistoryTiles (pair : Option Tile) : Multiset Tile :=
  pair.elim 0 pairTiles

def taatsuHistoryTiles : List Taatsu → Multiset Tile
  | [] => 0
  | taatsu :: taatsus => taatsuTiles taatsu + taatsuHistoryTiles taatsus

def taatsuCompletionMelds : List Taatsu → List Meld
  | [] => []
  | taatsu :: taatsus =>
      taatsuCompletionMeld taatsu :: taatsuCompletionMelds taatsus

def taatsuCompletionTiles : List Taatsu → Multiset Tile
  | [] => 0
  | taatsu :: taatsus =>
      Multiset.replicate 1 (taatsuCompletionTile taatsu) +
        taatsuCompletionTiles taatsus

lemma taatsuHistoryTiles_add_completionTiles
    (taatsus : List Taatsu) :
    taatsuHistoryTiles taatsus + taatsuCompletionTiles taatsus =
      meldsTiles (taatsuCompletionMelds taatsus) := by
  induction taatsus with
  | nil =>
      rfl
  | cons taatsu taatsus ih =>
      simp only [taatsuHistoryTiles, taatsuCompletionTiles,
        taatsuCompletionMelds, meldsTiles]
      calc
        _ =
            (taatsuTiles taatsu +
                Multiset.replicate 1 (taatsuCompletionTile taatsu)) +
              (taatsuHistoryTiles taatsus + taatsuCompletionTiles taatsus) := by
                ac_rfl
        _ = meldTiles (taatsuCompletionMeld taatsu) +
              meldsTiles (taatsuCompletionMelds taatsus) := by
                rw [taatsuTiles_add_completionTile, ih]
        _ = _ := by rfl

lemma taatsuCompletionMelds_length (taatsus : List Taatsu) :
    (taatsuCompletionMelds taatsus).length = taatsus.length := by
  induction taatsus <;> simp [taatsuCompletionMelds, *]

lemma taatsuCompletionTiles_card (taatsus : List Taatsu) :
    (taatsuCompletionTiles taatsus).card = taatsus.length := by
  induction taatsus with
  | nil =>
      rfl
  | cons taatsu taatsus ih =>
      simp [taatsuCompletionTiles, ih]

lemma pairTiles_card (tile : Tile) :
    (pairTiles tile).card = 2 := by
  simp [pairTiles]

lemma meldTiles_card (meld : Meld) : (meldTiles meld).card = 3 := by
  cases meld <;> simp [meldTiles]

lemma meldsTiles_card (melds : List Meld) :
    (meldsTiles melds).card = 3 * melds.length := by
  induction melds with
  | nil =>
      rfl
  | cons meld melds ih =>
      change (meldTiles meld + meldsTiles melds).card =
        3 * (melds.length + 1)
      rw [Multiset.card_add, meldTiles_card, ih]
      omega

def completedMeldsForState (state : StandardSearchState) : List Meld :=
  state.meldHistory.reverse ++
    taatsuCompletionMelds state.taatsuHistory.reverse

lemma completedMeldsForState_length
    (state : StandardSearchState) :
    (completedMeldsForState state).length =
      state.meldHistory.length + state.taatsuHistory.length := by
  simp [completedMeldsForState, taatsuCompletionMelds_length,
    Nat.add_comm]

lemma meldsTiles_append (left right : List Meld) :
    meldsTiles (left ++ right) = meldsTiles left + meldsTiles right := by
  induction left with
  | nil =>
      simp [meldsTiles]
  | cons meld left ih =>
      change meldTiles meld + meldsTiles (left ++ right) =
        (meldTiles meld + meldsTiles left) + meldsTiles right
      rw [ih]
      ac_rfl

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

def StandardBlockSearchOnTiles
    (hand : Hand) (tiles : List Tile) : Prop :=
  ∃ state, reachableOnTiles hand tiles state ∧
    IsStandardBlockSearchComplete hand state

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

lemma standardBlockSearch_complete_iff
    (hand : Hand) (fuel : Nat) :
    StandardBlockSearch hand fuel ↔
        ∃ state, reachableWithin hand fuel state ∧
          state.melds + state.taatsu + hand.fixedMelds = 4 ∧
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

lemma completedMeldsForState_tiles
    (state : StandardSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    pairTiles pair + meldsTiles (completedMeldsForState state) =
      standardTargetWithTaatsu pair state.meldHistory.reverse
          state.taatsuHistory.reverse +
        taatsuCompletionTiles state.taatsuHistory.reverse := by
  simp only [completedMeldsForState, standardTargetWithTaatsu, standardTarget]
  rw [meldsTiles_append]
  rw [← taatsuHistoryTiles_add_completionTiles]
  ac_rfl

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

lemma exists_lt_of_sum_eq_of_ne
    (current target : TileCounts)
    (hsum : (∑ tile : Tile, current tile) =
      ∑ tile : Tile, target tile)
    (hne : current ≠ target) :
    ∃ tile, current tile < target tile := by
  by_contra hexists
  push_neg at hexists
  have hle : ∀ tile, target tile ≤ current tile := by
    intro tile
    exact hexists tile
  have heq :
      ∀ tile ∈ (Finset.univ : Finset Tile), target tile = current tile := by
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := target) (g := current) (fun tile _ => hle tile)).mp
    exact hsum.symm
  apply hne
  funext tile
  exact (heq tile (Finset.mem_univ tile)).symm

lemma exists_target_exchange_tiles
    (before : Hand) (target : TileCounts)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile)
    (hne : before.counts ≠ target) :
    ∃ discarded drawn,
      target drawn > before.counts drawn ∧
      before.counts discarded > target discarded ∧
      discarded ≠ drawn := by
  obtain ⟨drawn, hdrawn⟩ :=
    exists_lt_of_sum_eq_of_ne before.counts target hsum hne
  obtain ⟨discarded, hdiscarded⟩ :=
    exists_lt_of_sum_eq_of_ne target before.counts hsum.symm
      (Ne.symm hne)
  refine ⟨discarded, drawn, hdrawn, hdiscarded, ?_⟩
  intro heq
  subst discarded
  omega

lemma targetExchange_exists_of_equal_sum
    (before : Hand) (target : TileCounts)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile)
    (hne : before.counts ≠ target) :
    ∃ after, TargetExchange target before after := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles⟩ :=
    exists_target_exchange_tiles before target hsum hne
  refine ⟨exchangeHand before discarded drawn, ?_⟩
  exact ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles, rfl⟩

lemma exchangeCounts_sum
    (before : Hand) (discarded drawn : Tile)
    (hne : discarded ≠ drawn) (hdiscarded : before.counts discarded > 0) :
    (∑ tile : Tile, exchangeCounts before discarded drawn tile) =
      ∑ tile : Tile, before.counts tile := by
  have hstep := exchangeCounts_step before discarded drawn hne hdiscarded
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
  omega

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

def targetHand (before : Hand) (target : TileCounts) : Hand :=
  { counts := target
    fixedMelds := before.fixedMelds }

def countsOfTiles (tiles : Multiset Tile) : TileCounts :=
  fun tile => tiles.count tile

lemma targetHand_hasTiles_countsOfTiles
    (before : Hand) (tiles : Multiset Tile) :
    HasTiles (targetHand before (countsOfTiles tiles)) tiles := by
  intro tile
  rfl

lemma countsOfTiles_sum_eq_card (tiles : Multiset Tile) :
    (∑ tile : Tile, countsOfTiles tiles tile) = tiles.card := by
  induction tiles using Multiset.induction_on with
  | empty =>
      simp [countsOfTiles]
  | @cons tile tiles ih =>
      simp [countsOfTiles, ih, Finset.sum_add_distrib]

lemma reachesExchange_targetHand_of_equal_sum
    (before : Hand) (target : TileCounts)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile) :
    ∃ distance,
      ReachesExchange before (targetHand before target) distance := by
  have aux : ∀ d : Nat, ∀ current : Hand,
      (∑ tile : Tile, current.counts tile) =
        ∑ tile : Tile, target tile →
      countDeficit current.counts target = d →
      ∃ distance,
        ReachesExchange current (targetHand current target) distance := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih current hsumCurrent hmeasure
    by_cases hd : d = 0
    · have hsumzero :
          (∑ tile : Tile, (target tile - current.counts tile)) = 0 := by
        simpa [countDeficit, hd] using hmeasure
      have hzero :
          ∀ tile ∈ (Finset.univ : Finset Tile),
            target tile - current.counts tile = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun tile _ => Nat.zero_le _)).mp
        exact hsumzero
      have hle : ∀ tile, target tile ≤ current.counts tile := by
        intro tile
        have hzeroTile := hzero tile (Finset.mem_univ tile)
        omega
      have heq :
          ∀ tile ∈ (Finset.univ : Finset Tile),
            target tile = current.counts tile := by
        apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
          (f := target) (g := current.counts)
          (fun tile _ => hle tile)).mp
        exact hsumCurrent.symm
      have hcounts : target = current.counts := by
        funext tile
        exact heq tile (Finset.mem_univ tile)
      subst hcounts
      exact ⟨0, ReachesExchange.done⟩
    · have hpositive : 0 < d := Nat.pos_of_ne_zero hd
      have hne : current.counts ≠ target := by
        intro hcounts
        subst hcounts
        apply hd
        simpa [countDeficit] using hmeasure.symm
      obtain ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles⟩ :=
        exists_target_exchange_tiles current target hsumCurrent hne
      let next := exchangeHand current discarded drawn
      have hsumAfter :
          (∑ tile : Tile, next.counts tile) =
            ∑ tile : Tile, target tile := by
        change (∑ tile : Tile, exchangeCounts current discarded drawn tile) =
          ∑ tile : Tile, target tile
        rw [exchangeCounts_sum current discarded drawn hneTiles
          (by omega)]
        exact hsumCurrent
      have hdefAfter :
          countDeficit next.counts target < d := by
        dsimp [next]
        rw [countDeficit_exchange target current discarded drawn
          hdrawn hdiscarded hneTiles, hmeasure]
        omega
      obtain ⟨distance, hrest⟩ := ih
        (countDeficit next.counts target) hdefAfter next
        hsumAfter rfl
      refine ⟨distance + 1, ?_⟩
      apply ReachesExchange.step
      · exact standardTargetExchange_handStep target current discarded drawn
          hdrawn hdiscarded hneTiles
      · simpa [next, targetHand, exchangeHand] using hrest
  exact aux (countDeficit before.counts target) before hsum rfl

lemma complete_standard_targetHand
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List Meld)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds)) :
    Complete .standard (targetHand before target) := by
  exact ⟨hvalid, pair, melds, hmelds, htiles⟩

lemma reachesCompletion_standard_of_equal_sum
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List Meld)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds)) :
    ∃ distance,
      ReachesCompletion Complete .standard before distance := by
  obtain ⟨distance, hexchange⟩ :=
    reachesExchange_targetHand_of_equal_sum before target hsum
  have hcomplete :
      Complete .standard (targetHand before target) :=
    complete_standard_targetHand before target pair melds
      hvalid hmelds htiles
  have hdone :
      ReachesCompletion Complete .standard
        (targetHand before target) 0 :=
    ReachesCompletion.done hcomplete
  exact ⟨distance,
    ReachesExchange.toReachesCompletion hexchange hdone⟩

/-- A target has the required number of concealed melds for a hand. -/
def HasStandardMeldCount (hand : Hand) (melds : List Meld) : Prop :=
  melds.length + hand.fixedMelds = 4

/-- A standard-form decomposition before completing its taatsu blocks. -/
structure StandardBlockDecomposition (hand : Hand) where
  pair : Tile
  melds : List Meld
  taatsus : List Taatsu
  blocks : melds.length + taatsus.length + hand.fixedMelds = 4
  targetWithinHand :
    ∀ tile,
      (standardTargetWithTaatsu pair melds taatsus).count tile ≤ hand.counts tile
  completionCopyLimit :
    ∀ tile,
      (standardTargetWithTaatsu pair melds taatsus +
        taatsuCompletionTiles taatsus).count tile ≤ 4

def standardChoiceTiles : List StandardChoice → Multiset Tile
  | [] => 0
  | choice :: choices =>
      choiceTiles choice + standardChoiceTiles choices

lemma standardChoiceTiles_append
    (left right : List StandardChoice) :
    standardChoiceTiles (left ++ right) =
      standardChoiceTiles left + standardChoiceTiles right := by
  induction left with
  | nil =>
      simp [standardChoiceTiles]
  | cons choice left ih =>
      simp [standardChoiceTiles, ih, Multiset.add_assoc]

def StandardBlockDecomposition.blockChoices
    {hand : Hand} (decomposition : StandardBlockDecomposition hand) :
    List StandardChoice :=
  .pair decomposition.pair ::
    decomposition.melds.map StandardChoice.meld ++
      decomposition.taatsus.map StandardChoice.taatsu

lemma StandardBlockDecomposition.blockChoices_length
    {hand : Hand} (decomposition : StandardBlockDecomposition hand) :
    decomposition.blockChoices.length =
      1 + decomposition.melds.length + decomposition.taatsus.length := by
  simp [StandardBlockDecomposition.blockChoices]
  omega

lemma StandardBlockDecomposition.blockChoices_mem_all
    {hand : Hand} (decomposition : StandardBlockDecomposition hand) :
    ∀ choice, choice ∈ decomposition.blockChoices →
      choice ∈ allStandardChoices := by
  intro choice hchoice
  unfold StandardBlockDecomposition.blockChoices at hchoice
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hchoice
  rcases hchoice with (hpair | hmeld) | htaatsu
  · rw [hpair]
    exact standardChoice_mem_all _
  · rcases hmeld with ⟨meld, _, hmeld⟩
    rw [← hmeld]
    exact standardChoice_mem_all _
  · rcases htaatsu with ⟨taatsu, _, htaatsu⟩
    rw [← htaatsu]
    exact standardChoice_mem_all _

lemma standardChoiceTiles_map_meld
    (melds : List Meld) :
    standardChoiceTiles (melds.map StandardChoice.meld) =
      meldsTiles melds := by
  induction melds with
  | nil =>
      rfl
  | cons meld melds ih =>
      simp [standardChoiceTiles, choiceTiles, meldsTiles, ih]

lemma standardChoiceTiles_map_taatsu
    (taatsus : List Taatsu) :
    standardChoiceTiles (taatsus.map StandardChoice.taatsu) =
      taatsuHistoryTiles taatsus := by
  induction taatsus with
  | nil =>
      rfl
  | cons taatsu taatsus ih =>
      simp [standardChoiceTiles, choiceTiles, taatsuHistoryTiles, ih]

lemma StandardBlockDecomposition.blockChoices_tiles
    {hand : Hand} (decomposition : StandardBlockDecomposition hand) :
    standardChoiceTiles decomposition.blockChoices =
      standardTargetWithTaatsu decomposition.pair decomposition.melds
        decomposition.taatsus := by
  unfold StandardBlockDecomposition.blockChoices
  simp [standardChoiceTiles, choiceTiles, List.map_append,
    standardChoiceTiles_append,
    standardChoiceTiles_map_meld, standardChoiceTiles_map_taatsu,
    standardTargetWithTaatsu, standardTarget]
  ac_rfl

lemma standardChoiceTiles_prefix_count_le
    (pre suffix : List StandardChoice) (tile : Tile) :
    (standardChoiceTiles pre).count tile ≤
      (standardChoiceTiles (pre ++ suffix)).count tile := by
  rw [standardChoiceTiles_append]
  simp only [Multiset.count_add]
  omega

lemma StandardBlockDecomposition.prefix_count_le_hand
    {hand : Hand} (decomposition : StandardBlockDecomposition hand)
    (pre suffix : List StandardChoice)
    (hchoices : decomposition.blockChoices = pre ++ suffix) :
    ∀ tile, (standardChoiceTiles pre).count tile ≤ hand.counts tile := by
  intro tile
  have hprefix :
      (standardChoiceTiles pre).count tile ≤
        (standardChoiceTiles decomposition.blockChoices).count tile := by
    rw [hchoices]
    exact standardChoiceTiles_prefix_count_le pre suffix tile
  have htarget :
      (standardChoiceTiles decomposition.blockChoices).count tile ≤
        hand.counts tile := by
    rw [decomposition.blockChoices_tiles]
    exact decomposition.targetWithinHand tile
  exact hprefix.trans htarget

lemma StandardBlockDecomposition.prefix_completion_count_le_four
    {hand : Hand} (decomposition : StandardBlockDecomposition hand)
    (pre suffix : List StandardChoice)
    (hchoices : decomposition.blockChoices = pre ++ suffix) :
    ∀ tile,
        (standardChoiceTiles pre +
        taatsuCompletionTiles decomposition.taatsus).count tile ≤ 4 := by
  intro tile
  have hprefix :
        (standardChoiceTiles pre).count tile ≤
        (standardChoiceTiles decomposition.blockChoices).count tile := by
    rw [hchoices]
    exact standardChoiceTiles_prefix_count_le pre suffix tile
  have hfull :
      (standardChoiceTiles decomposition.blockChoices +
        taatsuCompletionTiles decomposition.taatsus).count tile ≤ 4 := by
    rw [decomposition.blockChoices_tiles]
    exact decomposition.completionCopyLimit tile
  rw [Multiset.count_add] at hfull ⊢
  omega

def StandardBlockDecomposition.completedTarget
    {hand : Hand} (decomposition : StandardBlockDecomposition hand) :
    Multiset Tile :=
  standardTargetWithTaatsu decomposition.pair decomposition.melds
      decomposition.taatsus +
    taatsuCompletionTiles decomposition.taatsus

lemma StandardBlockDecomposition.completedTarget_eq
    {hand : Hand} (decomposition : StandardBlockDecomposition hand) :
    decomposition.completedTarget =
      pairTiles decomposition.pair +
        meldsTiles
          (decomposition.melds ++
            taatsuCompletionMelds decomposition.taatsus) := by
  unfold StandardBlockDecomposition.completedTarget
    standardTargetWithTaatsu standardTarget
  rw [meldsTiles_append]
  rw [← taatsuHistoryTiles_add_completionTiles]
  ac_rfl

lemma StandardBlockDecomposition.validCounts_completedTarget
    {hand : Hand} (decomposition : StandardBlockDecomposition hand) :
    ValidCounts
      (targetHand hand (countsOfTiles decomposition.completedTarget)) := by
  intro tile
  exact decomposition.completionCopyLimit tile

lemma StandardBlockDecomposition.completedMeldCount
    {hand : Hand} (decomposition : StandardBlockDecomposition hand) :
    (decomposition.melds ++
      taatsuCompletionMelds decomposition.taatsus).length +
        hand.fixedMelds = 4 := by
  rw [List.length_append, taatsuCompletionMelds_length]
  have hblocks := decomposition.blocks
  omega

def completedTargetForState (state : StandardSearchState) (pair : Tile) :
    Multiset Tile :=
  pairTiles pair + meldsTiles (completedMeldsForState state)

def CompletionRespectsCopyLimit (state : StandardSearchState) : Prop :=
  ∀ tile,
    (state.used + taatsuCompletionTiles state.taatsuHistory.reverse).count tile ≤ 4

def ValidStandardChoiceWithCopyLimit
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice) : Prop :=
  ∃ hvalid : ValidStandardChoice hand state choice,
    CompletionRespectsCopyLimit
      (applyStandardChoice hand state choice hvalid)

lemma validStandardChoiceWithCopyLimit_of
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice)
    (hvalid : ValidStandardChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyStandardChoice hand state choice hvalid)) :
    ValidStandardChoiceWithCopyLimit hand state choice :=
  ⟨hvalid, hcopy⟩

def NextStandardStateWithCopyLimit
    (hand : Hand) (state next : StandardSearchState) : Prop :=
  ∃ choice, choice ∈ allStandardChoices ∧
    ∃ hvalid : ValidStandardChoice hand state choice,
      CompletionRespectsCopyLimit
        (applyStandardChoice hand state choice hvalid) ∧
      next = applyStandardChoice hand state choice hvalid

lemma nextStandardStateWithCopyLimit_of_choice
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice)
    (hchoice : choice ∈ allStandardChoices)
    (hvalid : ValidStandardChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyStandardChoice hand state choice hvalid)) :
    NextStandardStateWithCopyLimit hand state
      (applyStandardChoice hand state choice hvalid) :=
  ⟨choice, hchoice, hvalid, hcopy, rfl⟩

noncomputable def copyLimitChoices
    (hand : Hand) (state : StandardSearchState) : Finset StandardChoice :=
  by
    classical
    exact allStandardChoices.filter
      (fun choice =>
        ∃ hvalid : ValidStandardChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyStandardChoice hand state choice hvalid))

lemma mem_copyLimitChoices_iff
    (hand : Hand) (state : StandardSearchState) (choice : StandardChoice) :
    choice ∈ copyLimitChoices hand state ↔
      choice ∈ allStandardChoices ∧
        ∃ hvalid : ValidStandardChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyStandardChoice hand state choice hvalid) := by
  classical
  change choice ∈ allStandardChoices.filter _ ↔ _
  rw [Finset.mem_filter]

lemma nextStandardStateWithCopyLimit_iff
    (hand : Hand) (state next : StandardSearchState) :
    NextStandardStateWithCopyLimit hand state next ↔
      ∃ choice, choice ∈ copyLimitChoices hand state ∧
        ∃ hvalid : ValidStandardChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyStandardChoice hand state choice hvalid) ∧
          next = applyStandardChoice hand state choice hvalid := by
  classical
  constructor
  · rintro ⟨choice, hchoice, hvalid, hcopy, rfl⟩
    refine ⟨choice, ?_, hvalid, hcopy, rfl⟩
    change choice ∈ allStandardChoices.filter _
    exact Finset.mem_filter.mpr ⟨hchoice, ⟨hvalid, hcopy⟩⟩
  · rintro ⟨choice, hchoice, hvalid, hcopy, rfl⟩
    change choice ∈ allStandardChoices.filter _ at hchoice
    exact ⟨choice, (Finset.mem_filter.mp hchoice).1,
      hvalid, hcopy, rfl⟩

noncomputable def choicesForTileWithCopyLimit
    (hand : Hand) (state : StandardSearchState) (tile : Tile) :
    Finset StandardChoice :=
  by
    classical
    exact (choicesForTile tile).filter
      (fun choice =>
        ∃ hvalid : ValidStandardChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyStandardChoice hand state choice hvalid))

lemma mem_choicesForTileWithCopyLimit_iff
    (hand : Hand) (state : StandardSearchState) (tile : Tile)
    (choice : StandardChoice) :
    choice ∈ choicesForTileWithCopyLimit hand state tile ↔
      choice ∈ choicesForTile tile ∧
        ∃ hvalid : ValidStandardChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyStandardChoice hand state choice hvalid) := by
  classical
  change choice ∈ (choicesForTile tile).filter _ ↔ _
  rw [Finset.mem_filter]

def NextStandardStateAtWithCopyLimit
    (hand : Hand) (tile : Tile) (state next : StandardSearchState) : Prop :=
  ∃ choice, choice ∈ choicesForTileWithCopyLimit hand state tile ∧
    ∃ hvalid : ValidStandardChoice hand state choice,
      CompletionRespectsCopyLimit
        (applyStandardChoice hand state choice hvalid) ∧
      next = applyStandardChoice hand state choice hvalid

lemma nextStandardStateAtWithCopyLimit_of_choice
    (hand : Hand) (tile : Tile) (state : StandardSearchState)
    (choice : StandardChoice)
    (hchoice : choice ∈ allStandardChoices)
    (htile : tile ∈ choiceTiles choice)
    (hvalid : ValidStandardChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyStandardChoice hand state choice hvalid)) :
    NextStandardStateAtWithCopyLimit hand tile state
      (applyStandardChoice hand state choice hvalid) := by
  refine ⟨choice, ?_, hvalid, hcopy, rfl⟩
  apply (mem_choicesForTileWithCopyLimit_iff hand state tile choice).mpr
  exact ⟨Finset.mem_filter.mpr ⟨hchoice, Or.inr htile⟩,
    ⟨hvalid, hcopy⟩⟩

lemma nextStandardStateAtWithCopyLimit_skip
    (hand : Hand) (tile : Tile) (state : StandardSearchState)
    (hused : ∀ tile, state.used.count tile ≤ hand.counts tile)
    (hcopy : CompletionRespectsCopyLimit state)
    (hmelds : state.melds ≤ 4)
    (htaatsu : state.taatsu ≤ 4) :
    NextStandardStateAtWithCopyLimit hand tile state
      (applyStandardChoice hand state .skip
        (by
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [choiceTiles] using hused
          · simpa [choiceUsesMeld] using hmelds
          · simpa [choiceUsesTaatsu] using htaatsu
          · simp [choiceUsesPair])) := by
  let hvalid : ValidStandardChoice hand state .skip := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [choiceTiles] using hused
    · simpa [choiceUsesMeld] using hmelds
    · simpa [choiceUsesTaatsu] using htaatsu
    · simp [choiceUsesPair]
  refine ⟨.skip, ?_, hvalid, ?_, rfl⟩
  apply (mem_choicesForTileWithCopyLimit_iff hand state tile .skip).mpr
  · exact ⟨by simp [choicesForTile, allStandardChoices],
      ⟨hvalid, by
        simpa [CompletionRespectsCopyLimit, applyStandardChoice,
          choiceTiles] using hcopy⟩⟩
  · simpa [CompletionRespectsCopyLimit, applyStandardChoice,
      choiceTiles] using hcopy

lemma nextStandardStateAtWithCopyLimit_toNext
    (hand : Hand) (tile : Tile) (state next : StandardSearchState)
    (hnext : NextStandardStateAtWithCopyLimit hand tile state next) :
    NextStandardStateAt hand tile state next := by
  rcases hnext with ⟨choice, hchoice, hvalid, hcopy, rfl⟩
  exact ⟨choice, (mem_choicesForTileWithCopyLimit_iff
    hand state tile choice).mp hchoice |>.1, hvalid, rfl⟩

lemma nextStandardStateAtWithCopyLimit_copyLimit
    (hand : Hand) (tile : Tile) (state next : StandardSearchState)
    (hnext : NextStandardStateAtWithCopyLimit hand tile state next) :
    CompletionRespectsCopyLimit next := by
  rcases hnext with ⟨choice, hchoice, hvalid, hcopy, rfl⟩
  exact hcopy

lemma nextStandardStateAtWithCopyLimit_toNextWithCopyLimit
    (hand : Hand) (tile : Tile) (state next : StandardSearchState)
    (hnext : NextStandardStateAtWithCopyLimit hand tile state next) :
    NextStandardStateWithCopyLimit hand state next := by
  classical
  rcases hnext with ⟨choice, hchoice, hvalid, hcopy, rfl⟩
  change choice ∈ (choicesForTile tile).filter _ at hchoice
  have hchoiceAll : choice ∈ allStandardChoices :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hchoice).1).1
  exact ⟨choice, hchoiceAll, hvalid, hcopy, rfl⟩

def reachableOnTilesFromWithCopyLimit
    (hand : Hand) : List Tile → StandardSearchState →
      StandardSearchState → Prop
  | [], start, state => state = start
  | tile :: tiles, start, state =>
      ∃ middle,
        NextStandardStateAtWithCopyLimit hand tile start middle ∧
          reachableOnTilesFromWithCopyLimit hand tiles middle state

def reachableOnTilesWithCopyLimit
    (hand : Hand) (tiles : List Tile) (state : StandardSearchState) : Prop :=
  reachableOnTilesFromWithCopyLimit hand tiles initialStandardState state

def StandardBlockSearchOnTilesWithCopyLimit
    (hand : Hand) (tiles : List Tile) : Prop :=
  ∃ state, reachableOnTilesWithCopyLimit hand tiles state ∧
    IsStandardBlockSearchComplete hand state

def StandardBlockSearchOnTileOrderWithCopyLimit (hand : Hand) : Prop :=
  StandardBlockSearchOnTilesWithCopyLimit hand standardTileOrder

lemma reachableOnTilesFromWithCopyLimit_to_reachableOnTilesFrom
    (hand : Hand) (tiles : List Tile) (start state : StandardSearchState)
    (hreachable : reachableOnTilesFromWithCopyLimit
      hand tiles start state) :
    reachableOnTilesFrom hand tiles start state := by
  induction tiles generalizing start state with
  | nil =>
      exact hreachable
  | cons tile tiles ih =>
      rcases hreachable with ⟨middle, hnext, hrest⟩
      exact ⟨middle, nextStandardStateAtWithCopyLimit_toNext
        hand tile start middle hnext, ih middle state hrest⟩

lemma standardBlockSearchOnTilesWithCopyLimit_to_standardBlockSearchOnTiles
    (hand : Hand) (tiles : List Tile)
    (hsearch : StandardBlockSearchOnTilesWithCopyLimit hand tiles) :
    StandardBlockSearchOnTiles hand tiles := by
  rcases hsearch with ⟨state, hreachable, hcomplete⟩
  exact ⟨state,
    reachableOnTilesFromWithCopyLimit_to_reachableOnTilesFrom
      hand tiles initialStandardState state hreachable, hcomplete⟩

lemma reachableOnTilesWithCopyLimit_copyLimit
    (hand : Hand) (tiles : List Tile) (state : StandardSearchState)
    (hreachable : reachableOnTilesWithCopyLimit hand tiles state) :
    CompletionRespectsCopyLimit state := by
  have hinitial : CompletionRespectsCopyLimit initialStandardState := by
    intro tile
    simp [CompletionRespectsCopyLimit, initialStandardState,
      taatsuCompletionTiles]
  have aux :
      ∀ (tiles : List Tile) (start state : StandardSearchState),
        CompletionRespectsCopyLimit start →
        reachableOnTilesFromWithCopyLimit hand tiles start state →
        CompletionRespectsCopyLimit state := by
    intro remaining
    induction remaining with
    | nil =>
        intro start state hstart hreach
        subst state
        exact hstart
    | cons tile remaining ih =>
        intro start state hstart hreach
        rcases hreach with ⟨middle, hnext, hrest⟩
        exact ih middle state
          (nextStandardStateAtWithCopyLimit_copyLimit
            hand tile start middle hnext) hrest
  exact aux tiles initialStandardState state hinitial hreachable

lemma nextStandardStateWithCopyLimit_copyLimit
    (hand : Hand) (state next : StandardSearchState)
    (hnext : NextStandardStateWithCopyLimit hand state next) :
    CompletionRespectsCopyLimit next := by
  rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
  exact hcopy

def reachableWithinWithCopyLimit
    (hand : Hand) : Nat → StandardSearchState → Prop
  | 0, state => state = initialStandardState
  | fuel + 1, state =>
      ∃ previous,
        reachableWithinWithCopyLimit hand fuel previous ∧
        NextStandardStateWithCopyLimit hand previous state

lemma initialStandardState_copyLimit :
    CompletionRespectsCopyLimit initialStandardState := by
  intro tile
  simp [CompletionRespectsCopyLimit, initialStandardState,
    taatsuCompletionTiles]

lemma reachableWithinWithCopyLimit_copyLimit
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    CompletionRespectsCopyLimit state := by
  induction fuel generalizing state with
  | zero =>
      rw [hreachable]
      exact initialStandardState_copyLimit
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      exact nextStandardStateWithCopyLimit_copyLimit hand previous state hnext

lemma reachableWithinWithCopyLimit_melds_le_four
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    state.melds ≤ 4 := by
  induction fuel generalizing state with
  | zero =>
      subst state
      simp [initialStandardState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
      have hbound := hvalid.2.1
      simp only [applyStandardChoice] at hbound ⊢
      omega

lemma reachableWithinWithCopyLimit_used_subset
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    ∀ tile, state.used.count tile ≤ hand.counts tile := by
  induction fuel generalizing state with
  | zero =>
      intro tile
      subst state
      simp [initialStandardState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      intro tile
      rcases hnext with ⟨choice, _, hvalid, _, rfl⟩
      exact hvalid.1 tile

lemma reachableWithinWithCopyLimit_taatsu_le_four
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    state.taatsu ≤ 4 := by
  induction fuel generalizing state with
  | zero =>
      subst state
      simp [initialStandardState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
      have hbound := hvalid.2.2.1
      simp only [applyStandardChoice] at hbound ⊢
      omega

lemma nextStandardStateAtWithCopyLimit_skip_of_reachable
    (hand : Hand) (tile : Tile) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    NextStandardStateAtWithCopyLimit hand tile state
      (applyStandardChoice hand state .skip
        (by
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [choiceTiles] using
              reachableWithinWithCopyLimit_used_subset
                hand fuel state hreachable
          · simpa [choiceUsesMeld] using
              reachableWithinWithCopyLimit_melds_le_four
                hand fuel state hreachable
          · simpa [choiceUsesTaatsu] using
              reachableWithinWithCopyLimit_taatsu_le_four
                hand fuel state hreachable
          · simp [choiceUsesPair])) := by
  apply nextStandardStateAtWithCopyLimit_skip
    hand tile state
    (reachableWithinWithCopyLimit_used_subset hand fuel state hreachable)
    (reachableWithinWithCopyLimit_copyLimit hand fuel state hreachable)
    (reachableWithinWithCopyLimit_melds_le_four hand fuel state hreachable)
    (reachableWithinWithCopyLimit_taatsu_le_four hand fuel state hreachable)

lemma reachableOnTilesFromWithCopyLimit_skips
    (hand : Hand) (tiles : List Tile) (fuel : Nat)
    (state : StandardSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    ∃ final,
      reachableOnTilesFromWithCopyLimit hand tiles state final ∧
        reachableWithinWithCopyLimit hand (fuel + tiles.length) final := by
  induction tiles generalizing fuel state with
  | nil =>
      exact ⟨state, rfl, by simpa using hreachable⟩
  | cons tile tiles ih =>
      let hvalid : ValidStandardChoice hand state .skip := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [choiceTiles] using
            reachableWithinWithCopyLimit_used_subset
              hand fuel state hreachable
        · simpa [choiceUsesMeld] using
            reachableWithinWithCopyLimit_melds_le_four
              hand fuel state hreachable
        · simpa [choiceUsesTaatsu] using
            reachableWithinWithCopyLimit_taatsu_le_four
              hand fuel state hreachable
        · simp [choiceUsesPair]
      have hstatecopy :
          CompletionRespectsCopyLimit state :=
        reachableWithinWithCopyLimit_copyLimit
          hand fuel state hreachable
      have hcopy :
          CompletionRespectsCopyLimit
            (applyStandardChoice hand state .skip hvalid) := by
        intro tile
        dsimp [applyStandardChoice]
        simp only [choiceTiles, Multiset.add_zero]
        exact hstatecopy tile
      have hskip :
          NextStandardStateAtWithCopyLimit hand tile state
            (applyStandardChoice hand state .skip hvalid) := by
        refine ⟨.skip, ?_, hvalid, ?_, rfl⟩
        · apply (mem_choicesForTileWithCopyLimit_iff
            hand state tile .skip).mpr
          exact ⟨by simp [choicesForTile, allStandardChoices],
            ⟨hvalid, hcopy⟩⟩
        · exact hcopy
      have hreachableNext :
          reachableWithinWithCopyLimit hand (fuel + 1)
            (applyStandardChoice hand state .skip hvalid) := by
        exact ⟨state, hreachable,
          nextStandardStateAtWithCopyLimit_toNextWithCopyLimit
            hand tile state
            (applyStandardChoice hand state .skip hvalid) hskip⟩
      obtain ⟨final, hpath, hfinal⟩ :=
        ih (fuel + 1)
          (applyStandardChoice hand state .skip hvalid) hreachableNext
      refine ⟨final, ?_, ?_⟩
      · exact ⟨applyStandardChoice hand state .skip hvalid, hskip, hpath⟩
      · have hlength :
            fuel + (tile :: tiles).length = fuel + 1 + tiles.length := by
          simp only [List.length_cons]
          omega
        rw [hlength]
        exact hfinal

lemma reachableOnTilesFromWithCopyLimit_choice_then_skips
    (hand : Hand) (tile : Tile) (tiles : List Tile) (fuel : Nat)
    (state : StandardSearchState) (choice : StandardChoice)
    (hreachable : reachableWithinWithCopyLimit hand fuel state)
    (hchoice : choice ∈ allStandardChoices)
    (htile : tile ∈ choiceTiles choice)
    (hvalid : ValidStandardChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyStandardChoice hand state choice hvalid)) :
    ∃ final,
      reachableOnTilesFromWithCopyLimit hand (tile :: tiles) state final ∧
        reachableWithinWithCopyLimit hand
          (fuel + 1 + tiles.length) final := by
  have hnext :
      NextStandardStateAtWithCopyLimit hand tile state
        (applyStandardChoice hand state choice hvalid) :=
    nextStandardStateAtWithCopyLimit_of_choice
      hand tile state choice hchoice htile hvalid hcopy
  have hreachableNext :
      reachableWithinWithCopyLimit hand (fuel + 1)
        (applyStandardChoice hand state choice hvalid) :=
    ⟨state, hreachable,
      nextStandardStateAtWithCopyLimit_toNextWithCopyLimit
        hand tile state (applyStandardChoice hand state choice hvalid) hnext⟩
  obtain ⟨final, htail, hfinal⟩ :=
    reachableOnTilesFromWithCopyLimit_skips
      hand tiles (fuel + 1)
        (applyStandardChoice hand state choice hvalid) hreachableNext
  refine ⟨final, ⟨applyStandardChoice hand state choice hvalid, hnext, htail⟩, ?_⟩
  exact hfinal

lemma reachableOnTilesFromWithCopyLimit_append
    (hand : Hand) (left right : List Tile)
    (start middle final : StandardSearchState)
    (hleft : reachableOnTilesFromWithCopyLimit hand left start middle)
    (hright : reachableOnTilesFromWithCopyLimit hand right middle final) :
    reachableOnTilesFromWithCopyLimit hand (left ++ right) start final := by
  induction left generalizing start middle final with
  | nil =>
      subst start
      exact hright
  | cons tile left ih =>
      rcases hleft with ⟨next, hnext, htail⟩
      exact ⟨next, hnext,
        ih (start := next) (middle := middle) (final := final) htail hright⟩

lemma reachableOnTilesFromWithCopyLimit_insert_choice
    (hand : Hand) (before after : List Tile) (tile : Tile)
    (fuel : Nat) (state : StandardSearchState) (choice : StandardChoice)
    (hreachable : reachableWithinWithCopyLimit hand fuel state)
    (hchoice : choice ∈ allStandardChoices)
    (htile : tile ∈ choiceTiles choice)
    (hvalid : ∀ middle,
      reachableWithinWithCopyLimit hand (fuel + before.length) middle →
        ValidStandardChoice hand middle choice)
    (hcopy : ∀ middle hmiddle,
      CompletionRespectsCopyLimit
        (applyStandardChoice hand middle choice (hvalid middle hmiddle))) :
    ∃ final,
      reachableOnTilesFromWithCopyLimit hand
        (before ++ tile :: after) state final ∧
        reachableWithinWithCopyLimit hand
          ((fuel + before.length) + 1 + after.length) final := by
  obtain ⟨middle, hbefore, hmiddle⟩ :=
    reachableOnTilesFromWithCopyLimit_skips
      hand before fuel state hreachable
  obtain ⟨final, hchosen, hfinal⟩ :=
    reachableOnTilesFromWithCopyLimit_choice_then_skips
      hand tile after (fuel + before.length) middle choice
      hmiddle hchoice htile (hvalid middle hmiddle) (hcopy middle hmiddle)
  refine ⟨final, ?_, hfinal⟩
  exact reachableOnTilesFromWithCopyLimit_append
    hand before (tile :: after) state middle final
    hbefore hchosen

inductive AppliesStandardChoices (hand : Hand) :
    StandardSearchState → List StandardChoice → StandardSearchState → Prop
  | nil (state : StandardSearchState) :
      AppliesStandardChoices hand state [] state
  | cons (state : StandardSearchState) (choice : StandardChoice)
      (hchoice : choice ∈ allStandardChoices)
      (hvalid : ValidStandardChoice hand state choice)
      (final : StandardSearchState)
      (htail :
        AppliesStandardChoices hand
          (applyStandardChoice hand state choice hvalid) choices final) :
      AppliesStandardChoices hand state (choice :: choices) final

lemma AppliesStandardChoices.used_eq
    {hand : Hand} {state final : StandardSearchState}
    {choices : List StandardChoice}
    (hpath : AppliesStandardChoices hand state choices final) :
    final.used = state.used + standardChoiceTiles choices := by
  induction hpath with
  | nil =>
      simp [standardChoiceTiles]
  | @cons state choice hvalid final choices htail ih =>
      cases choice <;>
        simp_all [applyStandardChoice, standardChoiceTiles, choiceTiles]
      all_goals
        try rw [ih]
        try simp [applyStandardChoice, choiceTiles]
        try ac_rfl

lemma nextStandardStateWithCopyLimit_toNext
    (hand : Hand) (state next : StandardSearchState)
    (hnext : NextStandardStateWithCopyLimit hand state next) :
    NextStandardState hand state next := by
  rcases hnext with ⟨choice, hchoice, hvalid, _, rfl⟩
  exact ⟨choice, hchoice, hvalid, rfl⟩

lemma reachableWithinWithCopyLimit_to_reachableWithin
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    reachableWithin hand fuel state := by
  induction fuel generalizing state with
  | zero =>
      exact hreachable
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rw [reachableWithin_succ_iff]
      exact ⟨previous, ih previous hprevious,
        nextStandardStateWithCopyLimit_toNext hand previous state hnext⟩

lemma reachableOnTilesWithCopyLimit_to_reachableWithinWithCopyLimit
    (hand : Hand) (tiles : List Tile) (state : StandardSearchState)
    (hreachable : reachableOnTilesWithCopyLimit hand tiles state) :
    reachableWithinWithCopyLimit hand tiles.length state := by
  have aux :
      ∀ (remaining : List Tile) (start state : StandardSearchState)
        (fuel : Nat),
        reachableWithinWithCopyLimit hand fuel start →
        reachableOnTilesFromWithCopyLimit hand remaining start state →
        reachableWithinWithCopyLimit hand (fuel + remaining.length) state := by
    intro remaining
    induction remaining with
    | nil =>
        intro start state fuel hprefix hrest
        subst state
        simpa using hprefix
    | cons tile remaining ih =>
        intro start state fuel hprefix hrest
        rcases hrest with ⟨middle, hnext, htail⟩
        have hmiddle :
            reachableWithinWithCopyLimit hand (fuel + 1) middle := by
          exact ⟨start, hprefix,
            nextStandardStateAtWithCopyLimit_toNextWithCopyLimit
              hand tile start middle hnext⟩
        have hresult := ih middle state (fuel + 1) hmiddle htail
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult
  have hresult := aux tiles initialStandardState state 0
    (by rfl) hreachable
  simpa using hresult

lemma completedTargetForState_eq_used_add_completion
    (state : StandardSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    completedTargetForState state pair =
      stateHistoryTiles state +
        taatsuCompletionTiles state.taatsuHistory.reverse := by
  rw [completedTargetForState, completedMeldsForState_tiles state pair hpair]
  rw [standardTargetWithTaatsuOfState_eq_stateHistoryTiles state pair hpair]

lemma validCounts_completedTarget_of_copyLimit
    (before : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcopy : CompletionRespectsCopyLimit state)
    (pair : Tile) (hpair : state.pair = some pair) :
    ValidCounts
      (targetHand before
        (countsOfTiles (completedTargetForState state pair))) := by
  intro tile
  have htarget := hcopy tile
  change (completedTargetForState state pair).count tile ≤ 4
  rw [completedTargetForState_eq_used_add_completion state pair hpair]
  rw [← reachableWithin_used_eq_historyTiles before fuel state hreachable]
  exact htarget

lemma completedMeldsForState_card (state : StandardSearchState) :
    (meldsTiles (completedMeldsForState state)).card =
      3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  rw [meldsTiles_card, completedMeldsForState_length]

lemma completedTargetForState_card
    (state : StandardSearchState) (pair : Tile) :
    (completedTargetForState state pair).card =
      2 + 3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  unfold completedTargetForState
  rw [Multiset.card_add, pairTiles_card, completedMeldsForState_card]

lemma completedTargetForState_sum
    (state : StandardSearchState) (pair : Tile) :
    (∑ tile : Tile, countsOfTiles (completedTargetForState state pair) tile) =
      2 + 3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  rw [countsOfTiles_sum_eq_card, completedTargetForState_card]

lemma completedTargetForState_sum_of_blockCount
    (before : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcount : state.melds + state.taatsu + before.fixedMelds = 4)
    (pair : Tile) :
    (∑ tile : Tile,
      countsOfTiles (completedTargetForState state pair) tile) =
        14 - 3 * before.fixedMelds := by
  have hmelds := reachableWithin_melds_eq_history_length
    before fuel state hreachable
  have htaatsu := reachableWithin_taatsu_eq_history_length
    before fuel state hreachable
  rw [completedTargetForState_sum, ← hmelds, ← htaatsu]
  omega

lemma completedTargetForState_sum_eq_tileCount
    (before : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcount : state.melds + state.taatsu + before.fixedMelds = 4)
    (hstanding : tileCount before = 14 - 3 * before.fixedMelds)
    (pair : Tile) :
    (∑ tile : Tile,
      countsOfTiles (completedTargetForState state pair) tile) =
        tileCount before := by
  rw [completedTargetForState_sum_of_blockCount
    before fuel state hreachable hcount pair]
  exact hstanding.symm

lemma complete_standard_completedTarget
    (before : Hand) (state : StandardSearchState) (pair : Tile)
    (hvalid : ValidCounts
      (targetHand before (countsOfTiles (completedTargetForState state pair))))
    (hmelds : HasStandardMeldCount before (completedMeldsForState state)) :
    Complete .standard
      (targetHand before (countsOfTiles (completedTargetForState state pair))) := by
  apply complete_standard_targetHand
  · exact hvalid
  · exact hmelds
  · exact targetHand_hasTiles_countsOfTiles before
      (completedTargetForState state pair)

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

lemma standardTargetDistance_eq_countDeficit
    (hand : Hand) (pair : Tile) (melds : List Meld) :
    standardTargetDistance hand pair melds =
      countDeficit hand.counts
        (countsOfTiles (standardTarget pair melds)) := by
  rfl

lemma standardTargetDistance_eq_zero_iff
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (standardTarget pair melds).count tile) :
    standardTargetDistance hand pair melds = 0 ↔
      hand.counts = countsOfTiles (standardTarget pair melds) := by
  constructor
  · intro hdistance
    have hdeficit :
        countDeficit hand.counts
          (countsOfTiles (standardTarget pair melds)) = 0 := by
      rw [← standardTargetDistance_eq_countDeficit]
      exact hdistance
    have hzero :
        ∀ tile ∈ (Finset.univ : Finset Tile),
          (countsOfTiles (standardTarget pair melds)) tile -
              hand.counts tile = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun tile _ => Nat.zero_le _)).mp
      exact hdeficit
    have hle :
        ∀ tile, (countsOfTiles (standardTarget pair melds)) tile ≤
          hand.counts tile := by
      intro tile
      have hzeroTile := hzero tile (Finset.mem_univ tile)
      omega
    apply funext
    intro tile
    have heq :
        ∀ tile ∈ (Finset.univ : Finset Tile),
          (countsOfTiles (standardTarget pair melds)) tile =
            hand.counts tile := by
      apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
        (f := countsOfTiles (standardTarget pair melds))
        (g := hand.counts)
        (fun tile _ => hle tile)).mp
      exact hsum.symm
    exact (heq tile (Finset.mem_univ tile)).symm
  · intro hcounts
    rw [standardTargetDistance_eq_countDeficit]
    simp [countDeficit, hcounts]

lemma standardTargetDistance_pos_iff
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (standardTarget pair melds).count tile) :
    0 < standardTargetDistance hand pair melds ↔
      hand.counts ≠ countsOfTiles (standardTarget pair melds) := by
  constructor
  · intro hpos hcounts
    have hzero : standardTargetDistance hand pair melds = 0 :=
      (standardTargetDistance_eq_zero_iff hand pair melds hsum).mpr hcounts
    omega
  · intro hne
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hne
        ((standardTargetDistance_eq_zero_iff hand pair melds hsum).mp hzero))

lemma standardTargetDistance_exchange
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (discarded drawn : Tile)
    (hdrawn :
      (standardTarget pair melds).count drawn > hand.counts drawn)
    (hdiscarded :
      hand.counts discarded >
        (standardTarget pair melds).count discarded)
    (hne : discarded ≠ drawn) :
    standardTargetDistance
        (exchangeHand hand discarded drawn) pair melds =
      standardTargetDistance hand pair melds - 1 := by
  rw [standardTargetDistance_eq_countDeficit,
    standardTargetDistance_eq_countDeficit]
  exact countDeficit_exchange
    (countsOfTiles (standardTarget pair melds))
    hand discarded drawn hdrawn hdiscarded hne

lemma exists_standardTarget_exchange
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (standardTarget pair melds).count tile)
    (hne :
      hand.counts ≠ countsOfTiles (standardTarget pair melds)) :
    ∃ discarded drawn,
      (standardTarget pair melds).count drawn > hand.counts drawn ∧
      hand.counts discarded >
        (standardTarget pair melds).count discarded ∧
      discarded ≠ drawn ∧
      standardTargetDistance
          (exchangeHand hand discarded drawn) pair melds =
        standardTargetDistance hand pair melds - 1 := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles⟩ :=
    exists_target_exchange_tiles hand
      (countsOfTiles (standardTarget pair melds)) hsum hne
  refine ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles, ?_⟩
  exact standardTargetDistance_exchange
    hand pair melds discarded drawn hdrawn hdiscarded hneTiles

lemma reachesCompletion_standard_of_standardTarget
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (standardTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (standardTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    ∃ distance,
      ReachesCompletion Complete .standard before distance := by
  apply reachesCompletion_standard_of_equal_sum
    before
    (countsOfTiles (standardTarget pair melds))
    pair melds hsum hvalid hmelds
  exact targetHand_hasTiles_countsOfTiles before
    (standardTarget pair melds)

lemma complete_standard_of_standardTarget_distance_zero
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : standardTargetDistance before pair melds = 0)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (standardTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (standardTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    Complete .standard before := by
  have hdeficit :
      countDeficit before.counts
        (countsOfTiles (standardTarget pair melds)) = 0 := by
    rw [← standardTargetDistance_eq_countDeficit]
    exact hdistance
  have hzero :
      ∀ tile ∈ (Finset.univ : Finset Tile),
        (countsOfTiles (standardTarget pair melds)) tile -
            before.counts tile = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun tile _ => Nat.zero_le _)).mp
    exact hdeficit
  have hle :
      ∀ tile, (countsOfTiles (standardTarget pair melds)) tile ≤
        before.counts tile := by
    intro tile
    have hzeroTile := hzero tile (Finset.mem_univ tile)
    omega
  have heq :
      ∀ tile ∈ (Finset.univ : Finset Tile),
        (countsOfTiles (standardTarget pair melds)) tile =
          before.counts tile := by
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := countsOfTiles (standardTarget pair melds))
      (g := before.counts)
      (fun tile _ => hle tile)).mp
    exact hsum.symm
  have hcounts :
      countsOfTiles (standardTarget pair melds) = before.counts := by
    funext tile
    exact heq tile (Finset.mem_univ tile)
  have hcomplete :
      Complete .standard
        (targetHand before
          (countsOfTiles (standardTarget pair melds))) := by
    exact complete_standard_targetHand before
      (countsOfTiles (standardTarget pair melds)) pair melds
      hvalid hmelds
      (targetHand_hasTiles_countsOfTiles before
        (standardTarget pair melds))
  simpa [targetHand, hcounts] using hcomplete

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

lemma completedMeldsForState_hasMeldCount
    (hand : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcount : state.melds + state.taatsu + hand.fixedMelds = 4) :
    HasStandardMeldCount hand (completedMeldsForState state) := by
  have hmelds := reachableWithin_melds_eq_history_length
    hand fuel state hreachable
  have htaatsu := reachableWithin_taatsu_eq_history_length
    hand fuel state hreachable
  unfold HasStandardMeldCount
  rw [completedMeldsForState_length, ← hmelds, ← htaatsu]
  omega

lemma complete_standard_of_blockSearch
    (before : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcomplete : IsStandardBlockSearchComplete before state)
    (hvalid : ∀ pair, state.pair = some pair →
      ValidCounts
        (targetHand before
          (countsOfTiles (completedTargetForState state pair)))) :
    ∃ pair,
      Complete .standard
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      refine ⟨pair, ?_⟩
      apply complete_standard_completedTarget before state pair
      · exact hvalid pair hstatePair
      · exact completedMeldsForState_hasMeldCount
          before fuel state hreachable hcount

lemma complete_standard_of_blockSearch_of_copyLimit
    (before : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcomplete : IsStandardBlockSearchComplete before state)
    (hcopy : CompletionRespectsCopyLimit state) :
    ∃ pair,
      Complete .standard
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      refine ⟨pair, ?_⟩
      apply complete_standard_completedTarget before state pair
      · exact validCounts_completedTarget_of_copyLimit
          before fuel state hreachable hcopy pair hstatePair
      · exact completedMeldsForState_hasMeldCount
          before fuel state hreachable hcount

lemma complete_standard_of_constrainedBlockSearch
    (before : Hand) (fuel : Nat) (state : StandardSearchState)
    (hreachable : reachableWithinWithCopyLimit before fuel state)
    (hcomplete : IsStandardBlockSearchComplete before state) :
    ∃ pair,
      Complete .standard
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  exact complete_standard_of_blockSearch_of_copyLimit
    before fuel state
    (reachableWithinWithCopyLimit_to_reachableWithin
      before fuel state hreachable)
    hcomplete
    (reachableWithinWithCopyLimit_copyLimit before fuel state hreachable)

end Shanten
