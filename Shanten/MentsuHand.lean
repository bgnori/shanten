import Shanten.Specification
import Shanten.SevenPairs

namespace Shanten

inductive Taatsu
  | pair (tile : Tile)
  | sequence (suit : Suit) (start : Fin 8)
  deriving DecidableEq, Fintype

/-- The counters carried by the mentsu-hand dynamic program. -/
structure MentsuHandSearchState where
  tileIndex : Nat
  used : Multiset Tile
  pair : Option Tile
  meldHistory : List Meld
  taatsuHistory : List Taatsu
  melds : Nat
  taatsu : Nat
  deriving DecidableEq

/-- One branch of the mentsu-hand decomposition search. -/
inductive MentsuHandChoice
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

def choiceTiles : MentsuHandChoice → Multiset Tile
  | .skip => 0
  | .pair tile => pairTiles tile
  | .taatsu taatsu => taatsuTiles taatsu
  | .meld meld => meldTiles meld

def choiceUsesMeld : MentsuHandChoice → Bool
  | .meld _ => true
  | _ => false

def choiceUsesPair : MentsuHandChoice → Bool
  | .pair _ => true
  | _ => false

def choiceUsesTaatsu : MentsuHandChoice → Bool
  | .taatsu _ => true
  | _ => false

def ValidMentsuHandChoice
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice) : Prop :=
  (∀ tile, (state.used + choiceTiles choice).count tile ≤ hand.counts tile) ∧
  state.melds + (if choiceUsesMeld choice = true then 1 else 0) ≤ 4 ∧
  state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0) ≤ 4 ∧
  (state.pair.isNone ∨ choiceUsesPair choice = false)

lemma validMentsuHandChoice_of
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hused :
      ∀ tile, (state.used + choiceTiles choice).count tile ≤ hand.counts tile)
    (hmelds :
      state.melds + (if choiceUsesMeld choice = true then 1 else 0) ≤ 4)
    (htaatsu :
      state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0) ≤ 4)
    (hpair : state.pair.isNone ∨ choiceUsesPair choice = false) :
    ValidMentsuHandChoice hand state choice :=
  ⟨hused, hmelds, htaatsu, hpair⟩

def applyMentsuHandChoice
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (_ : ValidMentsuHandChoice hand state choice) : MentsuHandSearchState :=
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

lemma applyMentsuHandChoice_used_subset
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice) :
    ∀ tile,
      (applyMentsuHandChoice hand state choice hvalid).used.count tile ≤
        hand.counts tile := by
  intro tile
  exact hvalid.1 tile

def allMentsuHandChoices : Finset MentsuHandChoice :=
  insert .skip
    (Finset.univ.image MentsuHandChoice.pair ∪
      Finset.univ.image MentsuHandChoice.meld ∪
      Finset.univ.image (fun taatsu =>
        MentsuHandChoice.taatsu taatsu))

lemma mentsuHandChoice_mem_all
    (choice : MentsuHandChoice) :
    choice ∈ allMentsuHandChoices := by
  cases choice with
  | skip =>
      simp [allMentsuHandChoices]
  | pair tile =>
      simp [allMentsuHandChoices]
  | taatsu taatsu =>
      simp [allMentsuHandChoices]
  | meld meld =>
      simp [allMentsuHandChoices]

def choicesForTile (tile : Tile) : Finset MentsuHandChoice :=
  allMentsuHandChoices.filter
    (fun choice => choice = .skip ∨ tile ∈ choiceTiles choice)

def NextMentsuHandState
    (hand : Hand) (state next : MentsuHandSearchState) : Prop :=
  ∃ choice, choice ∈ allMentsuHandChoices ∧
    ∃ hvalid : ValidMentsuHandChoice hand state choice,
      next = applyMentsuHandChoice hand state choice hvalid

def NextMentsuHandStateAt
    (hand : Hand) (tile : Tile) (state next : MentsuHandSearchState) : Prop :=
  ∃ choice, choice ∈ choicesForTile tile ∧
    ∃ hvalid : ValidMentsuHandChoice hand state choice,
      next = applyMentsuHandChoice hand state choice hvalid

lemma nextMentsuHandState_used_subset
    (hand : Hand) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandState hand state next) :
    ∀ tile, next.used.count tile ≤ hand.counts tile := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  exact applyMentsuHandChoice_used_subset hand state choice hvalid

lemma nextMentsuHandState_tileIndex
    (hand : Hand) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandState hand state next) :
    state.tileIndex < next.tileIndex := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  simp [applyMentsuHandChoice]

lemma nextMentsuHandStateAt_used_subset
    (hand : Hand) (tile : Tile) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandStateAt hand tile state next) :
    ∀ tile', next.used.count tile' ≤ hand.counts tile' := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  exact applyMentsuHandChoice_used_subset hand state choice hvalid

lemma nextMentsuHandStateAt_tileIndex
    (hand : Hand) (tile : Tile) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandStateAt hand tile state next) :
    state.tileIndex < next.tileIndex := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  simp [applyMentsuHandChoice]

def initialMentsuHandState : MentsuHandSearchState :=
  { tileIndex := 0
    used := 0
    pair := none
    meldHistory := []
    taatsuHistory := []
    melds := 0
    taatsu := 0 }

/-- States reachable after exactly `fuel` decomposition choices. -/
def reachableWithin
    (hand : Hand) : Nat → MentsuHandSearchState → Prop
  | 0, state => state = initialMentsuHandState
  | fuel + 1, state =>
      ∃ previous,
        reachableWithin hand fuel previous ∧
          NextMentsuHandState hand previous state

def IsMentsuHandSearchComplete
    (hand : Hand) (state : MentsuHandSearchState) : Prop :=
  state.melds + hand.fixedMelds = 4 ∧ state.pair.isSome

/-- A DP state containing four meld-or-taatsu blocks and one pair. -/
def IsMentsuHandBlockSearchComplete
    (hand : Hand) (state : MentsuHandSearchState) : Prop :=
  state.melds + state.taatsu + hand.fixedMelds = 4 ∧ state.pair.isSome

/-- The DP query: a complete mentsuHand decomposition is reachable in `fuel` choices. -/
def MentsuHandSearch
    (hand : Hand) (fuel : Nat) : Prop :=
  ∃ state, reachableWithin hand fuel state ∧
    IsMentsuHandSearchComplete hand state

/-- The DP query using the four-block criterion. -/
def MentsuHandBlockSearch
    (hand : Hand) (fuel : Nat) : Prop :=
  ∃ state, reachableWithin hand fuel state ∧
    IsMentsuHandBlockSearchComplete hand state

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

def completedMeldsForState (state : MentsuHandSearchState) : List Meld :=
  state.meldHistory.reverse ++
    taatsuCompletionMelds state.taatsuHistory.reverse

lemma completedMeldsForState_length
    (state : MentsuHandSearchState) :
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

def stateHistoryTiles (state : MentsuHandSearchState) : Multiset Tile :=
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

lemma applyMentsuHandChoice_used_eq_historyTiles
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hstate : state.used = stateHistoryTiles state) :
    (applyMentsuHandChoice hand state choice hvalid).used =
      stateHistoryTiles (applyMentsuHandChoice hand state choice hvalid) := by
  cases choice with
  | skip =>
      simpa [applyMentsuHandChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles] using hstate
  | pair tile =>
      have hpair : state.pair.isNone := by
        simpa [choiceUsesPair] using hvalid.2.2.2
      cases hstatePair : state.pair with
      | none =>
          simp only [applyMentsuHandChoice]
          change state.used + pairTiles tile = _
          rw [hstate]
          simp [applyMentsuHandChoice, stateHistoryTiles, pairHistoryTiles,
            taatsuHistoryTiles, choiceTiles, hstatePair]
          ac_rfl
      | some oldPair =>
          simp [hstatePair] at hpair
  | taatsu taatsu =>
      simp only [applyMentsuHandChoice]
      change state.used + taatsuTiles taatsu = _
      rw [hstate]
      simp [applyMentsuHandChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles, List.reverse_cons,
        taatsuHistoryTiles_append_single]
      ac_rfl
  | meld meld =>
      simp only [applyMentsuHandChoice]
      change state.used + meldTiles meld = _
      rw [hstate]
      simp [applyMentsuHandChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles, List.reverse_cons,
        meldsTiles_append_single]
      ac_rfl

lemma reachableWithin_used_eq_historyTiles
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.used = stateHistoryTiles state := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyMentsuHandChoice_used_eq_historyTiles
        hand previous choice hvalid (ih previous hprevious)

lemma applyMentsuHandChoice_melds_eq_history_length
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hstate : state.melds = state.meldHistory.length) :
    (applyMentsuHandChoice hand state choice hvalid).melds =
      (applyMentsuHandChoice hand state choice hvalid).meldHistory.length := by
  cases choice <;> simp [applyMentsuHandChoice, hstate, choiceUsesMeld]

lemma reachableWithin_melds_eq_history_length
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.melds = state.meldHistory.length := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyMentsuHandChoice_melds_eq_history_length
        hand previous choice hvalid (ih previous hprevious)

lemma applyMentsuHandChoice_taatsu_eq_history_length
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hstate : state.taatsu = state.taatsuHistory.length) :
    (applyMentsuHandChoice hand state choice hvalid).taatsu =
      (applyMentsuHandChoice hand state choice hvalid).taatsuHistory.length := by
  cases choice <;> simp [applyMentsuHandChoice, hstate, choiceUsesTaatsu]

lemma reachableWithin_taatsu_eq_history_length
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.taatsu = state.taatsuHistory.length := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyMentsuHandChoice_taatsu_eq_history_length
        hand previous choice hvalid (ih previous hprevious)

/-- States reached from a given state while processing tile kinds in order. -/
def reachableOnTilesFrom
    (hand : Hand) : List Tile → MentsuHandSearchState →
      MentsuHandSearchState → Prop
  | [], start, state => state = start
  | tile :: tiles, start, state =>
      ∃ middle,
        NextMentsuHandStateAt hand tile start middle ∧
          reachableOnTilesFrom hand tiles middle state

/-- States reached while processing a prescribed sequence of tile kinds. -/
def reachableOnTiles
    (hand : Hand) (tiles : List Tile) (state : MentsuHandSearchState) : Prop :=
  reachableOnTilesFrom hand tiles initialMentsuHandState state

def MentsuHandSearchOnTiles
    (hand : Hand) (tiles : List Tile) : Prop :=
  ∃ state, reachableOnTiles hand tiles state ∧
    IsMentsuHandSearchComplete hand state

def MentsuHandBlockSearchOnTiles
    (hand : Hand) (tiles : List Tile) : Prop :=
  ∃ state, reachableOnTiles hand tiles state ∧
    IsMentsuHandBlockSearchComplete hand state

lemma reachableWithin_zero_iff
    (hand : Hand) (state : MentsuHandSearchState) :
    reachableWithin hand 0 state ↔ state = initialMentsuHandState := by
  rfl

lemma reachableWithin_succ_iff
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState) :
    reachableWithin hand (fuel + 1) state ↔
      ∃ previous,
        reachableWithin hand fuel previous ∧
          NextMentsuHandState hand previous state := by
  rfl

lemma reachableWithin_used_subset
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) :
    ∀ tile, state.used.count tile ≤ hand.counts tile := by
  induction fuel generalizing state with
  | zero =>
      intro tile
      subst state
      simp [initialMentsuHandState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      intro tile
      exact nextMentsuHandState_used_subset hand previous state hnext tile

lemma mentsuHandSearch_complete_iff
    (hand : Hand) (fuel : Nat) :
    MentsuHandSearch hand fuel ↔
      ∃ state, reachableWithin hand fuel state ∧
        state.melds + hand.fixedMelds = 4 ∧
        state.pair.isSome := by
  rfl

lemma mentsuHandBlockSearch_complete_iff
    (hand : Hand) (fuel : Nat) :
    MentsuHandBlockSearch hand fuel ↔
        ∃ state, reachableWithin hand fuel state ∧
          state.melds + state.taatsu + hand.fixedMelds = 4 ∧
          state.pair.isSome := by
  rfl

def mentsuHandTileAt (index : Fin 34) : Tile :=
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

def mentsuHandTileOrder : List Tile :=
  (List.finRange 34).map mentsuHandTileAt

def MentsuHandSearchOnTileOrder (hand : Hand) : Prop :=
  MentsuHandSearchOnTiles hand mentsuHandTileOrder

lemma mentsuHandTileOrder_length :
    mentsuHandTileOrder.length = 34 := by
  simp [mentsuHandTileOrder]

lemma tile_mem_mentsuHandTileOrder :
    ∀ tile : Tile, tile ∈ mentsuHandTileOrder := by
  native_decide

/-- A mentsu-hand-form target before the fixed melds are added. -/
def mentsuHandTarget (pair : Tile) (melds : List Meld) : Multiset Tile :=
  pairTiles pair + meldsTiles melds

def mentsuHandTargetWithTaatsu
    (pair : Tile) (melds : List Meld) (taatsus : List Taatsu) : Multiset Tile :=
  mentsuHandTarget pair melds + taatsuHistoryTiles taatsus

lemma completedMeldsForState_tiles
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    pairTiles pair + meldsTiles (completedMeldsForState state) =
      mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
          state.taatsuHistory.reverse +
        taatsuCompletionTiles state.taatsuHistory.reverse := by
  simp only [completedMeldsForState, mentsuHandTargetWithTaatsu, mentsuHandTarget]
  rw [meldsTiles_append]
  rw [← taatsuHistoryTiles_add_completionTiles]
  ac_rfl

def mentsuHandTargetWithTaatsuOfState
    (state : MentsuHandSearchState) : Option (Multiset Tile) :=
  state.pair.map fun pair =>
    mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
      state.taatsuHistory.reverse

lemma mentsuHandTargetWithTaatsuOfState_eq_some_iff
    (state : MentsuHandSearchState) (target : Multiset Tile) :
    mentsuHandTargetWithTaatsuOfState state = some target ↔
      ∃ pair, state.pair = some pair ∧
        target = mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
          state.taatsuHistory.reverse := by
  constructor
  · intro htarget
    cases hpair : state.pair with
    | none =>
        simp [mentsuHandTargetWithTaatsuOfState, hpair] at htarget
    | some pair =>
        refine ⟨pair, rfl, ?_⟩
        simpa [mentsuHandTargetWithTaatsuOfState, hpair] using htarget.symm
  · rintro ⟨pair, hpair, rfl⟩
    rw [mentsuHandTargetWithTaatsuOfState, hpair]
    rfl

lemma mentsuHandTargetWithTaatsuOfState_eq_stateHistoryTiles
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
        state.taatsuHistory.reverse =
      stateHistoryTiles state := by
  simp [mentsuHandTargetWithTaatsu, mentsuHandTarget, stateHistoryTiles,
    pairHistoryTiles, hpair, Multiset.add_assoc]

lemma mentsuHandTargetWithTaatsu_count_le_hand
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTargetWithTaatsu pair state.meldHistory.reverse
        state.taatsuHistory.reverse).count tile ≤ hand.counts tile := by
  intro tile
  rw [mentsuHandTargetWithTaatsuOfState_eq_stateHistoryTiles state pair hpair]
  rw [← reachableWithin_used_eq_historyTiles hand fuel state hreachable]
  exact reachableWithin_used_subset hand fuel state hreachable tile

lemma mentsuHandTargetExchange_handStep
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
    (mentsuHandTargetExchange_handStep target before discarded drawn
      hdrawn hdiscarded hne)
  exact hrest

lemma exchangeHand_fixedMelds
    (before : Hand) (discarded drawn : Tile) :
    (exchangeHand before discarded drawn).fixedMelds = before.fixedMelds := by
  rfl

def mentsuHandTargetOfState
    (state : MentsuHandSearchState) : Option (Multiset Tile) :=
  state.pair.map fun pair =>
    mentsuHandTarget pair state.meldHistory.reverse

lemma mentsuHandTargetOfState_eq_some_iff
    (state : MentsuHandSearchState) (target : Multiset Tile) :
    mentsuHandTargetOfState state = some target ↔
      ∃ pair, state.pair = some pair ∧
        target = mentsuHandTarget pair state.meldHistory.reverse := by
  constructor
  · intro htarget
    cases hpair : state.pair with
    | none =>
        simp [mentsuHandTargetOfState, hpair] at htarget
    | some pair =>
        refine ⟨pair, rfl, ?_⟩
        simpa [mentsuHandTargetOfState, hpair] using htarget.symm
  · rintro ⟨pair, hpair, rfl⟩
    rw [mentsuHandTargetOfState, hpair]
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

lemma countDeficit_handStep_le
    (before after : Hand) (target : TileCounts)
    (hstep : HandStep before after) :
    countDeficit before.counts target ≤
      countDeficit after.counts target + 1 := by
  have finish (drawn : Tile)
      (hpoint : ∀ tile,
        target tile - before.counts tile ≤
          target tile - after.counts tile +
            (if tile = drawn then 1 else 0)) :
      countDeficit before.counts target ≤
        countDeficit after.counts target + 1 := by
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun tile _ => hpoint tile)
    calc
      countDeficit before.counts target =
          ∑ tile : Tile, (target tile - before.counts tile) := rfl
      _ ≤ ∑ tile : Tile,
          (target tile - after.counts tile +
            (if tile = drawn then 1 else 0)) := hsum
      _ = countDeficit after.counts target + 1 := by
        simp [countDeficit, Finset.sum_add_distrib]
  rcases hstep.2 with ⟨drawn, _, hcounts⟩ |
    ⟨discarded, drawn, hne, hpositive, hcounts⟩
  · apply finish drawn
    intro tile
    have hcount := hcounts tile
    by_cases hdrawn : tile = drawn
    · subst tile
      simp at hcount
      simp
      omega
    · simp [hdrawn] at hcount
      simp [hdrawn]
      omega
  · apply finish drawn
    intro tile
    by_cases hdiscarded : tile = discarded
    · subst tile
      have hcount := hcounts discarded
      simp [hne] at hcount
      simp [hne]
      omega
    · by_cases hdrawn : tile = drawn
      · subst tile
        have hcount := hcounts drawn
        simp [hne, Ne.symm hne] at hcount
        simp [hne, Ne.symm hne]
        omega
      · have hcount := hcounts tile
        simp [hdiscarded, hdrawn] at hcount
        simp [hdrawn]
        omega

lemma exists_complete_mentsuHand_with_deficit_le
    (before : Hand) (distance : Nat)
    (hreach : ReachesCompletion Complete .mentsuHand before distance) :
    ∃ after,
      Complete .mentsuHand after ∧
        after.fixedMelds = before.fixedMelds ∧
        countDeficit before.counts after.counts ≤ distance := by
  induction distance generalizing before with
  | zero =>
      cases hreach with
      | done hcomplete =>
          exact ⟨before, hcomplete, rfl, by simp [countDeficit]⟩
  | succ distance ih =>
      cases hreach with
      | @step hand next distance hstep hrest =>
          obtain ⟨after, hcomplete, hfixed, hbound⟩ :=
            ih next hrest
          refine ⟨after, hcomplete, ?_, ?_⟩
          · exact hfixed.trans hstep.1.symm
          have hstepBound :=
            countDeficit_handStep_le before next after.counts hstep
          omega

def targetHand (before : Hand) (target : TileCounts) : Hand :=
  { counts := target
    fixedMelds := before.fixedMelds }

def countsOfTiles (tiles : Multiset Tile) : TileCounts :=
  fun tile => tiles.count tile

lemma countDeficit_draw
    (before : Hand) (target : TileCounts) (drawn : Tile)
    (hdrawn : target drawn > before.counts drawn) :
    countDeficit
        (fun tile =>
          before.counts tile + (if tile = drawn then 1 else 0))
        target + 1 =
      countDeficit before.counts target := by
  let deficit : Tile → Nat :=
    fun tile => target tile - before.counts tile
  let afterDeficit : Tile → Nat :=
    fun tile =>
      target tile -
        (before.counts tile + (if tile = drawn then 1 else 0))
  have hdrawn' : afterDeficit drawn + 1 = deficit drawn := by
    simp [afterDeficit, deficit]
    omega
  have hother (tile : Tile) (htile : tile ≠ drawn) :
      afterDeficit tile = deficit tile := by
    simp [afterDeficit, deficit, htile]
  have hpoint (tile : Tile) :
      afterDeficit tile + (if tile = drawn then 1 else 0) =
        deficit tile := by
    by_cases htile : tile = drawn
    · subst tile
      simpa using hdrawn'
    · simp [htile, hother tile htile]
  have hsum :
      (∑ tile : Tile, afterDeficit tile) + 1 =
        ∑ tile : Tile, deficit tile := by
    calc
      (∑ tile : Tile, afterDeficit tile) + 1 =
          ∑ tile : Tile,
            (afterDeficit tile + (if tile = drawn then 1 else 0)) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ tile : Tile, deficit tile := by
        apply Finset.sum_congr rfl
        intro tile _
        exact hpoint tile
  change (∑ tile : Tile, afterDeficit tile) + 1 =
    ∑ tile : Tile, deficit tile
  exact hsum

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
      distance = countDeficit before.counts target ∧
      ReachesExchange before (targetHand before target) distance := by
  have aux : ∀ d : Nat, ∀ current : Hand,
      (∑ tile : Tile, current.counts tile) =
        ∑ tile : Tile, target tile →
      countDeficit current.counts target = d →
      ∃ distance,
        distance = d ∧
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
      refine ⟨0, ?_, ReachesExchange.done⟩
      simp [countDeficit] at hmeasure
      omega
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
      have hdefAfterEq :
          countDeficit next.counts target = d - 1 := by
        dsimp [next]
        rw [countDeficit_exchange target current discarded drawn
          hdrawn hdiscarded hneTiles, hmeasure]
      have hdefAfter : countDeficit next.counts target < d := by
        omega
      obtain ⟨distance, hdistanceRest, hrest⟩ := ih
        (countDeficit next.counts target) hdefAfter next
        hsumAfter rfl
      refine ⟨distance + 1, ?_, ?_⟩
      · omega
      · apply ReachesExchange.step
        · exact mentsuHandTargetExchange_handStep target current discarded drawn
            hdrawn hdiscarded hneTiles
        · simpa [next, targetHand, exchangeHand] using hrest
  exact aux (countDeficit before.counts target) before hsum rfl

lemma complete_mentsuHand_targetHand
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List Meld)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds)) :
    Complete .mentsuHand (targetHand before target) := by
  exact ⟨hvalid, pair, melds, hmelds, htiles⟩

lemma reachesCompletion_mentsuHand_of_equal_sum
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List Meld)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds)) :
    ReachesCompletion Complete .mentsuHand before
      (countDeficit before.counts target) := by
  obtain ⟨distance, hdistance, hexchange⟩ :=
    reachesExchange_targetHand_of_equal_sum before target hsum
  have hcomplete :
      Complete .mentsuHand (targetHand before target) :=
    complete_mentsuHand_targetHand before target pair melds
      hvalid hmelds htiles
  have hdone :
      ReachesCompletion Complete .mentsuHand
        (targetHand before target) 0 :=
    ReachesCompletion.done hcomplete
  simpa only [Nat.add_zero, hdistance] using
    ReachesExchange.toReachesCompletion hexchange hdone

lemma reachesCompletion_mentsuHand_of_one_more_target_tile
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, target tile) =
        (∑ tile : Tile, before.counts tile) + 1)
    (hbeforeValid : ValidCounts before)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds)) :
    ∃ distance,
      distance = countDeficit before.counts target ∧
      ReachesCompletion Complete .mentsuHand before distance := by
  have hdrawnExists : ∃ drawn, before.counts drawn < target drawn := by
    by_contra hnone
    push_neg at hnone
    have hle : ∀ tile, target tile ≤ before.counts tile := by
      intro tile
      exact hnone tile
    have hsumLe :=
      Finset.sum_le_sum (s := Finset.univ)
        (fun tile _ => hle tile)
    omega
  obtain ⟨drawn, hdrawn⟩ := hdrawnExists
  let next : Hand :=
    { counts := fun tile =>
        before.counts tile + (if tile = drawn then 1 else 0)
      fixedMelds := before.fixedMelds }
  have hnextValid : ValidCounts next := by
    intro tile
    by_cases htile : tile = drawn
    · subst tile
      have htarget := hvalid drawn
      change next.counts drawn ≤ 4
      simp [next]
      change target drawn ≤ 4 at htarget
      omega
    · have hbefore := hbeforeValid tile
      simpa [next, htile] using hbefore
  have hstep : HandStep before next := by
    refine ⟨rfl, Or.inl ⟨drawn, hnextValid, ?_⟩⟩
    intro tile
    rfl
  have hsumNext :
      (∑ tile : Tile, next.counts tile) =
        ∑ tile : Tile, target tile := by
    calc
      (∑ tile : Tile, next.counts tile) =
          (∑ tile : Tile, before.counts tile) + 1 := by
        simp [next, Finset.sum_add_distrib]
      _ = ∑ tile : Tile, target tile := by omega
  have hvalidNext : ValidCounts (targetHand next target) := by
    change ValidCounts (targetHand before target)
    exact hvalid
  have hmeldsNext : melds.length + next.fixedMelds = 4 := by
    change melds.length + before.fixedMelds = 4
    exact hmelds
  have htilesNext :
      HasTiles (targetHand next target)
        (pairTiles pair + meldsTiles melds) := by
    change HasTiles (targetHand before target)
      (pairTiles pair + meldsTiles melds)
    exact htiles
  have hcomplete :
      Complete .mentsuHand (targetHand next target) :=
    complete_mentsuHand_targetHand next target pair melds
      hvalidNext hmeldsNext htilesNext
  have hdone :
      ReachesCompletion Complete .mentsuHand
        (targetHand next target) 0 :=
    ReachesCompletion.done hcomplete
  obtain ⟨distance, hdistance, hexchange⟩ :=
    reachesExchange_targetHand_of_equal_sum next target hsumNext
  have hrest :
      ReachesCompletion Complete .mentsuHand next distance := by
    simpa using ReachesExchange.toReachesCompletion hexchange hdone
  have hdeficitNext :
      countDeficit next.counts target + 1 =
        countDeficit before.counts target := by
    change countDeficit
      (fun tile =>
        before.counts tile + (if tile = drawn then 1 else 0))
      target + 1 =
        countDeficit before.counts target
    exact countDeficit_draw before target drawn hdrawn
  have hdistanceTotal :
      distance + 1 = countDeficit before.counts target := by
    rw [hdistance]
    exact hdeficitNext
  exact ⟨distance + 1, hdistanceTotal,
    ReachesCompletion.step hstep hrest⟩

/-- A target has the required number of concealed melds for a hand. -/
def HasMentsuHandMeldCount (hand : Hand) (melds : List Meld) : Prop :=
  melds.length + hand.fixedMelds = 4

/-- A mentsu-hand-form decomposition before completing its taatsu blocks. -/
structure MentsuHandBlockDecomposition (hand : Hand) where
  pair : Tile
  melds : List Meld
  taatsus : List Taatsu
  blocks : melds.length + taatsus.length + hand.fixedMelds = 4
  targetWithinHand :
    ∀ tile,
      (mentsuHandTargetWithTaatsu pair melds taatsus).count tile ≤ hand.counts tile
  completionCopyLimit :
    ∀ tile,
      (mentsuHandTargetWithTaatsu pair melds taatsus +
        taatsuCompletionTiles taatsus).count tile ≤ 4

def mentsuHandChoiceTiles : List MentsuHandChoice → Multiset Tile
  | [] => 0
  | choice :: choices =>
      choiceTiles choice + mentsuHandChoiceTiles choices

lemma mentsuHandChoiceTiles_append
    (left right : List MentsuHandChoice) :
    mentsuHandChoiceTiles (left ++ right) =
      mentsuHandChoiceTiles left + mentsuHandChoiceTiles right := by
  induction left with
  | nil =>
      simp [mentsuHandChoiceTiles]
  | cons choice left ih =>
      simp [mentsuHandChoiceTiles, ih, Multiset.add_assoc]

def MentsuHandBlockDecomposition.blockChoices
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    List MentsuHandChoice :=
  .pair decomposition.pair ::
    decomposition.melds.map MentsuHandChoice.meld ++
      decomposition.taatsus.map MentsuHandChoice.taatsu

lemma MentsuHandBlockDecomposition.blockChoices_length
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    decomposition.blockChoices.length =
      1 + decomposition.melds.length + decomposition.taatsus.length := by
  simp [MentsuHandBlockDecomposition.blockChoices]
  omega

lemma MentsuHandBlockDecomposition.blockChoices_mem_all
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    ∀ choice, choice ∈ decomposition.blockChoices →
      choice ∈ allMentsuHandChoices := by
  intro choice hchoice
  unfold MentsuHandBlockDecomposition.blockChoices at hchoice
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hchoice
  rcases hchoice with (hpair | hmeld) | htaatsu
  · rw [hpair]
    exact mentsuHandChoice_mem_all _
  · rcases hmeld with ⟨meld, _, hmeld⟩
    rw [← hmeld]
    exact mentsuHandChoice_mem_all _
  · rcases htaatsu with ⟨taatsu, _, htaatsu⟩
    rw [← htaatsu]
    exact mentsuHandChoice_mem_all _

lemma mentsuHandChoiceTiles_map_meld
    (melds : List Meld) :
    mentsuHandChoiceTiles (melds.map MentsuHandChoice.meld) =
      meldsTiles melds := by
  induction melds with
  | nil =>
      rfl
  | cons meld melds ih =>
      simp [mentsuHandChoiceTiles, choiceTiles, meldsTiles, ih]

lemma mentsuHandChoiceTiles_map_taatsu
    (taatsus : List Taatsu) :
    mentsuHandChoiceTiles (taatsus.map MentsuHandChoice.taatsu) =
      taatsuHistoryTiles taatsus := by
  induction taatsus with
  | nil =>
      rfl
  | cons taatsu taatsus ih =>
      simp [mentsuHandChoiceTiles, choiceTiles, taatsuHistoryTiles, ih]

lemma MentsuHandBlockDecomposition.blockChoices_tiles
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    mentsuHandChoiceTiles decomposition.blockChoices =
      mentsuHandTargetWithTaatsu decomposition.pair decomposition.melds
        decomposition.taatsus := by
  unfold MentsuHandBlockDecomposition.blockChoices
  simp [mentsuHandChoiceTiles, choiceTiles, List.map_append,
    mentsuHandChoiceTiles_append,
    mentsuHandChoiceTiles_map_meld, mentsuHandChoiceTiles_map_taatsu,
    mentsuHandTargetWithTaatsu, mentsuHandTarget]
  ac_rfl

lemma mentsuHandChoiceTiles_prefix_count_le
    (pre suffix : List MentsuHandChoice) (tile : Tile) :
    (mentsuHandChoiceTiles pre).count tile ≤
      (mentsuHandChoiceTiles (pre ++ suffix)).count tile := by
  rw [mentsuHandChoiceTiles_append]
  simp only [Multiset.count_add]
  omega

lemma MentsuHandBlockDecomposition.prefix_count_le_hand
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
    (pre suffix : List MentsuHandChoice)
    (hchoices : decomposition.blockChoices = pre ++ suffix) :
    ∀ tile, (mentsuHandChoiceTiles pre).count tile ≤ hand.counts tile := by
  intro tile
  have hprefix :
      (mentsuHandChoiceTiles pre).count tile ≤
        (mentsuHandChoiceTiles decomposition.blockChoices).count tile := by
    rw [hchoices]
    exact mentsuHandChoiceTiles_prefix_count_le pre suffix tile
  have htarget :
      (mentsuHandChoiceTiles decomposition.blockChoices).count tile ≤
        hand.counts tile := by
    rw [decomposition.blockChoices_tiles]
    exact decomposition.targetWithinHand tile
  exact hprefix.trans htarget

lemma MentsuHandBlockDecomposition.prefix_completion_count_le_four
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
    (pre suffix : List MentsuHandChoice)
    (hchoices : decomposition.blockChoices = pre ++ suffix) :
    ∀ tile,
        (mentsuHandChoiceTiles pre +
        taatsuCompletionTiles decomposition.taatsus).count tile ≤ 4 := by
  intro tile
  have hprefix :
        (mentsuHandChoiceTiles pre).count tile ≤
        (mentsuHandChoiceTiles decomposition.blockChoices).count tile := by
    rw [hchoices]
    exact mentsuHandChoiceTiles_prefix_count_le pre suffix tile
  have hfull :
      (mentsuHandChoiceTiles decomposition.blockChoices +
        taatsuCompletionTiles decomposition.taatsus).count tile ≤ 4 := by
    rw [decomposition.blockChoices_tiles]
    exact decomposition.completionCopyLimit tile
  rw [Multiset.count_add] at hfull ⊢
  omega

def MentsuHandBlockDecomposition.completedTarget
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    Multiset Tile :=
  mentsuHandTargetWithTaatsu decomposition.pair decomposition.melds
      decomposition.taatsus +
    taatsuCompletionTiles decomposition.taatsus

lemma MentsuHandBlockDecomposition.completedTarget_eq
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    decomposition.completedTarget =
      pairTiles decomposition.pair +
        meldsTiles
          (decomposition.melds ++
            taatsuCompletionMelds decomposition.taatsus) := by
  unfold MentsuHandBlockDecomposition.completedTarget
    mentsuHandTargetWithTaatsu mentsuHandTarget
  rw [meldsTiles_append]
  rw [← taatsuHistoryTiles_add_completionTiles]
  ac_rfl

lemma MentsuHandBlockDecomposition.validCounts_completedTarget
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    ValidCounts
      (targetHand hand (countsOfTiles decomposition.completedTarget)) := by
  intro tile
  exact decomposition.completionCopyLimit tile

lemma MentsuHandBlockDecomposition.completedMeldCount
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand) :
    (decomposition.melds ++
      taatsuCompletionMelds decomposition.taatsus).length +
        hand.fixedMelds = 4 := by
  rw [List.length_append, taatsuCompletionMelds_length]
  have hblocks := decomposition.blocks
  omega

def completedTargetForState (state : MentsuHandSearchState) (pair : Tile) :
    Multiset Tile :=
  pairTiles pair + meldsTiles (completedMeldsForState state)

def CompletionRespectsCopyLimit (state : MentsuHandSearchState) : Prop :=
  ∀ tile,
    (state.used + taatsuCompletionTiles state.taatsuHistory.reverse).count tile ≤ 4

def ValidMentsuHandChoiceWithCopyLimit
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice) : Prop :=
  ∃ hvalid : ValidMentsuHandChoice hand state choice,
    CompletionRespectsCopyLimit
      (applyMentsuHandChoice hand state choice hvalid)

lemma validMentsuHandChoiceWithCopyLimit_of
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid)) :
    ValidMentsuHandChoiceWithCopyLimit hand state choice :=
  ⟨hvalid, hcopy⟩

def NextMentsuHandStateWithCopyLimit
    (hand : Hand) (state next : MentsuHandSearchState) : Prop :=
  ∃ choice, choice ∈ allMentsuHandChoices ∧
    ∃ hvalid : ValidMentsuHandChoice hand state choice,
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid) ∧
      next = applyMentsuHandChoice hand state choice hvalid

lemma nextMentsuHandStateWithCopyLimit_of_choice
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hchoice : choice ∈ allMentsuHandChoices)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid)) :
    NextMentsuHandStateWithCopyLimit hand state
      (applyMentsuHandChoice hand state choice hvalid) :=
  ⟨choice, hchoice, hvalid, hcopy, rfl⟩

noncomputable def copyLimitChoices
    (hand : Hand) (state : MentsuHandSearchState) : Finset MentsuHandChoice :=
  by
    classical
    exact allMentsuHandChoices.filter
      (fun choice =>
        ∃ hvalid : ValidMentsuHandChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuHandChoice hand state choice hvalid))

lemma mem_copyLimitChoices_iff
    (hand : Hand) (state : MentsuHandSearchState) (choice : MentsuHandChoice) :
    choice ∈ copyLimitChoices hand state ↔
      choice ∈ allMentsuHandChoices ∧
        ∃ hvalid : ValidMentsuHandChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuHandChoice hand state choice hvalid) := by
  classical
  change choice ∈ allMentsuHandChoices.filter _ ↔ _
  rw [Finset.mem_filter]

lemma nextMentsuHandStateWithCopyLimit_iff
    (hand : Hand) (state next : MentsuHandSearchState) :
    NextMentsuHandStateWithCopyLimit hand state next ↔
      ∃ choice, choice ∈ copyLimitChoices hand state ∧
        ∃ hvalid : ValidMentsuHandChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuHandChoice hand state choice hvalid) ∧
          next = applyMentsuHandChoice hand state choice hvalid := by
  classical
  constructor
  · rintro ⟨choice, hchoice, hvalid, hcopy, rfl⟩
    refine ⟨choice, ?_, hvalid, hcopy, rfl⟩
    change choice ∈ allMentsuHandChoices.filter _
    exact Finset.mem_filter.mpr ⟨hchoice, ⟨hvalid, hcopy⟩⟩
  · rintro ⟨choice, hchoice, hvalid, hcopy, rfl⟩
    change choice ∈ allMentsuHandChoices.filter _ at hchoice
    exact ⟨choice, (Finset.mem_filter.mp hchoice).1,
      hvalid, hcopy, rfl⟩

noncomputable def choicesForTileWithCopyLimit
    (hand : Hand) (state : MentsuHandSearchState) (tile : Tile) :
    Finset MentsuHandChoice :=
  by
    classical
    exact (choicesForTile tile).filter
      (fun choice =>
        ∃ hvalid : ValidMentsuHandChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuHandChoice hand state choice hvalid))

lemma mem_choicesForTileWithCopyLimit_iff
    (hand : Hand) (state : MentsuHandSearchState) (tile : Tile)
    (choice : MentsuHandChoice) :
    choice ∈ choicesForTileWithCopyLimit hand state tile ↔
      choice ∈ choicesForTile tile ∧
        ∃ hvalid : ValidMentsuHandChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuHandChoice hand state choice hvalid) := by
  classical
  change choice ∈ (choicesForTile tile).filter _ ↔ _
  rw [Finset.mem_filter]

def NextMentsuHandStateAtWithCopyLimit
    (hand : Hand) (tile : Tile) (state next : MentsuHandSearchState) : Prop :=
  ∃ choice, choice ∈ choicesForTileWithCopyLimit hand state tile ∧
    ∃ hvalid : ValidMentsuHandChoice hand state choice,
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid) ∧
      next = applyMentsuHandChoice hand state choice hvalid

lemma nextMentsuHandStateAtWithCopyLimit_of_choice
    (hand : Hand) (tile : Tile) (state : MentsuHandSearchState)
    (choice : MentsuHandChoice)
    (hchoice : choice ∈ allMentsuHandChoices)
    (htile : tile ∈ choiceTiles choice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid)) :
    NextMentsuHandStateAtWithCopyLimit hand tile state
      (applyMentsuHandChoice hand state choice hvalid) := by
  refine ⟨choice, ?_, hvalid, hcopy, rfl⟩
  apply (mem_choicesForTileWithCopyLimit_iff hand state tile choice).mpr
  exact ⟨Finset.mem_filter.mpr ⟨hchoice, Or.inr htile⟩,
    ⟨hvalid, hcopy⟩⟩

lemma nextMentsuHandStateAtWithCopyLimit_skip
    (hand : Hand) (tile : Tile) (state : MentsuHandSearchState)
    (hused : ∀ tile, state.used.count tile ≤ hand.counts tile)
    (hcopy : CompletionRespectsCopyLimit state)
    (hmelds : state.melds ≤ 4)
    (htaatsu : state.taatsu ≤ 4) :
    NextMentsuHandStateAtWithCopyLimit hand tile state
      (applyMentsuHandChoice hand state .skip
        (by
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [choiceTiles] using hused
          · simpa [choiceUsesMeld] using hmelds
          · simpa [choiceUsesTaatsu] using htaatsu
          · simp [choiceUsesPair])) := by
  let hvalid : ValidMentsuHandChoice hand state .skip := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [choiceTiles] using hused
    · simpa [choiceUsesMeld] using hmelds
    · simpa [choiceUsesTaatsu] using htaatsu
    · simp [choiceUsesPair]
  refine ⟨.skip, ?_, hvalid, ?_, rfl⟩
  apply (mem_choicesForTileWithCopyLimit_iff hand state tile .skip).mpr
  · exact ⟨by simp [choicesForTile, allMentsuHandChoices],
      ⟨hvalid, by
        simpa [CompletionRespectsCopyLimit, applyMentsuHandChoice,
          choiceTiles] using hcopy⟩⟩
  · simpa [CompletionRespectsCopyLimit, applyMentsuHandChoice,
      choiceTiles] using hcopy

lemma nextMentsuHandStateAtWithCopyLimit_toNext
    (hand : Hand) (tile : Tile) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandStateAtWithCopyLimit hand tile state next) :
    NextMentsuHandStateAt hand tile state next := by
  rcases hnext with ⟨choice, hchoice, hvalid, hcopy, rfl⟩
  exact ⟨choice, (mem_choicesForTileWithCopyLimit_iff
    hand state tile choice).mp hchoice |>.1, hvalid, rfl⟩

lemma nextMentsuHandStateAtWithCopyLimit_copyLimit
    (hand : Hand) (tile : Tile) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandStateAtWithCopyLimit hand tile state next) :
    CompletionRespectsCopyLimit next := by
  rcases hnext with ⟨choice, hchoice, hvalid, hcopy, rfl⟩
  exact hcopy

lemma nextMentsuHandStateAtWithCopyLimit_toNextWithCopyLimit
    (hand : Hand) (tile : Tile) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandStateAtWithCopyLimit hand tile state next) :
    NextMentsuHandStateWithCopyLimit hand state next := by
  classical
  rcases hnext with ⟨choice, hchoice, hvalid, hcopy, rfl⟩
  change choice ∈ (choicesForTile tile).filter _ at hchoice
  have hchoiceAll : choice ∈ allMentsuHandChoices :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hchoice).1).1
  exact ⟨choice, hchoiceAll, hvalid, hcopy, rfl⟩

def reachableOnTilesFromWithCopyLimit
    (hand : Hand) : List Tile → MentsuHandSearchState →
      MentsuHandSearchState → Prop
  | [], start, state => state = start
  | tile :: tiles, start, state =>
      ∃ middle,
        NextMentsuHandStateAtWithCopyLimit hand tile start middle ∧
          reachableOnTilesFromWithCopyLimit hand tiles middle state

def reachableOnTilesWithCopyLimit
    (hand : Hand) (tiles : List Tile) (state : MentsuHandSearchState) : Prop :=
  reachableOnTilesFromWithCopyLimit hand tiles initialMentsuHandState state

def MentsuHandBlockSearchOnTilesWithCopyLimit
    (hand : Hand) (tiles : List Tile) : Prop :=
  ∃ state, reachableOnTilesWithCopyLimit hand tiles state ∧
    IsMentsuHandBlockSearchComplete hand state

def MentsuHandBlockSearchOnTileOrderWithCopyLimit (hand : Hand) : Prop :=
  MentsuHandBlockSearchOnTilesWithCopyLimit hand mentsuHandTileOrder

lemma reachableOnTilesFromWithCopyLimit_to_reachableOnTilesFrom
    (hand : Hand) (tiles : List Tile) (start state : MentsuHandSearchState)
    (hreachable : reachableOnTilesFromWithCopyLimit
      hand tiles start state) :
    reachableOnTilesFrom hand tiles start state := by
  induction tiles generalizing start state with
  | nil =>
      exact hreachable
  | cons tile tiles ih =>
      rcases hreachable with ⟨middle, hnext, hrest⟩
      exact ⟨middle, nextMentsuHandStateAtWithCopyLimit_toNext
        hand tile start middle hnext, ih middle state hrest⟩

lemma mentsuHandBlockSearchOnTilesWithCopyLimit_to_mentsuHandBlockSearchOnTiles
    (hand : Hand) (tiles : List Tile)
    (hsearch : MentsuHandBlockSearchOnTilesWithCopyLimit hand tiles) :
    MentsuHandBlockSearchOnTiles hand tiles := by
  rcases hsearch with ⟨state, hreachable, hcomplete⟩
  exact ⟨state,
    reachableOnTilesFromWithCopyLimit_to_reachableOnTilesFrom
      hand tiles initialMentsuHandState state hreachable, hcomplete⟩

lemma reachableOnTilesWithCopyLimit_copyLimit
    (hand : Hand) (tiles : List Tile) (state : MentsuHandSearchState)
    (hreachable : reachableOnTilesWithCopyLimit hand tiles state) :
    CompletionRespectsCopyLimit state := by
  have hinitial : CompletionRespectsCopyLimit initialMentsuHandState := by
    intro tile
    simp [CompletionRespectsCopyLimit, initialMentsuHandState,
      taatsuCompletionTiles]
  have aux :
      ∀ (tiles : List Tile) (start state : MentsuHandSearchState),
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
          (nextMentsuHandStateAtWithCopyLimit_copyLimit
            hand tile start middle hnext) hrest
  exact aux tiles initialMentsuHandState state hinitial hreachable

lemma nextMentsuHandStateWithCopyLimit_copyLimit
    (hand : Hand) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandStateWithCopyLimit hand state next) :
    CompletionRespectsCopyLimit next := by
  rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
  exact hcopy

def reachableWithinWithCopyLimit
    (hand : Hand) : Nat → MentsuHandSearchState → Prop
  | 0, state => state = initialMentsuHandState
  | fuel + 1, state =>
      ∃ previous,
        reachableWithinWithCopyLimit hand fuel previous ∧
        NextMentsuHandStateWithCopyLimit hand previous state

lemma initialMentsuHandState_copyLimit :
    CompletionRespectsCopyLimit initialMentsuHandState := by
  intro tile
  simp [CompletionRespectsCopyLimit, initialMentsuHandState,
    taatsuCompletionTiles]

lemma reachableWithinWithCopyLimit_copyLimit
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    CompletionRespectsCopyLimit state := by
  induction fuel generalizing state with
  | zero =>
      rw [hreachable]
      exact initialMentsuHandState_copyLimit
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      exact nextMentsuHandStateWithCopyLimit_copyLimit hand previous state hnext

lemma reachableWithinWithCopyLimit_melds_le_four
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    state.melds ≤ 4 := by
  induction fuel generalizing state with
  | zero =>
      subst state
      simp [initialMentsuHandState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
      have hbound := hvalid.2.1
      simp only [applyMentsuHandChoice] at hbound ⊢
      omega

lemma reachableWithinWithCopyLimit_used_subset
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    ∀ tile, state.used.count tile ≤ hand.counts tile := by
  induction fuel generalizing state with
  | zero =>
      intro tile
      subst state
      simp [initialMentsuHandState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      intro tile
      rcases hnext with ⟨choice, _, hvalid, _, rfl⟩
      exact hvalid.1 tile

lemma reachableWithinWithCopyLimit_taatsu_le_four
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    state.taatsu ≤ 4 := by
  induction fuel generalizing state with
  | zero =>
      subst state
      simp [initialMentsuHandState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
      have hbound := hvalid.2.2.1
      simp only [applyMentsuHandChoice] at hbound ⊢
      omega

lemma nextMentsuHandStateAtWithCopyLimit_skip_of_reachable
    (hand : Hand) (tile : Tile) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    NextMentsuHandStateAtWithCopyLimit hand tile state
      (applyMentsuHandChoice hand state .skip
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
  apply nextMentsuHandStateAtWithCopyLimit_skip
    hand tile state
    (reachableWithinWithCopyLimit_used_subset hand fuel state hreachable)
    (reachableWithinWithCopyLimit_copyLimit hand fuel state hreachable)
    (reachableWithinWithCopyLimit_melds_le_four hand fuel state hreachable)
    (reachableWithinWithCopyLimit_taatsu_le_four hand fuel state hreachable)

lemma reachableOnTilesFromWithCopyLimit_skips
    (hand : Hand) (tiles : List Tile) (fuel : Nat)
    (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    ∃ final,
      reachableOnTilesFromWithCopyLimit hand tiles state final ∧
        reachableWithinWithCopyLimit hand (fuel + tiles.length) final := by
  induction tiles generalizing fuel state with
  | nil =>
      exact ⟨state, rfl, by simpa using hreachable⟩
  | cons tile tiles ih =>
      let hvalid : ValidMentsuHandChoice hand state .skip := by
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
            (applyMentsuHandChoice hand state .skip hvalid) := by
        intro tile
        dsimp [applyMentsuHandChoice]
        simp only [choiceTiles, Multiset.add_zero]
        exact hstatecopy tile
      have hskip :
          NextMentsuHandStateAtWithCopyLimit hand tile state
            (applyMentsuHandChoice hand state .skip hvalid) := by
        refine ⟨.skip, ?_, hvalid, ?_, rfl⟩
        · apply (mem_choicesForTileWithCopyLimit_iff
            hand state tile .skip).mpr
          exact ⟨by simp [choicesForTile, allMentsuHandChoices],
            ⟨hvalid, hcopy⟩⟩
        · exact hcopy
      have hreachableNext :
          reachableWithinWithCopyLimit hand (fuel + 1)
            (applyMentsuHandChoice hand state .skip hvalid) := by
        exact ⟨state, hreachable,
          nextMentsuHandStateAtWithCopyLimit_toNextWithCopyLimit
            hand tile state
            (applyMentsuHandChoice hand state .skip hvalid) hskip⟩
      obtain ⟨final, hpath, hfinal⟩ :=
        ih (fuel + 1)
          (applyMentsuHandChoice hand state .skip hvalid) hreachableNext
      refine ⟨final, ?_, ?_⟩
      · exact ⟨applyMentsuHandChoice hand state .skip hvalid, hskip, hpath⟩
      · have hlength :
            fuel + (tile :: tiles).length = fuel + 1 + tiles.length := by
          simp only [List.length_cons]
          omega
        rw [hlength]
        exact hfinal

lemma reachableOnTilesFromWithCopyLimit_choice_then_skips
    (hand : Hand) (tile : Tile) (tiles : List Tile) (fuel : Nat)
    (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hreachable : reachableWithinWithCopyLimit hand fuel state)
    (hchoice : choice ∈ allMentsuHandChoices)
    (htile : tile ∈ choiceTiles choice)
    (hvalid : ValidMentsuHandChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand state choice hvalid)) :
    ∃ final,
      reachableOnTilesFromWithCopyLimit hand (tile :: tiles) state final ∧
        reachableWithinWithCopyLimit hand
          (fuel + 1 + tiles.length) final := by
  have hnext :
      NextMentsuHandStateAtWithCopyLimit hand tile state
        (applyMentsuHandChoice hand state choice hvalid) :=
    nextMentsuHandStateAtWithCopyLimit_of_choice
      hand tile state choice hchoice htile hvalid hcopy
  have hreachableNext :
      reachableWithinWithCopyLimit hand (fuel + 1)
        (applyMentsuHandChoice hand state choice hvalid) :=
    ⟨state, hreachable,
      nextMentsuHandStateAtWithCopyLimit_toNextWithCopyLimit
        hand tile state (applyMentsuHandChoice hand state choice hvalid) hnext⟩
  obtain ⟨final, htail, hfinal⟩ :=
    reachableOnTilesFromWithCopyLimit_skips
      hand tiles (fuel + 1)
        (applyMentsuHandChoice hand state choice hvalid) hreachableNext
  refine ⟨final, ⟨applyMentsuHandChoice hand state choice hvalid, hnext, htail⟩, ?_⟩
  exact hfinal

lemma reachableOnTilesFromWithCopyLimit_append
    (hand : Hand) (left right : List Tile)
    (start middle final : MentsuHandSearchState)
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
    (fuel : Nat) (state : MentsuHandSearchState) (choice : MentsuHandChoice)
    (hreachable : reachableWithinWithCopyLimit hand fuel state)
    (hchoice : choice ∈ allMentsuHandChoices)
    (htile : tile ∈ choiceTiles choice)
    (hvalid : ∀ middle,
      reachableWithinWithCopyLimit hand (fuel + before.length) middle →
        ValidMentsuHandChoice hand middle choice)
    (hcopy : ∀ middle hmiddle,
      CompletionRespectsCopyLimit
        (applyMentsuHandChoice hand middle choice (hvalid middle hmiddle))) :
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

inductive AppliesMentsuHandChoices (hand : Hand) :
    MentsuHandSearchState → List MentsuHandChoice → MentsuHandSearchState → Prop
  | nil (state : MentsuHandSearchState) :
      AppliesMentsuHandChoices hand state [] state
  | cons (state : MentsuHandSearchState) (choice : MentsuHandChoice)
      (hchoice : choice ∈ allMentsuHandChoices)
      (hvalid : ValidMentsuHandChoice hand state choice)
      (final : MentsuHandSearchState)
      (htail :
        AppliesMentsuHandChoices hand
          (applyMentsuHandChoice hand state choice hvalid) choices final) :
      AppliesMentsuHandChoices hand state (choice :: choices) final

lemma AppliesMentsuHandChoices.used_eq
    {hand : Hand} {state final : MentsuHandSearchState}
    {choices : List MentsuHandChoice}
    (hpath : AppliesMentsuHandChoices hand state choices final) :
    final.used = state.used + mentsuHandChoiceTiles choices := by
  induction hpath with
  | nil =>
      simp [mentsuHandChoiceTiles]
  | @cons state choice hvalid final choices htail ih =>
      cases choice <;>
        simp_all [applyMentsuHandChoice, mentsuHandChoiceTiles, choiceTiles]
      all_goals
        try rw [ih]
        try simp [applyMentsuHandChoice, choiceTiles]
        try ac_rfl

lemma nextMentsuHandStateWithCopyLimit_toNext
    (hand : Hand) (state next : MentsuHandSearchState)
    (hnext : NextMentsuHandStateWithCopyLimit hand state next) :
    NextMentsuHandState hand state next := by
  rcases hnext with ⟨choice, hchoice, hvalid, _, rfl⟩
  exact ⟨choice, hchoice, hvalid, rfl⟩

lemma reachableWithinWithCopyLimit_to_reachableWithin
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    reachableWithin hand fuel state := by
  induction fuel generalizing state with
  | zero =>
      exact hreachable
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rw [reachableWithin_succ_iff]
      exact ⟨previous, ih previous hprevious,
        nextMentsuHandStateWithCopyLimit_toNext hand previous state hnext⟩

lemma reachableOnTilesWithCopyLimit_to_reachableWithinWithCopyLimit
    (hand : Hand) (tiles : List Tile) (state : MentsuHandSearchState)
    (hreachable : reachableOnTilesWithCopyLimit hand tiles state) :
    reachableWithinWithCopyLimit hand tiles.length state := by
  have aux :
      ∀ (remaining : List Tile) (start state : MentsuHandSearchState)
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
            nextMentsuHandStateAtWithCopyLimit_toNextWithCopyLimit
              hand tile start middle hnext⟩
        have hresult := ih middle state (fuel + 1) hmiddle htail
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult
  have hresult := aux tiles initialMentsuHandState state 0
    (by rfl) hreachable
  simpa using hresult

lemma completedTargetForState_eq_used_add_completion
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    completedTargetForState state pair =
      stateHistoryTiles state +
        taatsuCompletionTiles state.taatsuHistory.reverse := by
  rw [completedTargetForState, completedMeldsForState_tiles state pair hpair]
  rw [mentsuHandTargetWithTaatsuOfState_eq_stateHistoryTiles state pair hpair]

lemma validCounts_completedTarget_of_copyLimit
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
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

lemma completedMeldsForState_card (state : MentsuHandSearchState) :
    (meldsTiles (completedMeldsForState state)).card =
      3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  rw [meldsTiles_card, completedMeldsForState_length]

lemma completedTargetForState_card
    (state : MentsuHandSearchState) (pair : Tile) :
    (completedTargetForState state pair).card =
      2 + 3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  unfold completedTargetForState
  rw [Multiset.card_add, pairTiles_card, completedMeldsForState_card]

lemma completedTargetForState_sum
    (state : MentsuHandSearchState) (pair : Tile) :
    (∑ tile : Tile, countsOfTiles (completedTargetForState state pair) tile) =
      2 + 3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  rw [countsOfTiles_sum_eq_card, completedTargetForState_card]

lemma completedTargetForState_sum_of_blockCount
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
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
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
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

lemma complete_mentsuHand_completedTarget
    (before : Hand) (state : MentsuHandSearchState) (pair : Tile)
    (hvalid : ValidCounts
      (targetHand before (countsOfTiles (completedTargetForState state pair))))
    (hmelds : HasMentsuHandMeldCount before (completedMeldsForState state)) :
    Complete .mentsuHand
      (targetHand before (countsOfTiles (completedTargetForState state pair))) := by
  apply complete_mentsuHand_targetHand
  · exact hvalid
  · exact hmelds
  · exact targetHand_hasTiles_countsOfTiles before
      (completedTargetForState state pair)

/-- A target is a valid mentsu-hand-form completion for the standing tiles. -/
def IsMentsuHandTarget
    (hand : Hand) (pair : Tile) (melds : List Meld) : Prop :=
  HasMentsuHandMeldCount hand melds ∧
    ∀ tile, hand.counts tile ≤
      (mentsuHandTarget pair melds).count tile

/-- The number of additional tiles needed to realize a mentsuHand target. -/
def mentsuHandTargetDistance
    (hand : Hand) (pair : Tile) (melds : List Meld) : Nat :=
  targetDeficit hand (mentsuHandTarget pair melds)

lemma mentsuHandTargetDistance_eq_countDeficit
    (hand : Hand) (pair : Tile) (melds : List Meld) :
    mentsuHandTargetDistance hand pair melds =
      countDeficit hand.counts
        (countsOfTiles (mentsuHandTarget pair melds)) := by
  rfl

def mentsuHandMeldListsOfLength : Nat → Finset (List Meld)
  | 0 => {[]}
  | length + 1 =>
      Finset.univ.biUnion fun meld =>
        (mentsuHandMeldListsOfLength length).image (meld :: ·)

lemma mem_mentsuHandMeldListsOfLength_iff
    (length : Nat) (melds : List Meld) :
    melds ∈ mentsuHandMeldListsOfLength length ↔ melds.length = length := by
  induction length generalizing melds with
  | zero =>
      simp [mentsuHandMeldListsOfLength]
  | succ length ih =>
      simp only [mentsuHandMeldListsOfLength, Finset.mem_biUnion,
        Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨head, tail, htail, rfl⟩
        have hlength := ih tail |>.1 htail
        simp only [List.length_cons]
        omega
      · intro hlength
        cases melds with
        | nil =>
            simp at hlength
        | cons head tail =>
            simp only [List.length_cons] at hlength
            refine ⟨head, tail, ?_, rfl⟩
            exact ih tail |>.2 (by omega)

def mentsuHandTargetConfigurations (fixedMelds : Nat) :
    Finset (Tile × List Meld) :=
  Finset.univ ×ˢ mentsuHandMeldListsOfLength (4 - fixedMelds)

def validCountsDecidable (hand : Hand) : Decidable (ValidCounts hand) := by
  unfold ValidCounts
  exact Fintype.decidableForallFintype

def validCountsBool (hand : Hand) : Bool :=
  @decide (ValidCounts hand) (validCountsDecidable hand)

lemma validCountsBool_eq_true_iff (hand : Hand) :
    validCountsBool hand = true ↔ ValidCounts hand := by
  simp [validCountsBool]

def validTileMultisetBool (tiles : Multiset Tile) : Bool :=
  validCountsBool
    { counts := countsOfTiles tiles
      fixedMelds := 0 }

lemma validTileMultisetBool_eq_true_iff (tiles : Multiset Tile) :
    validTileMultisetBool tiles = true ↔
      ∀ tile, tiles.count tile ≤ 4 := by
  change validCountsBool
    { counts := countsOfTiles tiles
      fixedMelds := 0 } = true ↔ _
  rw [validCountsBool_eq_true_iff]
  rfl

lemma validTileMultisetBool_add_left
    (tiles extra : Multiset Tile)
    (hvalid : validTileMultisetBool (tiles + extra) = true) :
    validTileMultisetBool tiles = true := by
  apply (validTileMultisetBool_eq_true_iff tiles).2
  intro tile
  have hsum :=
    (validTileMultisetBool_eq_true_iff (tiles + extra)).1 hvalid tile
  have hle : tiles.count tile ≤ (tiles + extra).count tile := by
    simp only [Multiset.count_add]
    omega
  omega

lemma validTileMultisetBool_eq_true_iff_targetHand
    (hand : Hand) (tiles : Multiset Tile) :
    validTileMultisetBool tiles = true ↔
      ValidCounts (targetHand hand (countsOfTiles tiles)) := by
  rw [validTileMultisetBool_eq_true_iff]
  change (∀ tile, tiles.count tile ≤ 4) ↔
    (∀ tile, tiles.count tile ≤ 4)
  rfl

lemma mem_mentsuHandTargetConfigurations_iff
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4)
    (pair : Tile) (melds : List Meld) :
    (pair, melds) ∈ mentsuHandTargetConfigurations fixedMelds ↔
      melds.length + fixedMelds = 4 := by
  rw [mentsuHandTargetConfigurations, Finset.mem_product]
  simp only [Finset.mem_univ, true_and,
    mem_mentsuHandMeldListsOfLength_iff]
  omega

def validMentsuHandTargetConfigurations (hand : Hand) :
    Finset (Tile × List Meld) :=
  (mentsuHandTargetConfigurations hand.fixedMelds).filter
    (fun candidate =>
      validCountsBool
        (targetHand hand
          (countsOfTiles
            (mentsuHandTarget candidate.1 candidate.2))) = true)

lemma mem_validMentsuHandTargetConfigurations_iff
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4)
    (pair : Tile) (melds : List Meld) :
    (pair, melds) ∈ validMentsuHandTargetConfigurations hand ↔
      melds.length + hand.fixedMelds = 4 ∧
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuHandTarget pair melds))) := by
  classical
  rw [validMentsuHandTargetConfigurations, Finset.mem_filter,
    mem_mentsuHandTargetConfigurations_iff
      hand.fixedMelds hfixed pair melds]
  rw [validCountsBool_eq_true_iff]

def mentsuHandMeldTileStatesDP : Nat → Finset (Multiset Tile)
  | 0 => {0}
  | meldCount + 1 =>
      (Finset.univ.biUnion fun meld =>
        (mentsuHandMeldTileStatesDP meldCount).image
          (fun tiles => meldTiles meld + tiles)).filter
        (fun tiles => validTileMultisetBool tiles = true)

lemma mem_mentsuHandMeldTileStatesDP_iff
    (meldCount : Nat) (tiles : Multiset Tile) :
    tiles ∈ mentsuHandMeldTileStatesDP meldCount ↔
      ∃ melds, melds.length = meldCount ∧
        meldsTiles melds = tiles ∧ validTileMultisetBool tiles = true := by
  induction meldCount generalizing tiles with
  | zero =>
      change tiles ∈ ({0} : Finset (Multiset Tile)) ↔ _
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl
        refine ⟨[], rfl, rfl, ?_⟩
        apply (validTileMultisetBool_eq_true_iff 0).2
        intro tile
        simp
      · rintro ⟨melds, hlength, htiles, _⟩
        cases melds with
        | nil =>
            simpa [meldsTiles] using htiles.symm
        | cons meld melds =>
            simp at hlength
  | succ meldCount ih =>
      simp only [mentsuHandMeldTileStatesDP, Finset.mem_filter,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨meld, previous, hprevious, heq⟩, hvalid⟩
        obtain ⟨melds, hlength, htiles, _⟩ :=
          (ih previous).mp hprevious
        refine ⟨meld :: melds, ?_, ?_, hvalid⟩
        · simp [hlength]
        · calc
            meldsTiles (meld :: melds) =
                meldTiles meld + meldsTiles melds := rfl
            _ = meldTiles meld + previous := by rw [htiles]
            _ = tiles := heq
      · rintro ⟨melds, hlength, htiles, hvalid⟩
        cases melds with
        | nil =>
            simp at hlength
        | cons meld melds =>
            simp only [List.length_cons] at hlength
            have hvalidFull' := hvalid
            have hvalidFull :
                validTileMultisetBool
                  (meldTiles meld + meldsTiles melds) = true := by
              rw [← htiles] at hvalidFull'
              simpa [meldsTiles] using hvalidFull'
            have htailValid :
                validTileMultisetBool (meldsTiles melds) = true := by
              apply validTileMultisetBool_add_left
                (meldsTiles melds) (meldTiles meld)
              simpa [Multiset.add_comm] using hvalidFull
            have hprevious :
                meldsTiles melds ∈ mentsuHandMeldTileStatesDP meldCount :=
              (ih (meldsTiles melds)).2
                ⟨melds, by omega, rfl, htailValid⟩
            refine ⟨⟨meld, meldsTiles melds, hprevious, ?_⟩, hvalid⟩
            calc
              meldTiles meld + meldsTiles melds =
                  meldsTiles (meld :: melds) := rfl
              _ = tiles := htiles

def mentsuHandTargetTileStatesDP (fixedMelds : Nat) :
    Finset (Multiset Tile) :=
  (Finset.univ.biUnion fun pair =>
    (mentsuHandMeldTileStatesDP (4 - fixedMelds)).image
      (fun meldTiles => pairTiles pair + meldTiles)).filter
    (fun tiles => validTileMultisetBool tiles = true)

lemma mem_mentsuHandTargetTileStatesDP_iff
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4)
    (tiles : Multiset Tile) :
    tiles ∈ mentsuHandTargetTileStatesDP fixedMelds ↔
      ∃ pair melds,
        melds.length + fixedMelds = 4 ∧
        mentsuHandTarget pair melds = tiles ∧
        validTileMultisetBool tiles = true := by
  unfold mentsuHandTargetTileStatesDP
  simp only [Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨pair, meldTiles, hmeldTiles, rfl⟩, hvalid⟩
    obtain ⟨melds, hlength, rfl, _⟩ :=
      (mem_mentsuHandMeldTileStatesDP_iff (4 - fixedMelds) meldTiles).mp
        hmeldTiles
    refine ⟨pair, melds, ?_, rfl, hvalid⟩
    omega
  · rintro ⟨pair, melds, hlength, rfl, hvalid⟩
    have hmeldValid :
        validTileMultisetBool (meldsTiles melds) = true := by
      apply validTileMultisetBool_add_left
        (meldsTiles melds) (pairTiles pair)
      simpa [mentsuHandTarget, Multiset.add_comm] using hvalid
    refine ⟨⟨pair, meldsTiles melds, ?_, rfl⟩, hvalid⟩
    · exact (mem_mentsuHandMeldTileStatesDP_iff (4 - fixedMelds)
        (meldsTiles melds)).2
        ⟨melds, by omega, rfl, hmeldValid⟩

def mentsuHandTargetCostStatesDP (hand : Hand) :
    Finset (Multiset Tile × Nat) :=
  (mentsuHandTargetTileStatesDP hand.fixedMelds).image
    (fun tiles =>
      (tiles, countDeficit hand.counts (countsOfTiles tiles)))

lemma mem_mentsuHandTargetCostStatesDP_iff
    (hand : Hand) (state : Multiset Tile × Nat) :
    state ∈ mentsuHandTargetCostStatesDP hand ↔
      state.1 ∈ mentsuHandTargetTileStatesDP hand.fixedMelds ∧
      state.2 = countDeficit hand.counts (countsOfTiles state.1) := by
  unfold mentsuHandTargetCostStatesDP
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨tiles, htiles, heq⟩
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    refine ⟨?_, ?_⟩
    · rw [← hfst]
      exact htiles
    · rw [← hfst]
      exact hsnd.symm
  · rintro ⟨htiles, hcost⟩
    refine ⟨state.1, htiles, ?_⟩
    exact Prod.ext rfl hcost.symm

lemma countsOfTiles_add (tiles extra : Multiset Tile) :
    countsOfTiles (tiles + extra) =
      countsOfTiles tiles + countsOfTiles extra := by
  funext tile
  simp [countsOfTiles, Multiset.count_add]

lemma countDeficit_tiles_add_mono
    (current : TileCounts) (tiles extra : Multiset Tile) :
    countDeficit current (countsOfTiles tiles) ≤
      countDeficit current (countsOfTiles (tiles + extra)) := by
  unfold countDeficit
  apply Finset.sum_le_sum
  intro tile _
  rw [countsOfTiles_add]
  simp only [Pi.add_apply]
  omega

/-- Extend a target state and add only the newly incurred deficit. -/
def mentsuHandCostStateAdd (hand : Hand)
    (state : Multiset Tile × Nat) (extra : Multiset Tile) :
    Multiset Tile × Nat :=
  let tiles := state.1 + extra
  (tiles,
    state.2 + (countDeficit hand.counts (countsOfTiles tiles) -
      countDeficit hand.counts (countsOfTiles state.1)))

lemma mentsuHandCostStateAdd_cost
    (hand : Hand) (state : Multiset Tile × Nat) (extra : Multiset Tile)
    (hcost :
      state.2 = countDeficit hand.counts (countsOfTiles state.1)) :
    (mentsuHandCostStateAdd hand state extra).2 =
      countDeficit hand.counts
        (countsOfTiles ((mentsuHandCostStateAdd hand state extra).1)) := by
  unfold mentsuHandCostStateAdd
  dsimp only
  rw [hcost]
  have hmono := countDeficit_tiles_add_mono
    hand.counts state.1 extra
  omega

def mentsuHandMeldCostStatesDP (hand : Hand) (initialTiles : Multiset Tile) :
    Nat → Finset (Multiset Tile × Nat)
  | 0 =>
      Finset.filter
        (fun state => validTileMultisetBool state.1 = true)
        ({(initialTiles,
            countDeficit hand.counts (countsOfTiles initialTiles))} :
          Finset (Multiset Tile × Nat))
  | meldCount + 1 =>
      (Finset.univ.biUnion fun meld =>
        (mentsuHandMeldCostStatesDP hand initialTiles meldCount).image
          (fun state => mentsuHandCostStateAdd hand state (meldTiles meld)))
        |>.filter (fun state => validTileMultisetBool state.1 = true)

lemma mentsuHandMeldCostStatesDP_cost
    (hand : Hand) (initialTiles : Multiset Tile) (meldCount : Nat)
    (state : Multiset Tile × Nat)
    (hstate : state ∈ mentsuHandMeldCostStatesDP hand initialTiles meldCount) :
    state.2 = countDeficit hand.counts (countsOfTiles state.1) := by
  induction meldCount generalizing state with
  | zero =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_singleton] at hstate
      rw [hstate.1]
  | succ meldCount ih =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image] at hstate
      rcases hstate with ⟨⟨meld, previous, hprevious, heq⟩, _⟩
      have hpreviousCost := ih previous hprevious
      have hnextCost :=
        mentsuHandCostStateAdd_cost hand previous (meldTiles meld)
          hpreviousCost
      calc
        state.2 =
            (mentsuHandCostStateAdd hand previous (meldTiles meld)).2 :=
          (congrArg Prod.snd heq).symm
        _ = countDeficit hand.counts
            (countsOfTiles
              (mentsuHandCostStateAdd hand previous (meldTiles meld)).1) :=
          hnextCost
        _ = countDeficit hand.counts (countsOfTiles state.1) := by
          rw [congrArg Prod.fst heq]

lemma mem_mentsuHandMeldCostStatesDP_iff
    (hand : Hand) (initialTiles : Multiset Tile)
    (meldCount : Nat) (state : Multiset Tile × Nat) :
    state ∈ mentsuHandMeldCostStatesDP hand initialTiles meldCount ↔
      ∃ melds,
        melds.length = meldCount ∧
        meldsTiles melds + initialTiles = state.1 ∧
        state.2 = countDeficit hand.counts (countsOfTiles state.1) ∧
        validTileMultisetBool state.1 = true := by
  induction meldCount generalizing state with
  | zero =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, hvalid⟩
        refine ⟨[], rfl, ?_, rfl, hvalid⟩
        simp [meldsTiles]
      · rintro ⟨melds, hlength, htiles, hcost, hvalid⟩
        cases melds with
        | nil =>
            simp only [List.length_nil] at hlength
            simp [meldsTiles] at htiles
            have hstate : state =
                (initialTiles,
                  countDeficit hand.counts (countsOfTiles initialTiles)) := by
              apply Prod.ext
              · exact htiles.symm
              · calc
                  state.2 =
                      countDeficit hand.counts (countsOfTiles state.1) := hcost
                  _ = countDeficit hand.counts
                      (countsOfTiles initialTiles) := by rw [htiles]
            exact ⟨hstate, hvalid⟩
        | cons meld melds =>
            simp at hlength
  | succ meldCount ih =>
      simp only [mentsuHandMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · intro hstate
        rcases hstate with ⟨⟨meld, previous, hprevious, heq⟩, hvalid⟩
        have hpreviousCost :=
          mentsuHandMeldCostStatesDP_cost hand initialTiles meldCount
            previous hprevious
        have hnextCost :=
          mentsuHandCostStateAdd_cost hand previous (meldTiles meld)
            hpreviousCost
        have hcost : state.2 =
            countDeficit hand.counts (countsOfTiles state.1) := by
          calc
            state.2 =
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).2 :=
              (congrArg Prod.snd heq).symm
            _ = countDeficit hand.counts
                (countsOfTiles
                  (mentsuHandCostStateAdd hand previous (meldTiles meld)).1) :=
              hnextCost
            _ = countDeficit hand.counts (countsOfTiles state.1) := by
              rw [congrArg Prod.fst heq]
        obtain ⟨melds, hlength, htiles, _, _⟩ :=
          (ih previous).mp hprevious
        have hfst := congrArg Prod.fst heq
        refine ⟨meld :: melds, by simp [hlength], ?_, hcost, hvalid⟩
        calc
          meldsTiles (meld :: melds) + initialTiles =
              meldTiles meld + (meldsTiles melds + initialTiles) := by
                rw [show meldsTiles (meld :: melds) =
                    meldTiles meld + meldsTiles melds by rfl]
                ac_rfl
          _ = meldTiles meld + previous.1 := by rw [htiles]
          _ = (mentsuHandCostStateAdd hand previous (meldTiles meld)).1 := by
                simp [mentsuHandCostStateAdd, Multiset.add_comm]
          _ = state.1 := hfst
      · rintro ⟨melds, hlength, htiles, hcost, hvalid⟩
        cases melds with
        | nil =>
            simp at hlength
        | cons meld melds =>
            simp only [List.length_cons] at hlength
            have htilesShape :
                meldsTiles (meld :: melds) + initialTiles =
                  (meldsTiles melds + initialTiles) + meldTiles meld := by
              rw [show meldsTiles (meld :: melds) =
                  meldTiles meld + meldsTiles melds by rfl]
              ac_rfl
            have hpreviousValid :
                validTileMultisetBool
                  (meldsTiles melds + initialTiles) = true := by
              apply validTileMultisetBool_add_left
                (meldsTiles melds + initialTiles) (meldTiles meld)
              have hfinalValid := hvalid
              rw [← htiles] at hfinalValid
              rw [htilesShape] at hfinalValid
              exact hfinalValid
            let previous : Multiset Tile × Nat :=
              (meldsTiles melds + initialTiles,
                countDeficit hand.counts
                  (countsOfTiles (meldsTiles melds + initialTiles)))
            have hprevious :
                previous ∈ mentsuHandMeldCostStatesDP hand initialTiles meldCount :=
              (ih previous).2
                ⟨melds, by omega, rfl, rfl, hpreviousValid⟩
            have hnextCost :=
              mentsuHandCostStateAdd_cost hand previous (meldTiles meld) rfl
            have hfirst :
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).1 =
                  state.1 := by
              calc
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).1 =
                    (meldsTiles melds + initialTiles) + meldTiles meld := by
                      simp [mentsuHandCostStateAdd, previous]
                _ = meldsTiles (meld :: melds) + initialTiles :=
                  htilesShape.symm
                _ = state.1 := htiles
            refine ⟨⟨meld, previous, hprevious, ?_⟩, hvalid⟩
            apply Prod.ext
            · exact hfirst
            · calc
                (mentsuHandCostStateAdd hand previous (meldTiles meld)).2 =
                    countDeficit hand.counts
                      (countsOfTiles
                        (mentsuHandCostStateAdd hand previous (meldTiles meld)).1) :=
                  hnextCost
                _ = countDeficit hand.counts
                    (countsOfTiles state.1) := by
                      rw [hfirst]
                _ = state.2 := hcost.symm

def recursiveMentsuHandTargetCostStatesDP (hand : Hand) :
    Finset (Multiset Tile × Nat) :=
  Finset.univ.biUnion fun pair =>
    mentsuHandMeldCostStatesDP hand (pairTiles pair)
      (4 - hand.fixedMelds)

lemma recursiveMentsuHandTargetCostStatesDP_eq
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4) :
    recursiveMentsuHandTargetCostStatesDP hand =
      mentsuHandTargetCostStatesDP hand := by
  ext state
  unfold recursiveMentsuHandTargetCostStatesDP
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  rw [mem_mentsuHandTargetCostStatesDP_iff]
  constructor
  · rintro ⟨pair, hstate⟩
    obtain ⟨melds, hlength, htiles, hcost, hvalid⟩ :=
      (mem_mentsuHandMeldCostStatesDP_iff hand (pairTiles pair)
        (4 - hand.fixedMelds) state).mp hstate
    have htargetLength : melds.length + hand.fixedMelds = 4 := by
      omega
    have htarget :
        mentsuHandTarget pair melds = state.1 := by
      rw [mentsuHandTarget]
      calc
        pairTiles pair + meldsTiles melds =
            meldsTiles melds + pairTiles pair := by ac_rfl
        _ = state.1 := htiles
    have htilesTarget :
        state.1 ∈ mentsuHandTargetTileStatesDP hand.fixedMelds :=
      (mem_mentsuHandTargetTileStatesDP_iff hand.fixedMelds hfixed
        state.1).2
        ⟨pair, melds, htargetLength, htarget, hvalid⟩
    exact ⟨htilesTarget, hcost⟩
  · rintro ⟨htiles, hcost⟩
    obtain ⟨pair, melds, hlength, htarget, hvalid⟩ :=
      (mem_mentsuHandTargetTileStatesDP_iff hand.fixedMelds hfixed
        state.1).mp htiles
    refine ⟨pair, ?_⟩
    apply (mem_mentsuHandMeldCostStatesDP_iff hand (pairTiles pair)
      (4 - hand.fixedMelds) state).2
    refine ⟨melds, ?_, ?_, hcost, ?_⟩
    · omega
    · rw [← htarget, mentsuHandTarget]
      ac_rfl
    · exact hvalid

def validMentsuHandTargetDistances (hand : Hand) :
    Finset Nat :=
  (recursiveMentsuHandTargetCostStatesDP hand).image Prod.snd

lemma mentsuHandTargetCostDistances_eq_tileDistances
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4) :
    validMentsuHandTargetDistances hand =
      (mentsuHandTargetTileStatesDP hand.fixedMelds).image
        (fun tiles => countDeficit hand.counts (countsOfTiles tiles)) := by
  unfold validMentsuHandTargetDistances
  rw [recursiveMentsuHandTargetCostStatesDP_eq hand hfixed]
  ext distance
  simp [mentsuHandTargetCostStatesDP, Finset.image_image]

/-- Exhaustive target-state search; equal tile multisets are deduplicated at each meld count. -/
def mentsuHandTargetMinimumSearch (hand : Hand) : Option Int :=
  let distances := validMentsuHandTargetDistances hand
  if h : distances.Nonempty then
    some ((distances.min' h : Int) - 1)
  else
    none

lemma mem_validMentsuHandTargetDistances_iff
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4) (distance : Nat) :
    distance ∈ validMentsuHandTargetDistances hand ↔
      ∃ pair melds,
        melds.length + hand.fixedMelds = 4 ∧
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuHandTarget pair melds))) ∧
        mentsuHandTargetDistance hand pair melds = distance := by
  classical
  rw [mentsuHandTargetCostDistances_eq_tileDistances hand hfixed]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨tiles, htiles, hdistance⟩
    obtain ⟨pair, melds, hmelds, htarget, hcopy⟩ :=
      (mem_mentsuHandTargetTileStatesDP_iff
        hand.fixedMelds hfixed tiles).mp htiles
    refine ⟨pair, melds, hmelds, ?_, ?_⟩
    · rw [← htarget] at hcopy
      exact (validTileMultisetBool_eq_true_iff_targetHand
        hand (mentsuHandTarget pair melds)).mp hcopy
    · rw [← htarget] at hdistance
      rw [mentsuHandTargetDistance_eq_countDeficit]
      exact hdistance
  · rintro ⟨pair, melds, hmelds, hvalid, hdistance⟩
    let tiles := mentsuHandTarget pair melds
    have hcopy :
        validTileMultisetBool tiles = true :=
      (validTileMultisetBool_eq_true_iff_targetHand hand tiles).mpr hvalid
    have htiles :
        tiles ∈ mentsuHandTargetTileStatesDP hand.fixedMelds :=
      (mem_mentsuHandTargetTileStatesDP_iff
        hand.fixedMelds hfixed tiles).mpr
        ⟨pair, melds, hmelds, rfl, hcopy⟩
    refine ⟨tiles, htiles, ?_⟩
    rw [mentsuHandTargetDistance_eq_countDeficit] at hdistance
    exact hdistance

lemma exists_min_validMentsuHandTargetDistance
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4)
    (hcandidate :
      ∃ pair melds,
        melds.length + hand.fixedMelds = 4 ∧
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuHandTarget pair melds)))) :
    ∃ distance, distance ∈ validMentsuHandTargetDistances hand ∧
      ∀ otherDistance,
        otherDistance ∈ validMentsuHandTargetDistances hand →
          distance ≤ otherDistance := by
  classical
  let distances := validMentsuHandTargetDistances hand
  have hnonempty : distances.Nonempty := by
    obtain ⟨pair, melds, hmelds, hvalid⟩ := hcandidate
    refine ⟨mentsuHandTargetDistance hand pair melds, ?_⟩
    exact (mem_validMentsuHandTargetDistances_iff
      hand hfixed (mentsuHandTargetDistance hand pair melds)).2
      ⟨pair, melds, hmelds, hvalid, rfl⟩
  let distance := distances.min' hnonempty
  refine ⟨distance, ?_, ?_⟩
  · change distance ∈ distances
    exact Finset.min'_mem distances hnonempty
  · intro otherDistance hother
    exact Finset.min'_le distances otherDistance hother

lemma exists_mentsuHandTarget_distance_le_of_reachesCompletion
    (before : Hand) (distance : Nat)
    (hreach : ReachesCompletion Complete .mentsuHand before distance) :
    ∃ pair melds,
      melds.length + before.fixedMelds = 4 ∧
        ValidCounts
          (targetHand before
            (countsOfTiles (mentsuHandTarget pair melds))) ∧
        mentsuHandTargetDistance before pair melds ≤ distance := by
  obtain ⟨after, hcomplete, hfixed, hdeficit⟩ :=
    exists_complete_mentsuHand_with_deficit_le before distance hreach
  rcases hcomplete with ⟨hvalidAfter, pair, melds, hmelds, htiles⟩
  have hcounts :
      after.counts =
        countsOfTiles (mentsuHandTarget pair melds) := by
    funext tile
    change after.counts tile =
      (mentsuHandTarget pair melds).count tile
    exact htiles tile
  have hvalidTarget :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))) := by
    intro tile
    change (countsOfTiles (mentsuHandTarget pair melds)) tile ≤ 4
    rw [← hcounts]
    exact hvalidAfter tile
  refine ⟨pair, melds, ?_, hvalidTarget, ?_⟩
  · rw [← hfixed]
    exact hmelds
  · rw [mentsuHandTargetDistance_eq_countDeficit]
    simpa [hcounts] using hdeficit

lemma no_shorter_mentsuHand_completion_of_minimal_mentsuHandTargetDistance
    (before : Hand) (pair : Tile) (melds : List Meld)
    (distance : Nat)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance before pair melds ≤
            mentsuHandTargetDistance before otherPair otherMelds) :
    ∀ smaller : Nat, smaller < distance →
      ¬ ReachesCompletion Complete .mentsuHand before smaller := by
  intro smaller hsmaller hreach
  obtain ⟨otherPair, otherMelds, hmelds, hvalid, hotherDistance⟩ :=
    exists_mentsuHandTarget_distance_le_of_reachesCompletion
      before smaller hreach
  have hminimal := hminimalTarget otherPair otherMelds hmelds hvalid
  omega

lemma mentsuHandTargetDistance_eq_zero_iff
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile) :
    mentsuHandTargetDistance hand pair melds = 0 ↔
      hand.counts = countsOfTiles (mentsuHandTarget pair melds) := by
  constructor
  · intro hdistance
    have hdeficit :
        countDeficit hand.counts
          (countsOfTiles (mentsuHandTarget pair melds)) = 0 := by
      rw [← mentsuHandTargetDistance_eq_countDeficit]
      exact hdistance
    have hzero :
        ∀ tile ∈ (Finset.univ : Finset Tile),
          (countsOfTiles (mentsuHandTarget pair melds)) tile -
              hand.counts tile = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun tile _ => Nat.zero_le _)).mp
      exact hdeficit
    have hle :
        ∀ tile, (countsOfTiles (mentsuHandTarget pair melds)) tile ≤
          hand.counts tile := by
      intro tile
      have hzeroTile := hzero tile (Finset.mem_univ tile)
      omega
    apply funext
    intro tile
    have heq :
        ∀ tile ∈ (Finset.univ : Finset Tile),
          (countsOfTiles (mentsuHandTarget pair melds)) tile =
            hand.counts tile := by
      apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
        (f := countsOfTiles (mentsuHandTarget pair melds))
        (g := hand.counts)
        (fun tile _ => hle tile)).mp
      exact hsum.symm
    exact (heq tile (Finset.mem_univ tile)).symm
  · intro hcounts
    rw [mentsuHandTargetDistance_eq_countDeficit]
    simp [countDeficit, hcounts]

lemma mentsuHandTargetDistance_pos_iff
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile) :
    0 < mentsuHandTargetDistance hand pair melds ↔
      hand.counts ≠ countsOfTiles (mentsuHandTarget pair melds) := by
  constructor
  · intro hpos hcounts
    have hzero : mentsuHandTargetDistance hand pair melds = 0 :=
      (mentsuHandTargetDistance_eq_zero_iff hand pair melds hsum).mpr hcounts
    omega
  · intro hne
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hne
        ((mentsuHandTargetDistance_eq_zero_iff hand pair melds hsum).mp hzero))

lemma mentsuHandTargetDistance_exchange
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (discarded drawn : Tile)
    (hdrawn :
      (mentsuHandTarget pair melds).count drawn > hand.counts drawn)
    (hdiscarded :
      hand.counts discarded >
        (mentsuHandTarget pair melds).count discarded)
    (hne : discarded ≠ drawn) :
    mentsuHandTargetDistance
        (exchangeHand hand discarded drawn) pair melds =
      mentsuHandTargetDistance hand pair melds - 1 := by
  rw [mentsuHandTargetDistance_eq_countDeficit,
    mentsuHandTargetDistance_eq_countDeficit]
  exact countDeficit_exchange
    (countsOfTiles (mentsuHandTarget pair melds))
    hand discarded drawn hdrawn hdiscarded hne

lemma exists_mentsuHandTarget_exchange
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hne :
      hand.counts ≠ countsOfTiles (mentsuHandTarget pair melds)) :
    ∃ discarded drawn,
      (mentsuHandTarget pair melds).count drawn > hand.counts drawn ∧
      hand.counts discarded >
        (mentsuHandTarget pair melds).count discarded ∧
      discarded ≠ drawn ∧
      mentsuHandTargetDistance
          (exchangeHand hand discarded drawn) pair melds =
        mentsuHandTargetDistance hand pair melds - 1 := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles⟩ :=
    exists_target_exchange_tiles hand
      (countsOfTiles (mentsuHandTarget pair melds)) hsum hne
  refine ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles, ?_⟩
  exact mentsuHandTargetDistance_exchange
    hand pair melds discarded drawn hdrawn hdiscarded hneTiles

lemma exists_mentsuHandTarget_exchange_of_pos
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hpos : 0 < mentsuHandTargetDistance hand pair melds) :
    ∃ discarded drawn,
      (mentsuHandTarget pair melds).count drawn > hand.counts drawn ∧
      hand.counts discarded >
        (mentsuHandTarget pair melds).count discarded ∧
      discarded ≠ drawn ∧
      mentsuHandTargetDistance
          (exchangeHand hand discarded drawn) pair melds =
        mentsuHandTargetDistance hand pair melds - 1 := by
  apply exists_mentsuHandTarget_exchange hand pair melds hsum
  exact (mentsuHandTargetDistance_pos_iff hand pair melds hsum).mp hpos

lemma reachesCompletion_mentsuHand_of_mentsuHandTarget
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    ReachesCompletion Complete .mentsuHand before
      (mentsuHandTargetDistance before pair melds) := by
  rw [mentsuHandTargetDistance_eq_countDeficit]
  apply reachesCompletion_mentsuHand_of_equal_sum
    before
    (countsOfTiles (mentsuHandTarget pair melds))
    pair melds hsum hvalid hmelds
  exact targetHand_hasTiles_countsOfTiles before
    (mentsuHandTarget pair melds)

lemma complete_mentsuHand_of_mentsuHandTarget_distance_zero
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = 0)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    Complete .mentsuHand before := by
  have hdeficit :
      countDeficit before.counts
        (countsOfTiles (mentsuHandTarget pair melds)) = 0 := by
    rw [← mentsuHandTargetDistance_eq_countDeficit]
    exact hdistance
  have hzero :
      ∀ tile ∈ (Finset.univ : Finset Tile),
        (countsOfTiles (mentsuHandTarget pair melds)) tile -
            before.counts tile = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun tile _ => Nat.zero_le _)).mp
    exact hdeficit
  have hle :
      ∀ tile, (countsOfTiles (mentsuHandTarget pair melds)) tile ≤
        before.counts tile := by
    intro tile
    have hzeroTile := hzero tile (Finset.mem_univ tile)
    omega
  have heq :
      ∀ tile ∈ (Finset.univ : Finset Tile),
        (countsOfTiles (mentsuHandTarget pair melds)) tile =
          before.counts tile := by
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := countsOfTiles (mentsuHandTarget pair melds))
      (g := before.counts)
      (fun tile _ => hle tile)).mp
    exact hsum.symm
  have hcounts :
      countsOfTiles (mentsuHandTarget pair melds) = before.counts := by
    funext tile
    exact heq tile (Finset.mem_univ tile)
  have hcomplete :
      Complete .mentsuHand
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))) := by
    exact complete_mentsuHand_targetHand before
      (countsOfTiles (mentsuHandTarget pair melds)) pair melds
      hvalid hmelds
      (targetHand_hasTiles_countsOfTiles before
        (mentsuHandTarget pair melds))
  simpa [targetHand, hcounts] using hcomplete

set_option maxHeartbeats 1000000 in
lemma reachesCompletion_mentsuHand_of_mentsuHandTarget_distance_one
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = 1)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    ReachesCompletion Complete .mentsuHand before 1 := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hne, hdistanceNext⟩ :=
    exists_mentsuHandTarget_exchange_of_pos
      before pair melds hsum (by omega)
  have hsumNext :
      (∑ tile : Tile, (exchangeHand before discarded drawn).counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile := by
    have hsumExchange :
        (∑ tile : Tile, (exchangeHand before discarded drawn).counts tile) =
          ∑ tile : Tile, before.counts tile := by
      change
        (∑ tile : Tile,
          exchangeCounts before discarded drawn tile) =
          ∑ tile : Tile, before.counts tile
      exact exchangeCounts_sum before discarded drawn hne (by omega)
    exact hsumExchange.trans hsum
  have hvalidNext :
      ValidCounts
        (targetHand (exchangeHand before discarded drawn)
          (countsOfTiles (mentsuHandTarget pair melds))) := by
    change
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds)))
    exact hvalid
  have hmeldsNext :
      melds.length + (exchangeHand before discarded drawn).fixedMelds = 4 := by
    change melds.length + before.fixedMelds = 4
    exact hmelds
  have hcomplete :
      Complete .mentsuHand (exchangeHand before discarded drawn) := by
    have hzeroNext :
        mentsuHandTargetDistance
            (exchangeHand before discarded drawn) pair melds = 0 := by
      omega
    have hcountsNext :
        (exchangeHand before discarded drawn).counts =
          countsOfTiles (mentsuHandTarget pair melds) :=
      (mentsuHandTargetDistance_eq_zero_iff
        (exchangeHand before discarded drawn) pair melds hsumNext).mp
        hzeroNext
    have htargetComplete :
        Complete .mentsuHand
          (targetHand (exchangeHand before discarded drawn)
            (countsOfTiles (mentsuHandTarget pair melds))) :=
      complete_mentsuHand_targetHand
        (exchangeHand before discarded drawn)
        (countsOfTiles (mentsuHandTarget pair melds))
        pair melds hvalidNext hmeldsNext
        (targetHand_hasTiles_countsOfTiles
          (exchangeHand before discarded drawn)
          (mentsuHandTarget pair melds))
    have hhand :
        exchangeHand before discarded drawn =
          targetHand (exchangeHand before discarded drawn)
            (countsOfTiles (mentsuHandTarget pair melds)) := by
      cases hnext : exchangeHand before discarded drawn with
      | mk counts fixed =>
          simp only [targetHand, hnext]
          simpa [hnext] using
            congrArg
              (fun counts : TileCounts =>
                ({ counts := counts, fixedMelds := fixed } : Hand))
              hcountsNext
    rw [hhand]
    exact htargetComplete
  apply ReachesCompletion.step
  · exact mentsuHandTargetExchange_handStep
      (countsOfTiles (mentsuHandTarget pair melds))
      before discarded drawn hdrawn hdiscarded hne
  · exact ReachesCompletion.done hcomplete

set_option maxHeartbeats 1000000 in
lemma reachesCompletion_mentsuHand_of_mentsuHandTarget_distance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    ReachesCompletion Complete .mentsuHand before distance := by
  induction distance generalizing before with
  | zero =>
      have hcomplete : Complete .mentsuHand before := by
        exact complete_mentsuHand_of_mentsuHandTarget_distance_zero
          before pair melds hdistance hsum hvalid hmelds
      exact ReachesCompletion.done hcomplete
  | succ distance ih =>
      obtain ⟨discarded, drawn, hdrawn, hdiscarded, hne, hdistanceNext⟩ :=
        exists_mentsuHandTarget_exchange_of_pos
          before pair melds hsum (by omega)
      have hsumNext :
          (∑ tile : Tile,
            (exchangeHand before discarded drawn).counts tile) =
            ∑ tile : Tile, (mentsuHandTarget pair melds).count tile := by
        have hsumExchange :
            (∑ tile : Tile,
              (exchangeHand before discarded drawn).counts tile) =
              ∑ tile : Tile, before.counts tile := by
          change
            (∑ tile : Tile,
              exchangeCounts before discarded drawn tile) =
              ∑ tile : Tile, before.counts tile
          exact exchangeCounts_sum before discarded drawn hne (by omega)
        exact hsumExchange.trans hsum
      have hvalidNext :
          ValidCounts
            (targetHand (exchangeHand before discarded drawn)
              (countsOfTiles (mentsuHandTarget pair melds))) := by
        change
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget pair melds)))
        exact hvalid
      have hmeldsNext :
          melds.length + (exchangeHand before discarded drawn).fixedMelds = 4 := by
        change melds.length + before.fixedMelds = 4
        exact hmelds
      have hdistanceNext' :
          mentsuHandTargetDistance
              (exchangeHand before discarded drawn) pair melds = distance := by
        omega
      have hrest :=
        ih (exchangeHand before discarded drawn)
          hdistanceNext' hsumNext hvalidNext hmeldsNext
      apply ReachesCompletion.step
      · exact mentsuHandTargetExchange_handStep
          (countsOfTiles (mentsuHandTarget pair melds))
          before discarded drawn hdrawn hdiscarded hne
      · exact hrest

lemma isShapeShanten_mentsuHand_of_mentsuHandTarget_distance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hminimal :
      ∀ smaller : Nat, smaller < distance →
        ¬ ReachesCompletion Complete .mentsuHand before smaller) :
    IsShapeShanten before .mentsuHand ((distance : Int) - 1) := by
  have hreaches :
      ReachesCompletion Complete .mentsuHand before distance :=
    reachesCompletion_mentsuHand_of_mentsuHandTarget_distance
      distance before pair melds hdistance hsum hvalid hmelds
  refine ⟨trivial, distance, ?_, hreaches, hminimal⟩
  omega

lemma isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuHandTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance before pair melds ≤
            mentsuHandTargetDistance before otherPair otherMelds) :
    IsShapeShanten before .mentsuHand ((distance : Int) - 1) := by
  apply isShapeShanten_mentsuHand_of_mentsuHandTarget_distance
    distance before pair melds hdistance hsum hvalid hmelds
  exact no_shorter_mentsuHand_completion_of_minimal_mentsuHandTargetDistance
    before pair melds distance hdistance hminimalTarget

lemma isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance_one_more
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuHandTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile,
        countsOfTiles (mentsuHandTarget pair melds) tile) =
        (∑ tile : Tile, before.counts tile) + 1)
    (hbeforeValid : ValidCounts before)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuHandTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance before pair melds ≤
            mentsuHandTargetDistance before otherPair otherMelds) :
    IsShapeShanten before .mentsuHand ((distance : Int) - 1) := by
  obtain ⟨reachedDistance, htargetDistance, hreach⟩ :=
    reachesCompletion_mentsuHand_of_one_more_target_tile
      before (countsOfTiles (mentsuHandTarget pair melds))
      pair melds hsum hbeforeValid hvalid hmelds
      (targetHand_hasTiles_countsOfTiles before
        (mentsuHandTarget pair melds))
  have hreachDistance :
      reachedDistance = distance := by
    calc
      reachedDistance =
          countDeficit before.counts
            (countsOfTiles (mentsuHandTarget pair melds)) :=
        htargetDistance
      _ = mentsuHandTargetDistance before pair melds :=
        (mentsuHandTargetDistance_eq_countDeficit before pair melds).symm
      _ = distance := hdistance
  have hreaches :
      ReachesCompletion Complete .mentsuHand before distance := by
    rw [← hreachDistance]
    exact hreach
  have hminimal :=
    no_shorter_mentsuHand_completion_of_minimal_mentsuHandTargetDistance
      before pair melds distance hdistance hminimalTarget
  refine ⟨trivial, distance, ?_, hreaches, hminimal⟩
  omega

private lemma nat_find_le_of_mem
    (predicate : Nat → Prop) [DecidablePred predicate]
    (hexists : ∃ n, predicate n)
    {value : Nat} (hvalue : predicate value) :
    Nat.find hexists ≤ value :=
  Nat.find_min' hexists hvalue

set_option maxHeartbeats 1000000 in
lemma exists_isShapeShanten_mentsuHand_of_valid_mentsuHandTarget
    (before : Hand)
    (hcandidate :
      ∃ pair melds,
        melds.length + before.fixedMelds = 4 ∧
          (∑ tile : Tile, before.counts tile) =
            ∑ tile : Tile, (mentsuHandTarget pair melds).count tile ∧
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget pair melds)))) :
    ∃ value : Int, IsShapeShanten before .mentsuHand value := by
  classical
  let candidateDistance : Nat → Prop := fun distance =>
    ∃ pair melds,
      melds.length + before.fixedMelds = 4 ∧
        (∑ tile : Tile, before.counts tile) =
          ∑ tile : Tile, (mentsuHandTarget pair melds).count tile ∧
        ValidCounts
          (targetHand before
            (countsOfTiles (mentsuHandTarget pair melds))) ∧
        mentsuHandTargetDistance before pair melds = distance
  have hexists : ∃ distance, candidateDistance distance := by
    obtain ⟨pair, melds, hmelds, hsum, hvalid⟩ := hcandidate
    exact ⟨mentsuHandTargetDistance before pair melds,
      pair, melds, hmelds, hsum, hvalid, rfl⟩
  let distance := Nat.find hexists
  obtain ⟨pair, melds, hmelds, hsum, hvalid, hdistance⟩ :=
    Nat.find_spec hexists
  have hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance before pair melds ≤
            mentsuHandTargetDistance before otherPair otherMelds := by
    intro otherPair otherMelds hotherMelds hotherValid
    have hlength : melds.length = otherMelds.length := by omega
    have hsumOther :
        (∑ tile : Tile, before.counts tile) =
          ∑ tile : Tile, (mentsuHandTarget otherPair otherMelds).count tile := by
      calc
        (∑ tile : Tile, before.counts tile) =
            ∑ tile : Tile, (mentsuHandTarget pair melds).count tile := hsum
        _ = (mentsuHandTarget pair melds).card := by
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuHandTarget pair melds))
        _ = (mentsuHandTarget otherPair otherMelds).card := by
          simp [mentsuHandTarget, Multiset.card_add, pairTiles_card,
            meldsTiles_card, hlength]
        _ = ∑ tile : Tile, (mentsuHandTarget otherPair otherMelds).count tile := by
          symm
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuHandTarget otherPair otherMelds))
    have hotherCandidate :
        candidateDistance (mentsuHandTargetDistance before otherPair otherMelds) :=
      ⟨otherPair, otherMelds, hotherMelds, hsumOther, hotherValid, rfl⟩
    calc
      mentsuHandTargetDistance before pair melds = distance := hdistance
      _ ≤ mentsuHandTargetDistance before otherPair otherMelds := by
        change Nat.find hexists ≤
          mentsuHandTargetDistance before otherPair otherMelds
        exact nat_find_le_of_mem candidateDistance hexists hotherCandidate
  have hshape :
      IsShapeShanten before .mentsuHand ((distance : Int) - 1) :=
    isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance
      distance before pair melds hdistance hsum hvalid hmelds hminimalTarget
  exact ⟨(distance : Int) - 1, hshape⟩

set_option maxHeartbeats 1000000 in
lemma exists_isShapeShanten_mentsuHand_of_valid_mentsuHandTarget_one_more
    (before : Hand) (hbeforeValid : ValidCounts before)
    (hcandidate :
      ∃ pair melds,
        melds.length + before.fixedMelds = 4 ∧
          (∑ tile : Tile,
            countsOfTiles (mentsuHandTarget pair melds) tile) =
            (∑ tile : Tile, before.counts tile) + 1 ∧
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget pair melds)))) :
    ∃ value : Int, IsShapeShanten before .mentsuHand value := by
  classical
  let candidateDistance : Nat → Prop := fun distance =>
    ∃ pair melds,
      melds.length + before.fixedMelds = 4 ∧
        (∑ tile : Tile,
          countsOfTiles (mentsuHandTarget pair melds) tile) =
          (∑ tile : Tile, before.counts tile) + 1 ∧
        ValidCounts
          (targetHand before
            (countsOfTiles (mentsuHandTarget pair melds))) ∧
        mentsuHandTargetDistance before pair melds = distance
  have hexists : ∃ distance, candidateDistance distance := by
    obtain ⟨pair, melds, hmelds, hsum, hvalid⟩ := hcandidate
    exact ⟨mentsuHandTargetDistance before pair melds,
      pair, melds, hmelds, hsum, hvalid, rfl⟩
  let distance := Nat.find hexists
  obtain ⟨pair, melds, hmelds, hsum, hvalid, hdistance⟩ :=
    Nat.find_spec hexists
  have hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance before pair melds ≤
            mentsuHandTargetDistance before otherPair otherMelds := by
    intro otherPair otherMelds hotherMelds hotherValid
    have hlength : melds.length = otherMelds.length := by omega
    have hsumOther :
        (∑ tile : Tile,
          countsOfTiles (mentsuHandTarget otherPair otherMelds) tile) =
          (∑ tile : Tile, before.counts tile) + 1 := by
      calc
        (∑ tile : Tile,
            countsOfTiles (mentsuHandTarget otherPair otherMelds) tile) =
            (mentsuHandTarget otherPair otherMelds).card := by
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuHandTarget otherPair otherMelds))
        _ = (mentsuHandTarget pair melds).card := by
          simp [mentsuHandTarget, Multiset.card_add, pairTiles_card,
            meldsTiles_card, hlength]
        _ = ∑ tile : Tile,
            countsOfTiles (mentsuHandTarget pair melds) tile := by
          symm
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuHandTarget pair melds))
        _ = (∑ tile : Tile, before.counts tile) + 1 := hsum
    have hotherCandidate :
        candidateDistance (mentsuHandTargetDistance before otherPair otherMelds) :=
      ⟨otherPair, otherMelds, hotherMelds, hsumOther, hotherValid, rfl⟩
    calc
      mentsuHandTargetDistance before pair melds = distance := hdistance
      _ ≤ mentsuHandTargetDistance before otherPair otherMelds := by
        change Nat.find hexists ≤
          mentsuHandTargetDistance before otherPair otherMelds
        exact nat_find_le_of_mem candidateDistance hexists hotherCandidate
  have hshape :
      IsShapeShanten before .mentsuHand ((distance : Int) - 1) :=
    isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance_one_more
      distance before pair melds hdistance hsum hbeforeValid
      hvalid hmelds hminimalTarget
  exact ⟨(distance : Int) - 1, hshape⟩

lemma sum_countsOfTiles_mentsuHandTarget_of_thirteen_tile_count
    (hand : Hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (pair : Tile) (melds : List Meld)
    (hmelds : melds.length + hand.fixedMelds = 4) :
    (∑ tile : Tile, countsOfTiles (mentsuHandTarget pair melds) tile) =
      (∑ tile : Tile, hand.counts tile) + 1 := by
  calc
    _ = (mentsuHandTarget pair melds).card := by
      exact countsOfTiles_sum_eq_card (mentsuHandTarget pair melds)
    _ = 2 + 3 * melds.length := by
      simp [mentsuHandTarget, Multiset.card_add, pairTiles_card,
        meldsTiles_card]
    _ = tileCount hand + 1 := by omega
    _ = (∑ tile : Tile, hand.counts tile) + 1 := by rfl

set_option maxHeartbeats 1000000 in
lemma exists_mentsuHandTarget_reaching_isShapeShanten_distance
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) (hshape : IsShapeShanten hand .mentsuHand value) :
    ∃ distance : Nat, ∃ pair melds,
      (distance : Int) = value + 1 ∧
      melds.length + hand.fixedMelds = 4 ∧
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuHandTarget pair melds))) ∧
      mentsuHandTargetDistance hand pair melds = distance ∧
      ReachesCompletion Complete .mentsuHand hand distance := by
  rcases hshape with ⟨_, distance, hvalue, hreach, hminimal⟩
  obtain ⟨pair, melds, hmelds, hvalid, hdistanceLE⟩ :=
    exists_mentsuHandTarget_distance_le_of_reachesCompletion
      hand distance hreach
  have hsum :=
    sum_countsOfTiles_mentsuHandTarget_of_thirteen_tile_count
      hand hstanding pair melds hmelds
  obtain ⟨targetDistance, htargetDistance, htargetReach⟩ :=
    reachesCompletion_mentsuHand_of_one_more_target_tile
      hand (countsOfTiles (mentsuHandTarget pair melds)) pair melds
      hsum hbeforeValid hvalid hmelds
      (targetHand_hasTiles_countsOfTiles hand
        (mentsuHandTarget pair melds))
  have hreachDistance :
      targetDistance = mentsuHandTargetDistance hand pair melds := by
    calc
      targetDistance =
          countDeficit hand.counts
            (countsOfTiles (mentsuHandTarget pair melds)) :=
        htargetDistance
      _ = mentsuHandTargetDistance hand pair melds :=
        (mentsuHandTargetDistance_eq_countDeficit hand pair melds).symm
  have htargetLE : targetDistance ≤ distance := by
    calc
      targetDistance = mentsuHandTargetDistance hand pair melds :=
        hreachDistance
      _ ≤ distance := hdistanceLE
  have hdistanceLEtarget : distance ≤ targetDistance := by
    by_contra hnot
    have hshorter : targetDistance < distance := by omega
    exact hminimal targetDistance hshorter htargetReach
  have htargetDistanceEq : mentsuHandTargetDistance hand pair melds = distance := by
    omega
  have htargetDistanceEqNat : targetDistance = distance := by
    calc
      targetDistance = mentsuHandTargetDistance hand pair melds :=
        hreachDistance
      _ = distance := htargetDistanceEq
  refine ⟨distance, pair, melds, hvalue, hmelds, hvalid,
    htargetDistanceEq, ?_⟩
  rw [← htargetDistanceEqNat]
  exact htargetReach

set_option maxHeartbeats 1000000 in
lemma exists_minimal_mentsuHandTarget_of_isShapeShanten_mentsuHand
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) (hshape : IsShapeShanten hand .mentsuHand value) :
    ∃ distance : Nat, ∃ pair melds,
      (distance : Int) = value + 1 ∧
      melds.length + hand.fixedMelds = 4 ∧
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuHandTarget pair melds))) ∧
      mentsuHandTargetDistance hand pair melds = distance ∧
      ReachesCompletion Complete .mentsuHand hand distance ∧
      ∀ otherPair otherMelds,
        otherMelds.length + hand.fixedMelds = 4 →
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
        mentsuHandTargetDistance hand pair melds ≤
          mentsuHandTargetDistance hand otherPair otherMelds := by
  obtain ⟨distance, pair, melds, hvalue, hmelds, hvalid,
      hdistance, hreach⟩ :=
    exists_mentsuHandTarget_reaching_isShapeShanten_distance
      hand hbeforeValid hstanding value hshape
  rcases hshape with ⟨_, actualDistance, hactualValue, _, hminimal⟩
  have hdistanceEq : distance = actualDistance := by omega
  refine ⟨distance, pair, melds, hvalue, hmelds, hvalid,
    hdistance, hreach, ?_⟩
  intro otherPair otherMelds hotherMelds hotherValid
  have hsumOther :=
    sum_countsOfTiles_mentsuHandTarget_of_thirteen_tile_count
      hand hstanding otherPair otherMelds hotherMelds
  obtain ⟨otherDistance, hotherDistance, hotherReach⟩ :=
    reachesCompletion_mentsuHand_of_one_more_target_tile
      hand (countsOfTiles (mentsuHandTarget otherPair otherMelds))
      otherPair otherMelds hsumOther hbeforeValid hotherValid
      hotherMelds
      (targetHand_hasTiles_countsOfTiles hand
        (mentsuHandTarget otherPair otherMelds))
  have hotherDistanceEq :
      otherDistance =
        mentsuHandTargetDistance hand otherPair otherMelds := by
    calc
      otherDistance =
          countDeficit hand.counts
            (countsOfTiles (mentsuHandTarget otherPair otherMelds)) :=
        hotherDistance
      _ = mentsuHandTargetDistance hand otherPair otherMelds :=
        (mentsuHandTargetDistance_eq_countDeficit hand otherPair otherMelds).symm
  by_contra hnotMinimal
  have hshorter : otherDistance < actualDistance := by
    omega
  exact hminimal otherDistance hshorter hotherReach

lemma isShapeShanten_mentsuHand_iff_exists_minimal_mentsuHandTarget
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) :
    IsShapeShanten hand .mentsuHand value ↔
      ∃ distance : Nat, ∃ pair melds,
        (distance : Int) = value + 1 ∧
        melds.length + hand.fixedMelds = 4 ∧
        (∑ tile : Tile,
          countsOfTiles (mentsuHandTarget pair melds) tile) =
          (∑ tile : Tile, hand.counts tile) + 1 ∧
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuHandTarget pair melds))) ∧
        mentsuHandTargetDistance hand pair melds = distance ∧
        ∀ otherPair otherMelds,
          otherMelds.length + hand.fixedMelds = 4 →
          ValidCounts
            (targetHand hand
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance hand pair melds ≤
            mentsuHandTargetDistance hand otherPair otherMelds := by
  constructor
  · intro hshape
    obtain ⟨distance, pair, melds, hvalue, hmelds, hvalid,
        hdistance, _, hminimal⟩ :=
      exists_minimal_mentsuHandTarget_of_isShapeShanten_mentsuHand
        hand hbeforeValid hstanding value hshape
    have hsum :=
      sum_countsOfTiles_mentsuHandTarget_of_thirteen_tile_count
        hand hstanding pair melds hmelds
    exact ⟨distance, pair, melds, hvalue, hmelds, hsum, hvalid,
      hdistance, hminimal⟩
  · rintro ⟨distance, pair, melds, hvalue, hmelds, hsum,
      hvalid, hdistance, hminimal⟩
    have hshape :
        IsShapeShanten hand .mentsuHand ((distance : Int) - 1) :=
      isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance_one_more
        distance hand pair melds hdistance hsum hbeforeValid
        hvalid hmelds hminimal
    have hvalueEq : (distance : Int) - 1 = value := by omega
    exact hvalueEq ▸ hshape

private def canonicalMentsuHandPair : Tile :=
  .honor ⟨0, by omega⟩

private def canonicalMentsuHandMelds : Nat → List Meld
  | 0 =>
      [ .sequence .man ⟨0, by omega⟩
      , .sequence .pin ⟨0, by omega⟩
      , .sequence .sou ⟨0, by omega⟩
      , .triplet (.honor ⟨1, by omega⟩) ]
  | 1 =>
      [ .sequence .man ⟨0, by omega⟩
      , .sequence .pin ⟨0, by omega⟩
      , .sequence .sou ⟨0, by omega⟩ ]
  | 2 =>
      [ .sequence .man ⟨0, by omega⟩
      , .sequence .pin ⟨0, by omega⟩ ]
  | 3 => [ .sequence .man ⟨0, by omega⟩ ]
  | _ => []

private lemma canonicalMentsuHandMelds_length
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4) :
    (canonicalMentsuHandMelds fixedMelds).length + fixedMelds = 4 := by
  have hcases :
      fixedMelds = 0 ∨ fixedMelds = 1 ∨ fixedMelds = 2 ∨
        fixedMelds = 3 ∨ fixedMelds = 4 := by omega
  rcases hcases with h | h | h | h | h
  all_goals subst fixedMelds <;> simp [canonicalMentsuHandMelds]

private lemma canonicalMentsuHandTarget_validCounts
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4) :
    ∀ tile,
      (mentsuHandTarget canonicalMentsuHandPair
        (canonicalMentsuHandMelds fixedMelds)).count tile ≤ 4 := by
  intro tile
  have hcases :
      fixedMelds = 0 ∨ fixedMelds = 1 ∨ fixedMelds = 2 ∨
        fixedMelds = 3 ∨ fixedMelds = 4 := by omega
  rcases hcases with h | h | h | h | h
  all_goals subst fixedMelds
  all_goals
    cases tile with
    | suited suit rank =>
        cases suit <;> fin_cases rank <;>
          simp [canonicalMentsuHandPair, canonicalMentsuHandMelds,
            mentsuHandTarget, pairTiles, meldsTiles, meldTiles]
    | honor rank =>
        fin_cases rank <;>
          simp [canonicalMentsuHandPair, canonicalMentsuHandMelds,
            mentsuHandTarget, pairTiles, meldsTiles, meldTiles]

set_option maxHeartbeats 1000000 in
lemma exists_mentsuHandShanten_as_min_validTargetDistance
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) :
    ∃ distance,
      distance ∈ validMentsuHandTargetDistances hand ∧
      (∀ otherDistance,
        otherDistance ∈ validMentsuHandTargetDistances hand →
          distance ≤ otherDistance) ∧
      IsShapeShanten hand .mentsuHand ((distance : Int) - 1) := by
  have hfixed : hand.fixedMelds ≤ 4 := by omega
  have hmelds :=
    canonicalMentsuHandMelds_length hand.fixedMelds hfixed
  have hvalid :
      ValidCounts
        (targetHand hand
          (countsOfTiles
            (mentsuHandTarget canonicalMentsuHandPair
              (canonicalMentsuHandMelds hand.fixedMelds)))) := by
    intro tile
    change
      (mentsuHandTarget canonicalMentsuHandPair
        (canonicalMentsuHandMelds hand.fixedMelds)).count tile ≤ 4
    exact canonicalMentsuHandTarget_validCounts
      hand.fixedMelds hfixed tile
  obtain ⟨distance, hdistanceMem, hminimalDistance⟩ :=
    exists_min_validMentsuHandTargetDistance hand hfixed
      ⟨canonicalMentsuHandPair, canonicalMentsuHandMelds hand.fixedMelds,
        hmelds, hvalid⟩
  obtain ⟨pair, melds, htargetMelds, htargetValid, htargetDistance⟩ :=
    (mem_validMentsuHandTargetDistances_iff
      hand hfixed distance).mp hdistanceMem
  have hsum :=
    sum_countsOfTiles_mentsuHandTarget_of_thirteen_tile_count
      hand hstanding pair melds htargetMelds
  have hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + hand.fixedMelds = 4 →
          ValidCounts
            (targetHand hand
              (countsOfTiles (mentsuHandTarget otherPair otherMelds))) →
          mentsuHandTargetDistance hand pair melds ≤
            mentsuHandTargetDistance hand otherPair otherMelds := by
    intro otherPair otherMelds hotherMelds hotherValid
    have hotherDistanceMem :
        mentsuHandTargetDistance hand otherPair otherMelds ∈
          validMentsuHandTargetDistances hand :=
      (mem_validMentsuHandTargetDistances_iff
        hand hfixed
        (mentsuHandTargetDistance hand otherPair otherMelds)).mpr
        ⟨otherPair, otherMelds, hotherMelds, hotherValid, rfl⟩
    calc
      mentsuHandTargetDistance hand pair melds = distance :=
        htargetDistance
      _ ≤ mentsuHandTargetDistance hand otherPair otherMelds :=
        hminimalDistance _ hotherDistanceMem
  have hshape :
      IsShapeShanten hand .mentsuHand ((distance : Int) - 1) :=
    isShapeShanten_mentsuHand_of_minimal_mentsuHandTargetDistance_one_more
      distance hand pair melds htargetDistance hsum hbeforeValid
      htargetValid htargetMelds hminimalTarget
  exact ⟨distance, hdistanceMem, hminimalDistance, hshape⟩

lemma mentsuHandTargetMinimumSearch_eq_some_iff
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) :
    mentsuHandTargetMinimumSearch hand = some value ↔
      IsShapeShanten hand .mentsuHand value := by
  obtain ⟨distance, hmem, hminimal, hshape⟩ :=
    exists_mentsuHandShanten_as_min_validTargetDistance
      hand hbeforeValid hstanding
  let distances := validMentsuHandTargetDistances hand
  have hnonempty : distances.Nonempty := ⟨distance, hmem⟩
  have hdistance :
      distances.min' hnonempty = distance := by
    apply Nat.le_antisymm
    · exact Finset.min'_le distances distance hmem
    · exact hminimal _ (Finset.min'_mem distances hnonempty)
  have hsearch :
      mentsuHandTargetMinimumSearch hand =
        some ((distance : Int) - 1) := by
    simp [mentsuHandTargetMinimumSearch, distances, hnonempty, hdistance]
  constructor
  · intro hresult
    have hvalues :
        some ((distance : Int) - 1) = some value :=
      hsearch.symm.trans hresult
    have hvalue : (distance : Int) - 1 = value :=
      Option.some.inj hvalues
    exact hvalue ▸ hshape
  · intro hvalue
    have heq :
        ((distance : Int) - 1) = value :=
      isShapeShanten_unique hshape hvalue
    rw [hsearch, heq]

lemma mentsuHandTargetMinimumSearch_eq_some_iff_of_thirteenTileHand
    (hand : Hand) (hthirteen : IsThirteenTileHand hand) (value : Int) :
    mentsuHandTargetMinimumSearch hand = some value ↔
      IsShapeShanten hand .mentsuHand value := by
  rcases hthirteen with ⟨hfixed, hcount, hvalid⟩
  apply mentsuHandTargetMinimumSearch_eq_some_iff hand hvalid
  rw [hfixed, hcount]

lemma exists_isShapeShanten_mentsuHand_of_valid_thirteen_tile_count
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) :
    ∃ value : Int, IsShapeShanten hand .mentsuHand value := by
  obtain ⟨distance, _, _, hshape⟩ :=
    exists_mentsuHandShanten_as_min_validTargetDistance
      hand hbeforeValid hstanding
  exact ⟨(distance : Int) - 1, hshape⟩

lemma exists_isShapeShanten_mentsuHand_of_thirteenTileHand
    (hand : Hand) (hthirteen : IsThirteenTileHand hand) :
    ∃ value : Int, IsShapeShanten hand .mentsuHand value := by
  rcases hthirteen with ⟨hfixed, hcount, hvalid⟩
  apply exists_isShapeShanten_mentsuHand_of_valid_thirteen_tile_count
    hand hvalid
  rw [hfixed, hcount]

lemma exists_isOverallShanten_of_thirteenTileHand
    (hand : Hand) (hthirteen : IsThirteenTileHand hand) :
    ∃ value : Int, IsOverallShanten hand value := by
  obtain ⟨mentsuHandValue, hmentsuHand⟩ :=
    exists_isShapeShanten_mentsuHand_of_thirteenTileHand hand hthirteen
  have hmentsuHandOption :
      ShapeShanten hand .mentsuHand = some mentsuHandValue :=
    (shapeShanten_eq_some_iff).2 hmentsuHand
  unfold IsOverallShanten OverallShanten
  rw [hmentsuHandOption]
  cases hseven : ShapeShanten hand .sevenPairs <;>
    cases horphans : ShapeShanten hand .thirteenOrphans <;>
      simp [minOption, hseven, horphans]

lemma MentsuHandBlockDecomposition.exists_isShapeShanten
    {hand : Hand} (decomposition : MentsuHandBlockDecomposition hand)
    (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) :
    ∃ value : Int, IsShapeShanten hand .mentsuHand value := by
  let melds :=
    decomposition.melds ++
      taatsuCompletionMelds decomposition.taatsus
  have htarget :
      mentsuHandTarget decomposition.pair melds =
        decomposition.completedTarget := by
    rw [MentsuHandBlockDecomposition.completedTarget_eq]
    rfl
  have hmelds :
      melds.length + hand.fixedMelds = 4 := by
    dsimp [melds]
    exact decomposition.completedMeldCount
  have htargetCard :
      (mentsuHandTarget decomposition.pair melds).card =
        tileCount hand + 1 := by
    rw [htarget, MentsuHandBlockDecomposition.completedTarget_eq]
    simp [Multiset.card_add, pairTiles_card, meldsTiles_card,
      List.length_append, taatsuCompletionMelds_length]
    have hblocks := decomposition.blocks
    omega
  have hsum :
      (∑ tile : Tile,
        countsOfTiles (mentsuHandTarget decomposition.pair melds) tile) =
        (∑ tile : Tile, hand.counts tile) + 1 := by
    calc
      _ = (mentsuHandTarget decomposition.pair melds).card := by
        exact countsOfTiles_sum_eq_card
          (mentsuHandTarget decomposition.pair melds)
      _ = tileCount hand + 1 := htargetCard
      _ = (∑ tile : Tile, hand.counts tile) + 1 := by
        rfl
  have hvalid :
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuHandTarget decomposition.pair melds))) := by
    rw [htarget]
    exact decomposition.validCounts_completedTarget
  exact exists_isShapeShanten_mentsuHand_of_valid_mentsuHandTarget_one_more
    hand hbeforeValid
    ⟨decomposition.pair, melds, hmelds, hsum, hvalid⟩

lemma mentsuHandTarget_count_le_stateHistoryTiles
    (state : MentsuHandSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTarget pair state.meldHistory.reverse).count tile ≤
        (stateHistoryTiles state).count tile := by
  intro tile
  simp [mentsuHandTarget, stateHistoryTiles, pairHistoryTiles, hpair,
    Multiset.count_add]

lemma mentsuHandTarget_count_le_used
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTarget pair state.meldHistory.reverse).count tile ≤
        state.used.count tile := by
  intro tile
  rw [reachableWithin_used_eq_historyTiles hand fuel state hreachable]
  exact mentsuHandTarget_count_le_stateHistoryTiles state pair hpair tile

lemma mentsuHandTarget_count_le_hand
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuHandTarget pair state.meldHistory.reverse).count tile ≤
        hand.counts tile := by
  intro tile
  exact le_trans
    (mentsuHandTarget_count_le_used hand fuel state hreachable pair hpair tile)
    (reachableWithin_used_subset hand fuel state hreachable tile)

lemma mentsuHandTarget_hasMeldCount_of_complete
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcomplete : IsMentsuHandSearchComplete hand state) :
    HasMentsuHandMeldCount hand state.meldHistory.reverse := by
  have hlength := reachableWithin_melds_eq_history_length
    hand fuel state hreachable
  rcases hcomplete with ⟨hmelds, _⟩
  unfold HasMentsuHandMeldCount
  simpa [List.length_reverse, hlength] using hmelds

lemma mentsuHandTargetOfState_exists_of_complete
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcomplete : IsMentsuHandSearchComplete hand state) :
    ∃ target, mentsuHandTargetOfState state = some target ∧
      HasMentsuHandMeldCount hand state.meldHistory.reverse := by
  cases hpair : state.pair with
  | none =>
      exfalso
      simpa [hpair] using hcomplete.2
  | some pair =>
      refine ⟨mentsuHandTarget pair state.meldHistory.reverse, ?_, ?_⟩
      · rw [mentsuHandTargetOfState, hpair]
        rfl
      · exact mentsuHandTarget_hasMeldCount_of_complete
          hand fuel state hreachable hcomplete

lemma completedMeldsForState_hasMeldCount
    (hand : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcount : state.melds + state.taatsu + hand.fixedMelds = 4) :
    HasMentsuHandMeldCount hand (completedMeldsForState state) := by
  have hmelds := reachableWithin_melds_eq_history_length
    hand fuel state hreachable
  have htaatsu := reachableWithin_taatsu_eq_history_length
    hand fuel state hreachable
  unfold HasMentsuHandMeldCount
  rw [completedMeldsForState_length, ← hmelds, ← htaatsu]
  omega

lemma complete_mentsuHand_of_blockSearch
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state)
    (hvalid : ∀ pair, state.pair = some pair →
      ValidCounts
        (targetHand before
          (countsOfTiles (completedTargetForState state pair)))) :
    ∃ pair,
      Complete .mentsuHand
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      refine ⟨pair, ?_⟩
      apply complete_mentsuHand_completedTarget before state pair
      · exact hvalid pair hstatePair
      · exact completedMeldsForState_hasMeldCount
          before fuel state hreachable hcount

lemma complete_mentsuHand_of_blockSearch_of_copyLimit
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state)
    (hcopy : CompletionRespectsCopyLimit state) :
    ∃ pair,
      Complete .mentsuHand
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      refine ⟨pair, ?_⟩
      apply complete_mentsuHand_completedTarget before state pair
      · exact validCounts_completedTarget_of_copyLimit
          before fuel state hreachable hcopy pair hstatePair
      · exact completedMeldsForState_hasMeldCount
          before fuel state hreachable hcount

lemma complete_mentsuHand_of_constrainedBlockSearch
    (before : Hand) (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state) :
    ∃ pair,
      Complete .mentsuHand
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  exact complete_mentsuHand_of_blockSearch_of_copyLimit
    before fuel state
    (reachableWithinWithCopyLimit_to_reachableWithin
      before fuel state hreachable)
    hcomplete
    (reachableWithinWithCopyLimit_copyLimit before fuel state hreachable)

lemma exists_isShapeShanten_mentsuHand_of_constrainedBlockSearch
    (before : Hand) (hbeforeValid : ValidCounts before)
    (hstanding : tileCount before + 3 * before.fixedMelds = 13)
    (fuel : Nat) (state : MentsuHandSearchState)
    (hreachable : reachableWithinWithCopyLimit before fuel state)
    (hcomplete : IsMentsuHandBlockSearchComplete before state) :
    ∃ value : Int, IsShapeShanten before .mentsuHand value := by
  have hreachable' :
      reachableWithin before fuel state :=
    reachableWithinWithCopyLimit_to_reachableWithin
      before fuel state hreachable
  have hcopy :
      CompletionRespectsCopyLimit state :=
    reachableWithinWithCopyLimit_copyLimit before fuel state hreachable
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      let melds := completedMeldsForState state
      have hmelds :
          melds.length + before.fixedMelds = 4 := by
        dsimp [melds]
        exact completedMeldsForState_hasMeldCount
          before fuel state hreachable' hcount
      have htarget :
          mentsuHandTarget pair melds =
            completedTargetForState state pair := by
        rfl
      have hsum' :=
        completedTargetForState_sum_of_blockCount
          before fuel state hreachable' hcount pair
      have hsum :
          (∑ tile : Tile,
            countsOfTiles (mentsuHandTarget pair melds) tile) =
            (∑ tile : Tile, before.counts tile) + 1 := by
        calc
          _ = 14 - 3 * before.fixedMelds := by
            rw [htarget]
            exact hsum'
          _ = tileCount before + 1 := by
            omega
          _ = (∑ tile : Tile, before.counts tile) + 1 := by
            rfl
      have hvalid :
          ValidCounts
            (targetHand before (countsOfTiles (mentsuHandTarget pair melds))) := by
        rw [htarget]
        exact validCounts_completedTarget_of_copyLimit
          before fuel state hreachable' hcopy pair hstatePair
      exact exists_isShapeShanten_mentsuHand_of_valid_mentsuHandTarget_one_more
        before hbeforeValid
        ⟨pair, melds, hmelds, hsum, hvalid⟩

end Shanten
