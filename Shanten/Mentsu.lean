import Shanten.Specification
import Shanten.SevenPairs

namespace Shanten

inductive Taatsu
  | pair (tile : Tile)
  | sequence (suit : Suit) (start : Fin 8)
  deriving DecidableEq, Fintype

/-- The counters carried by the mentsu-hand dynamic program. -/
structure MentsuSearchState where
  tileIndex : Nat
  used : Multiset Tile
  pair : Option Tile
  meldHistory : List Meld
  taatsuHistory : List Taatsu
  melds : Nat
  taatsu : Nat
  deriving DecidableEq

/-- One branch of the mentsu-hand decomposition search. -/
inductive MentsuChoice
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

def choiceTiles : MentsuChoice → Multiset Tile
  | .skip => 0
  | .pair tile => pairTiles tile
  | .taatsu taatsu => taatsuTiles taatsu
  | .meld meld => meldTiles meld

def choiceUsesMeld : MentsuChoice → Bool
  | .meld _ => true
  | _ => false

def choiceUsesPair : MentsuChoice → Bool
  | .pair _ => true
  | _ => false

def choiceUsesTaatsu : MentsuChoice → Bool
  | .taatsu _ => true
  | _ => false

def ValidMentsuChoice
    (hand : Hand) (state : MentsuSearchState) (choice : MentsuChoice) : Prop :=
  (∀ tile, (state.used + choiceTiles choice).count tile ≤ hand.counts tile) ∧
  state.melds + (if choiceUsesMeld choice = true then 1 else 0) ≤ 4 ∧
  state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0) ≤ 4 ∧
  (state.pair.isNone ∨ choiceUsesPair choice = false)

lemma validMentsuChoice_of
    (hand : Hand) (state : MentsuSearchState) (choice : MentsuChoice)
    (hused :
      ∀ tile, (state.used + choiceTiles choice).count tile ≤ hand.counts tile)
    (hmelds :
      state.melds + (if choiceUsesMeld choice = true then 1 else 0) ≤ 4)
    (htaatsu :
      state.taatsu + (if choiceUsesTaatsu choice = true then 1 else 0) ≤ 4)
    (hpair : state.pair.isNone ∨ choiceUsesPair choice = false) :
    ValidMentsuChoice hand state choice :=
  ⟨hused, hmelds, htaatsu, hpair⟩

def applyMentsuChoice
    (hand : Hand) (state : MentsuSearchState) (choice : MentsuChoice)
    (_ : ValidMentsuChoice hand state choice) : MentsuSearchState :=
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

lemma applyMentsuChoice_used_subset
    (hand : Hand) (state : MentsuSearchState) (choice : MentsuChoice)
    (hvalid : ValidMentsuChoice hand state choice) :
    ∀ tile,
      (applyMentsuChoice hand state choice hvalid).used.count tile ≤
        hand.counts tile := by
  intro tile
  exact hvalid.1 tile

def allMentsuChoices : Finset MentsuChoice :=
  insert .skip
    (Finset.univ.image MentsuChoice.pair ∪
      Finset.univ.image MentsuChoice.meld ∪
      Finset.univ.image (fun taatsu =>
        MentsuChoice.taatsu taatsu))

lemma mentsuChoice_mem_all
    (choice : MentsuChoice) :
    choice ∈ allMentsuChoices := by
  cases choice with
  | skip =>
      simp [allMentsuChoices]
  | pair tile =>
      simp [allMentsuChoices]
  | taatsu taatsu =>
      simp [allMentsuChoices]
  | meld meld =>
      simp [allMentsuChoices]

def choicesForTile (tile : Tile) : Finset MentsuChoice :=
  allMentsuChoices.filter
    (fun choice => choice = .skip ∨ tile ∈ choiceTiles choice)

def NextMentsuState
    (hand : Hand) (state next : MentsuSearchState) : Prop :=
  ∃ choice, choice ∈ allMentsuChoices ∧
    ∃ hvalid : ValidMentsuChoice hand state choice,
      next = applyMentsuChoice hand state choice hvalid

def NextMentsuStateAt
    (hand : Hand) (tile : Tile) (state next : MentsuSearchState) : Prop :=
  ∃ choice, choice ∈ choicesForTile tile ∧
    ∃ hvalid : ValidMentsuChoice hand state choice,
      next = applyMentsuChoice hand state choice hvalid

lemma nextMentsuState_used_subset
    (hand : Hand) (state next : MentsuSearchState)
    (hnext : NextMentsuState hand state next) :
    ∀ tile, next.used.count tile ≤ hand.counts tile := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  exact applyMentsuChoice_used_subset hand state choice hvalid

lemma nextMentsuState_tileIndex
    (hand : Hand) (state next : MentsuSearchState)
    (hnext : NextMentsuState hand state next) :
    state.tileIndex < next.tileIndex := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  simp [applyMentsuChoice]

lemma nextMentsuStateAt_used_subset
    (hand : Hand) (tile : Tile) (state next : MentsuSearchState)
    (hnext : NextMentsuStateAt hand tile state next) :
    ∀ tile', next.used.count tile' ≤ hand.counts tile' := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  exact applyMentsuChoice_used_subset hand state choice hvalid

lemma nextMentsuStateAt_tileIndex
    (hand : Hand) (tile : Tile) (state next : MentsuSearchState)
    (hnext : NextMentsuStateAt hand tile state next) :
    state.tileIndex < next.tileIndex := by
  rcases hnext with ⟨choice, _, hvalid, rfl⟩
  simp [applyMentsuChoice]

def initialMentsuState : MentsuSearchState :=
  { tileIndex := 0
    used := 0
    pair := none
    meldHistory := []
    taatsuHistory := []
    melds := 0
    taatsu := 0 }

/-- States reachable after exactly `fuel` decomposition choices. -/
def reachableWithin
    (hand : Hand) : Nat → MentsuSearchState → Prop
  | 0, state => state = initialMentsuState
  | fuel + 1, state =>
      ∃ previous,
        reachableWithin hand fuel previous ∧
          NextMentsuState hand previous state

def IsMentsuSearchComplete
    (hand : Hand) (state : MentsuSearchState) : Prop :=
  state.melds + hand.fixedMelds = 4 ∧ state.pair.isSome

/-- A DP state containing four meld-or-taatsu blocks and one pair. -/
def IsMentsuBlockSearchComplete
    (hand : Hand) (state : MentsuSearchState) : Prop :=
  state.melds + state.taatsu + hand.fixedMelds = 4 ∧ state.pair.isSome

/-- The DP query: a complete mentsu decomposition is reachable in `fuel` choices. -/
def MentsuSearch
    (hand : Hand) (fuel : Nat) : Prop :=
  ∃ state, reachableWithin hand fuel state ∧
    IsMentsuSearchComplete hand state

/-- The DP query using the four-block criterion. -/
def MentsuBlockSearch
    (hand : Hand) (fuel : Nat) : Prop :=
  ∃ state, reachableWithin hand fuel state ∧
    IsMentsuBlockSearchComplete hand state

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

def completedMeldsForState (state : MentsuSearchState) : List Meld :=
  state.meldHistory.reverse ++
    taatsuCompletionMelds state.taatsuHistory.reverse

lemma completedMeldsForState_length
    (state : MentsuSearchState) :
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

def stateHistoryTiles (state : MentsuSearchState) : Multiset Tile :=
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

lemma applyMentsuChoice_used_eq_historyTiles
    (hand : Hand) (state : MentsuSearchState) (choice : MentsuChoice)
    (hvalid : ValidMentsuChoice hand state choice)
    (hstate : state.used = stateHistoryTiles state) :
    (applyMentsuChoice hand state choice hvalid).used =
      stateHistoryTiles (applyMentsuChoice hand state choice hvalid) := by
  cases choice with
  | skip =>
      simpa [applyMentsuChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles] using hstate
  | pair tile =>
      have hpair : state.pair.isNone := by
        simpa [choiceUsesPair] using hvalid.2.2.2
      cases hstatePair : state.pair with
      | none =>
          simp only [applyMentsuChoice]
          change state.used + pairTiles tile = _
          rw [hstate]
          simp [applyMentsuChoice, stateHistoryTiles, pairHistoryTiles,
            taatsuHistoryTiles, choiceTiles, hstatePair]
          ac_rfl
      | some oldPair =>
          simp [hstatePair] at hpair
  | taatsu taatsu =>
      simp only [applyMentsuChoice]
      change state.used + taatsuTiles taatsu = _
      rw [hstate]
      simp [applyMentsuChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles, List.reverse_cons,
        taatsuHistoryTiles_append_single]
      ac_rfl
  | meld meld =>
      simp only [applyMentsuChoice]
      change state.used + meldTiles meld = _
      rw [hstate]
      simp [applyMentsuChoice, stateHistoryTiles, pairHistoryTiles,
        taatsuHistoryTiles, choiceTiles, List.reverse_cons,
        meldsTiles_append_single]
      ac_rfl

lemma reachableWithin_used_eq_historyTiles
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.used = stateHistoryTiles state := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyMentsuChoice_used_eq_historyTiles
        hand previous choice hvalid (ih previous hprevious)

lemma applyMentsuChoice_melds_eq_history_length
    (hand : Hand) (state : MentsuSearchState) (choice : MentsuChoice)
    (hvalid : ValidMentsuChoice hand state choice)
    (hstate : state.melds = state.meldHistory.length) :
    (applyMentsuChoice hand state choice hvalid).melds =
      (applyMentsuChoice hand state choice hvalid).meldHistory.length := by
  cases choice <;> simp [applyMentsuChoice, hstate, choiceUsesMeld]

lemma reachableWithin_melds_eq_history_length
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.melds = state.meldHistory.length := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyMentsuChoice_melds_eq_history_length
        hand previous choice hvalid (ih previous hprevious)

lemma applyMentsuChoice_taatsu_eq_history_length
    (hand : Hand) (state : MentsuSearchState) (choice : MentsuChoice)
    (hvalid : ValidMentsuChoice hand state choice)
    (hstate : state.taatsu = state.taatsuHistory.length) :
    (applyMentsuChoice hand state choice hvalid).taatsu =
      (applyMentsuChoice hand state choice hvalid).taatsuHistory.length := by
  cases choice <;> simp [applyMentsuChoice, hstate, choiceUsesTaatsu]

lemma reachableWithin_taatsu_eq_history_length
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin hand fuel state) :
    state.taatsu = state.taatsuHistory.length := by
  induction fuel generalizing state with
  | zero =>
      subst state
      rfl
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, rfl⟩
      exact applyMentsuChoice_taatsu_eq_history_length
        hand previous choice hvalid (ih previous hprevious)

/-- States reached from a given state while processing tile kinds in order. -/
def reachableOnTilesFrom
    (hand : Hand) : List Tile → MentsuSearchState →
      MentsuSearchState → Prop
  | [], start, state => state = start
  | tile :: tiles, start, state =>
      ∃ middle,
        NextMentsuStateAt hand tile start middle ∧
          reachableOnTilesFrom hand tiles middle state

/-- States reached while processing a prescribed sequence of tile kinds. -/
def reachableOnTiles
    (hand : Hand) (tiles : List Tile) (state : MentsuSearchState) : Prop :=
  reachableOnTilesFrom hand tiles initialMentsuState state

def MentsuSearchOnTiles
    (hand : Hand) (tiles : List Tile) : Prop :=
  ∃ state, reachableOnTiles hand tiles state ∧
    IsMentsuSearchComplete hand state

def MentsuBlockSearchOnTiles
    (hand : Hand) (tiles : List Tile) : Prop :=
  ∃ state, reachableOnTiles hand tiles state ∧
    IsMentsuBlockSearchComplete hand state

lemma reachableWithin_zero_iff
    (hand : Hand) (state : MentsuSearchState) :
    reachableWithin hand 0 state ↔ state = initialMentsuState := by
  rfl

lemma reachableWithin_succ_iff
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState) :
    reachableWithin hand (fuel + 1) state ↔
      ∃ previous,
        reachableWithin hand fuel previous ∧
          NextMentsuState hand previous state := by
  rfl

lemma reachableWithin_used_subset
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin hand fuel state) :
    ∀ tile, state.used.count tile ≤ hand.counts tile := by
  induction fuel generalizing state with
  | zero =>
      intro tile
      subst state
      simp [initialMentsuState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      intro tile
      exact nextMentsuState_used_subset hand previous state hnext tile

lemma mentsuSearch_complete_iff
    (hand : Hand) (fuel : Nat) :
    MentsuSearch hand fuel ↔
      ∃ state, reachableWithin hand fuel state ∧
        state.melds + hand.fixedMelds = 4 ∧
        state.pair.isSome := by
  rfl

lemma mentsuBlockSearch_complete_iff
    (hand : Hand) (fuel : Nat) :
    MentsuBlockSearch hand fuel ↔
        ∃ state, reachableWithin hand fuel state ∧
          state.melds + state.taatsu + hand.fixedMelds = 4 ∧
          state.pair.isSome := by
  rfl

def mentsuTileAt (index : Fin 34) : Tile :=
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

def mentsuTileOrder : List Tile :=
  (List.finRange 34).map mentsuTileAt

def MentsuSearchOnTileOrder (hand : Hand) : Prop :=
  MentsuSearchOnTiles hand mentsuTileOrder

lemma mentsuTileOrder_length :
    mentsuTileOrder.length = 34 := by
  simp [mentsuTileOrder]

lemma tile_mem_mentsuTileOrder :
    ∀ tile : Tile, tile ∈ mentsuTileOrder := by
  native_decide

/-- A mentsu-form target before the fixed melds are added. -/
def mentsuTarget (pair : Tile) (melds : List Meld) : Multiset Tile :=
  pairTiles pair + meldsTiles melds

def mentsuTargetWithTaatsu
    (pair : Tile) (melds : List Meld) (taatsus : List Taatsu) : Multiset Tile :=
  mentsuTarget pair melds + taatsuHistoryTiles taatsus

lemma completedMeldsForState_tiles
    (state : MentsuSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    pairTiles pair + meldsTiles (completedMeldsForState state) =
      mentsuTargetWithTaatsu pair state.meldHistory.reverse
          state.taatsuHistory.reverse +
        taatsuCompletionTiles state.taatsuHistory.reverse := by
  simp only [completedMeldsForState, mentsuTargetWithTaatsu, mentsuTarget]
  rw [meldsTiles_append]
  rw [← taatsuHistoryTiles_add_completionTiles]
  ac_rfl

def mentsuTargetWithTaatsuOfState
    (state : MentsuSearchState) : Option (Multiset Tile) :=
  state.pair.map fun pair =>
    mentsuTargetWithTaatsu pair state.meldHistory.reverse
      state.taatsuHistory.reverse

lemma mentsuTargetWithTaatsuOfState_eq_some_iff
    (state : MentsuSearchState) (target : Multiset Tile) :
    mentsuTargetWithTaatsuOfState state = some target ↔
      ∃ pair, state.pair = some pair ∧
        target = mentsuTargetWithTaatsu pair state.meldHistory.reverse
          state.taatsuHistory.reverse := by
  constructor
  · intro htarget
    cases hpair : state.pair with
    | none =>
        simp [mentsuTargetWithTaatsuOfState, hpair] at htarget
    | some pair =>
        refine ⟨pair, rfl, ?_⟩
        simpa [mentsuTargetWithTaatsuOfState, hpair] using htarget.symm
  · rintro ⟨pair, hpair, rfl⟩
    rw [mentsuTargetWithTaatsuOfState, hpair]
    rfl

lemma mentsuTargetWithTaatsuOfState_eq_stateHistoryTiles
    (state : MentsuSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    mentsuTargetWithTaatsu pair state.meldHistory.reverse
        state.taatsuHistory.reverse =
      stateHistoryTiles state := by
  simp [mentsuTargetWithTaatsu, mentsuTarget, stateHistoryTiles,
    pairHistoryTiles, hpair, Multiset.add_assoc]

lemma mentsuTargetWithTaatsu_count_le_hand
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuTargetWithTaatsu pair state.meldHistory.reverse
        state.taatsuHistory.reverse).count tile ≤ hand.counts tile := by
  intro tile
  rw [mentsuTargetWithTaatsuOfState_eq_stateHistoryTiles state pair hpair]
  rw [← reachableWithin_used_eq_historyTiles hand fuel state hreachable]
  exact reachableWithin_used_subset hand fuel state hreachable tile

lemma mentsuTargetExchange_handStep
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
    (mentsuTargetExchange_handStep target before discarded drawn
      hdrawn hdiscarded hne)
  exact hrest

lemma exchangeHand_fixedMelds
    (before : Hand) (discarded drawn : Tile) :
    (exchangeHand before discarded drawn).fixedMelds = before.fixedMelds := by
  rfl

def mentsuTargetOfState
    (state : MentsuSearchState) : Option (Multiset Tile) :=
  state.pair.map fun pair =>
    mentsuTarget pair state.meldHistory.reverse

lemma mentsuTargetOfState_eq_some_iff
    (state : MentsuSearchState) (target : Multiset Tile) :
    mentsuTargetOfState state = some target ↔
      ∃ pair, state.pair = some pair ∧
        target = mentsuTarget pair state.meldHistory.reverse := by
  constructor
  · intro htarget
    cases hpair : state.pair with
    | none =>
        simp [mentsuTargetOfState, hpair] at htarget
    | some pair =>
        refine ⟨pair, rfl, ?_⟩
        simpa [mentsuTargetOfState, hpair] using htarget.symm
  · rintro ⟨pair, hpair, rfl⟩
    rw [mentsuTargetOfState, hpair]
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

lemma exists_complete_mentsu_with_deficit_le
    (before : Hand) (distance : Nat)
    (hreach : ReachesCompletion Complete .mentsu before distance) :
    ∃ after,
      Complete .mentsu after ∧
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
        · exact mentsuTargetExchange_handStep target current discarded drawn
            hdrawn hdiscarded hneTiles
        · simpa [next, targetHand, exchangeHand] using hrest
  exact aux (countDeficit before.counts target) before hsum rfl

lemma complete_mentsu_targetHand
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List Meld)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds)) :
    Complete .mentsu (targetHand before target) := by
  exact ⟨hvalid, pair, melds, hmelds, htiles⟩

lemma reachesCompletion_mentsu_of_equal_sum
    (before : Hand) (target : TileCounts)
    (pair : Tile) (melds : List Meld)
    (hsum : (∑ tile : Tile, before.counts tile) =
      ∑ tile : Tile, target tile)
    (hvalid : ValidCounts (targetHand before target))
    (hmelds : melds.length + before.fixedMelds = 4)
    (htiles :
      HasTiles (targetHand before target)
        (pairTiles pair + meldsTiles melds)) :
    ReachesCompletion Complete .mentsu before
      (countDeficit before.counts target) := by
  obtain ⟨distance, hdistance, hexchange⟩ :=
    reachesExchange_targetHand_of_equal_sum before target hsum
  have hcomplete :
      Complete .mentsu (targetHand before target) :=
    complete_mentsu_targetHand before target pair melds
      hvalid hmelds htiles
  have hdone :
      ReachesCompletion Complete .mentsu
        (targetHand before target) 0 :=
    ReachesCompletion.done hcomplete
  simpa only [Nat.add_zero, hdistance] using
    ReachesExchange.toReachesCompletion hexchange hdone

lemma reachesCompletion_mentsu_of_one_more_target_tile
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
      ReachesCompletion Complete .mentsu before distance := by
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
      Complete .mentsu (targetHand next target) :=
    complete_mentsu_targetHand next target pair melds
      hvalidNext hmeldsNext htilesNext
  have hdone :
      ReachesCompletion Complete .mentsu
        (targetHand next target) 0 :=
    ReachesCompletion.done hcomplete
  obtain ⟨distance, hdistance, hexchange⟩ :=
    reachesExchange_targetHand_of_equal_sum next target hsumNext
  have hrest :
      ReachesCompletion Complete .mentsu next distance := by
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
def HasMentsuMeldCount (hand : Hand) (melds : List Meld) : Prop :=
  melds.length + hand.fixedMelds = 4

/-- A mentsu-form decomposition before completing its taatsu blocks. -/
structure MentsuBlockDecomposition (hand : Hand) where
  pair : Tile
  melds : List Meld
  taatsus : List Taatsu
  blocks : melds.length + taatsus.length + hand.fixedMelds = 4
  targetWithinHand :
    ∀ tile,
      (mentsuTargetWithTaatsu pair melds taatsus).count tile ≤ hand.counts tile
  completionCopyLimit :
    ∀ tile,
      (mentsuTargetWithTaatsu pair melds taatsus +
        taatsuCompletionTiles taatsus).count tile ≤ 4

def mentsuChoiceTiles : List MentsuChoice → Multiset Tile
  | [] => 0
  | choice :: choices =>
      choiceTiles choice + mentsuChoiceTiles choices

lemma mentsuChoiceTiles_append
    (left right : List MentsuChoice) :
    mentsuChoiceTiles (left ++ right) =
      mentsuChoiceTiles left + mentsuChoiceTiles right := by
  induction left with
  | nil =>
      simp [mentsuChoiceTiles]
  | cons choice left ih =>
      simp [mentsuChoiceTiles, ih, Multiset.add_assoc]

def MentsuBlockDecomposition.blockChoices
    {hand : Hand} (decomposition : MentsuBlockDecomposition hand) :
    List MentsuChoice :=
  .pair decomposition.pair ::
    decomposition.melds.map MentsuChoice.meld ++
      decomposition.taatsus.map MentsuChoice.taatsu

lemma MentsuBlockDecomposition.blockChoices_length
    {hand : Hand} (decomposition : MentsuBlockDecomposition hand) :
    decomposition.blockChoices.length =
      1 + decomposition.melds.length + decomposition.taatsus.length := by
  simp [MentsuBlockDecomposition.blockChoices]
  omega

lemma MentsuBlockDecomposition.blockChoices_mem_all
    {hand : Hand} (decomposition : MentsuBlockDecomposition hand) :
    ∀ choice, choice ∈ decomposition.blockChoices →
      choice ∈ allMentsuChoices := by
  intro choice hchoice
  unfold MentsuBlockDecomposition.blockChoices at hchoice
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hchoice
  rcases hchoice with (hpair | hmeld) | htaatsu
  · rw [hpair]
    exact mentsuChoice_mem_all _
  · rcases hmeld with ⟨meld, _, hmeld⟩
    rw [← hmeld]
    exact mentsuChoice_mem_all _
  · rcases htaatsu with ⟨taatsu, _, htaatsu⟩
    rw [← htaatsu]
    exact mentsuChoice_mem_all _

lemma mentsuChoiceTiles_map_meld
    (melds : List Meld) :
    mentsuChoiceTiles (melds.map MentsuChoice.meld) =
      meldsTiles melds := by
  induction melds with
  | nil =>
      rfl
  | cons meld melds ih =>
      simp [mentsuChoiceTiles, choiceTiles, meldsTiles, ih]

lemma mentsuChoiceTiles_map_taatsu
    (taatsus : List Taatsu) :
    mentsuChoiceTiles (taatsus.map MentsuChoice.taatsu) =
      taatsuHistoryTiles taatsus := by
  induction taatsus with
  | nil =>
      rfl
  | cons taatsu taatsus ih =>
      simp [mentsuChoiceTiles, choiceTiles, taatsuHistoryTiles, ih]

lemma MentsuBlockDecomposition.blockChoices_tiles
    {hand : Hand} (decomposition : MentsuBlockDecomposition hand) :
    mentsuChoiceTiles decomposition.blockChoices =
      mentsuTargetWithTaatsu decomposition.pair decomposition.melds
        decomposition.taatsus := by
  unfold MentsuBlockDecomposition.blockChoices
  simp [mentsuChoiceTiles, choiceTiles, List.map_append,
    mentsuChoiceTiles_append,
    mentsuChoiceTiles_map_meld, mentsuChoiceTiles_map_taatsu,
    mentsuTargetWithTaatsu, mentsuTarget]
  ac_rfl

lemma mentsuChoiceTiles_prefix_count_le
    (pre suffix : List MentsuChoice) (tile : Tile) :
    (mentsuChoiceTiles pre).count tile ≤
      (mentsuChoiceTiles (pre ++ suffix)).count tile := by
  rw [mentsuChoiceTiles_append]
  simp only [Multiset.count_add]
  omega

lemma MentsuBlockDecomposition.prefix_count_le_hand
    {hand : Hand} (decomposition : MentsuBlockDecomposition hand)
    (pre suffix : List MentsuChoice)
    (hchoices : decomposition.blockChoices = pre ++ suffix) :
    ∀ tile, (mentsuChoiceTiles pre).count tile ≤ hand.counts tile := by
  intro tile
  have hprefix :
      (mentsuChoiceTiles pre).count tile ≤
        (mentsuChoiceTiles decomposition.blockChoices).count tile := by
    rw [hchoices]
    exact mentsuChoiceTiles_prefix_count_le pre suffix tile
  have htarget :
      (mentsuChoiceTiles decomposition.blockChoices).count tile ≤
        hand.counts tile := by
    rw [decomposition.blockChoices_tiles]
    exact decomposition.targetWithinHand tile
  exact hprefix.trans htarget

lemma MentsuBlockDecomposition.prefix_completion_count_le_four
    {hand : Hand} (decomposition : MentsuBlockDecomposition hand)
    (pre suffix : List MentsuChoice)
    (hchoices : decomposition.blockChoices = pre ++ suffix) :
    ∀ tile,
        (mentsuChoiceTiles pre +
        taatsuCompletionTiles decomposition.taatsus).count tile ≤ 4 := by
  intro tile
  have hprefix :
        (mentsuChoiceTiles pre).count tile ≤
        (mentsuChoiceTiles decomposition.blockChoices).count tile := by
    rw [hchoices]
    exact mentsuChoiceTiles_prefix_count_le pre suffix tile
  have hfull :
      (mentsuChoiceTiles decomposition.blockChoices +
        taatsuCompletionTiles decomposition.taatsus).count tile ≤ 4 := by
    rw [decomposition.blockChoices_tiles]
    exact decomposition.completionCopyLimit tile
  rw [Multiset.count_add] at hfull ⊢
  omega

def MentsuBlockDecomposition.completedTarget
    {hand : Hand} (decomposition : MentsuBlockDecomposition hand) :
    Multiset Tile :=
  mentsuTargetWithTaatsu decomposition.pair decomposition.melds
      decomposition.taatsus +
    taatsuCompletionTiles decomposition.taatsus

lemma MentsuBlockDecomposition.completedTarget_eq
    {hand : Hand} (decomposition : MentsuBlockDecomposition hand) :
    decomposition.completedTarget =
      pairTiles decomposition.pair +
        meldsTiles
          (decomposition.melds ++
            taatsuCompletionMelds decomposition.taatsus) := by
  unfold MentsuBlockDecomposition.completedTarget
    mentsuTargetWithTaatsu mentsuTarget
  rw [meldsTiles_append]
  rw [← taatsuHistoryTiles_add_completionTiles]
  ac_rfl

lemma MentsuBlockDecomposition.validCounts_completedTarget
    {hand : Hand} (decomposition : MentsuBlockDecomposition hand) :
    ValidCounts
      (targetHand hand (countsOfTiles decomposition.completedTarget)) := by
  intro tile
  exact decomposition.completionCopyLimit tile

lemma MentsuBlockDecomposition.completedMeldCount
    {hand : Hand} (decomposition : MentsuBlockDecomposition hand) :
    (decomposition.melds ++
      taatsuCompletionMelds decomposition.taatsus).length +
        hand.fixedMelds = 4 := by
  rw [List.length_append, taatsuCompletionMelds_length]
  have hblocks := decomposition.blocks
  omega

def completedTargetForState (state : MentsuSearchState) (pair : Tile) :
    Multiset Tile :=
  pairTiles pair + meldsTiles (completedMeldsForState state)

def CompletionRespectsCopyLimit (state : MentsuSearchState) : Prop :=
  ∀ tile,
    (state.used + taatsuCompletionTiles state.taatsuHistory.reverse).count tile ≤ 4

def ValidMentsuChoiceWithCopyLimit
    (hand : Hand) (state : MentsuSearchState) (choice : MentsuChoice) : Prop :=
  ∃ hvalid : ValidMentsuChoice hand state choice,
    CompletionRespectsCopyLimit
      (applyMentsuChoice hand state choice hvalid)

lemma validMentsuChoiceWithCopyLimit_of
    (hand : Hand) (state : MentsuSearchState) (choice : MentsuChoice)
    (hvalid : ValidMentsuChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuChoice hand state choice hvalid)) :
    ValidMentsuChoiceWithCopyLimit hand state choice :=
  ⟨hvalid, hcopy⟩

def NextMentsuStateWithCopyLimit
    (hand : Hand) (state next : MentsuSearchState) : Prop :=
  ∃ choice, choice ∈ allMentsuChoices ∧
    ∃ hvalid : ValidMentsuChoice hand state choice,
      CompletionRespectsCopyLimit
        (applyMentsuChoice hand state choice hvalid) ∧
      next = applyMentsuChoice hand state choice hvalid

lemma nextMentsuStateWithCopyLimit_of_choice
    (hand : Hand) (state : MentsuSearchState) (choice : MentsuChoice)
    (hchoice : choice ∈ allMentsuChoices)
    (hvalid : ValidMentsuChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuChoice hand state choice hvalid)) :
    NextMentsuStateWithCopyLimit hand state
      (applyMentsuChoice hand state choice hvalid) :=
  ⟨choice, hchoice, hvalid, hcopy, rfl⟩

noncomputable def copyLimitChoices
    (hand : Hand) (state : MentsuSearchState) : Finset MentsuChoice :=
  by
    classical
    exact allMentsuChoices.filter
      (fun choice =>
        ∃ hvalid : ValidMentsuChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuChoice hand state choice hvalid))

lemma mem_copyLimitChoices_iff
    (hand : Hand) (state : MentsuSearchState) (choice : MentsuChoice) :
    choice ∈ copyLimitChoices hand state ↔
      choice ∈ allMentsuChoices ∧
        ∃ hvalid : ValidMentsuChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuChoice hand state choice hvalid) := by
  classical
  change choice ∈ allMentsuChoices.filter _ ↔ _
  rw [Finset.mem_filter]

lemma nextMentsuStateWithCopyLimit_iff
    (hand : Hand) (state next : MentsuSearchState) :
    NextMentsuStateWithCopyLimit hand state next ↔
      ∃ choice, choice ∈ copyLimitChoices hand state ∧
        ∃ hvalid : ValidMentsuChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuChoice hand state choice hvalid) ∧
          next = applyMentsuChoice hand state choice hvalid := by
  classical
  constructor
  · rintro ⟨choice, hchoice, hvalid, hcopy, rfl⟩
    refine ⟨choice, ?_, hvalid, hcopy, rfl⟩
    change choice ∈ allMentsuChoices.filter _
    exact Finset.mem_filter.mpr ⟨hchoice, ⟨hvalid, hcopy⟩⟩
  · rintro ⟨choice, hchoice, hvalid, hcopy, rfl⟩
    change choice ∈ allMentsuChoices.filter _ at hchoice
    exact ⟨choice, (Finset.mem_filter.mp hchoice).1,
      hvalid, hcopy, rfl⟩

noncomputable def choicesForTileWithCopyLimit
    (hand : Hand) (state : MentsuSearchState) (tile : Tile) :
    Finset MentsuChoice :=
  by
    classical
    exact (choicesForTile tile).filter
      (fun choice =>
        ∃ hvalid : ValidMentsuChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuChoice hand state choice hvalid))

lemma mem_choicesForTileWithCopyLimit_iff
    (hand : Hand) (state : MentsuSearchState) (tile : Tile)
    (choice : MentsuChoice) :
    choice ∈ choicesForTileWithCopyLimit hand state tile ↔
      choice ∈ choicesForTile tile ∧
        ∃ hvalid : ValidMentsuChoice hand state choice,
          CompletionRespectsCopyLimit
            (applyMentsuChoice hand state choice hvalid) := by
  classical
  change choice ∈ (choicesForTile tile).filter _ ↔ _
  rw [Finset.mem_filter]

def NextMentsuStateAtWithCopyLimit
    (hand : Hand) (tile : Tile) (state next : MentsuSearchState) : Prop :=
  ∃ choice, choice ∈ choicesForTileWithCopyLimit hand state tile ∧
    ∃ hvalid : ValidMentsuChoice hand state choice,
      CompletionRespectsCopyLimit
        (applyMentsuChoice hand state choice hvalid) ∧
      next = applyMentsuChoice hand state choice hvalid

lemma nextMentsuStateAtWithCopyLimit_of_choice
    (hand : Hand) (tile : Tile) (state : MentsuSearchState)
    (choice : MentsuChoice)
    (hchoice : choice ∈ allMentsuChoices)
    (htile : tile ∈ choiceTiles choice)
    (hvalid : ValidMentsuChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuChoice hand state choice hvalid)) :
    NextMentsuStateAtWithCopyLimit hand tile state
      (applyMentsuChoice hand state choice hvalid) := by
  refine ⟨choice, ?_, hvalid, hcopy, rfl⟩
  apply (mem_choicesForTileWithCopyLimit_iff hand state tile choice).mpr
  exact ⟨Finset.mem_filter.mpr ⟨hchoice, Or.inr htile⟩,
    ⟨hvalid, hcopy⟩⟩

lemma nextMentsuStateAtWithCopyLimit_skip
    (hand : Hand) (tile : Tile) (state : MentsuSearchState)
    (hused : ∀ tile, state.used.count tile ≤ hand.counts tile)
    (hcopy : CompletionRespectsCopyLimit state)
    (hmelds : state.melds ≤ 4)
    (htaatsu : state.taatsu ≤ 4) :
    NextMentsuStateAtWithCopyLimit hand tile state
      (applyMentsuChoice hand state .skip
        (by
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [choiceTiles] using hused
          · simpa [choiceUsesMeld] using hmelds
          · simpa [choiceUsesTaatsu] using htaatsu
          · simp [choiceUsesPair])) := by
  let hvalid : ValidMentsuChoice hand state .skip := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [choiceTiles] using hused
    · simpa [choiceUsesMeld] using hmelds
    · simpa [choiceUsesTaatsu] using htaatsu
    · simp [choiceUsesPair]
  refine ⟨.skip, ?_, hvalid, ?_, rfl⟩
  apply (mem_choicesForTileWithCopyLimit_iff hand state tile .skip).mpr
  · exact ⟨by simp [choicesForTile, allMentsuChoices],
      ⟨hvalid, by
        simpa [CompletionRespectsCopyLimit, applyMentsuChoice,
          choiceTiles] using hcopy⟩⟩
  · simpa [CompletionRespectsCopyLimit, applyMentsuChoice,
      choiceTiles] using hcopy

lemma nextMentsuStateAtWithCopyLimit_toNext
    (hand : Hand) (tile : Tile) (state next : MentsuSearchState)
    (hnext : NextMentsuStateAtWithCopyLimit hand tile state next) :
    NextMentsuStateAt hand tile state next := by
  rcases hnext with ⟨choice, hchoice, hvalid, hcopy, rfl⟩
  exact ⟨choice, (mem_choicesForTileWithCopyLimit_iff
    hand state tile choice).mp hchoice |>.1, hvalid, rfl⟩

lemma nextMentsuStateAtWithCopyLimit_copyLimit
    (hand : Hand) (tile : Tile) (state next : MentsuSearchState)
    (hnext : NextMentsuStateAtWithCopyLimit hand tile state next) :
    CompletionRespectsCopyLimit next := by
  rcases hnext with ⟨choice, hchoice, hvalid, hcopy, rfl⟩
  exact hcopy

lemma nextMentsuStateAtWithCopyLimit_toNextWithCopyLimit
    (hand : Hand) (tile : Tile) (state next : MentsuSearchState)
    (hnext : NextMentsuStateAtWithCopyLimit hand tile state next) :
    NextMentsuStateWithCopyLimit hand state next := by
  classical
  rcases hnext with ⟨choice, hchoice, hvalid, hcopy, rfl⟩
  change choice ∈ (choicesForTile tile).filter _ at hchoice
  have hchoiceAll : choice ∈ allMentsuChoices :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hchoice).1).1
  exact ⟨choice, hchoiceAll, hvalid, hcopy, rfl⟩

def reachableOnTilesFromWithCopyLimit
    (hand : Hand) : List Tile → MentsuSearchState →
      MentsuSearchState → Prop
  | [], start, state => state = start
  | tile :: tiles, start, state =>
      ∃ middle,
        NextMentsuStateAtWithCopyLimit hand tile start middle ∧
          reachableOnTilesFromWithCopyLimit hand tiles middle state

def reachableOnTilesWithCopyLimit
    (hand : Hand) (tiles : List Tile) (state : MentsuSearchState) : Prop :=
  reachableOnTilesFromWithCopyLimit hand tiles initialMentsuState state

def MentsuBlockSearchOnTilesWithCopyLimit
    (hand : Hand) (tiles : List Tile) : Prop :=
  ∃ state, reachableOnTilesWithCopyLimit hand tiles state ∧
    IsMentsuBlockSearchComplete hand state

def MentsuBlockSearchOnTileOrderWithCopyLimit (hand : Hand) : Prop :=
  MentsuBlockSearchOnTilesWithCopyLimit hand mentsuTileOrder

lemma reachableOnTilesFromWithCopyLimit_to_reachableOnTilesFrom
    (hand : Hand) (tiles : List Tile) (start state : MentsuSearchState)
    (hreachable : reachableOnTilesFromWithCopyLimit
      hand tiles start state) :
    reachableOnTilesFrom hand tiles start state := by
  induction tiles generalizing start state with
  | nil =>
      exact hreachable
  | cons tile tiles ih =>
      rcases hreachable with ⟨middle, hnext, hrest⟩
      exact ⟨middle, nextMentsuStateAtWithCopyLimit_toNext
        hand tile start middle hnext, ih middle state hrest⟩

lemma mentsuBlockSearchOnTilesWithCopyLimit_to_mentsuBlockSearchOnTiles
    (hand : Hand) (tiles : List Tile)
    (hsearch : MentsuBlockSearchOnTilesWithCopyLimit hand tiles) :
    MentsuBlockSearchOnTiles hand tiles := by
  rcases hsearch with ⟨state, hreachable, hcomplete⟩
  exact ⟨state,
    reachableOnTilesFromWithCopyLimit_to_reachableOnTilesFrom
      hand tiles initialMentsuState state hreachable, hcomplete⟩

lemma reachableOnTilesWithCopyLimit_copyLimit
    (hand : Hand) (tiles : List Tile) (state : MentsuSearchState)
    (hreachable : reachableOnTilesWithCopyLimit hand tiles state) :
    CompletionRespectsCopyLimit state := by
  have hinitial : CompletionRespectsCopyLimit initialMentsuState := by
    intro tile
    simp [CompletionRespectsCopyLimit, initialMentsuState,
      taatsuCompletionTiles]
  have aux :
      ∀ (tiles : List Tile) (start state : MentsuSearchState),
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
          (nextMentsuStateAtWithCopyLimit_copyLimit
            hand tile start middle hnext) hrest
  exact aux tiles initialMentsuState state hinitial hreachable

lemma nextMentsuStateWithCopyLimit_copyLimit
    (hand : Hand) (state next : MentsuSearchState)
    (hnext : NextMentsuStateWithCopyLimit hand state next) :
    CompletionRespectsCopyLimit next := by
  rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
  exact hcopy

def reachableWithinWithCopyLimit
    (hand : Hand) : Nat → MentsuSearchState → Prop
  | 0, state => state = initialMentsuState
  | fuel + 1, state =>
      ∃ previous,
        reachableWithinWithCopyLimit hand fuel previous ∧
        NextMentsuStateWithCopyLimit hand previous state

lemma initialMentsuState_copyLimit :
    CompletionRespectsCopyLimit initialMentsuState := by
  intro tile
  simp [CompletionRespectsCopyLimit, initialMentsuState,
    taatsuCompletionTiles]

lemma reachableWithinWithCopyLimit_copyLimit
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    CompletionRespectsCopyLimit state := by
  induction fuel generalizing state with
  | zero =>
      rw [hreachable]
      exact initialMentsuState_copyLimit
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      exact nextMentsuStateWithCopyLimit_copyLimit hand previous state hnext

lemma reachableWithinWithCopyLimit_melds_le_four
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    state.melds ≤ 4 := by
  induction fuel generalizing state with
  | zero =>
      subst state
      simp [initialMentsuState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
      have hbound := hvalid.2.1
      simp only [applyMentsuChoice] at hbound ⊢
      omega

lemma reachableWithinWithCopyLimit_used_subset
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    ∀ tile, state.used.count tile ≤ hand.counts tile := by
  induction fuel generalizing state with
  | zero =>
      intro tile
      subst state
      simp [initialMentsuState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      intro tile
      rcases hnext with ⟨choice, _, hvalid, _, rfl⟩
      exact hvalid.1 tile

lemma reachableWithinWithCopyLimit_taatsu_le_four
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    state.taatsu ≤ 4 := by
  induction fuel generalizing state with
  | zero =>
      subst state
      simp [initialMentsuState]
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rcases hnext with ⟨choice, _, hvalid, hcopy, rfl⟩
      have hbound := hvalid.2.2.1
      simp only [applyMentsuChoice] at hbound ⊢
      omega

lemma nextMentsuStateAtWithCopyLimit_skip_of_reachable
    (hand : Hand) (tile : Tile) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    NextMentsuStateAtWithCopyLimit hand tile state
      (applyMentsuChoice hand state .skip
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
  apply nextMentsuStateAtWithCopyLimit_skip
    hand tile state
    (reachableWithinWithCopyLimit_used_subset hand fuel state hreachable)
    (reachableWithinWithCopyLimit_copyLimit hand fuel state hreachable)
    (reachableWithinWithCopyLimit_melds_le_four hand fuel state hreachable)
    (reachableWithinWithCopyLimit_taatsu_le_four hand fuel state hreachable)

lemma reachableOnTilesFromWithCopyLimit_skips
    (hand : Hand) (tiles : List Tile) (fuel : Nat)
    (state : MentsuSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    ∃ final,
      reachableOnTilesFromWithCopyLimit hand tiles state final ∧
        reachableWithinWithCopyLimit hand (fuel + tiles.length) final := by
  induction tiles generalizing fuel state with
  | nil =>
      exact ⟨state, rfl, by simpa using hreachable⟩
  | cons tile tiles ih =>
      let hvalid : ValidMentsuChoice hand state .skip := by
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
            (applyMentsuChoice hand state .skip hvalid) := by
        intro tile
        dsimp [applyMentsuChoice]
        simp only [choiceTiles, Multiset.add_zero]
        exact hstatecopy tile
      have hskip :
          NextMentsuStateAtWithCopyLimit hand tile state
            (applyMentsuChoice hand state .skip hvalid) := by
        refine ⟨.skip, ?_, hvalid, ?_, rfl⟩
        · apply (mem_choicesForTileWithCopyLimit_iff
            hand state tile .skip).mpr
          exact ⟨by simp [choicesForTile, allMentsuChoices],
            ⟨hvalid, hcopy⟩⟩
        · exact hcopy
      have hreachableNext :
          reachableWithinWithCopyLimit hand (fuel + 1)
            (applyMentsuChoice hand state .skip hvalid) := by
        exact ⟨state, hreachable,
          nextMentsuStateAtWithCopyLimit_toNextWithCopyLimit
            hand tile state
            (applyMentsuChoice hand state .skip hvalid) hskip⟩
      obtain ⟨final, hpath, hfinal⟩ :=
        ih (fuel + 1)
          (applyMentsuChoice hand state .skip hvalid) hreachableNext
      refine ⟨final, ?_, ?_⟩
      · exact ⟨applyMentsuChoice hand state .skip hvalid, hskip, hpath⟩
      · have hlength :
            fuel + (tile :: tiles).length = fuel + 1 + tiles.length := by
          simp only [List.length_cons]
          omega
        rw [hlength]
        exact hfinal

lemma reachableOnTilesFromWithCopyLimit_choice_then_skips
    (hand : Hand) (tile : Tile) (tiles : List Tile) (fuel : Nat)
    (state : MentsuSearchState) (choice : MentsuChoice)
    (hreachable : reachableWithinWithCopyLimit hand fuel state)
    (hchoice : choice ∈ allMentsuChoices)
    (htile : tile ∈ choiceTiles choice)
    (hvalid : ValidMentsuChoice hand state choice)
    (hcopy :
      CompletionRespectsCopyLimit
        (applyMentsuChoice hand state choice hvalid)) :
    ∃ final,
      reachableOnTilesFromWithCopyLimit hand (tile :: tiles) state final ∧
        reachableWithinWithCopyLimit hand
          (fuel + 1 + tiles.length) final := by
  have hnext :
      NextMentsuStateAtWithCopyLimit hand tile state
        (applyMentsuChoice hand state choice hvalid) :=
    nextMentsuStateAtWithCopyLimit_of_choice
      hand tile state choice hchoice htile hvalid hcopy
  have hreachableNext :
      reachableWithinWithCopyLimit hand (fuel + 1)
        (applyMentsuChoice hand state choice hvalid) :=
    ⟨state, hreachable,
      nextMentsuStateAtWithCopyLimit_toNextWithCopyLimit
        hand tile state (applyMentsuChoice hand state choice hvalid) hnext⟩
  obtain ⟨final, htail, hfinal⟩ :=
    reachableOnTilesFromWithCopyLimit_skips
      hand tiles (fuel + 1)
        (applyMentsuChoice hand state choice hvalid) hreachableNext
  refine ⟨final, ⟨applyMentsuChoice hand state choice hvalid, hnext, htail⟩, ?_⟩
  exact hfinal

lemma reachableOnTilesFromWithCopyLimit_append
    (hand : Hand) (left right : List Tile)
    (start middle final : MentsuSearchState)
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
    (fuel : Nat) (state : MentsuSearchState) (choice : MentsuChoice)
    (hreachable : reachableWithinWithCopyLimit hand fuel state)
    (hchoice : choice ∈ allMentsuChoices)
    (htile : tile ∈ choiceTiles choice)
    (hvalid : ∀ middle,
      reachableWithinWithCopyLimit hand (fuel + before.length) middle →
        ValidMentsuChoice hand middle choice)
    (hcopy : ∀ middle hmiddle,
      CompletionRespectsCopyLimit
        (applyMentsuChoice hand middle choice (hvalid middle hmiddle))) :
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

inductive AppliesMentsuChoices (hand : Hand) :
    MentsuSearchState → List MentsuChoice → MentsuSearchState → Prop
  | nil (state : MentsuSearchState) :
      AppliesMentsuChoices hand state [] state
  | cons (state : MentsuSearchState) (choice : MentsuChoice)
      (hchoice : choice ∈ allMentsuChoices)
      (hvalid : ValidMentsuChoice hand state choice)
      (final : MentsuSearchState)
      (htail :
        AppliesMentsuChoices hand
          (applyMentsuChoice hand state choice hvalid) choices final) :
      AppliesMentsuChoices hand state (choice :: choices) final

lemma AppliesMentsuChoices.used_eq
    {hand : Hand} {state final : MentsuSearchState}
    {choices : List MentsuChoice}
    (hpath : AppliesMentsuChoices hand state choices final) :
    final.used = state.used + mentsuChoiceTiles choices := by
  induction hpath with
  | nil =>
      simp [mentsuChoiceTiles]
  | @cons state choice hvalid final choices htail ih =>
      cases choice <;>
        simp_all [applyMentsuChoice, mentsuChoiceTiles, choiceTiles]
      all_goals
        try rw [ih]
        try simp [applyMentsuChoice, choiceTiles]
        try ac_rfl

lemma nextMentsuStateWithCopyLimit_toNext
    (hand : Hand) (state next : MentsuSearchState)
    (hnext : NextMentsuStateWithCopyLimit hand state next) :
    NextMentsuState hand state next := by
  rcases hnext with ⟨choice, hchoice, hvalid, _, rfl⟩
  exact ⟨choice, hchoice, hvalid, rfl⟩

lemma reachableWithinWithCopyLimit_to_reachableWithin
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithinWithCopyLimit hand fuel state) :
    reachableWithin hand fuel state := by
  induction fuel generalizing state with
  | zero =>
      exact hreachable
  | succ fuel ih =>
      rcases hreachable with ⟨previous, hprevious, hnext⟩
      rw [reachableWithin_succ_iff]
      exact ⟨previous, ih previous hprevious,
        nextMentsuStateWithCopyLimit_toNext hand previous state hnext⟩

lemma reachableOnTilesWithCopyLimit_to_reachableWithinWithCopyLimit
    (hand : Hand) (tiles : List Tile) (state : MentsuSearchState)
    (hreachable : reachableOnTilesWithCopyLimit hand tiles state) :
    reachableWithinWithCopyLimit hand tiles.length state := by
  have aux :
      ∀ (remaining : List Tile) (start state : MentsuSearchState)
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
            nextMentsuStateAtWithCopyLimit_toNextWithCopyLimit
              hand tile start middle hnext⟩
        have hresult := ih middle state (fuel + 1) hmiddle htail
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult
  have hresult := aux tiles initialMentsuState state 0
    (by rfl) hreachable
  simpa using hresult

lemma completedTargetForState_eq_used_add_completion
    (state : MentsuSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    completedTargetForState state pair =
      stateHistoryTiles state +
        taatsuCompletionTiles state.taatsuHistory.reverse := by
  rw [completedTargetForState, completedMeldsForState_tiles state pair hpair]
  rw [mentsuTargetWithTaatsuOfState_eq_stateHistoryTiles state pair hpair]

lemma validCounts_completedTarget_of_copyLimit
    (before : Hand) (fuel : Nat) (state : MentsuSearchState)
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

lemma completedMeldsForState_card (state : MentsuSearchState) :
    (meldsTiles (completedMeldsForState state)).card =
      3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  rw [meldsTiles_card, completedMeldsForState_length]

lemma completedTargetForState_card
    (state : MentsuSearchState) (pair : Tile) :
    (completedTargetForState state pair).card =
      2 + 3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  unfold completedTargetForState
  rw [Multiset.card_add, pairTiles_card, completedMeldsForState_card]

lemma completedTargetForState_sum
    (state : MentsuSearchState) (pair : Tile) :
    (∑ tile : Tile, countsOfTiles (completedTargetForState state pair) tile) =
      2 + 3 * (state.meldHistory.length + state.taatsuHistory.length) := by
  rw [countsOfTiles_sum_eq_card, completedTargetForState_card]

lemma completedTargetForState_sum_of_blockCount
    (before : Hand) (fuel : Nat) (state : MentsuSearchState)
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
    (before : Hand) (fuel : Nat) (state : MentsuSearchState)
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

lemma complete_mentsu_completedTarget
    (before : Hand) (state : MentsuSearchState) (pair : Tile)
    (hvalid : ValidCounts
      (targetHand before (countsOfTiles (completedTargetForState state pair))))
    (hmelds : HasMentsuMeldCount before (completedMeldsForState state)) :
    Complete .mentsu
      (targetHand before (countsOfTiles (completedTargetForState state pair))) := by
  apply complete_mentsu_targetHand
  · exact hvalid
  · exact hmelds
  · exact targetHand_hasTiles_countsOfTiles before
      (completedTargetForState state pair)

/-- A target is a valid mentsu-form completion for the standing tiles. -/
def IsMentsuTarget
    (hand : Hand) (pair : Tile) (melds : List Meld) : Prop :=
  HasMentsuMeldCount hand melds ∧
    ∀ tile, hand.counts tile ≤
      (mentsuTarget pair melds).count tile

/-- The number of additional tiles needed to realize a mentsu target. -/
def mentsuTargetDistance
    (hand : Hand) (pair : Tile) (melds : List Meld) : Nat :=
  targetDeficit hand (mentsuTarget pair melds)

lemma mentsuTargetDistance_eq_countDeficit
    (hand : Hand) (pair : Tile) (melds : List Meld) :
    mentsuTargetDistance hand pair melds =
      countDeficit hand.counts
        (countsOfTiles (mentsuTarget pair melds)) := by
  rfl

def mentsuMeldListsOfLength : Nat → Finset (List Meld)
  | 0 => {[]}
  | length + 1 =>
      Finset.univ.biUnion fun meld =>
        (mentsuMeldListsOfLength length).image (meld :: ·)

lemma mem_mentsuMeldListsOfLength_iff
    (length : Nat) (melds : List Meld) :
    melds ∈ mentsuMeldListsOfLength length ↔ melds.length = length := by
  induction length generalizing melds with
  | zero =>
      simp [mentsuMeldListsOfLength]
  | succ length ih =>
      simp only [mentsuMeldListsOfLength, Finset.mem_biUnion,
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

def mentsuTargetConfigurations (fixedMelds : Nat) :
    Finset (Tile × List Meld) :=
  Finset.univ ×ˢ mentsuMeldListsOfLength (4 - fixedMelds)

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

lemma mem_mentsuTargetConfigurations_iff
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4)
    (pair : Tile) (melds : List Meld) :
    (pair, melds) ∈ mentsuTargetConfigurations fixedMelds ↔
      melds.length + fixedMelds = 4 := by
  rw [mentsuTargetConfigurations, Finset.mem_product]
  simp only [Finset.mem_univ, true_and,
    mem_mentsuMeldListsOfLength_iff]
  omega

def validMentsuTargetConfigurations (hand : Hand) :
    Finset (Tile × List Meld) :=
  (mentsuTargetConfigurations hand.fixedMelds).filter
    (fun candidate =>
      validCountsBool
        (targetHand hand
          (countsOfTiles
            (mentsuTarget candidate.1 candidate.2))) = true)

lemma mem_validMentsuTargetConfigurations_iff
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4)
    (pair : Tile) (melds : List Meld) :
    (pair, melds) ∈ validMentsuTargetConfigurations hand ↔
      melds.length + hand.fixedMelds = 4 ∧
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuTarget pair melds))) := by
  classical
  rw [validMentsuTargetConfigurations, Finset.mem_filter,
    mem_mentsuTargetConfigurations_iff
      hand.fixedMelds hfixed pair melds]
  rw [validCountsBool_eq_true_iff]

def mentsuMeldTileStatesDP : Nat → Finset (Multiset Tile)
  | 0 => {0}
  | meldCount + 1 =>
      (Finset.univ.biUnion fun meld =>
        (mentsuMeldTileStatesDP meldCount).image
          (fun tiles => meldTiles meld + tiles)).filter
        (fun tiles => validTileMultisetBool tiles = true)

lemma mem_mentsuMeldTileStatesDP_iff
    (meldCount : Nat) (tiles : Multiset Tile) :
    tiles ∈ mentsuMeldTileStatesDP meldCount ↔
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
      simp only [mentsuMeldTileStatesDP, Finset.mem_filter,
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
                meldsTiles melds ∈ mentsuMeldTileStatesDP meldCount :=
              (ih (meldsTiles melds)).2
                ⟨melds, by omega, rfl, htailValid⟩
            refine ⟨⟨meld, meldsTiles melds, hprevious, ?_⟩, hvalid⟩
            calc
              meldTiles meld + meldsTiles melds =
                  meldsTiles (meld :: melds) := rfl
              _ = tiles := htiles

def mentsuTargetTileStatesDP (fixedMelds : Nat) :
    Finset (Multiset Tile) :=
  (Finset.univ.biUnion fun pair =>
    (mentsuMeldTileStatesDP (4 - fixedMelds)).image
      (fun meldTiles => pairTiles pair + meldTiles)).filter
    (fun tiles => validTileMultisetBool tiles = true)

lemma mem_mentsuTargetTileStatesDP_iff
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4)
    (tiles : Multiset Tile) :
    tiles ∈ mentsuTargetTileStatesDP fixedMelds ↔
      ∃ pair melds,
        melds.length + fixedMelds = 4 ∧
        mentsuTarget pair melds = tiles ∧
        validTileMultisetBool tiles = true := by
  unfold mentsuTargetTileStatesDP
  simp only [Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨pair, meldTiles, hmeldTiles, rfl⟩, hvalid⟩
    obtain ⟨melds, hlength, rfl, _⟩ :=
      (mem_mentsuMeldTileStatesDP_iff (4 - fixedMelds) meldTiles).mp
        hmeldTiles
    refine ⟨pair, melds, ?_, rfl, hvalid⟩
    omega
  · rintro ⟨pair, melds, hlength, rfl, hvalid⟩
    have hmeldValid :
        validTileMultisetBool (meldsTiles melds) = true := by
      apply validTileMultisetBool_add_left
        (meldsTiles melds) (pairTiles pair)
      simpa [mentsuTarget, Multiset.add_comm] using hvalid
    refine ⟨⟨pair, meldsTiles melds, ?_, rfl⟩, hvalid⟩
    · exact (mem_mentsuMeldTileStatesDP_iff (4 - fixedMelds)
        (meldsTiles melds)).2
        ⟨melds, by omega, rfl, hmeldValid⟩

def mentsuTargetCostStatesDP (hand : Hand) :
    Finset (Multiset Tile × Nat) :=
  (mentsuTargetTileStatesDP hand.fixedMelds).image
    (fun tiles =>
      (tiles, countDeficit hand.counts (countsOfTiles tiles)))

lemma mem_mentsuTargetCostStatesDP_iff
    (hand : Hand) (state : Multiset Tile × Nat) :
    state ∈ mentsuTargetCostStatesDP hand ↔
      state.1 ∈ mentsuTargetTileStatesDP hand.fixedMelds ∧
      state.2 = countDeficit hand.counts (countsOfTiles state.1) := by
  unfold mentsuTargetCostStatesDP
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
def mentsuCostStateAdd (hand : Hand)
    (state : Multiset Tile × Nat) (extra : Multiset Tile) :
    Multiset Tile × Nat :=
  let tiles := state.1 + extra
  (tiles,
    state.2 + (countDeficit hand.counts (countsOfTiles tiles) -
      countDeficit hand.counts (countsOfTiles state.1)))

lemma mentsuCostStateAdd_cost
    (hand : Hand) (state : Multiset Tile × Nat) (extra : Multiset Tile)
    (hcost :
      state.2 = countDeficit hand.counts (countsOfTiles state.1)) :
    (mentsuCostStateAdd hand state extra).2 =
      countDeficit hand.counts
        (countsOfTiles ((mentsuCostStateAdd hand state extra).1)) := by
  unfold mentsuCostStateAdd
  dsimp only
  rw [hcost]
  have hmono := countDeficit_tiles_add_mono
    hand.counts state.1 extra
  omega

def mentsuMeldCostStatesDP (hand : Hand) (initialTiles : Multiset Tile) :
    Nat → Finset (Multiset Tile × Nat)
  | 0 =>
      Finset.filter
        (fun state => validTileMultisetBool state.1 = true)
        ({(initialTiles,
            countDeficit hand.counts (countsOfTiles initialTiles))} :
          Finset (Multiset Tile × Nat))
  | meldCount + 1 =>
      (Finset.univ.biUnion fun meld =>
        (mentsuMeldCostStatesDP hand initialTiles meldCount).image
          (fun state => mentsuCostStateAdd hand state (meldTiles meld)))
        |>.filter (fun state => validTileMultisetBool state.1 = true)

lemma mentsuMeldCostStatesDP_cost
    (hand : Hand) (initialTiles : Multiset Tile) (meldCount : Nat)
    (state : Multiset Tile × Nat)
    (hstate : state ∈ mentsuMeldCostStatesDP hand initialTiles meldCount) :
    state.2 = countDeficit hand.counts (countsOfTiles state.1) := by
  induction meldCount generalizing state with
  | zero =>
      simp only [mentsuMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_singleton] at hstate
      rw [hstate.1]
  | succ meldCount ih =>
      simp only [mentsuMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image] at hstate
      rcases hstate with ⟨⟨meld, previous, hprevious, heq⟩, _⟩
      have hpreviousCost := ih previous hprevious
      have hnextCost :=
        mentsuCostStateAdd_cost hand previous (meldTiles meld)
          hpreviousCost
      calc
        state.2 =
            (mentsuCostStateAdd hand previous (meldTiles meld)).2 :=
          (congrArg Prod.snd heq).symm
        _ = countDeficit hand.counts
            (countsOfTiles
              (mentsuCostStateAdd hand previous (meldTiles meld)).1) :=
          hnextCost
        _ = countDeficit hand.counts (countsOfTiles state.1) := by
          rw [congrArg Prod.fst heq]

lemma mem_mentsuMeldCostStatesDP_iff
    (hand : Hand) (initialTiles : Multiset Tile)
    (meldCount : Nat) (state : Multiset Tile × Nat) :
    state ∈ mentsuMeldCostStatesDP hand initialTiles meldCount ↔
      ∃ melds,
        melds.length = meldCount ∧
        meldsTiles melds + initialTiles = state.1 ∧
        state.2 = countDeficit hand.counts (countsOfTiles state.1) ∧
        validTileMultisetBool state.1 = true := by
  induction meldCount generalizing state with
  | zero =>
      simp only [mentsuMeldCostStatesDP, Finset.mem_filter,
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
      simp only [mentsuMeldCostStatesDP, Finset.mem_filter,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · intro hstate
        rcases hstate with ⟨⟨meld, previous, hprevious, heq⟩, hvalid⟩
        have hpreviousCost :=
          mentsuMeldCostStatesDP_cost hand initialTiles meldCount
            previous hprevious
        have hnextCost :=
          mentsuCostStateAdd_cost hand previous (meldTiles meld)
            hpreviousCost
        have hcost : state.2 =
            countDeficit hand.counts (countsOfTiles state.1) := by
          calc
            state.2 =
                (mentsuCostStateAdd hand previous (meldTiles meld)).2 :=
              (congrArg Prod.snd heq).symm
            _ = countDeficit hand.counts
                (countsOfTiles
                  (mentsuCostStateAdd hand previous (meldTiles meld)).1) :=
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
          _ = (mentsuCostStateAdd hand previous (meldTiles meld)).1 := by
                simp [mentsuCostStateAdd, Multiset.add_comm]
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
                previous ∈ mentsuMeldCostStatesDP hand initialTiles meldCount :=
              (ih previous).2
                ⟨melds, by omega, rfl, rfl, hpreviousValid⟩
            have hnextCost :=
              mentsuCostStateAdd_cost hand previous (meldTiles meld) rfl
            have hfirst :
                (mentsuCostStateAdd hand previous (meldTiles meld)).1 =
                  state.1 := by
              calc
                (mentsuCostStateAdd hand previous (meldTiles meld)).1 =
                    (meldsTiles melds + initialTiles) + meldTiles meld := by
                      simp [mentsuCostStateAdd, previous]
                _ = meldsTiles (meld :: melds) + initialTiles :=
                  htilesShape.symm
                _ = state.1 := htiles
            refine ⟨⟨meld, previous, hprevious, ?_⟩, hvalid⟩
            apply Prod.ext
            · exact hfirst
            · calc
                (mentsuCostStateAdd hand previous (meldTiles meld)).2 =
                    countDeficit hand.counts
                      (countsOfTiles
                        (mentsuCostStateAdd hand previous (meldTiles meld)).1) :=
                  hnextCost
                _ = countDeficit hand.counts
                    (countsOfTiles state.1) := by
                      rw [hfirst]
                _ = state.2 := hcost.symm

def recursiveMentsuTargetCostStatesDP (hand : Hand) :
    Finset (Multiset Tile × Nat) :=
  Finset.univ.biUnion fun pair =>
    mentsuMeldCostStatesDP hand (pairTiles pair)
      (4 - hand.fixedMelds)

lemma recursiveMentsuTargetCostStatesDP_eq
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4) :
    recursiveMentsuTargetCostStatesDP hand =
      mentsuTargetCostStatesDP hand := by
  ext state
  unfold recursiveMentsuTargetCostStatesDP
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  rw [mem_mentsuTargetCostStatesDP_iff]
  constructor
  · rintro ⟨pair, hstate⟩
    obtain ⟨melds, hlength, htiles, hcost, hvalid⟩ :=
      (mem_mentsuMeldCostStatesDP_iff hand (pairTiles pair)
        (4 - hand.fixedMelds) state).mp hstate
    have htargetLength : melds.length + hand.fixedMelds = 4 := by
      omega
    have htarget :
        mentsuTarget pair melds = state.1 := by
      rw [mentsuTarget]
      calc
        pairTiles pair + meldsTiles melds =
            meldsTiles melds + pairTiles pair := by ac_rfl
        _ = state.1 := htiles
    have htilesTarget :
        state.1 ∈ mentsuTargetTileStatesDP hand.fixedMelds :=
      (mem_mentsuTargetTileStatesDP_iff hand.fixedMelds hfixed
        state.1).2
        ⟨pair, melds, htargetLength, htarget, hvalid⟩
    exact ⟨htilesTarget, hcost⟩
  · rintro ⟨htiles, hcost⟩
    obtain ⟨pair, melds, hlength, htarget, hvalid⟩ :=
      (mem_mentsuTargetTileStatesDP_iff hand.fixedMelds hfixed
        state.1).mp htiles
    refine ⟨pair, ?_⟩
    apply (mem_mentsuMeldCostStatesDP_iff hand (pairTiles pair)
      (4 - hand.fixedMelds) state).2
    refine ⟨melds, ?_, ?_, hcost, ?_⟩
    · omega
    · rw [← htarget, mentsuTarget]
      ac_rfl
    · exact hvalid

def validMentsuTargetDistances (hand : Hand) :
    Finset Nat :=
  (recursiveMentsuTargetCostStatesDP hand).image Prod.snd

lemma mentsuTargetCostDistances_eq_tileDistances
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4) :
    validMentsuTargetDistances hand =
      (mentsuTargetTileStatesDP hand.fixedMelds).image
        (fun tiles => countDeficit hand.counts (countsOfTiles tiles)) := by
  unfold validMentsuTargetDistances
  rw [recursiveMentsuTargetCostStatesDP_eq hand hfixed]
  ext distance
  simp [mentsuTargetCostStatesDP, Finset.image_image]

/-- Exhaustive target-state search; equal tile multisets are deduplicated at each meld count. -/
def mentsuTargetMinimumSearch (hand : Hand) : Option Int :=
  let distances := validMentsuTargetDistances hand
  if h : distances.Nonempty then
    some ((distances.min' h : Int) - 1)
  else
    none

lemma mem_validMentsuTargetDistances_iff
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4) (distance : Nat) :
    distance ∈ validMentsuTargetDistances hand ↔
      ∃ pair melds,
        melds.length + hand.fixedMelds = 4 ∧
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuTarget pair melds))) ∧
        mentsuTargetDistance hand pair melds = distance := by
  classical
  rw [mentsuTargetCostDistances_eq_tileDistances hand hfixed]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨tiles, htiles, hdistance⟩
    obtain ⟨pair, melds, hmelds, htarget, hcopy⟩ :=
      (mem_mentsuTargetTileStatesDP_iff
        hand.fixedMelds hfixed tiles).mp htiles
    refine ⟨pair, melds, hmelds, ?_, ?_⟩
    · rw [← htarget] at hcopy
      exact (validTileMultisetBool_eq_true_iff_targetHand
        hand (mentsuTarget pair melds)).mp hcopy
    · rw [← htarget] at hdistance
      rw [mentsuTargetDistance_eq_countDeficit]
      exact hdistance
  · rintro ⟨pair, melds, hmelds, hvalid, hdistance⟩
    let tiles := mentsuTarget pair melds
    have hcopy :
        validTileMultisetBool tiles = true :=
      (validTileMultisetBool_eq_true_iff_targetHand hand tiles).mpr hvalid
    have htiles :
        tiles ∈ mentsuTargetTileStatesDP hand.fixedMelds :=
      (mem_mentsuTargetTileStatesDP_iff
        hand.fixedMelds hfixed tiles).mpr
        ⟨pair, melds, hmelds, rfl, hcopy⟩
    refine ⟨tiles, htiles, ?_⟩
    rw [mentsuTargetDistance_eq_countDeficit] at hdistance
    exact hdistance

lemma exists_min_validMentsuTargetDistance
    (hand : Hand) (hfixed : hand.fixedMelds ≤ 4)
    (hcandidate :
      ∃ pair melds,
        melds.length + hand.fixedMelds = 4 ∧
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuTarget pair melds)))) :
    ∃ distance, distance ∈ validMentsuTargetDistances hand ∧
      ∀ otherDistance,
        otherDistance ∈ validMentsuTargetDistances hand →
          distance ≤ otherDistance := by
  classical
  let distances := validMentsuTargetDistances hand
  have hnonempty : distances.Nonempty := by
    obtain ⟨pair, melds, hmelds, hvalid⟩ := hcandidate
    refine ⟨mentsuTargetDistance hand pair melds, ?_⟩
    exact (mem_validMentsuTargetDistances_iff
      hand hfixed (mentsuTargetDistance hand pair melds)).2
      ⟨pair, melds, hmelds, hvalid, rfl⟩
  let distance := distances.min' hnonempty
  refine ⟨distance, ?_, ?_⟩
  · change distance ∈ distances
    exact Finset.min'_mem distances hnonempty
  · intro otherDistance hother
    exact Finset.min'_le distances otherDistance hother

lemma exists_mentsuTarget_distance_le_of_reachesCompletion
    (before : Hand) (distance : Nat)
    (hreach : ReachesCompletion Complete .mentsu before distance) :
    ∃ pair melds,
      melds.length + before.fixedMelds = 4 ∧
        ValidCounts
          (targetHand before
            (countsOfTiles (mentsuTarget pair melds))) ∧
        mentsuTargetDistance before pair melds ≤ distance := by
  obtain ⟨after, hcomplete, hfixed, hdeficit⟩ :=
    exists_complete_mentsu_with_deficit_le before distance hreach
  rcases hcomplete with ⟨hvalidAfter, pair, melds, hmelds, htiles⟩
  have hcounts :
      after.counts =
        countsOfTiles (mentsuTarget pair melds) := by
    funext tile
    change after.counts tile =
      (mentsuTarget pair melds).count tile
    exact htiles tile
  have hvalidTarget :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuTarget pair melds))) := by
    intro tile
    change (countsOfTiles (mentsuTarget pair melds)) tile ≤ 4
    rw [← hcounts]
    exact hvalidAfter tile
  refine ⟨pair, melds, ?_, hvalidTarget, ?_⟩
  · rw [← hfixed]
    exact hmelds
  · rw [mentsuTargetDistance_eq_countDeficit]
    simpa [hcounts] using hdeficit

lemma no_shorter_mentsu_completion_of_minimal_mentsuTargetDistance
    (before : Hand) (pair : Tile) (melds : List Meld)
    (distance : Nat)
    (hdistance : mentsuTargetDistance before pair melds = distance)
    (hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuTarget otherPair otherMelds))) →
          mentsuTargetDistance before pair melds ≤
            mentsuTargetDistance before otherPair otherMelds) :
    ∀ smaller : Nat, smaller < distance →
      ¬ ReachesCompletion Complete .mentsu before smaller := by
  intro smaller hsmaller hreach
  obtain ⟨otherPair, otherMelds, hmelds, hvalid, hotherDistance⟩ :=
    exists_mentsuTarget_distance_le_of_reachesCompletion
      before smaller hreach
  have hminimal := hminimalTarget otherPair otherMelds hmelds hvalid
  omega

lemma mentsuTargetDistance_eq_zero_iff
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuTarget pair melds).count tile) :
    mentsuTargetDistance hand pair melds = 0 ↔
      hand.counts = countsOfTiles (mentsuTarget pair melds) := by
  constructor
  · intro hdistance
    have hdeficit :
        countDeficit hand.counts
          (countsOfTiles (mentsuTarget pair melds)) = 0 := by
      rw [← mentsuTargetDistance_eq_countDeficit]
      exact hdistance
    have hzero :
        ∀ tile ∈ (Finset.univ : Finset Tile),
          (countsOfTiles (mentsuTarget pair melds)) tile -
              hand.counts tile = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun tile _ => Nat.zero_le _)).mp
      exact hdeficit
    have hle :
        ∀ tile, (countsOfTiles (mentsuTarget pair melds)) tile ≤
          hand.counts tile := by
      intro tile
      have hzeroTile := hzero tile (Finset.mem_univ tile)
      omega
    apply funext
    intro tile
    have heq :
        ∀ tile ∈ (Finset.univ : Finset Tile),
          (countsOfTiles (mentsuTarget pair melds)) tile =
            hand.counts tile := by
      apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
        (f := countsOfTiles (mentsuTarget pair melds))
        (g := hand.counts)
        (fun tile _ => hle tile)).mp
      exact hsum.symm
    exact (heq tile (Finset.mem_univ tile)).symm
  · intro hcounts
    rw [mentsuTargetDistance_eq_countDeficit]
    simp [countDeficit, hcounts]

lemma mentsuTargetDistance_pos_iff
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuTarget pair melds).count tile) :
    0 < mentsuTargetDistance hand pair melds ↔
      hand.counts ≠ countsOfTiles (mentsuTarget pair melds) := by
  constructor
  · intro hpos hcounts
    have hzero : mentsuTargetDistance hand pair melds = 0 :=
      (mentsuTargetDistance_eq_zero_iff hand pair melds hsum).mpr hcounts
    omega
  · intro hne
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hne
        ((mentsuTargetDistance_eq_zero_iff hand pair melds hsum).mp hzero))

lemma mentsuTargetDistance_exchange
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (discarded drawn : Tile)
    (hdrawn :
      (mentsuTarget pair melds).count drawn > hand.counts drawn)
    (hdiscarded :
      hand.counts discarded >
        (mentsuTarget pair melds).count discarded)
    (hne : discarded ≠ drawn) :
    mentsuTargetDistance
        (exchangeHand hand discarded drawn) pair melds =
      mentsuTargetDistance hand pair melds - 1 := by
  rw [mentsuTargetDistance_eq_countDeficit,
    mentsuTargetDistance_eq_countDeficit]
  exact countDeficit_exchange
    (countsOfTiles (mentsuTarget pair melds))
    hand discarded drawn hdrawn hdiscarded hne

lemma exists_mentsuTarget_exchange
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuTarget pair melds).count tile)
    (hne :
      hand.counts ≠ countsOfTiles (mentsuTarget pair melds)) :
    ∃ discarded drawn,
      (mentsuTarget pair melds).count drawn > hand.counts drawn ∧
      hand.counts discarded >
        (mentsuTarget pair melds).count discarded ∧
      discarded ≠ drawn ∧
      mentsuTargetDistance
          (exchangeHand hand discarded drawn) pair melds =
        mentsuTargetDistance hand pair melds - 1 := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles⟩ :=
    exists_target_exchange_tiles hand
      (countsOfTiles (mentsuTarget pair melds)) hsum hne
  refine ⟨discarded, drawn, hdrawn, hdiscarded, hneTiles, ?_⟩
  exact mentsuTargetDistance_exchange
    hand pair melds discarded drawn hdrawn hdiscarded hneTiles

lemma exists_mentsuTarget_exchange_of_pos
    (hand : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, hand.counts tile) =
        ∑ tile : Tile, (mentsuTarget pair melds).count tile)
    (hpos : 0 < mentsuTargetDistance hand pair melds) :
    ∃ discarded drawn,
      (mentsuTarget pair melds).count drawn > hand.counts drawn ∧
      hand.counts discarded >
        (mentsuTarget pair melds).count discarded ∧
      discarded ≠ drawn ∧
      mentsuTargetDistance
          (exchangeHand hand discarded drawn) pair melds =
        mentsuTargetDistance hand pair melds - 1 := by
  apply exists_mentsuTarget_exchange hand pair melds hsum
  exact (mentsuTargetDistance_pos_iff hand pair melds hsum).mp hpos

lemma reachesCompletion_mentsu_of_mentsuTarget
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    ReachesCompletion Complete .mentsu before
      (mentsuTargetDistance before pair melds) := by
  rw [mentsuTargetDistance_eq_countDeficit]
  apply reachesCompletion_mentsu_of_equal_sum
    before
    (countsOfTiles (mentsuTarget pair melds))
    pair melds hsum hvalid hmelds
  exact targetHand_hasTiles_countsOfTiles before
    (mentsuTarget pair melds)

lemma complete_mentsu_of_mentsuTarget_distance_zero
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuTargetDistance before pair melds = 0)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    Complete .mentsu before := by
  have hdeficit :
      countDeficit before.counts
        (countsOfTiles (mentsuTarget pair melds)) = 0 := by
    rw [← mentsuTargetDistance_eq_countDeficit]
    exact hdistance
  have hzero :
      ∀ tile ∈ (Finset.univ : Finset Tile),
        (countsOfTiles (mentsuTarget pair melds)) tile -
            before.counts tile = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun tile _ => Nat.zero_le _)).mp
    exact hdeficit
  have hle :
      ∀ tile, (countsOfTiles (mentsuTarget pair melds)) tile ≤
        before.counts tile := by
    intro tile
    have hzeroTile := hzero tile (Finset.mem_univ tile)
    omega
  have heq :
      ∀ tile ∈ (Finset.univ : Finset Tile),
        (countsOfTiles (mentsuTarget pair melds)) tile =
          before.counts tile := by
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := countsOfTiles (mentsuTarget pair melds))
      (g := before.counts)
      (fun tile _ => hle tile)).mp
    exact hsum.symm
  have hcounts :
      countsOfTiles (mentsuTarget pair melds) = before.counts := by
    funext tile
    exact heq tile (Finset.mem_univ tile)
  have hcomplete :
      Complete .mentsu
        (targetHand before
          (countsOfTiles (mentsuTarget pair melds))) := by
    exact complete_mentsu_targetHand before
      (countsOfTiles (mentsuTarget pair melds)) pair melds
      hvalid hmelds
      (targetHand_hasTiles_countsOfTiles before
        (mentsuTarget pair melds))
  simpa [targetHand, hcounts] using hcomplete

set_option maxHeartbeats 1000000 in
lemma reachesCompletion_mentsu_of_mentsuTarget_distance_one
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuTargetDistance before pair melds = 1)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    ReachesCompletion Complete .mentsu before 1 := by
  obtain ⟨discarded, drawn, hdrawn, hdiscarded, hne, hdistanceNext⟩ :=
    exists_mentsuTarget_exchange_of_pos
      before pair melds hsum (by omega)
  have hsumNext :
      (∑ tile : Tile, (exchangeHand before discarded drawn).counts tile) =
        ∑ tile : Tile, (mentsuTarget pair melds).count tile := by
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
          (countsOfTiles (mentsuTarget pair melds))) := by
    change
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuTarget pair melds)))
    exact hvalid
  have hmeldsNext :
      melds.length + (exchangeHand before discarded drawn).fixedMelds = 4 := by
    change melds.length + before.fixedMelds = 4
    exact hmelds
  have hcomplete :
      Complete .mentsu (exchangeHand before discarded drawn) := by
    have hzeroNext :
        mentsuTargetDistance
            (exchangeHand before discarded drawn) pair melds = 0 := by
      omega
    have hcountsNext :
        (exchangeHand before discarded drawn).counts =
          countsOfTiles (mentsuTarget pair melds) :=
      (mentsuTargetDistance_eq_zero_iff
        (exchangeHand before discarded drawn) pair melds hsumNext).mp
        hzeroNext
    have htargetComplete :
        Complete .mentsu
          (targetHand (exchangeHand before discarded drawn)
            (countsOfTiles (mentsuTarget pair melds))) :=
      complete_mentsu_targetHand
        (exchangeHand before discarded drawn)
        (countsOfTiles (mentsuTarget pair melds))
        pair melds hvalidNext hmeldsNext
        (targetHand_hasTiles_countsOfTiles
          (exchangeHand before discarded drawn)
          (mentsuTarget pair melds))
    have hhand :
        exchangeHand before discarded drawn =
          targetHand (exchangeHand before discarded drawn)
            (countsOfTiles (mentsuTarget pair melds)) := by
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
  · exact mentsuTargetExchange_handStep
      (countsOfTiles (mentsuTarget pair melds))
      before discarded drawn hdrawn hdiscarded hne
  · exact ReachesCompletion.done hcomplete

set_option maxHeartbeats 1000000 in
lemma reachesCompletion_mentsu_of_mentsuTarget_distance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4) :
    ReachesCompletion Complete .mentsu before distance := by
  induction distance generalizing before with
  | zero =>
      have hcomplete : Complete .mentsu before := by
        exact complete_mentsu_of_mentsuTarget_distance_zero
          before pair melds hdistance hsum hvalid hmelds
      exact ReachesCompletion.done hcomplete
  | succ distance ih =>
      obtain ⟨discarded, drawn, hdrawn, hdiscarded, hne, hdistanceNext⟩ :=
        exists_mentsuTarget_exchange_of_pos
          before pair melds hsum (by omega)
      have hsumNext :
          (∑ tile : Tile,
            (exchangeHand before discarded drawn).counts tile) =
            ∑ tile : Tile, (mentsuTarget pair melds).count tile := by
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
              (countsOfTiles (mentsuTarget pair melds))) := by
        change
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuTarget pair melds)))
        exact hvalid
      have hmeldsNext :
          melds.length + (exchangeHand before discarded drawn).fixedMelds = 4 := by
        change melds.length + before.fixedMelds = 4
        exact hmelds
      have hdistanceNext' :
          mentsuTargetDistance
              (exchangeHand before discarded drawn) pair melds = distance := by
        omega
      have hrest :=
        ih (exchangeHand before discarded drawn)
          hdistanceNext' hsumNext hvalidNext hmeldsNext
      apply ReachesCompletion.step
      · exact mentsuTargetExchange_handStep
          (countsOfTiles (mentsuTarget pair melds))
          before discarded drawn hdrawn hdiscarded hne
      · exact hrest

lemma isShapeShanten_mentsu_of_mentsuTarget_distance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hminimal :
      ∀ smaller : Nat, smaller < distance →
        ¬ ReachesCompletion Complete .mentsu before smaller) :
    IsShapeShanten before .mentsu ((distance : Int) - 1) := by
  have hreaches :
      ReachesCompletion Complete .mentsu before distance :=
    reachesCompletion_mentsu_of_mentsuTarget_distance
      distance before pair melds hdistance hsum hvalid hmelds
  refine ⟨trivial, distance, ?_, hreaches, hminimal⟩
  omega

lemma isShapeShanten_mentsu_of_minimal_mentsuTargetDistance
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile, before.counts tile) =
        ∑ tile : Tile, (mentsuTarget pair melds).count tile)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuTarget otherPair otherMelds))) →
          mentsuTargetDistance before pair melds ≤
            mentsuTargetDistance before otherPair otherMelds) :
    IsShapeShanten before .mentsu ((distance : Int) - 1) := by
  apply isShapeShanten_mentsu_of_mentsuTarget_distance
    distance before pair melds hdistance hsum hvalid hmelds
  exact no_shorter_mentsu_completion_of_minimal_mentsuTargetDistance
    before pair melds distance hdistance hminimalTarget

lemma isShapeShanten_mentsu_of_minimal_mentsuTargetDistance_one_more
    (distance : Nat)
    (before : Hand) (pair : Tile) (melds : List Meld)
    (hdistance : mentsuTargetDistance before pair melds = distance)
    (hsum :
      (∑ tile : Tile,
        countsOfTiles (mentsuTarget pair melds) tile) =
        (∑ tile : Tile, before.counts tile) + 1)
    (hbeforeValid : ValidCounts before)
    (hvalid :
      ValidCounts
        (targetHand before
          (countsOfTiles (mentsuTarget pair melds))))
    (hmelds : melds.length + before.fixedMelds = 4)
    (hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuTarget otherPair otherMelds))) →
          mentsuTargetDistance before pair melds ≤
            mentsuTargetDistance before otherPair otherMelds) :
    IsShapeShanten before .mentsu ((distance : Int) - 1) := by
  obtain ⟨reachedDistance, htargetDistance, hreach⟩ :=
    reachesCompletion_mentsu_of_one_more_target_tile
      before (countsOfTiles (mentsuTarget pair melds))
      pair melds hsum hbeforeValid hvalid hmelds
      (targetHand_hasTiles_countsOfTiles before
        (mentsuTarget pair melds))
  have hreachDistance :
      reachedDistance = distance := by
    calc
      reachedDistance =
          countDeficit before.counts
            (countsOfTiles (mentsuTarget pair melds)) :=
        htargetDistance
      _ = mentsuTargetDistance before pair melds :=
        (mentsuTargetDistance_eq_countDeficit before pair melds).symm
      _ = distance := hdistance
  have hreaches :
      ReachesCompletion Complete .mentsu before distance := by
    rw [← hreachDistance]
    exact hreach
  have hminimal :=
    no_shorter_mentsu_completion_of_minimal_mentsuTargetDistance
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
lemma exists_isShapeShanten_mentsu_of_valid_mentsuTarget
    (before : Hand)
    (hcandidate :
      ∃ pair melds,
        melds.length + before.fixedMelds = 4 ∧
          (∑ tile : Tile, before.counts tile) =
            ∑ tile : Tile, (mentsuTarget pair melds).count tile ∧
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuTarget pair melds)))) :
    ∃ value : Int, IsShapeShanten before .mentsu value := by
  classical
  let candidateDistance : Nat → Prop := fun distance =>
    ∃ pair melds,
      melds.length + before.fixedMelds = 4 ∧
        (∑ tile : Tile, before.counts tile) =
          ∑ tile : Tile, (mentsuTarget pair melds).count tile ∧
        ValidCounts
          (targetHand before
            (countsOfTiles (mentsuTarget pair melds))) ∧
        mentsuTargetDistance before pair melds = distance
  have hexists : ∃ distance, candidateDistance distance := by
    obtain ⟨pair, melds, hmelds, hsum, hvalid⟩ := hcandidate
    exact ⟨mentsuTargetDistance before pair melds,
      pair, melds, hmelds, hsum, hvalid, rfl⟩
  let distance := Nat.find hexists
  obtain ⟨pair, melds, hmelds, hsum, hvalid, hdistance⟩ :=
    Nat.find_spec hexists
  have hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuTarget otherPair otherMelds))) →
          mentsuTargetDistance before pair melds ≤
            mentsuTargetDistance before otherPair otherMelds := by
    intro otherPair otherMelds hotherMelds hotherValid
    have hlength : melds.length = otherMelds.length := by omega
    have hsumOther :
        (∑ tile : Tile, before.counts tile) =
          ∑ tile : Tile, (mentsuTarget otherPair otherMelds).count tile := by
      calc
        (∑ tile : Tile, before.counts tile) =
            ∑ tile : Tile, (mentsuTarget pair melds).count tile := hsum
        _ = (mentsuTarget pair melds).card := by
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuTarget pair melds))
        _ = (mentsuTarget otherPair otherMelds).card := by
          simp [mentsuTarget, Multiset.card_add, pairTiles_card,
            meldsTiles_card, hlength]
        _ = ∑ tile : Tile, (mentsuTarget otherPair otherMelds).count tile := by
          symm
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuTarget otherPair otherMelds))
    have hotherCandidate :
        candidateDistance (mentsuTargetDistance before otherPair otherMelds) :=
      ⟨otherPair, otherMelds, hotherMelds, hsumOther, hotherValid, rfl⟩
    calc
      mentsuTargetDistance before pair melds = distance := hdistance
      _ ≤ mentsuTargetDistance before otherPair otherMelds := by
        change Nat.find hexists ≤
          mentsuTargetDistance before otherPair otherMelds
        exact nat_find_le_of_mem candidateDistance hexists hotherCandidate
  have hshape :
      IsShapeShanten before .mentsu ((distance : Int) - 1) :=
    isShapeShanten_mentsu_of_minimal_mentsuTargetDistance
      distance before pair melds hdistance hsum hvalid hmelds hminimalTarget
  exact ⟨(distance : Int) - 1, hshape⟩

set_option maxHeartbeats 1000000 in
lemma exists_isShapeShanten_mentsu_of_valid_mentsuTarget_one_more
    (before : Hand) (hbeforeValid : ValidCounts before)
    (hcandidate :
      ∃ pair melds,
        melds.length + before.fixedMelds = 4 ∧
          (∑ tile : Tile,
            countsOfTiles (mentsuTarget pair melds) tile) =
            (∑ tile : Tile, before.counts tile) + 1 ∧
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuTarget pair melds)))) :
    ∃ value : Int, IsShapeShanten before .mentsu value := by
  classical
  let candidateDistance : Nat → Prop := fun distance =>
    ∃ pair melds,
      melds.length + before.fixedMelds = 4 ∧
        (∑ tile : Tile,
          countsOfTiles (mentsuTarget pair melds) tile) =
          (∑ tile : Tile, before.counts tile) + 1 ∧
        ValidCounts
          (targetHand before
            (countsOfTiles (mentsuTarget pair melds))) ∧
        mentsuTargetDistance before pair melds = distance
  have hexists : ∃ distance, candidateDistance distance := by
    obtain ⟨pair, melds, hmelds, hsum, hvalid⟩ := hcandidate
    exact ⟨mentsuTargetDistance before pair melds,
      pair, melds, hmelds, hsum, hvalid, rfl⟩
  let distance := Nat.find hexists
  obtain ⟨pair, melds, hmelds, hsum, hvalid, hdistance⟩ :=
    Nat.find_spec hexists
  have hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + before.fixedMelds = 4 →
          ValidCounts
            (targetHand before
              (countsOfTiles (mentsuTarget otherPair otherMelds))) →
          mentsuTargetDistance before pair melds ≤
            mentsuTargetDistance before otherPair otherMelds := by
    intro otherPair otherMelds hotherMelds hotherValid
    have hlength : melds.length = otherMelds.length := by omega
    have hsumOther :
        (∑ tile : Tile,
          countsOfTiles (mentsuTarget otherPair otherMelds) tile) =
          (∑ tile : Tile, before.counts tile) + 1 := by
      calc
        (∑ tile : Tile,
            countsOfTiles (mentsuTarget otherPair otherMelds) tile) =
            (mentsuTarget otherPair otherMelds).card := by
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuTarget otherPair otherMelds))
        _ = (mentsuTarget pair melds).card := by
          simp [mentsuTarget, Multiset.card_add, pairTiles_card,
            meldsTiles_card, hlength]
        _ = ∑ tile : Tile,
            countsOfTiles (mentsuTarget pair melds) tile := by
          symm
          simpa [countsOfTiles] using
            (countsOfTiles_sum_eq_card (mentsuTarget pair melds))
        _ = (∑ tile : Tile, before.counts tile) + 1 := hsum
    have hotherCandidate :
        candidateDistance (mentsuTargetDistance before otherPair otherMelds) :=
      ⟨otherPair, otherMelds, hotherMelds, hsumOther, hotherValid, rfl⟩
    calc
      mentsuTargetDistance before pair melds = distance := hdistance
      _ ≤ mentsuTargetDistance before otherPair otherMelds := by
        change Nat.find hexists ≤
          mentsuTargetDistance before otherPair otherMelds
        exact nat_find_le_of_mem candidateDistance hexists hotherCandidate
  have hshape :
      IsShapeShanten before .mentsu ((distance : Int) - 1) :=
    isShapeShanten_mentsu_of_minimal_mentsuTargetDistance_one_more
      distance before pair melds hdistance hsum hbeforeValid
      hvalid hmelds hminimalTarget
  exact ⟨(distance : Int) - 1, hshape⟩

lemma sum_countsOfTiles_mentsuTarget_of_thirteen_tile_count
    (hand : Hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (pair : Tile) (melds : List Meld)
    (hmelds : melds.length + hand.fixedMelds = 4) :
    (∑ tile : Tile, countsOfTiles (mentsuTarget pair melds) tile) =
      (∑ tile : Tile, hand.counts tile) + 1 := by
  calc
    _ = (mentsuTarget pair melds).card := by
      exact countsOfTiles_sum_eq_card (mentsuTarget pair melds)
    _ = 2 + 3 * melds.length := by
      simp [mentsuTarget, Multiset.card_add, pairTiles_card,
        meldsTiles_card]
    _ = tileCount hand + 1 := by omega
    _ = (∑ tile : Tile, hand.counts tile) + 1 := by rfl

set_option maxHeartbeats 1000000 in
lemma exists_mentsuTarget_reaching_isShapeShanten_distance
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) (hshape : IsShapeShanten hand .mentsu value) :
    ∃ distance : Nat, ∃ pair melds,
      (distance : Int) = value + 1 ∧
      melds.length + hand.fixedMelds = 4 ∧
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuTarget pair melds))) ∧
      mentsuTargetDistance hand pair melds = distance ∧
      ReachesCompletion Complete .mentsu hand distance := by
  rcases hshape with ⟨_, distance, hvalue, hreach, hminimal⟩
  obtain ⟨pair, melds, hmelds, hvalid, hdistanceLE⟩ :=
    exists_mentsuTarget_distance_le_of_reachesCompletion
      hand distance hreach
  have hsum :=
    sum_countsOfTiles_mentsuTarget_of_thirteen_tile_count
      hand hstanding pair melds hmelds
  obtain ⟨targetDistance, htargetDistance, htargetReach⟩ :=
    reachesCompletion_mentsu_of_one_more_target_tile
      hand (countsOfTiles (mentsuTarget pair melds)) pair melds
      hsum hbeforeValid hvalid hmelds
      (targetHand_hasTiles_countsOfTiles hand
        (mentsuTarget pair melds))
  have hreachDistance :
      targetDistance = mentsuTargetDistance hand pair melds := by
    calc
      targetDistance =
          countDeficit hand.counts
            (countsOfTiles (mentsuTarget pair melds)) :=
        htargetDistance
      _ = mentsuTargetDistance hand pair melds :=
        (mentsuTargetDistance_eq_countDeficit hand pair melds).symm
  have htargetLE : targetDistance ≤ distance := by
    calc
      targetDistance = mentsuTargetDistance hand pair melds :=
        hreachDistance
      _ ≤ distance := hdistanceLE
  have hdistanceLEtarget : distance ≤ targetDistance := by
    by_contra hnot
    have hshorter : targetDistance < distance := by omega
    exact hminimal targetDistance hshorter htargetReach
  have htargetDistanceEq : mentsuTargetDistance hand pair melds = distance := by
    omega
  have htargetDistanceEqNat : targetDistance = distance := by
    calc
      targetDistance = mentsuTargetDistance hand pair melds :=
        hreachDistance
      _ = distance := htargetDistanceEq
  refine ⟨distance, pair, melds, hvalue, hmelds, hvalid,
    htargetDistanceEq, ?_⟩
  rw [← htargetDistanceEqNat]
  exact htargetReach

set_option maxHeartbeats 1000000 in
lemma exists_minimal_mentsuTarget_of_isShapeShanten_mentsu
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) (hshape : IsShapeShanten hand .mentsu value) :
    ∃ distance : Nat, ∃ pair melds,
      (distance : Int) = value + 1 ∧
      melds.length + hand.fixedMelds = 4 ∧
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuTarget pair melds))) ∧
      mentsuTargetDistance hand pair melds = distance ∧
      ReachesCompletion Complete .mentsu hand distance ∧
      ∀ otherPair otherMelds,
        otherMelds.length + hand.fixedMelds = 4 →
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuTarget otherPair otherMelds))) →
        mentsuTargetDistance hand pair melds ≤
          mentsuTargetDistance hand otherPair otherMelds := by
  obtain ⟨distance, pair, melds, hvalue, hmelds, hvalid,
      hdistance, hreach⟩ :=
    exists_mentsuTarget_reaching_isShapeShanten_distance
      hand hbeforeValid hstanding value hshape
  rcases hshape with ⟨_, actualDistance, hactualValue, _, hminimal⟩
  have hdistanceEq : distance = actualDistance := by omega
  refine ⟨distance, pair, melds, hvalue, hmelds, hvalid,
    hdistance, hreach, ?_⟩
  intro otherPair otherMelds hotherMelds hotherValid
  have hsumOther :=
    sum_countsOfTiles_mentsuTarget_of_thirteen_tile_count
      hand hstanding otherPair otherMelds hotherMelds
  obtain ⟨otherDistance, hotherDistance, hotherReach⟩ :=
    reachesCompletion_mentsu_of_one_more_target_tile
      hand (countsOfTiles (mentsuTarget otherPair otherMelds))
      otherPair otherMelds hsumOther hbeforeValid hotherValid
      hotherMelds
      (targetHand_hasTiles_countsOfTiles hand
        (mentsuTarget otherPair otherMelds))
  have hotherDistanceEq :
      otherDistance =
        mentsuTargetDistance hand otherPair otherMelds := by
    calc
      otherDistance =
          countDeficit hand.counts
            (countsOfTiles (mentsuTarget otherPair otherMelds)) :=
        hotherDistance
      _ = mentsuTargetDistance hand otherPair otherMelds :=
        (mentsuTargetDistance_eq_countDeficit hand otherPair otherMelds).symm
  by_contra hnotMinimal
  have hshorter : otherDistance < actualDistance := by
    omega
  exact hminimal otherDistance hshorter hotherReach

lemma isShapeShanten_mentsu_iff_exists_minimal_mentsuTarget
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) :
    IsShapeShanten hand .mentsu value ↔
      ∃ distance : Nat, ∃ pair melds,
        (distance : Int) = value + 1 ∧
        melds.length + hand.fixedMelds = 4 ∧
        (∑ tile : Tile,
          countsOfTiles (mentsuTarget pair melds) tile) =
          (∑ tile : Tile, hand.counts tile) + 1 ∧
        ValidCounts
          (targetHand hand
            (countsOfTiles (mentsuTarget pair melds))) ∧
        mentsuTargetDistance hand pair melds = distance ∧
        ∀ otherPair otherMelds,
          otherMelds.length + hand.fixedMelds = 4 →
          ValidCounts
            (targetHand hand
              (countsOfTiles (mentsuTarget otherPair otherMelds))) →
          mentsuTargetDistance hand pair melds ≤
            mentsuTargetDistance hand otherPair otherMelds := by
  constructor
  · intro hshape
    obtain ⟨distance, pair, melds, hvalue, hmelds, hvalid,
        hdistance, _, hminimal⟩ :=
      exists_minimal_mentsuTarget_of_isShapeShanten_mentsu
        hand hbeforeValid hstanding value hshape
    have hsum :=
      sum_countsOfTiles_mentsuTarget_of_thirteen_tile_count
        hand hstanding pair melds hmelds
    exact ⟨distance, pair, melds, hvalue, hmelds, hsum, hvalid,
      hdistance, hminimal⟩
  · rintro ⟨distance, pair, melds, hvalue, hmelds, hsum,
      hvalid, hdistance, hminimal⟩
    have hshape :
        IsShapeShanten hand .mentsu ((distance : Int) - 1) :=
      isShapeShanten_mentsu_of_minimal_mentsuTargetDistance_one_more
        distance hand pair melds hdistance hsum hbeforeValid
        hvalid hmelds hminimal
    have hvalueEq : (distance : Int) - 1 = value := by omega
    exact hvalueEq ▸ hshape

private def canonicalMentsuPair : Tile :=
  .honor ⟨0, by omega⟩

private def canonicalMentsuMelds : Nat → List Meld
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

private lemma canonicalMentsuMelds_length
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4) :
    (canonicalMentsuMelds fixedMelds).length + fixedMelds = 4 := by
  have hcases :
      fixedMelds = 0 ∨ fixedMelds = 1 ∨ fixedMelds = 2 ∨
        fixedMelds = 3 ∨ fixedMelds = 4 := by omega
  rcases hcases with h | h | h | h | h
  all_goals subst fixedMelds <;> simp [canonicalMentsuMelds]

private lemma canonicalMentsuTarget_validCounts
    (fixedMelds : Nat) (hfixed : fixedMelds ≤ 4) :
    ∀ tile,
      (mentsuTarget canonicalMentsuPair
        (canonicalMentsuMelds fixedMelds)).count tile ≤ 4 := by
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
          simp [canonicalMentsuPair, canonicalMentsuMelds,
            mentsuTarget, pairTiles, meldsTiles, meldTiles]
    | honor rank =>
        fin_cases rank <;>
          simp [canonicalMentsuPair, canonicalMentsuMelds,
            mentsuTarget, pairTiles, meldsTiles, meldTiles]

set_option maxHeartbeats 1000000 in
lemma exists_mentsuShanten_as_min_validTargetDistance
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) :
    ∃ distance,
      distance ∈ validMentsuTargetDistances hand ∧
      (∀ otherDistance,
        otherDistance ∈ validMentsuTargetDistances hand →
          distance ≤ otherDistance) ∧
      IsShapeShanten hand .mentsu ((distance : Int) - 1) := by
  have hfixed : hand.fixedMelds ≤ 4 := by omega
  have hmelds :=
    canonicalMentsuMelds_length hand.fixedMelds hfixed
  have hvalid :
      ValidCounts
        (targetHand hand
          (countsOfTiles
            (mentsuTarget canonicalMentsuPair
              (canonicalMentsuMelds hand.fixedMelds)))) := by
    intro tile
    change
      (mentsuTarget canonicalMentsuPair
        (canonicalMentsuMelds hand.fixedMelds)).count tile ≤ 4
    exact canonicalMentsuTarget_validCounts
      hand.fixedMelds hfixed tile
  obtain ⟨distance, hdistanceMem, hminimalDistance⟩ :=
    exists_min_validMentsuTargetDistance hand hfixed
      ⟨canonicalMentsuPair, canonicalMentsuMelds hand.fixedMelds,
        hmelds, hvalid⟩
  obtain ⟨pair, melds, htargetMelds, htargetValid, htargetDistance⟩ :=
    (mem_validMentsuTargetDistances_iff
      hand hfixed distance).mp hdistanceMem
  have hsum :=
    sum_countsOfTiles_mentsuTarget_of_thirteen_tile_count
      hand hstanding pair melds htargetMelds
  have hminimalTarget :
      ∀ otherPair otherMelds,
        otherMelds.length + hand.fixedMelds = 4 →
          ValidCounts
            (targetHand hand
              (countsOfTiles (mentsuTarget otherPair otherMelds))) →
          mentsuTargetDistance hand pair melds ≤
            mentsuTargetDistance hand otherPair otherMelds := by
    intro otherPair otherMelds hotherMelds hotherValid
    have hotherDistanceMem :
        mentsuTargetDistance hand otherPair otherMelds ∈
          validMentsuTargetDistances hand :=
      (mem_validMentsuTargetDistances_iff
        hand hfixed
        (mentsuTargetDistance hand otherPair otherMelds)).mpr
        ⟨otherPair, otherMelds, hotherMelds, hotherValid, rfl⟩
    calc
      mentsuTargetDistance hand pair melds = distance :=
        htargetDistance
      _ ≤ mentsuTargetDistance hand otherPair otherMelds :=
        hminimalDistance _ hotherDistanceMem
  have hshape :
      IsShapeShanten hand .mentsu ((distance : Int) - 1) :=
    isShapeShanten_mentsu_of_minimal_mentsuTargetDistance_one_more
      distance hand pair melds htargetDistance hsum hbeforeValid
      htargetValid htargetMelds hminimalTarget
  exact ⟨distance, hdistanceMem, hminimalDistance, hshape⟩

lemma mentsuTargetMinimumSearch_eq_some_iff
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13)
    (value : Int) :
    mentsuTargetMinimumSearch hand = some value ↔
      IsShapeShanten hand .mentsu value := by
  obtain ⟨distance, hmem, hminimal, hshape⟩ :=
    exists_mentsuShanten_as_min_validTargetDistance
      hand hbeforeValid hstanding
  let distances := validMentsuTargetDistances hand
  have hnonempty : distances.Nonempty := ⟨distance, hmem⟩
  have hdistance :
      distances.min' hnonempty = distance := by
    apply Nat.le_antisymm
    · exact Finset.min'_le distances distance hmem
    · exact hminimal _ (Finset.min'_mem distances hnonempty)
  have hsearch :
      mentsuTargetMinimumSearch hand =
        some ((distance : Int) - 1) := by
    simp [mentsuTargetMinimumSearch, distances, hnonempty, hdistance]
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

lemma exists_isShapeShanten_mentsu_of_valid_thirteen_tile_count
    (hand : Hand) (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) :
    ∃ value : Int, IsShapeShanten hand .mentsu value := by
  obtain ⟨distance, _, _, hshape⟩ :=
    exists_mentsuShanten_as_min_validTargetDistance
      hand hbeforeValid hstanding
  exact ⟨(distance : Int) - 1, hshape⟩

lemma exists_isShapeShanten_mentsu_of_thirteenTileHand
    (hand : Hand) (hthirteen : IsThirteenTileHand hand) :
    ∃ value : Int, IsShapeShanten hand .mentsu value := by
  rcases hthirteen with ⟨hfixed, hcount, hvalid⟩
  apply exists_isShapeShanten_mentsu_of_valid_thirteen_tile_count
    hand hvalid
  rw [hfixed, hcount]

lemma exists_isOverallShanten_of_thirteenTileHand
    (hand : Hand) (hthirteen : IsThirteenTileHand hand) :
    ∃ value : Int, IsOverallShanten hand value := by
  obtain ⟨mentsuValue, hmentsu⟩ :=
    exists_isShapeShanten_mentsu_of_thirteenTileHand hand hthirteen
  have hmentsuOption :
      ShapeShanten hand .mentsu = some mentsuValue :=
    (shapeShanten_eq_some_iff).2 hmentsu
  unfold IsOverallShanten OverallShanten
  rw [hmentsuOption]
  cases hseven : ShapeShanten hand .sevenPairs <;>
    cases horphans : ShapeShanten hand .thirteenOrphans <;>
      simp [minOption, hseven, horphans]

lemma MentsuBlockDecomposition.exists_isShapeShanten
    {hand : Hand} (decomposition : MentsuBlockDecomposition hand)
    (hbeforeValid : ValidCounts hand)
    (hstanding : tileCount hand + 3 * hand.fixedMelds = 13) :
    ∃ value : Int, IsShapeShanten hand .mentsu value := by
  let melds :=
    decomposition.melds ++
      taatsuCompletionMelds decomposition.taatsus
  have htarget :
      mentsuTarget decomposition.pair melds =
        decomposition.completedTarget := by
    rw [MentsuBlockDecomposition.completedTarget_eq]
    rfl
  have hmelds :
      melds.length + hand.fixedMelds = 4 := by
    dsimp [melds]
    exact decomposition.completedMeldCount
  have htargetCard :
      (mentsuTarget decomposition.pair melds).card =
        tileCount hand + 1 := by
    rw [htarget, MentsuBlockDecomposition.completedTarget_eq]
    simp [Multiset.card_add, pairTiles_card, meldsTiles_card,
      List.length_append, taatsuCompletionMelds_length]
    have hblocks := decomposition.blocks
    omega
  have hsum :
      (∑ tile : Tile,
        countsOfTiles (mentsuTarget decomposition.pair melds) tile) =
        (∑ tile : Tile, hand.counts tile) + 1 := by
    calc
      _ = (mentsuTarget decomposition.pair melds).card := by
        exact countsOfTiles_sum_eq_card
          (mentsuTarget decomposition.pair melds)
      _ = tileCount hand + 1 := htargetCard
      _ = (∑ tile : Tile, hand.counts tile) + 1 := by
        rfl
  have hvalid :
      ValidCounts
        (targetHand hand
          (countsOfTiles (mentsuTarget decomposition.pair melds))) := by
    rw [htarget]
    exact decomposition.validCounts_completedTarget
  exact exists_isShapeShanten_mentsu_of_valid_mentsuTarget_one_more
    hand hbeforeValid
    ⟨decomposition.pair, melds, hmelds, hsum, hvalid⟩

lemma mentsuTarget_count_le_stateHistoryTiles
    (state : MentsuSearchState) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuTarget pair state.meldHistory.reverse).count tile ≤
        (stateHistoryTiles state).count tile := by
  intro tile
  simp [mentsuTarget, stateHistoryTiles, pairHistoryTiles, hpair,
    Multiset.count_add]

lemma mentsuTarget_count_le_used
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuTarget pair state.meldHistory.reverse).count tile ≤
        state.used.count tile := by
  intro tile
  rw [reachableWithin_used_eq_historyTiles hand fuel state hreachable]
  exact mentsuTarget_count_le_stateHistoryTiles state pair hpair tile

lemma mentsuTarget_count_le_hand
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin hand fuel state) (pair : Tile)
    (hpair : state.pair = some pair) :
    ∀ tile,
      (mentsuTarget pair state.meldHistory.reverse).count tile ≤
        hand.counts tile := by
  intro tile
  exact le_trans
    (mentsuTarget_count_le_used hand fuel state hreachable pair hpair tile)
    (reachableWithin_used_subset hand fuel state hreachable tile)

lemma mentsuTarget_hasMeldCount_of_complete
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcomplete : IsMentsuSearchComplete hand state) :
    HasMentsuMeldCount hand state.meldHistory.reverse := by
  have hlength := reachableWithin_melds_eq_history_length
    hand fuel state hreachable
  rcases hcomplete with ⟨hmelds, _⟩
  unfold HasMentsuMeldCount
  simpa [List.length_reverse, hlength] using hmelds

lemma mentsuTargetOfState_exists_of_complete
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcomplete : IsMentsuSearchComplete hand state) :
    ∃ target, mentsuTargetOfState state = some target ∧
      HasMentsuMeldCount hand state.meldHistory.reverse := by
  cases hpair : state.pair with
  | none =>
      exfalso
      simpa [hpair] using hcomplete.2
  | some pair =>
      refine ⟨mentsuTarget pair state.meldHistory.reverse, ?_, ?_⟩
      · rw [mentsuTargetOfState, hpair]
        rfl
      · exact mentsuTarget_hasMeldCount_of_complete
          hand fuel state hreachable hcomplete

lemma completedMeldsForState_hasMeldCount
    (hand : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin hand fuel state)
    (hcount : state.melds + state.taatsu + hand.fixedMelds = 4) :
    HasMentsuMeldCount hand (completedMeldsForState state) := by
  have hmelds := reachableWithin_melds_eq_history_length
    hand fuel state hreachable
  have htaatsu := reachableWithin_taatsu_eq_history_length
    hand fuel state hreachable
  unfold HasMentsuMeldCount
  rw [completedMeldsForState_length, ← hmelds, ← htaatsu]
  omega

lemma complete_mentsu_of_blockSearch
    (before : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcomplete : IsMentsuBlockSearchComplete before state)
    (hvalid : ∀ pair, state.pair = some pair →
      ValidCounts
        (targetHand before
          (countsOfTiles (completedTargetForState state pair)))) :
    ∃ pair,
      Complete .mentsu
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      refine ⟨pair, ?_⟩
      apply complete_mentsu_completedTarget before state pair
      · exact hvalid pair hstatePair
      · exact completedMeldsForState_hasMeldCount
          before fuel state hreachable hcount

lemma complete_mentsu_of_blockSearch_of_copyLimit
    (before : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithin before fuel state)
    (hcomplete : IsMentsuBlockSearchComplete before state)
    (hcopy : CompletionRespectsCopyLimit state) :
    ∃ pair,
      Complete .mentsu
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  rcases hcomplete with ⟨hcount, hpair⟩
  cases hstatePair : state.pair with
  | none =>
      simp [hstatePair] at hpair
  | some pair =>
      refine ⟨pair, ?_⟩
      apply complete_mentsu_completedTarget before state pair
      · exact validCounts_completedTarget_of_copyLimit
          before fuel state hreachable hcopy pair hstatePair
      · exact completedMeldsForState_hasMeldCount
          before fuel state hreachable hcount

lemma complete_mentsu_of_constrainedBlockSearch
    (before : Hand) (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithinWithCopyLimit before fuel state)
    (hcomplete : IsMentsuBlockSearchComplete before state) :
    ∃ pair,
      Complete .mentsu
        (targetHand before
          (countsOfTiles (completedTargetForState state pair))) := by
  exact complete_mentsu_of_blockSearch_of_copyLimit
    before fuel state
    (reachableWithinWithCopyLimit_to_reachableWithin
      before fuel state hreachable)
    hcomplete
    (reachableWithinWithCopyLimit_copyLimit before fuel state hreachable)

lemma exists_isShapeShanten_mentsu_of_constrainedBlockSearch
    (before : Hand) (hbeforeValid : ValidCounts before)
    (hstanding : tileCount before + 3 * before.fixedMelds = 13)
    (fuel : Nat) (state : MentsuSearchState)
    (hreachable : reachableWithinWithCopyLimit before fuel state)
    (hcomplete : IsMentsuBlockSearchComplete before state) :
    ∃ value : Int, IsShapeShanten before .mentsu value := by
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
          mentsuTarget pair melds =
            completedTargetForState state pair := by
        rfl
      have hsum' :=
        completedTargetForState_sum_of_blockCount
          before fuel state hreachable' hcount pair
      have hsum :
          (∑ tile : Tile,
            countsOfTiles (mentsuTarget pair melds) tile) =
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
            (targetHand before (countsOfTiles (mentsuTarget pair melds))) := by
        rw [htarget]
        exact validCounts_completedTarget_of_copyLimit
          before fuel state hreachable' hcopy pair hstatePair
      exact exists_isShapeShanten_mentsu_of_valid_mentsuTarget_one_more
        before hbeforeValid
        ⟨pair, melds, hmelds, hsum, hvalid⟩

end Shanten
