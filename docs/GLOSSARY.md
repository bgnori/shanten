# 用語集

この文書は、リポジトリの文書・Go契約・Lean4モデルで使う用語を、初めて
読む人が同じ意味で解釈できるように整理したものです。

## 読み方

- **正式語**: このリポジトリで優先して使う表記。
- **別名**: 一般に使われる表記。ただし、意味が同じとは限らない場合は注意書きを
  付けています。
- **範囲**: `[麻雀]` はゲーム上の概念、`[Go]` はGo契約、`[Lean]` はLean
  の定義、`[数学]` は証明・仕様の概念、`[IT]` はソフトウェア設計の概念です。
- 英語の識別子は、説明中ではバッククォートで囲みます。識別子が似ていても、
  GoとLeanで意味が異なる場合は別の項目として扱います。

## まず押さえる区別

| 混同しやすい語 | このリポジトリでの区別 |
|---|---|
| **面子** と **ブロック** | 面子は完成した3枚組（槓はゲーム上4枚でも1面子）。ブロックは完成面子または搭子で、未完成の面子手にも使う。 |
| **雀頭** と **対子形搭子** | どちらも同じ牌2枚だが、雀頭は面子手で別枠の1組として選んだもの。対子形搭子は面子系ブロックの候補。 |
| **固定面子** と Leanの `Meld` | Go契約の固定面子は副露・暗槓など入力に含まれる面子。Leanの `Meld` は現在、探索中の（主に門前の）完成面子を表す。 |
| **牌種** と **牌** | 牌種は「5萬」のような種類。牌は実物1枚を指すことがある。Leanの `Tile` は牌種で、個々の牌の識別子ではない。 |
| **シャンテン数** と **距離** | 距離0は完成、距離1はテンパイ。シャンテン数は距離から1を引いた値なので、完成は-1、テンパイは0。 |
| **適用不可** と **未実装・非対応** | 七対子・国士無双が固定面子のため対象外なのは適用不可。計算器が機能を持たないのは非対応（`ErrUnsupported`）。 |
| **4枚制限** と **見えている牌** | 4枚制限は完成形・遷移が実在する牌種容量を超えないための不変条件。見えている牌や残り枚数を使った待ちの評価とは別。 |

## 一般・データ表現

### 用語

- **牌種 (tile kind)** `[麻雀][Lean]`
  牌の種類。正規化後は萬子・筒子・索子の数牌と字牌を合わせた34種類。
  `Tile` はこの牌種を表す。赤5は計算時に通常の5へ統合するため、Leanの
  `Tile` では別種ではない。

- **牌 (tile)** `[麻雀]`
  実物の1枚、または文脈によって牌種の略称。枚数制約を論じるときは、牌種ごとの
  枚数と混同しないよう「牌種」と書く。

- **数牌 (suited tile)** `[麻雀]`
  萬子・筒子・索子の1から9。Leanでは `Tile.suited suit rank`。

- **字牌 (honor)** `[麻雀]`
  東南西北白發中。Leanでは `Tile.honor rank`。

- **么九牌 (terminal/orphan)** `[麻雀]`
  各色の1・9と字牌。国士無双の対象牌種を指すときは、字牌を含む
  「么九牌・字牌」全13種という意味で使う。

- **正規化 (normalization)** `[Go][Lean]`
  赤5など入力表現の差を、計算で使う標準表現へ写すこと。本契約では赤5を
  通常の5に合算する。正規化は入力そのものを変更せず、シャンテンの意味を
  変えてはならない。

- **カウント (count)** `[一般][Go][Lean]`
  牌種ごとの枚数。Goでは `Counts37` の各要素、Leanでは `Tile → Nat` で表す。
  手牌全体の枚数とは別に、特定の牌種のカウントを指すことがある。

- **牌種容量 / 4枚制限 (copy limit)** `[麻雀][数学]`
  1牌種につき通常4枚までという制約。`ValidCounts` や
  `CompletionRespectsCopyLimit` が表現する。これは「その牌が山に残っている
  か」ではなく、完成形が5枚目を要求していないかを確認する条件。

- **多重集合 (multiset)** `[数学][Lean]`
  順序を無視し、要素の重複回数だけを持つ集合。Leanの `Multiset Tile` は
  牌の組み合わせを表す。`List` と違って並び順は意味を持たない。

- **有限集合 (finite set)** `[数学][Lean]`
  重複を持たない集合。Leanの `Finset Tile` は牌種の集合、例えば「存在する
  牌種」や「七対子で選んだ7種類」を表す。多重集合とは別物。

- **有限型 (finite type)** `[Lean]`
  要素を有限個列挙できる型。`Fintype` により `Tile` や `Suit` の全要素を
  列挙でき、総和や有限探索に使える。

## 麻雀用語

- **手牌 (hand)** `[麻雀]`
  計算対象の牌の状態。本リポジトリでは、Goの `Input` は副露を除く
  `Standing` と固定面子 `Melds` を分けて持つ。これは「門前」や「立直」を
  宣言したことを意味しない。Leanの `Hand` は
  `counts` と `fixedMelds` を持つ抽象モデルで、現状は固定面子の牌内容を
  保持しない。

- **手元牌 (standing tiles)** `[麻雀][Go]`
  固定面子に含まれない手牌。Goの `Input.Standing` は暗槓を含むすべての
  `Melds` を除いた枚数である。「門前」とは副露していない状態を指す場合も
  あるため、この契約では状態名として「standing」を優先する。

- **固定面子 (fixed meld)** `[麻雀][Go]`
  副露面子または暗槓など、入力時点ですでに確定している面子。面子手では
  面子1個として数える。暗槓は門前扱いを保つことがあるが、七対子・国士無双を
  適用可能にはしない。

- **面子 (meld)** `[麻雀]`
  完成した組。順子または刻子を基本とし、槓は牌を4枚使うが面子数では1個と
  数える。未完成の2枚組を面子とは呼ばず、搭子と呼ぶ。

- **順子 (sequence / chi)** `[麻雀][Go][Lean]`
  同じ種類の連続した3枚。例は3・4・5萬。Goの `Chi` は固定順子、
  Leanの `Meld.sequence` は順子の牌種集合を表す。

- **刻子 (triplet / pon)** `[麻雀][Go][Lean]`
  同じ牌種3枚。Goの `Pon` は固定刻子、Leanの `Meld.triplet` は完成した
  刻子を表す。

- **槓 (kan)** `[麻雀][Go]`
  同じ牌種4枚からなる固定面子。`Ankan`（暗槓）、`Daiminkan`（大明槓）、
  `Kakan`（加槓）を区別する。`Kakan` は元のポンに4枚目を加えた一つの
  面子であり、ポンと別の面子として数えない。

- **対子 (pair)** `[麻雀]`
  同じ牌種2枚の組。面子手の雀頭にも、面子手の対子形搭子にもなりうる。
  七対子では異なる7牌種それぞれの対を指す。

- **雀頭 (head / pair)** `[麻雀][Lean]`
  面子手で面子系ブロック4個とは別に必要な1対。Leanの面子手探索では
  `MentsuHandSearchState.pair : Option Tile` が候補の有無を表す。

- **搭子 (taatsu)** `[麻雀][Lean]`
  1枚補えば面子になる未完成の2枚組。対子形搭子と順子形搭子がある。
  Leanの `Taatsu.pair` と `Taatsu.sequence` が対応する。両面・嵌張などの
  呼び方は麻雀上の待ちの説明であり、モデル上は順子形搭子として扱う。

- **ブロック (block)** `[麻雀][プロジェクト]`
  面子手の面子系部品。完成面子または搭子を指す。未完成分解は
  **4ブロック＋雀頭**、完成形は**4面子＋雀頭**と表現する。

- **面子手 (mentsu hand)** `[麻雀]`
  4面子と1雀頭からなる形。固定面子も4面子の一部として数える。
  Leanの `Shape.mentsuHand` がこの形を表す。

- **七対子 (seven pairs)** `[麻雀]`
  異なる7牌種の対7組からなる特殊形。固定面子がある手には適用しない。
  Leanの `Shape.sevenPairs` がこの形を表す。

- **国士無双 (thirteen orphans / kokushi)** `[麻雀]`
  么九牌・字牌13種を1枚ずつそろえ、そのうち1種を対子にする特殊形。
  固定面子がある手には適用しない。Leanの `Shape.thirteenOrphans` が表す。

- **完成 / 和了形 (completion)** `[麻雀][数学]`
  選択した形の必要条件を満たした状態。ここでは役・フリテン・見逃し・
  流し満貫などを評価せず、形の構造だけを判定する。

- **テンパイ (tenpai)** `[麻雀]`
  1回の改善で完成できる状態。この契約の数値は `0`。

- **シャンテン数 (shanten)** `[麻雀][プロジェクト]`
  完成までに必要な改善回数から1を引いた値。完成は `-1`、テンパイは `0`、
  1シャンテンは `1`。Goの `Result` とLeanの `ShapeShanten` はこの符号規約を
  共有する。

- **形 (shape)** `[数学][Lean]`
  面子手・七対子・国士無双のいずれか。Leanの `Shape` はこの3候補を列挙する
  型であり、一般的な「形状」という意味の語と区別する。

- **適用可能性 (applicability)** `[数学][Go][Lean]`
  その形を手牌に対して評価してよいか。面子手は常に適用可能。七対子と
  国士無双は固定面子がない場合だけ適用可能。適用不可はエラーではない。

## Go・情報技術の用語

- **契約 (contract)** `[IT][Go]`
  型、入力制約、結果の意味、エラー、所有権・決定性など、実装が守る境界。
  このリポジトリのGoパッケージは計算器そのものではなく、
  `aka37-shanten/v2` 契約を定義する。

- **API / インターフェース** `[IT][Go]`
  呼び出し側から見える型と操作の境界。Goの `Calculator` インターフェースは
  `Calculate(Input) (Result, error)` だけを要求する。

- **アダプター (adapter)** `[IT]`
  Go契約の入力・出力を、特定の計算バックエンドの形式へ変換する層。入力検証、
  赤5の正規化、結果検証、エラーのラッピングを担う。バックエンド自体とは別。

- **バックエンド (backend)** `[IT]`
  実際に数値計算を行う交換可能な実装。v1パッケージには含まれず、将来の
  アダプターから利用する。

- **能力 (capability)** `[IT]`
  バックエンドが特定の形を計算できること。形が適用不可なのと、バックエンドが
  未対応なのは別である。未対応は `ErrUnsupported`。

- **センチネルエラー (sentinel error)** `[Go]`
  `errors.Is` で分類するための共有エラー値。`ErrInvalidCount` などが該当する。
  呼び出し側はエラーメッセージ文字列ではなく `errors.Is` を使う。

- **所有権 (ownership)** `[IT]`
  入力の変更・保持に関する責任。`Calculator` は入力を変更せず、後で使うために
  スライスを保持してはならない。呼び出し側も計算中は入力を変更しない。

- **決定性 (determinism)** `[IT][数学]`
  同じ正規化済み入力に対して同じ結果を返す性質。探索順やバックエンドの交換が
  あっても契約上の結果は変わらない。

- **サブモジュール (submodule)** `[Git]`
  Gitリポジトリを別リポジトリの特定コミットとして参照する仕組み。親
  `aka37` からは `modules/shanten` として参照する想定で、Goの
  `require` や `replace` とは異なる。

- **ファサード (facade)** `[IT][Lean]`
  内部モジュールをまとめて既存利用者に見せる入口。最上位の `Shanten.lean` は
  `Core` などをimportする互換入口である。

- **動的計画法 (dynamic programming, DP)** `[アルゴリズム]`
  部分問題の状態を再利用して有限探索を行う方法。面子手では、牌を使った量、
  雀頭・面子・搭子の履歴などを `MentsuHandSearchState` に保存する。

## Lean4・数学的証明の用語

- **型 (type)** `[Lean][数学]`
  値の種類を表すもの。`Tile` や `Hand` は型であり、型の違いにより不正な
  値の扱いをコンパイル時に制限できる。

- **命題 (proposition)** `[数学][Lean]`
  真偽を持つ主張。Leanでは `Prop` の値として表現され、証明がその命題の
  値になる。

- **述語 (predicate)** `[数学][Lean]`
  入力に対して命題を返す関数。`ValidCounts hand`、
  `Applicable shape hand`、`Complete shape hand` などが述語。

- **定義 (definition)** `[Lean]`
  `def` で導入する計算可能または論理的な名前。例として `tileCount` は
  枚数を計算し、`Complete` は完成条件を定義する。

- **構造体 (structure)** `[Lean]`
  名前付きフィールドを持つ型。`Hand` と `MentsuHandSearchState` が該当する。
  フィールドが満たすべき命題を持つ構造体は、データと不変条件を一緒に扱える。

- **帰納型 (inductive type)** `[Lean][数学]`
  コンストラクタで値を構成する型。`Shape`、`Meld`、`Taatsu` や
  `ReachesCompletion` が該当する。帰納型の各コンストラクタに対する場合分けや
  帰納法で証明する。

- **有限添字 `Fin n`** `[Lean]`
  `0` 以上 `n` 未満の整数を表す型。`Fin 9` は数牌のランク、`Fin 7` は字牌の
  ランクに使い、範囲外のランクを表せないようにする。

- **`Nat` / `Int`** `[Lean]`
  `Nat` は非負整数で、枚数・距離・個数に使う。`Int` は負数を含む整数で、
  完成を`-1`とするシャンテン値に使う。

- **`Option`** `[Lean]`
  値がない可能性を `none`、ある値を `some value` で表す型。
  `MentsuHandSearchState.pair` は雀頭候補がまだない状態を `none` で表す。
  `ShapeShanten` の `none` は値が存在しない（通常は適用不可または到達不能）
  ことを表す。

- **証明 (proof)** `[数学][Lean]`
  命題が成り立つことをLeanの規則で検査可能な形にしたもの。証明はコメントや
  テスト結果ではなく、Leanカーネルが受理する項である。

- **補題 (lemma)** `[数学][Lean]`
  大きな定理の証明に再利用する名前付き命題。`theorem` と同じくカーネルで
  検査されるが、役割や粒度を示す命名上の区別である。

- **定理 (theorem)** `[数学][Lean]`
  証明済みの命題。`lemma` と本質的な検査機構は同じで、重要な結果や外部に
  示す結果を `theorem` と呼ぶことが多い。

- **存在証明 / witness** `[数学][Lean]`
  `∃ x, P x` を満たす具体的な `x` と、その性質の証明。完成する面子列や
  到達距離を「存在する」とだけ言わず、証明内で取り出せるデータとして扱う。

- **同値 (`iff`)** `[数学][Lean]`
  `P ↔ Q`。`P` から `Q` と `Q` から `P` の両方向を証明したもの。
  探索アルゴリズムと宣言的仕様が同じ意味だと示すときに使う。

- **不変条件 (invariant)** `[数学][アルゴリズム]`
  遷移や帰納の前後で保たれる条件。例は「使用した牌が手牌のカウントを
  超えない」「牌種カウントが4以下」「固定面子数が変わらない」。

- **到達可能 (reachable)** `[数学][Lean]`
  初期状態から、定義された遷移を有限回適用して状態へ到達できること。
  `reachableWithin` は指定した燃料（選択回数）での到達を表す。

- **遷移 (step / transition)** `[数学][アルゴリズム]`
  ある状態から次の状態へ進む1回の操作。`HandStep` は牌を引く、または1枚を
  別の牌種に交換する改善操作、`NextMentsuHandState` は面子手DPの1選択を表す。

- **最短距離 (minimal distance)** `[数学]`
  到達可能な距離のうち最小のもの。距離0が完成、距離1がテンパイになるため、
  シャンテン値は最短距離から1を引く。

- **健全性 (soundness)** `[数学][検証]`
  計算器が「完成」と報告したものが、宣言的な完成条件を実際に満たす性質。

- **完全性 (completeness)** `[数学][検証]`
  宣言的に存在する有効な完成候補を、探索が取りこぼさない性質。健全性だけでは
  正しい最小シャンテン値を保証できない。

## プロジェクト固有の識別子

| 識別子 | 意味 | 主な場所 |
|---|---|---|
| `Counts37` | 赤5を別要素として保持する37要素のGoカウント配列。計算前に通常5へ合算する。 | [`shanten.go`](../shanten.go) |
| `Result.MentsuHand` | Go契約における面子手のシャンテン値。常に適用可能で、完成は`-1`。 | [`shanten.go`](../shanten.go) |
| `Hand` | Leanの手牌抽象モデル。`counts` と固定面子数を持つ。固定面子の牌内容はまだ持たない。 | [`Shanten/Core.lean`](../Shanten/Core.lean) |
| `Tile` | Leanの正規化済み牌種。34種類相当で、赤5を分離しない。 | [`Shanten/Core.lean`](../Shanten/Core.lean) |
| `Meld` | Leanで表す完成面子。`triplet` または `sequence`。Goの入力固定面子と同義ではない。 | [`Shanten/Core.lean`](../Shanten/Core.lean) |
| `Taatsu` | Leanで表す未完成の2枚組。対子形または順子形。 | [`Shanten/MentsuHand.lean`](../Shanten/MentsuHand.lean) |
| `ValidCounts` | 各牌種のカウントが4以下であるという述語。 | [`Shanten/Core.lean`](../Shanten/Core.lean) |
| `IsThirteenTileHand` | 固定面子なし、手元牌13枚、かつ4枚制限を満たすという述語。 | [`Shanten/Core.lean`](../Shanten/Core.lean) |
| `Shape` | `mentsuHand`、`sevenPairs`、`thirteenOrphans` の形の列挙型。 | [`Shanten/Specification.lean`](../Shanten/Specification.lean) |
| `Applicable` | 形を評価できるかを表す述語。特殊形は固定面子なしの場合だけ真。 | [`Shanten/Specification.lean`](../Shanten/Specification.lean) |
| `Complete` | 指定した形の完成条件。役や待ちの良し悪しは含めない。 | [`Shanten/Specification.lean`](../Shanten/Specification.lean) |
| `HandStep` | 1枚ドローまたは1枚交換による改善遷移。固定面子数は保存する。 | [`Shanten/Specification.lean`](../Shanten/Specification.lean) |
| `ReachesCompletion` | 指定回数の `HandStep` で完成条件へ到達する関係。 | [`Shanten/Specification.lean`](../Shanten/Specification.lean) |
| `ShapeShanten` | 形ごとの最小到達距離をシャンテン値へ変換した、値の候補。 | [`Shanten/Specification.lean`](../Shanten/Specification.lean) |
| `OverallShanten` | 適用可能な形のシャンテン値の最小値。 | [`Shanten/Specification.lean`](../Shanten/Specification.lean) |
| `MentsuHandSearchState` | 面子手DPの状態。使用牌、雀頭、面子・搭子の履歴と個数を持つ。 | [`Shanten/MentsuHand.lean`](../Shanten/MentsuHand.lean) |
| `MentsuHandChoice` | 面子手DPの1分岐。`skip`、雀頭、搭子、面子を選ぶ。 | [`Shanten/MentsuHand.lean`](../Shanten/MentsuHand.lean) |
| `MentsuHandSearch` | 完成面子4個＋雀頭という、現行の面子手探索の完了条件。 | [`Shanten/MentsuHand.lean`](../Shanten/MentsuHand.lean) |
| `MentsuHandBlockSearch` | 面子＋搭子の合計4ブロック＋雀頭というブロック探索の完了条件。 | [`Shanten/MentsuHand.lean`](../Shanten/MentsuHand.lean) |
| `MentsuHandBlockDecomposition` | 面子手を雀頭・完成面子・搭子へ分解した証明付き構造。 | [`Shanten/MentsuHand.lean`](../Shanten/MentsuHand.lean) |
| `target` | 到達したい完成形の牌の多重集合。`mentsuHandTarget` などで構成する。 | [`Shanten/MentsuHand.lean`](../Shanten/MentsuHand.lean) |
| `deficit` | 現在のカウントが目標に不足する枚数。必要な交換・ドローの下限に使う。 | [`Shanten/MentsuHand.lean`](../Shanten/MentsuHand.lean) / [`Shanten/SevenPairs.lean`](../Shanten/SevenPairs.lean) |
| `CompletionRespectsCopyLimit` | 搭子を補充して完成させても、各牌種4枚を超えないという述語。 | [`Shanten/MentsuHand.lean`](../Shanten/MentsuHand.lean) |
| `ReachesExchange` | 交換操作を指定回数つないだ関係。七対子の構成的証明で使う。 | [`Shanten/SevenPairs.lean`](../Shanten/SevenPairs.lean) |
| `PairingExchange` / `PairMakingExchange` | 既存の対を保ちながら、対を作るための交換の分類。 | [`Shanten/SevenPairs.lean`](../Shanten/SevenPairs.lean) |
| `ProtectedPairMakingExchange` | 保護対象の牌種を残したまま対を作る交換の分類。 | [`Shanten/SevenPairs.lean`](../Shanten/SevenPairs.lean) |
| `kokushiDistinctCount` / `kokushiPairCount` | 国士対象13種のうち、登場する種類数／2枚以上ある種類数。 | [`Shanten/Core.lean`](../Shanten/Core.lean) |

## 表記上のルール

1. 最終完成形だけを指すときは「4面子＋雀頭」、未完成の面子手分解を指すときは
   「4ブロック＋雀頭」と書く。
2. 「距離」と「シャンテン数」を同じ数として説明しない。必要なら
   `shanten = distance - 1` と明記する。
3. Goの `Meld` は入力の固定面子、Leanの `Meld` は現行モデルの完成面子として、
   文脈または修飾語を付ける。
4. 「適用不可」は特殊形の仕様上の対象外に限り、未実装・バックエンド非対応には
   「非対応」または `ErrUnsupported` を使う。
5. 「牌」は実物の枚数を、「牌種」は種類の集合・カウントを説明するときに使い分ける。
6. 証明結果を説明するときは、単に「動く」「計算できる」と書かず、
   健全性（誤った完成を認めない）と完全性（有効な候補を漏らさない）を区別する。
