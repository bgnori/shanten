# Leanソースの構造方針

## 結論

現在の [Shanten.lean](../Shanten.lean) は約2200行あり、牌モデル、シャンテン
仕様、交換操作、七対子の構成的証明、最終的な上界定理を一つのモジュールに
含んでいる。

今後ドキュメントコメントが増えることも考慮し、まず次の4ファイルへ分割する。

```text
Shanten/
  Core.lean
  Specification.lean
  SevenPairs.lean
  Bounds.lean
Shanten.lean
```

ここで最上位の `Shanten.lean` は既存の利用箇所との互換性を保つための
facade とし、各モジュールを import する。

```lean
import Shanten.Core
import Shanten.Specification
import Shanten.SevenPairs
import Shanten.Bounds
```

面子手および国士無双のシャンテン数に関する証明が追加されるまでは、
この4ファイルを超える細分化は行わない。証明が追加され、各形の責務や
依存関係が明確になった時点で、必要なら改めて分割を検討する。

## 各ファイルの責務

### `Core.lean`

牌と手牌の基礎モデル、および複数の形で共有する基本補題を置く。

- `Suit`
- `Tile`
- `TileCounts`
- `Hand`
- `Meld`
- `meldTiles`
- `meldsTiles`
- `HasTiles`
- `pairTiles`
- `ValidCounts`
- `tileCount`
- `pairCount`
- `distinctTileCount`
- `presentTiles`
- 牌数・種類数・対子数に関する共有補題
- `IsThirteenTileHand`

このファイルには、特定のシャンテン形や七対子の交換戦略に依存する証明は
置かない。将来、面子手や国士無双の証明を追加するときにも再利用できる
最小限の基礎層とする。

### `Specification.lean`

シャンテンの宣言的な意味と、形に依存しない到達関係を定義する。

- `Shape`
- `Applicable`
- `Complete`
- `HandStep`
- `ReachesCompletion`
- `IsShapeShanten`
- `isShapeShanten_unique`
- `ShapeShanten`
- `shapeShanten_eq_some_iff`
- `OverallShanten`
- `IsOverallShanten`
- `minOption`

`Complete` は当面、標準形・七対子・国士無双を一つの `Shape` による
定義として維持する。各形の証明が揃っていない段階で、無理に形ごとの
完全な仕様ファイルへ分割しない。

### `SevenPairs.lean`

七対子のテンパイ・完成形と、完成形へ到達するための交換操作および
その不変条件をまとめる。

- `IsSevenPairsTenpai`
- `sevenPairsTarget`
- `sevenPairsCompleteCounts`
- `sevenPairsTenpai_decomposition`
- `countDeficit`
- `exchangeDistance`
- `exchangeCounts`
- `exchangeHand`
- `ReachesExchange`
- `PairingExchange`
- `DistinctnessExchange`
- `PairMakingExchange`
- `ProtectedPairMakingExchange`
- `ReachesDistinctness`
- `ReachesPairMaking`
- `ReachesProtectedPairMaking`
- 種類数を7にするための補題
- 対子数を6にするための補題
- 七対子テンパイから完成形へ進む補題

現時点では七対子に関する証明が最も大きなまとまりであるため、他の形の
証明が追加されるまでは、これをさらに細分化しない。

### `Bounds.lean`

各形の到達可能性からシャンテン数の上界を導く、上位レベルの定理を置く。

- `reaches_sevenPairs_completion`
- `overallShanten_le_six_of_thirteenTileHand`
- `shapeShanten_le_six_of_completion_bound`
- `sevenPairsShanten_le_six_of_completion_bound`
- `standardShanten_le_eight_of_completion_bound`
- `overallShanten_le_eight_of_fixedMelds`
- 標準形・国士無双向けの上界定理
- 国士無双の直接計算に関する定理

DPの探索状態・遷移・評価関数そのものは、このファイルには置かない。実行用計算器
と証明で共有する一般形DPは、形の仕様と独立した計算モジュールとして追加する。
`Bounds.lean` は、そのDPが提供する到達性補題をシャンテン数の上界へ変換する層とする。

このファイルは個別の交換操作の詳細を持たず、`Specification.lean` と
`SevenPairs.lean` が提供する定義・補題を組み合わせる層とする。

## 依存関係

基本的な依存方向は次のとおりとする。

```text
Core
 ├── Specification
 ├── SevenPairs
 └── Bounds
       ├── Specification
       └── SevenPairs
```

実際の import は、必要な定義が提供される最小のモジュールを参照する。
`Core` から上位モジュールを import しないこと、また `Specification` と
`SevenPairs` が互いに import しないことを原則とする。循環依存が必要に
なった場合は、共有定義または共有補題を `Core` へ移す。

## 移行方針

分割時は定義の変更とファイル移動を同時に行わず、次の順で進める。

1. 現在の宣言を責務ごとに移動する。
2. `Shanten.lean` を facade にして、既存の import 利用者を維持する。
3. `lake build Shanten` で各段階を検証する。
4. import が安定した後に、関連するドキュメントコメントを各ファイルへ移す。
5. 最後に、旧ファイルに残った重複定義や不要な import を整理する。

この分割では、定義名・namespace・命題の内容を変更しない。したがって、
ファイル構成を整理することによる保守性の改善と、仕様変更による証明の
変化を分離できる。

## 今回は行わないこと

以下は今回の4ファイル分割の対象外とする。

- `Complete` の標準形・七対子・国士無双ごとの完全な分離
- 七対子の証明を交換操作ごとに複数ファイルへ分割すること
- 固定面子の牌内容を `Hand` に追加するモデル変更
- 面子手および国士無双の未完成な証明を先回りして配置すること

計算可能なシャンテン計算器は、面子手の証明を進めるための共通DPとして追加する。
ただし、最適化版の計算器やGo側の実装は、枝刈りのない基準DPとその正当性が確立
した後に着手する。

特に、面子手や国士無双の証明が加わる前に形ごとのファイルを増やすと、
未確定の依存関係を固定してしまう。まず4ファイル構成で責務を分け、
証明が追加された時点で実際の依存グラフを見て再評価する。

## 再評価の条件

次のいずれかに該当した場合は、追加分割を検討する。

- `SevenPairs.lean` が再び1000行を大きく超える。
- 面子手の証明が、七対子とは独立した共有補題群を持つ。
- 国士無双の直接計算とその証明が、`Bounds.lean` の責務を圧迫する。
- `Complete` の形ごとの定義を独立して再利用する必要が生じる。
- ビルド時間や変更時の再コンパイル範囲が問題になる。

この時点で初めて、`SevenPairs/Exchange.lean` や `Kokushi.lean` などの
サブディレクトリ構成を候補にする。

