#import "@preview/touying:0.7.4": *
#import themes.stargazer: *

#show: stargazer-theme.with(
  aspect-ratio: "16-9",
  // Each level-one heading is an actual slide, not a section divider.
  config-common(new-section-slide-fn: none),
  config-info(
    title: [Lean QASM の静的コスト報告],
    subtitle: [canonical IR を階層的な Report に写す],
    author: [Lean QASM],
    date: datetime.today(),
  ),
)

// Japanese text needs a font with CJK glyphs even when the theme uses a Latin font.
#show regex("[\\p{scx:Han}\\p{scx:Hira}\\p{scx:Kana}]"): set text(
  font: "Hiragino Sans", lang: "ja"
)

= Lean QASM の静的コスト報告

*実行せずに canonical IR をたどり、異なる単位を混ぜずに資源を報告する。*

#v(1em)

このスライドでは、加算可能な記録を合成する考え方から始め、Lean QASM が
`StateM Report` で静的コストを集める現在の実装を見る。

= なぜ単一の数値だけでは足りないのか

同じプログラムでも、宣言数・制御構造・操作数・CNOT数・補助量子ビット数は別の単位である。

#grid(
  columns: (1fr, 1fr),
  column-gutter: 1.2em,
[
  *単一スカラー*

  `cost : Nat`

  CNOT数と分岐数を足す重み付けを
  暗黙に選んでしまう。
],
[
  *階層的な報告*

  `Report`

  単位ごとに独立して記録し、
  重み付けは利用者が後で決める。
])

*要点:* 計測の合成規則と、何を数えるかを分離する。

= 加算可能な記録という考え方

最も単純な Cost Monad は、値 `alpha` と自然数コストを組にする。これは導入用の
モデルであり、現行Lean QASMの実装は後述する `StateM Report` である。

#block(fill: rgb("#f1f5f9"), inset: 0.8em, radius: 5pt)[
  $ "Cost" alpha = alpha times "Nat" $

  $ ("value", "cost") : "Cost" alpha $
]

- `value` は計算が返した答え。
- `cost` は答えを得るまでに蓄積した量。
- コストの単位は設計で決める。ステップ数、バイト数、ゲート数のどれでもよい。

この形は Writer Monad の特別な場合でもある。`Nat` の加算を、
より一般の「結合できる記録」に取り替えることもできる。

= return はコストを増やさない

値をそのまま返す計算には、追加の料金を請求しない。

#block(fill: rgb("#f1f5f9"), inset: 0.8em, radius: 5pt)[
  $ "pure"(a) = (a, 0) $
]

```lean
def pure (a : α) : Cost α :=
  (a, 0)
```

`pure` は「計測を始める前の基準点」である。これにより、
普通の値を Cost の世界へ安全に持ち上げられる。

= bind が順番どおりにコストを合算する

`bind` は、前の結果を次の計算へ渡し、二つのコストを足す。

#block(fill: rgb("#f1f5f9"), inset: 0.75em, radius: 5pt)[
  $ (a, c) " >>= " f = $
  $ "let" (b, d) = f(a) "; " (b, c + d) $
]

#grid(
  columns: (1fr, 1fr),
  column-gutter: 1.2em,
[
  *データの流れ*

  $ a arrow.r f(a) arrow.r b $

  前の値だけが次の段階へ進む。
],
[
  *コストの流れ*

  $ c arrow.r c + d $

  順に実行した分だけ、記録が増える。
])

= 小さな例で追いかける

二つの操作がそれぞれ 2 と 3 のコストを持つとする。

```lean
def double (n : Nat) : Cost Nat := (2 * n, 2)
def addOne (n : Nat) : Cost Nat := (n + 1, 3)

#eval (double 10 >>= addOne)
-- (21, 5)
```

#block(fill: rgb("#fff7ed"), inset: 0.75em, radius: 5pt)[
  *読む順序*

  1. `double 10` は値 `20` とコスト `2` を返す。
  2. `addOne 20` は値 `21` とコスト `3` を返す。
  3. `bind` が合計し、結果は `(21, 5)` になる。
]

= do 記法は bind の連鎖を読みやすくする

実際のプログラムでは、`>>=` を並べるより `do` 記法の方が構造を読み取りやすい。

#grid(
  columns: (1fr, 1fr),
  column-gutter: 1.2em,
[
  *明示した形*

```lean
double 10 >>= fun x =>
  addOne x
```
],
[
  *do 記法*

```lean
do
  let x <- double 10
  addOne x
```
])

どちらも同じ合成規則を使う。Cost Monad は、値の依存関係を隠さずに
副産物であるコストだけを自動で受け渡す。

= QASM の静的コスト報告では StateM を使う

Lean QASM では、コストは実行結果に添えるのではなく、走査中の `Report` 状態として集める。
`Report` は異なる単位を入れ子レコードに分けるため、CNOT 数と分岐数を混ぜない。

```lean
namespace QASM.Cost

abbrev CostM := StateM Report

def charge (delta : Report) : CostM Unit :=
  modify fun cost => cost + delta
```

`charge` は値を返さず、現在の集計値だけを更新する。走査器は根拠を持つ区分だけを指定する。

= Report は四つの責務を分ける

#grid(
  columns: (1fr, 1fr, 1fr, 1fr),
  column-gutter: 0.55em,
[
  *`declarations`*

  `gates`

  `subroutines`

  `externs`
],
[
  *`shape`*

  `allocationSites`

  `branchNodes`

  `loopNodes`
],
[
  *`operations`*

  `applications`

  `measurements`

  `classical`
],
[
  *`resources`*

  `oracle`

  `gates`

  `workspace`
])

#block(fill: rgb("#ecfdf5"), inset: 0.75em, radius: 5pt)[
  *設計上の境界*

  `resources.oracle` はアルゴリズムの約束、`resources.gates` は可視な素ゲート、
  `resources.workspace` はピーク空間である。互いに自動換算しない。
]

= 合成規則は IR の木構造に対応する

`Circuit` や `Proc` を再帰的にたどるとき、逐次・並列風の構成子は
子ノードの計測を順に合成できる。

```lean
def costCircuit : Circuit → CostM Unit -- 本体からの抜粋
  | .primitive primitive => charge {
      operations := { applications := 1 }
      resources := primitiveResources primitive.kind }
  | .compose first second => costCircuit first *> costCircuit second
  | .tensor first second  => costCircuit first *> costCircuit second
  | .unsupported _ _ _ _  => charge { operations := { unsupported := 1 } }
```

#block(fill: rgb("#ecfdf5"), inset: 0.75em, radius: 5pt)[
  *大事な境界*

  静的コスト計測はプログラムを実行しない。canonical IR の構造だけを読み、
  バックエンドや量子状態には依存しない。
]

= Op ごとに根拠のある区分だけを加算する

```lean
def costOp : Op → CostM Unit -- 本体からの抜粋
  | .apply gate _ => charge {
      operations := { applications := 1 }
      resources := primitiveResources gate.target }
  | .allocate decl => charge {
      shape := { allocationSites := 1, allocatedQubits := decl.size } }
  | .measure _ _ => charge { operations := { measurements := 1 } }
  | .call _ _ => charge { operations := { subroutineCalls := 1 } }
  | .unsupported _ _ => charge { operations := { unsupported := 1 } }
```

この投影は `QASM.Execution.run` を呼ばない。ループ本体と各分岐本体は一度だけ訪問し、
反復回数・実行時間・バックエンドの分解は推定しない。

= 資源は同じ Report に併置するが、換算しない

`resources` の三つの部分は、同じ加算器で運べても意味は異なる。`measure` が自動で
埋められるのは、canonical IR に現れる `gates` の一部だけである。

#grid(
  columns: (1fr, 1fr, 1fr),
  column-gutter: 0.8em,
[
  *`oracle`*

  QSVT の `U`、`U†`、

  射影制御NOTの呼出し。
],
[
  *`gates`*

  CNOT、1量子ビット、

  その他の可視primitive。
],
[
  *`workspace`*

  `peakAncillaQubits`。

  加算でなく最大値を取る。
])

= QSVT 計画は明示的な Resources として加える

`Resources.qsvtAlternatingPhase n` は、長さ `n` の交互位相列を次の形で記録する。

#grid(
  columns: (1fr, 1fr),
  column-gutter: 1.2em,
[
  *`oracle`*

  `unitary = (n + 1) / 2`

  `inverseUnitary = n / 2`

  二種の射影制御NOTは各 `n`
],
[
  *`gates` と `workspace`*

  `oneQubit = n`

  `peakAncillaQubits = 1`
])

この計画をCNOT数へ換算するには、`U` と射影oracleの実装を別途与える必要がある。

= Report の合成は成分ごとに定義する

`Report.add` は各所有区分の `Add` を使う。宣言・形状・操作・oracle・gate数は加算し、
補助量子ビットの要求だけは最大値を取る。

#block(fill: rgb("#f1f5f9"), inset: 0.7em, radius: 5pt)[
  $ (r_1 + r_2) + r_3 = r_1 + (r_2 + r_3) $

  $ 0 + r = r = r + 0 $
]

- カウンタの合成は `Nat` の加算、workspace の合成は `max` である。
- どちらも結合的で `0` を単位元に持つため、走査の括弧付けで報告が変わらない。
- したがって `StateM Report` は、局所的な計測関数を大きな静的解析へ安全に組み立てられる。

= まとめ

*Lean QASM は canonical IR の構造を `StateM Report` で、単位を保ったまま集計する。*

#block(fill: rgb("#eef2ff"), inset: 0.9em, radius: 5pt)[
  1. `Report` は `declarations`、`shape`、`operations`、`resources` を分離する。
  2. `measure` はIRを一度たどり、実行や再帰的なcall展開をしない。
  3. 可視なprimitiveは `resources.gates` へ、QSVT計画は `resources.oracle` へ記録する。
  4. `workspace` はピーク値なので `max` で合成する。
]

次に考えるべき問いは、*どの資源を具体的なハードウェアコストへ換算し、どのまま報告として残すか* である。
