#import "@preview/touying:0.7.4": *
#import themes.stargazer: *

#show: stargazer-theme.with(
  aspect-ratio: "16-9",
  // Each level-one heading is an actual slide, not a section divider.
  config-common(new-section-slide-fn: none),
  config-info(
    title: [Cost Monad 入門],
    subtitle: [計算の結果と「かかった量」を一緒に扱う],
    author: [Lean QASM],
    date: datetime.today(),
  ),
)

// Japanese text needs a font with CJK glyphs even when the theme uses a Latin font.
#show regex("[\\p{scx:Han}\\p{scx:Hira}\\p{scx:Kana}]"): set text(
  font: "Hiragino Sans", lang: "ja"
)

= Cost Monad 入門

*計算結果にコストを添えると、プログラムの構造を保ったまま資源を数えられる。*

#v(1em)

このスライドでは、Cost Monad を「値」と「加算できる記録」を結ぶ小さな抽象化として導入し、
Lean QASM の静的メトリクスにどう使われるかを見る。

= なぜ戻り値だけでは足りないのか

ある計算を実行すると、値だけでなく時間・ログ・消費電力・ゲート数なども生じる。

#grid(
  columns: (1fr, 1fr),
  column-gutter: 1.2em,
[
  *普通の関数*

  `compile : Source -> Program`

  結果の `Program` は得られるが、
  途中で何をどれだけ使ったかは捨てられる。
],
[
  *コストつきの関数*

  `compile : Source -> Cost Program`

  同じ結果とともに、計算で集めた
  メトリクスを返す。
])

*要点:* コスト計測を各関数の戻り値に手作業で織り込まず、
合成の規則を一度だけ定める。

= Cost は「値 × コスト」である

最も単純な Cost Monad は、値 `alpha` と自然数コストを組にする。

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
`Report` は宣言一覧、プログラム形状、操作数、資源見積りを別々の入れ子レコードに持つため、
たとえば CNOT 数と分岐数を同じスカラーへ混ぜない。

```lean
namespace QASM.Cost

abbrev CostM := StateM Report

def charge (delta : Report) : CostM Unit :=
  modify fun cost => cost + delta
```

`charge` は値を返さず、現在の集計値だけを更新する。走査器は知っている区分だけを指定する。
たとえば `h` は `resources.gates.oneQubit`、`cx` は `resources.gates.cnot`、
分岐は `shape.branchNodes` に記録する。QSVT の `U` 呼出しのように、OpenQASM の構造から
判定できない資源は `resources.oracle` へ明示的な計画として加える。

= 合成規則は IR の木構造に対応する

`Circuit` や `Proc` を再帰的にたどるとき、逐次・並列風の構成子は
子ノードの計測を順に合成できる。

```lean
partial def costCircuit : Circuit -> CostM Unit
  | .compose first second => costCircuit first *> costCircuit second
  | .tensor first second  => costCircuit first *> costCircuit second
  | .primitive _          => charge { operations := { applications := 1 } }
```

#block(fill: rgb("#ecfdf5"), inset: 0.75em, radius: 5pt)[
  *大事な境界*

  静的コスト計測はプログラムを実行しない。canonical IR の構造だけを読み、
  バックエンドや量子状態には依存しない。
]

= 「何を数えるか」は Monad の外で決める

Monad が保証するのは *蓄積の仕組み* であって、メトリクスの意味ではない。

#grid(
  columns: (1fr, 1fr, 1fr),
  column-gutter: 0.8em,
[
  *時間モデル*

  各操作に推定時間を割り当てる。
],
[
  *回路モデル*

  ゲート、測定、制御、深さを数える。
],
[
  *安全な解析*

  実行せず、構文木だけから上界を求める。
])

同じ `bind` / `do` の形を保ちつつ、`Nat` を `Report` や重みつきコストへ交換できる。

= Monad 則が「合成しても意味が変わらない」ことを支える

Cost の足し算が結合的で、`0` が単位元なら、計算の括弧付けを変えても意味は変わらない。

#block(fill: rgb("#f1f5f9"), inset: 0.7em, radius: 5pt)[
  $ (c_1 + c_2) + c_3 = c_1 + (c_2 + c_3) $

  $ 0 + c = c = c + 0 $
]

- 左・右単位律は `pure` の余計なコストがないことに対応する。
- 結合律は、長いパイプラインを部分ごとに分けて実装してもよいことを保証する。
- したがって Cost Monad は、局所的な計測関数を大きな解析へ安全に組み立てる道具になる。

= まとめ

*Cost Monad は「値の計算」と「加算できる観測」を分離しながら、一緒に合成する。*

#block(fill: rgb("#eef2ff"), inset: 0.9em, radius: 5pt)[
  1. `pure` は値をコスト 0 で持ち上げる。
  2. `bind` は値をつなぎ、コストを合算する。
  3. `do` 記法で大きな計測処理も普通のプログラムとして書ける。
  4. QASM では同じ発想を `StateM Report` と canonical IR の走査に使う。
]

次に考えるべき問いは、*どのメトリクスが目的に対して意味を持ち、どこまでを静的に数えるか* である。
