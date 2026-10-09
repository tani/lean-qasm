    import LiterateLean
    import Init.Data.Rat
    open scoped LiterateLean

# Exact numeric literals

Numeric syntax survives lowering without an intermediate floating-point approximation.
Decimals retain their significand and base-ten exponent; named mathematical constants
remain distinct from a binary floating-point value. Runtime adapters may approximate
these values, but those adapters are not the definition of their mathematical meaning.

```lean
namespace QASM.IR

inductive RealConstant
  | pi | tau | euler
  deriving Repr, BEq, DecidableEq, Inhabited

def RealConstant.toQasm : RealConstant → String
  | .pi => "pi"
  | .tau => "tau"
  | .euler => "euler"

structure DecimalLiteral where
  significand : Int
  exponent10 : Int
  deriving Repr, BEq, DecidableEq, Inhabited

namespace DecimalLiteral

def toQasm (value : DecimalLiteral) : String :=
  s!"{value.significand}e{value.exponent10}"

def toRat (value : DecimalLiteral) : Rat :=
  if value.exponent10 ≥ 0 then
    (value.significand : Rat) * (10 : Rat) ^ value.exponent10.toNat
  else (value.significand : Rat) / (10 : Rat) ^ value.exponent10.natAbs

```

## Parsing and normalization

Parsing validates decimal digits before constructing the exact value. Trailing zeroes
are removed from the significand so emission and reparsing preserve the same literal.
This operation does not round, and no host-sized integer bounds the significand.

```lean
def parse (text : String) : Except String DecimalLiteral := do
  let text := (text.replace "_" "").replace "E" "e"
  let fields := text.splitOn "e"
  let (mantissa, exponent) ← match fields with
    | [mantissa] => pure (mantissa, (0 : Int))
    | [mantissa, exponent] =>
      let exponent := if exponent.startsWith "+" then exponent.drop 1 |>.toString else exponent
      match exponent.toInt? with
      | some exponent => pure (mantissa, exponent)
      | none => throw "invalid decimal exponent"
    | _ => throw "invalid decimal literal"
  let negative := mantissa.startsWith "-"
  let mantissa := if negative || mantissa.startsWith "+" then
    mantissa.drop 1 |>.toString else mantissa
  let (whole, fraction) ← match mantissa.splitOn "." with
    | [whole] => pure (whole, "")
    | [whole, fraction] => pure (whole, fraction)
    | _ => throw "invalid decimal point"
  let digits := whole ++ fraction
  if digits.isEmpty || !digits.toList.all Char.isDigit then throw "invalid decimal digits"
  let zeros := digits.toList.reverse.takeWhile (· == '0') |>.length
  let significant := digits.dropEnd zeros |>.toString
  if significant.isEmpty then return ⟨0, 0⟩
  let raw ← match significant.toNat? with
    | some value => pure value
    | none => throw "invalid decimal significand"
  pure ⟨if negative then -(Int.ofNat raw) else Int.ofNat raw,
    exponent - Int.ofNat fraction.length + Int.ofNat zeros⟩

end DecimalLiteral
end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
