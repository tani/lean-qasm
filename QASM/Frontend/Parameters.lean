    import LiterateLean
    open scoped LiterateLean

# Symbolic integer parameters during compilation

A family parameter is a Lean natural number, embedded into integer designator arithmetic.
The frontend keeps addition, subtraction, and multiplication symbolic rather than testing
one representative parameter value. Closed arithmetic is normalized immediately. Sizes
store these integers until quotation emits ordinary Lean `Nat` terms; positivity is an
explicit precondition of the generated family.

```lean
namespace QASM.Parameters

inductive Integer where
  | literal (value : Int)
  | parameter (name : String)
  | add (left right : Integer)
  | sub (left right : Integer)
  | mul (left right : Integer)
  | neg (value : Integer)
  deriving Repr, BEq, Inhabited

instance (n : Nat) : OfNat Integer n := ⟨.literal n⟩
instance : Coe Int Integer := ⟨.literal⟩
instance : Coe Nat Integer := ⟨fun n => .literal n⟩

def Integer.closed? : Integer → Option Int
  | .literal value => some value
  | _ => none

def Integer.plus (left right : Integer) : Integer :=
  match left, right with
  | .literal x, .literal y => .literal (x + y)
  | .literal 0, y => y
  | x, .literal 0 => x
  | x, y => .add x y

def Integer.minus (left right : Integer) : Integer :=
  match left, right with
  | .literal x, .literal y => .literal (x - y)
  | x, .literal 0 => x
  | x, y => .sub x y

def Integer.times (left right : Integer) : Integer :=
  match left, right with
  | .literal x, .literal y => .literal (x * y)
  | .literal 0, _ | _, .literal 0 => .literal 0
  | .literal 1, y => y
  | x, .literal 1 => x
  | x, y => .mul x y

instance : Add Integer := ⟨Integer.plus⟩
instance : Sub Integer := ⟨Integer.minus⟩
instance : Mul Integer := ⟨Integer.times⟩

structure Size where
  value : Integer
  deriving Repr, BEq, Inhabited

instance : ToString Size := ⟨reprStr⟩

instance (n : Nat) : OfNat Size n := ⟨⟨.literal n⟩⟩
instance : Coe Nat Size := ⟨fun n => ⟨.literal n⟩⟩
instance : Add Size := ⟨fun x y => ⟨x.value + y.value⟩⟩

def Integer.eval (parameters : String → Nat) : Integer → Int
  | .literal value => value
  | .parameter name => Int.ofNat (parameters name)
  | .add left right => eval parameters left + eval parameters right
  | .sub left right => eval parameters left - eval parameters right
  | .mul left right => eval parameters left * eval parameters right
  | .neg value => -eval parameters value

def Size.eval (parameters : String → Nat) (size : Size) : Nat :=
  (size.value.eval parameters).toNat

def Size.Positive (parameters : String → Nat) (size : Size) : Prop :=
  0 < size.value.eval parameters

/-- Lean source used only by the command elaborator's generated boundary declarations. -/
def Integer.leanCode : Integer → String
  | .literal value => s!"({value} : Int)"
  | .parameter name => s!"Int.ofNat «{name}»"
  | .add left right => s!"({left.leanCode} + {right.leanCode})"
  | .sub left right => s!"({left.leanCode} - {right.leanCode})"
  | .mul left right => s!"({left.leanCode} * {right.leanCode})"
  | .neg value => s!"(-{value.leanCode})"

def Size.leanCode (size : Size) : String :=
  match size.value.closed? with
  | some value => toString value.toNat
  | none => s!"({size.value.leanCode}).toNat"

end QASM.Parameters
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
