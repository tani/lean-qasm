    import LiterateLean
    import QASM.IR.Program
    open scoped LiterateLean

# QFT with residual finite loops

The quantum transformation body is separate from allocation, so its correctness can
be stated for an arbitrary input register. Register zero and local identifiers one
through four are reserved by this family. Size zero is the empty program.

Both loops remain Proc nodes for every size. The angle is halved using a same-width
unsigned divisor, avoiding an overflowing power computation. The canonical profile
uses angle width at least max(3,n) and signed index width n+2. Backend capacity and
finite-to-mathematical refinement are separate conditions.

```lean
namespace QASM.IR.QFT
private def integer (width : Nat) (value : Int) : Expr :=
  { type := .scalar (.sint width), node := .intLit value }
private def readVar (var : Var) : Expr := { type := var.type, node := .var var.id }
private def binary (type : QASM.IR.Type) (op : BinaryOp) (a b : Expr) : Expr :=
  { type, node := .binary op a b }
private def target (var : Var) : LValue := { root := var.id, type := var.type }
private def apply (kind : PrimitiveKind) (name : String) (parameters : Array Expr)
    (indices : Array Expr) : Proc :=
  .operation (.apply { target := kind, name, parameters }
    (indices.map fun i => .wire ⟨0⟩ #[i]))

def body (n width indexWidth : Nat) : Proc := Id.run do
  if n = 0 then return .skip
  let intTy : QASM.IR.Type := .scalar (.sint indexWidth)
  let angleTy : QASM.IR.Type := .scalar (.angle width)
  let uintTy : QASM.IR.Type := .scalar (.uint width)
  let j : Var := { id := ⟨1⟩, name := "j", type := intTy }
  let k : Var := { id := ⟨2⟩, name := "k", type := intTy }
  let theta : Var := { id := ⟨3⟩, name := "theta", type := angleTy }
  let two : Var := { id := ⟨4⟩, name := "two", type := uintTy }
  let lit := integer indexWidth
  let jMinusOne := binary intTy .sub (readVar j) (lit 1)
  let hasInner := binary (.scalar .boolean) .gt (readVar j) (lit 0)
  let inner := Proc.forLoop k (.range jMinusOne (lit (-1)) (lit 0))
    (.sequence #[
      .operation (.assign (target theta) (binary angleTy .div (readVar theta) (readVar two))),
      apply .cp "cp" #[readVar theta] #[readVar k, readVar j]])
  let outer := Proc.forLoop j (.range (lit (Int.ofNat n - 1)) (lit (-1)) (lit 0))
    (.scope #[theta] (.sequence #[
      apply .h "h" #[] #[readVar j],
      .operation (.declare theta (some { type := .scalar (.float 64), node := .realConstant .pi })),
      .branch hasInner inner none]))
  let swaps := if n < 2 then Proc.skip else
    Proc.forLoop j (.range (lit 0) (lit 1) (lit (Int.ofNat (n / 2) - 1)))
      (apply .swap "swap" #[] #[readVar j,
        binary intTy .sub (lit (Int.ofNat n - 1)) (readVar j)])
  return .scope #[two] (.sequence #[
    .operation (.declare two (some { type := uintTy, node := .intLit 2 })), outer, swaps])

def program (n width indexWidth : Nat) : Program :=
  if n = 0 then {} else
    { body := .sequence #[.operation (.allocate { var := ⟨0⟩, name := "q", size := n }),
        body n width indexWidth] }

def canonical (n : Nat) : Program := program n (max 3 n) (n+2)

@[simp] theorem body_zero (width indexWidth : Nat) : body 0 width indexWidth = .skip := by
  simp [body]
@[simp] theorem program_zero (width indexWidth : Nat) : program 0 width indexWidth = {} := by
  simp [program]
end QASM.IR.QFT
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
