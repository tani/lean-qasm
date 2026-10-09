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
def integer (width : Nat) (value : Int) : Expr :=
  { type := .scalar (.sint width), node := .intLit value }
def readVar (var : Var) : Expr := { type := var.type, node := .var var.id }
def binary (type : QASM.IR.Type) (op : BinaryOp) (a b : Expr) : Expr :=
  { type, node := .binary op a b }
def target (var : Var) : LValue := { root := var.id, type := var.type }
def apply (kind : PrimitiveKind) (name : String) (parameters : Array Expr)
    (indices : Array Expr) : Proc :=
  .operation (.apply { target := kind, name, parameters }
    (indices.map fun i => .wire ⟨0⟩ #[i]))

def jVar (indexWidth : Nat) : Var :=
  { id := ⟨1⟩, name := "j", type := .scalar (.sint indexWidth) }
def kVar (indexWidth : Nat) : Var :=
  { id := ⟨2⟩, name := "k", type := .scalar (.sint indexWidth) }
def thetaVar (width : Nat) : Var :=
  { id := ⟨3⟩, name := "theta", type := .scalar (.angle width) }
def twoVar (width : Nat) : Var :=
  { id := ⟨4⟩, name := "two", type := .scalar (.uint width) }

```

## Loop components

Named components expose the residual syntax to proofs without expanding any loop.
The inner iteration first updates the stored angle, then reads that updated value
for the controlled phase. The outer scope restores theta after each target.

```lean
def innerStep (width indexWidth : Nat) : Proc := .sequence #[
  .operation (.assign (target (thetaVar width))
    (binary (.scalar (.angle width)) .div
      (readVar (thetaVar width)) (readVar (twoVar width)))),
  apply .cp "cp" #[readVar (thetaVar width)]
    #[readVar (kVar indexWidth), readVar (jVar indexWidth)]]

def innerLoop (width indexWidth : Nat) : Proc :=
  .forLoop (kVar indexWidth)
    (.range (binary (.scalar (.sint indexWidth)) .sub
      (readVar (jVar indexWidth)) (integer indexWidth 1))
      (integer indexWidth (-1)) (integer indexWidth 0))
    (innerStep width indexWidth)

def outerStep (width indexWidth : Nat) : Proc :=
  .scope #[thetaVar width] (.sequence #[
    apply .h "h" #[] #[readVar (jVar indexWidth)],
    .operation (.declare (thetaVar width)
      (some { type := .scalar (.float 64), node := .realConstant .pi })),
    .branch (binary (.scalar .boolean) .gt
      (readVar (jVar indexWidth)) (integer indexWidth 0))
      (innerLoop width indexWidth) none])

def outerLoop (n width indexWidth : Nat) : Proc :=
  .forLoop (jVar indexWidth)
    (.range (integer indexWidth (Int.ofNat n - 1))
      (integer indexWidth (-1)) (integer indexWidth 0))
    (outerStep width indexWidth)

def swapStep (n indexWidth : Nat) : Proc :=
  apply .swap "swap" #[] #[readVar (jVar indexWidth),
    binary (.scalar (.sint indexWidth)) .sub
      (integer indexWidth (Int.ofNat n - 1)) (readVar (jVar indexWidth))]

def swapLoop (n indexWidth : Nat) : Proc :=
  if n < 2 then .skip else
    .forLoop (jVar indexWidth)
      (.range (integer indexWidth 0) (integer indexWidth 1)
        (integer indexWidth (Int.ofNat (n / 2) - 1)))
      (swapStep n indexWidth)

def body (n width indexWidth : Nat) : Proc :=
  if n = 0 then .skip else
    .scope #[twoVar width] (.sequence #[
      .operation (.declare (twoVar width)
        (some { type := .scalar (.uint width), node := .intLit 2 })),
      outerLoop n width indexWidth, swapLoop n indexWidth])

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
