    import LiterateLean
    import QASMVerification.AngleRefinement
    import QASMVerification.TraceRefinement
    import QASMVerification.MachineLaws
    open scoped LiterateLean

# Exact execution model for residual QFT programs

This kernel evaluates resolved expressions and wire indices rather than recognizing a
QFT program by its syntax. Signed literals and subtraction are checked against their
finite type width. Angle division uses the existing runtime Value.binary operation;
initialization from pi retains the exact half-turn bit pattern. Unsupported atomic
operations fail explicitly. Quantum operations append their ideal matrices, with CP
using the actual stored angle, not a phase reconstructed from its wire indices.

The model covers the unitary QFT fragment on an already supplied arbitrary input
register. It uses the shared control machine for every Proc constructor. It does not
identify the interpreter's final Float conversion with the ideal complex matrix.

```lean
noncomputable section
namespace QASMVerification.QFTExecution
open QASM.IR
open QASM.Execution.Semantics (Flow)
open QASM.Execution.VerifiedControl

structure State (n : Nat) where
  values : Nat → QASM.Value := fun _ => .unit
  events : GateEvents n := []

instance : Inhabited (State n) := ⟨{}⟩

def put (s : State n) (id : Nat) (v : QASM.Value) : State n :=
  { s with values := Function.update s.values id v }

def emit (s : State n) (u : Operator n) : State n :=
  { s with events := s.events ++ [u] }

def restore (locals : Array Var) (saved final : State n) : State n :=
  locals.foldl (fun s var => put s var.id.value (saved.values var.id.value)) final

def signed (w : Nat) (i : Int) : Option QASM.Value :=
  if -(2 : Int)^(w-1) ≤ i ∧ i < (2 : Int)^(w-1) then some (.sint w i) else none

def unsigned (w : Nat) (i : Int) : Option QASM.Value :=
  if 0 ≤ i ∧ i < (2 : Int)^w then some (.uint w i.toNat) else none

def expression (e : Expr) (s : State n) : Option QASM.Value :=
  match _hn : e.node with
  | .var id => some (s.values id.value)
  | .intLit i => match e.type with
    | .scalar (.sint w) => signed w i
    | .scalar (.uint w) => unsigned w i
    | _ => none
  | .binary op a b => do
    let x ← expression a s
    let y ← expression b s
    match op, x, y, e.type with
    | .sub, .sint _ i, .sint _ j, .scalar (.sint w) => signed w (i-j)
    | .gt, .sint _ i, .sint _ j, .scalar .boolean => some (.boolean (decide (i > j)))
    | .div, .angle w bits, .uint v d, .scalar (.angle t) =>
      if w = v ∧ w = t ∧ 0 < d then
        some (QASM.Value.binary "/" (.angle w bits) (.uint v d)) else none
    | _, _, _, _ => none
  | _ => none

termination_by sizeOf e
decreasing_by
  all_goals cases e; simp_all; omega

def wire (operand : QuantumOperand) (s : State n) : Option Nat := do
  match operand with
  | .wire id indices approximate =>
    if id.value ≠ 0 ∨ approximate then none else do
      match indices.toList with
      | [index] =>
        match ← expression index s with
        | .sint _ i => if 0 ≤ i ∧ i.toNat < n then some i.toNat else none
        | _ => none
      | _ => none
  | _ => none

def cp (n k j : Nat) (angle : ℝ) : Operator n := fun row col =>
  if k < n ∧ j < n ∧ k ≠ j ∧ row = col then
    if basisBit col.val k = 1 ∧ basisBit col.val j = 1 then phase angle else 1
  else 0

```

## Atomic transitions and finite ranges

Unit-step ranges include both endpoints. Their list length is a nonnegative integer
span, so even descending ranges with a negative starting point terminate. Bindings and
scope restoration affect only the classical store; accumulated quantum action survives.

```lean
def atomic (op : Op) (s : State n) : Option (State n) := do
  match op with
  | .declare var (some e) =>
    let v ← match var.type, e.node with
      | .scalar (.angle w), .realConstant .pi =>
        if 0 < w then some (.angle w (thetaBits w 0)) else none
      | _, _ => expression e s
    return put s var.id.value v
  | .assign target e =>
    if target.indices.isEmpty then
      let v ← expression e s
      return put s target.root.value v
    else none
  | .apply gate operands =>
    if !gate.modifiers.isEmpty then none else do
      match gate.target, gate.parameters.toList, operands.toList with
      | .h, [], [q] =>
        let j ← wire q s
        return emit s (stepOperator n (.hadamard j))
      | .cp, [angle], [a, b] =>
        let k ← wire a s
        let j ← wire b s
        match ← expression angle s with
        | .angle w bits =>
          if bits < 2^w ∧ k ≠ j then return emit s (cp n k j (bitAngle w bits))
          else none
        | _ => none
      | .swap, [], [a, b] =>
        let j ← wire a s
        let k ← wire b s
        return emit s (stepOperator n (.swap j k))
      | _, _, _ => none
  | _ => none

def operation (op : Op) (s : State n) : Option (State n × Flow) :=
  (atomic op s).map (fun t => (t, .next))

def integers (start step stop : Int) : Option (List Int) :=
  if step = -1 then
    some ((List.range (start-stop+1).toNat).reverse.map (fun i => stop + Int.ofNat i))
  else if step = 1 then
    some ((List.range (stop-start+1).toNat).map (fun i => start + Int.ofNat i))
  else none

def domain (d : IterationDomain) (s : State n) : Option (State n × Option (List QASM.Value)) := do
  match d with
  | .range a b c =>
    match ← expression a s, ← expression b s, ← expression c s with
    | .sint w start, .sint _ step, .sint _ stop =>
      let values ← integers start step stop
      return (s, some (values.map (QASM.Value.sint w)))
    | _, _, _ => none
  | _ => none

def kernel (n : Nat) : Kernel (State n) where
  operation := operation
  condition e s := do
    match ← expression e s with
    | .boolean b => some (s, some b)
    | _ => none
  domain := domain
  switchCase _ _ _ _ := none
  returnValue _ _ := none
  bindIterator var value s := put s var.id.value value
  restore := restore

def checked (s : State n) (result : Option (State n × α)) :
    Option (State n × Except Unit α) :=
  some (match result with | some (t, a) => (t, .ok a) | none => (s, .error ()))

def machine (n : Nat) : QASM.Execution.ControlMachine.Kernel Option (State n) Unit where
  operation op s := checked s ((kernel n).operation op s)
  condition e s := checked s ((kernel n).condition e s)
  domain d s := checked s ((kernel n).domain d s)
  switchCase e cases other s := checked s ((kernel n).switchCase e cases other s)
  returnValue e s := checked s ((kernel n).returnValue e s)
  bindIterator := (kernel n).bindIterator
  restore := (kernel n).restore

@[simp] theorem erase_checked (s : State n) (r : Option (State n × α)) :
    Machine.erase (checked s r) = r := by
  cases r with
  | none => rfl
  | some p => cases p; rfl

theorem project_machine (n : Nat) : Machine.project (machine n) = kernel n := by
  unfold Machine.project machine
  simp only [erase_checked]

theorem operation_normal {op : Op} {s t : State n} {flow : Flow}
    (h : operation op s = some (t, flow)) : flow = .next := by
  obtain ⟨a, _, he⟩ := Option.map_eq_some_iff.mp h
  exact (congrArg Prod.snd he).symm

theorem machine_normal (n : Nat) : Machine.OperationsNormal (machine n) := by
  intro op s t flow h
  have he : operation op s = some (t, flow) := by
    have := (Machine.erase_some _ _ _).2 h
    simpa [machine, kernel] using this
  exact Or.inl (operation_normal he)

end QASMVerification.QFTExecution
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
