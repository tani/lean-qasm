    import LiterateLean
    import QASMVerification.QFTLoopLaws
    import QASMVerification.QFTSwapLaws
    open scoped LiterateLean

# Total correctness of the residual QFT program

These proofs execute the original nested Proc loops in the exact atomic model.
They construct a finite normal execution, identify every successful result, and
exclude machine faults. The store is restored for arbitrary initial local values.
The Fourier equality therefore holds on every input state of the supplied register.

```lean
noncomputable section
namespace QASMVerification.QFTExecution
open QASM.IR
open QASM.IR.QFT
open QASM.Execution.Semantics (Flow)
open QASM.Execution.EffectSemantics
open QASM.Execution.VerifiedControl (model)

def targetSteps (j : Nat) : List QFTStep := .hadamard j :: innerSteps j j

theorem outer_step (safe : QFTRangeSafe n w iw) (hj : j < n) (s : State n)
    (sj : s.values 1 = .sint iw j) (s2 : s.values 4 = .uint w 2) :
    ∃ t, Runs n (outerStep w iw) s t .next ∧ t.values = s.values ∧
      t.events = s.events ++ matrices n (targetSteps j) := by
  let hstate := emit s (stepOperator n (.hadamard j))
  let astate := put hstate 3 (.angle w (thetaBits w 0))
  have hrun : Runs n (apply .h "h" #[] #[readVar (jVar iw)]) s hstate .next := by
    apply Exec.operation
    simp [model, kernel, operation, atomic, jVar, wire, sj, hj, hstate]
  have arun : Runs n (.operation (.declare (thetaVar w)
      (some { type := .scalar (.float 64), node := .realConstant .pi }))) hstate astate .next := by
    have hw : 0 < w := by have := safe.1; have := Nat.le_max_left 3 n; omega
    apply Exec.operation
    simp [model, kernel, operation, atomic, thetaVar, hw, astate]
  let test := binary (.scalar .boolean) .gt (readVar (jVar iw)) (integer iw 0)
  have condition : (kernel n).condition test astate = some (astate, some (decide (0 < j))) := by
    simp [kernel, test, jVar, astate, hstate, put, emit, Function.update, sj,
      signed_safe safe 0 (by omega) (by omega)]
  have branch : ∃ t, Runs n (.branch test (innerLoop w iw) none) astate t .next ∧
      t.events = astate.events ++ matrices n (innerSteps j j) ∧ Preserves astate t [3] := by
    by_cases hz : j = 0
    · subst j
      refine ⟨astate, Exec.branchFalse ?_ (Exec.skip _), ?_, ?_⟩
      · simpa [model] using condition
      · simp [innerSteps, matrices]
      · intro i _; rfl
    · obtain ⟨t, run, trace, preserved⟩ := inner_loop safe hj astate
        (by simpa [astate, hstate, put, emit, Function.update] using sj)
        (by simpa [astate, hstate, put, emit, Function.update] using s2)
        (by simp [astate])
      refine ⟨t, Exec.branchTrue ?_ run, trace, preserved⟩
      simpa [model, show 0 < j by omega] using condition
  obtain ⟨t, brun, trace, preserved⟩ := branch
  refine ⟨restore #[thetaVar w] s t, ?_, ?_, ?_⟩
  · apply Exec.scope
    exact Exec.sequence (ExecSequence.next hrun (ExecSequence.next arun
      (ExecSequence.next brun (ExecSequence.nil _))))
  · funext i
    by_cases hi : i = 3
    · subst i; simp [thetaVar]
    · simp only [restore_one, thetaVar, put_other _ _ _ _ hi]
      rw [preserved i (by simp [hi])]
      simp [astate, hstate, put, emit, Function.update, hi]
  · simp only [restore_one, thetaVar, put_events, trace]
    simp [astate, hstate, put, emit, targetSteps, matrices, List.append_assoc]

```

## Finite iteration composition

For a finite domain, the body invariant preserves every value after binding the
iterator. Induction composes its event traces. Restoring the iterator then gives
identity on the entire classical store, while retaining all quantum matrices.

```lean
theorem finite_iterations (iterator : Var) (proc : Proc) (iw : Nat) (indices : List Nat)
    (events : Nat → GateEvents n) (P : (Nat → QASM.Value) → Prop)
    (bindP : ∀ (s : State n) (i : Nat), P s.values →
      P (put s iterator.id.value (.sint iw i)).values)
    (step : ∀ i ∈ indices, ∀ s : State n, P s.values →
      ∃ t, Runs n proc (put s iterator.id.value (.sint iw i)) t .next ∧
        t.values = (put s iterator.id.value (.sint iw i)).values ∧
        t.events = s.events ++ events i)
    (s : State n) (hs : P s.values) :
    ∃ t, Iterates n iterator proc (counters iw indices) s t .next ∧
      Preserves s t [iterator.id.value] ∧ t.events = s.events ++ indices.flatMap events := by
  induction indices generalizing s with
  | nil =>
    exact ⟨s, ExecFor.nil _, (fun _ _ => rfl), by simp⟩
  | cons i rest ih =>
    obtain ⟨middle, head, values, trace⟩ := step i (by simp) s hs
    have pm : P middle.values := by rw [values]; exact bindP s i hs
    obtain ⟨t, tail, preserved, traceTail⟩ := ih
      (fun k hk => step k (by simp [hk])) middle pm
    refine ⟨t, ?_, ?_, ?_⟩
    · exact ExecFor.next head (Or.inl rfl) tail
    · intro k hk
      rw [preserved k hk, values]
      have hk' : k ≠ iterator.id.value := by simpa using hk
      exact put_other _ _ _ _ hk'
    · rw [traceTail, trace]
      simp [List.append_assoc]

theorem restored_values (s t : State n) (iterator : Var)
    (h : Preserves s t [iterator.id.value]) :
    (restore #[iterator] s t).values = s.values := by
  funext i
  by_cases hi : i = iterator.id.value
  · subst i; simp
  · simp only [restore_one, put_other _ _ _ _ hi]
    exact h i (by simp [hi])

```

## Outer loop and physical swaps

The outer domain descends through every target exactly once. The swap domain ascends
through the lower half of the register. All evaluated indices satisfy the register
bounds and all signed arithmetic remains within the declared index width.

```lean
theorem outer_loop (safe : QFTRangeSafe n w iw) (s : State n)
    (s2 : s.values 4 = .uint w 2) :
    ∃ t, Runs n (outerLoop n w iw) s t .next ∧ t.values = s.values ∧
      t.events = s.events ++ matrices n (qftCore n) := by
  obtain ⟨t, iterations, preserved, trace⟩ := finite_iterations
    (jVar iw) (outerStep w iw) iw (List.range n).reverse
    (fun j => matrices n (targetSteps j)) (fun values => values 4 = .uint w 2)
    (by intro a i ha; simpa [jVar, put, Function.update] using ha)
    (by
      intro j hj a ha
      have hjn : j < n := by simpa using hj
      obtain ⟨b, run, values, trace⟩ := outer_step safe hjn
        (put a 1 (.sint iw j)) (by simp) (by simpa [put, Function.update] using ha)
      exact ⟨b, run, values, trace⟩) s s2
  have start : expression (integer iw (Int.ofNat n-1)) s =
      some (.sint iw ((n : Int)-1)) := by
    simpa [Int.ofNat_eq_natCast] using integer_eval safe s ((n : Int)-1) (by omega) (by omega)
  refine ⟨restore #[jVar iw] s t, Exec.forLoop (domain_down safe s _ n start) iterations,
    restored_values s t _ preserved, ?_⟩
  simpa [qftCore, targetSteps, innerSteps, matrices, List.map_flatMap, Function.comp_def] using trace

theorem swap_step (safe : QFTRangeSafe n w iw) (hj : j < n/2) (s : State n)
    (sj : s.values 1 = .sint iw j) :
    Runs n (swapStep n iw) s
      (emit s (stepOperator n (.swap j (n-1-j)))) .next := by
  have hjn : j < n := by omega
  have hkn : n-1-j < n := by omega
  have hi : (n : Int)-1-j = ((n-1-j : Nat) : Int) := by omega
  apply Exec.operation
  simp [model, kernel, operation, atomic, jVar, wire, sj,
    integer_eval safe s ((n : Int)-1) (by omega) (by omega), Int.ofNat_eq_natCast,
    signed_safe safe ((n-1-j : Nat) : Int) (by omega) (by omega), hi, hjn, hkn]

theorem swap_loop (safe : QFTRangeSafe n w iw) (s : State n) :
    ∃ t, Runs n (swapLoop n iw) s t .next ∧ t.values = s.values ∧
      t.events = s.events ++ matrices n (qftSwaps n) := by
  by_cases hn : n < 2
  · have hz : n/2 = 0 := by omega
    exact ⟨s, by simpa [swapLoop, hn] using Exec.skip (model := model (kernel n)) s,
      rfl, by simp [qftSwaps, matrices, hz]⟩
  · obtain ⟨t, iterations, preserved, trace⟩ := finite_iterations
      (jVar iw) (swapStep n iw) iw (List.range (n/2))
      (fun j => [stepOperator n (.swap j (n-1-j))]) (fun _ => True)
      (by simp)
      (by
        intro j hj a _
        have hj' : j < n/2 := by simpa using hj
        exact ⟨emit (put a 1 (.sint iw j)) (stepOperator n (.swap j (n-1-j))),
          swap_step safe hj' (put a 1 (.sint iw j)) (by simp), rfl, rfl⟩) s trivial
    refine ⟨restore #[jVar iw] s t, ?_, restored_values s t _ preserved, ?_⟩
    · rw [swapLoop, if_neg hn]
      exact Exec.forLoop (domain_up safe (by omega) (by omega) s) iterations
    · simpa [qftSwaps, matrices, ← List.map_eq_flatMap, List.map_map, Function.comp_def] using trace

```

## Complete body execution

Existence is proved by composing the three finite loops, rather than assuming an
execution or a program-level simulation. The result is normal completion with the
entire initial store restored and exactly the QFT matrices appended to the trace.

```lean
theorem body_exec (safe : QFTRangeSafe n w iw) (s : State n) :
    ∃ t, Runs n (body n w iw) s t .next ∧ t.values = s.values ∧
      t.events = s.events ++ matrices n (qftSteps n) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨s, by simpa using Exec.skip (model := model (kernel 0)) s, rfl, by simp [matrices]⟩
  · let start := put s 4 (.uint w 2)
    have two : expression { type := .scalar (.uint w), node := .intLit 2 } s =
        some (.uint w 2) := by rw [expression]; exact unsigned_two safe
    have declare : Runs n (.operation (.declare (twoVar w)
        (some { type := .scalar (.uint w), node := .intLit 2 }))) s start .next := by
      apply Exec.operation
      simp [model, kernel, operation, atomic, twoVar, two, start]
    obtain ⟨middle, outer, outerValues, outerTrace⟩ := outer_loop safe start (by simp [start])
    obtain ⟨final, swaps, swapValues, swapTrace⟩ := swap_loop safe middle
    refine ⟨restore #[twoVar w] s final, ?_, ?_, ?_⟩
    · rw [body, if_neg hn]
      exact Exec.scope (Exec.sequence (ExecSequence.next declare
        (ExecSequence.next outer (ExecSequence.next swaps (ExecSequence.nil _)))))
    · funext i
      by_cases hi : i = 4
      · subst i; simp [twoVar]
      · simp only [restore_one, twoVar, put_other _ _ _ _ hi, swapValues, outerValues]
        exact put_other _ _ _ _ hi
    · simp only [restore_one, twoVar, put_events, swapTrace, outerTrace]
      simp [start, qftSteps, matrices, List.map_append, List.append_assoc]

theorem machine_eval_iff (proc : Proc) (s t : State n) (flow : Flow) :
    QASM.Execution.ControlMachine.eval (machine n) proc s = some (t, .ok flow) ↔
      Runs n proc s t flow := by
  simpa only [project_machine] using
    Machine.machine_proc_refinement_iff (machine n) (machine_normal n) proc s t flow

theorem body_total (safe : QFTRangeSafe n w iw) (s : State n) :
    ∃ t, QASM.Execution.ControlMachine.eval (machine n) (body n w iw) s = some (t, .ok .next) ∧
      t.values = s.values ∧ t.events = s.events ++ matrices n (qftSteps n) := by
  obtain ⟨t, run, values, trace⟩ := body_exec safe s
  exact ⟨t, (machine_eval_iff _ _ _ _).2 run, values, trace⟩

def executes (n : Nat) (proc : Proc) (u : Operator n) : Prop :=
  ∃ t, QASM.Execution.ControlMachine.eval (machine n) proc (default : State n) =
    some (t, .ok .next) ∧ eventMatrix t.events = u

def faultFrom (proc : Proc) (s : State n) : Prop :=
  ∃ t, QASM.Execution.ControlMachine.eval (machine n) proc s = some (t, .error ())

def fault (n : Nat) (proc : Proc) : Prop := faultFrom proc (default : State n)

theorem body_totalCorrect (safe : QFTRangeSafe n w iw) (s : State n) :
    TotalCorrect (model (kernel n)) faultFrom (body n w iw) s
      (fun t flow => flow = .next ∧ t.values = s.values ∧
        t.events = s.events ++ matrices n (qftSteps n)) := by
  obtain ⟨t, run, values, trace⟩ := body_total safe s
  refine ⟨⟨t, .next, (machine_eval_iff _ _ _ _).1 run⟩, ?_, ?_⟩
  · intro final flow h
    have result := (machine_eval_iff _ _ _ _).2 h
    have eq := Option.some.inj (result.symm.trans run)
    have ht : final = t := congrArg Prod.fst eq
    have hf : flow = .next := by
      have hf := congrArg Prod.snd eq
      exact Except.ok.inj hf
    refine ⟨hf, ?_⟩
    simpa only [ht] using And.intro values trace
  · rintro ⟨final, failed⟩
    rw [run] at failed
    cases failed

theorem eventMatrix_steps (steps : List QFTStep) :
    eventMatrix (matrices n steps) =
      steps.foldl (fun acc step => sequential acc (stepOperator n step)) 1 := by
  simp [eventMatrix, matrices, List.foldl_map, sequential]

theorem body_action (safe : QFTRangeSafe n w iw) (s : State n) :
    ∃ t, QASM.Execution.ControlMachine.eval (machine n) (body n w iw) s = some (t, .ok .next) ∧
      t.values = s.values ∧ eventMatrix t.events = fourier n * eventMatrix s.events := by
  obtain ⟨t, run, values, trace⟩ := body_total safe s
  refine ⟨t, run, values, ?_⟩
  rw [trace, eventMatrix_append, eventMatrix_steps, ← qftMatrix, qftCorrect]

/-- Unconditional every-size total correctness for the original residual Proc body. -/
theorem qftProgramCorrect : QFTProgramCorrect executes fault := by
  intro n
  obtain ⟨t, run, _, trace⟩ := body_total (canonical_range_safe n) (default : State n)
  have matrix : eventMatrix t.events = fourier n := by
    rw [trace]
    change eventMatrix (matrices n (qftSteps n)) = fourier n
    rw [eventMatrix_steps, ← qftMatrix, qftCorrect]
  refine ⟨⟨t, run, matrix⟩, ?_, ?_⟩
  · intro u h
    obtain ⟨other, result, hu⟩ := h
    have ht : other = t := congrArg Prod.fst (Option.some.inj (result.symm.trans run))
    exact hu.symm.trans (ht ▸ matrix)
  · rintro ⟨other, failed⟩
    rw [run] at failed
    cases failed

end QASMVerification.QFTExecution

namespace QASMVerification
/-- The residual-loop contract, instantiated by the exact shared-machine model. -/
theorem qftProgramCorrect_all :
    QFTProgramCorrect QFTExecution.executes QFTExecution.fault :=
  QFTExecution.qftProgramCorrect
end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
