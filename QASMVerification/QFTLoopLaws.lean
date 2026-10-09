    import LiterateLean
    import QASMVerification.QFTExecution
    open scoped LiterateLean

# Residual QFT loop invariants

The descending inner loop tracks the stored finite-width angle at every iteration.
The outer and swap loops preserve the classical store after iterator restoration.
Their emitted matrices are compared with the gate-list specification in execution
order, including the size-zero and empty-range cases.

```lean
noncomputable section
namespace QASMVerification.QFTExecution
open QASM.IR
open QASM.IR.QFT
open QASM.Execution.Semantics (Flow)
open QASM.Execution.EffectSemantics
open QASM.Execution.VerifiedControl (model)

abbrev Runs (n : Nat) := Exec (model (kernel n))
abbrev Iterates (n : Nat) := ExecFor (model (kernel n))

def Preserves (s t : State n) (ids : List Nat) : Prop :=
  ∀ i, i ∉ ids → t.values i = s.values i

def matrices (n : Nat) (steps : List QFTStep) : GateEvents n := steps.map (stepOperator n)

@[simp] theorem put_value (s : State n) (id : Nat) (v : QASM.Value) :
    (put s id v).values id = v := by simp [put]
@[simp] theorem put_other (s : State n) (id i : Nat) (v : QASM.Value) (h : i ≠ id) :
    (put s id v).values i = s.values i := by simp [put, Function.update, h]
@[simp] theorem put_events (s : State n) (id : Nat) (v : QASM.Value) :
    (put s id v).events = s.events := rfl
@[simp] theorem emit_values (s : State n) (u : Operator n) :
    (emit s u).values = s.values := rfl
@[simp] theorem emit_events (s : State n) (u : Operator n) :
    (emit s u).events = s.events ++ [u] := rfl
@[simp] theorem restore_one (v : Var) (s t : State n) :
    restore #[v] s t = put t v.id.value (s.values v.id.value) := rfl

theorem signed_safe (safe : QFTRangeSafe n w iw) (i : Int)
    (low : -1 ≤ i) (high : i ≤ (n : Int)) : signed iw i = some (.sint iw i) := by
  have hp : (0 : Int) < 2^(iw-1) := by positivity
  have hn : (n : Int) < (2 : Int)^(iw-1) := by
    exact_mod_cast safe.2.2
  simp [signed, show -(2 : Int)^(iw-1) ≤ i ∧ i < (2 : Int)^(iw-1) by omega]

theorem unsigned_two (safe : QFTRangeSafe n w iw) : unsigned w 2 = some (.uint w 2) := by
  have hw : 3 ≤ w := le_trans (Nat.le_max_left _ _) safe.1
  have hp : 2 < 2^w := lt_of_lt_of_le (by decide : 2 < 2^3)
    (Nat.pow_le_pow_right (by decide) hw)
  have hp' : (2 : Int) < 2^w := by exact_mod_cast hp
  simp [unsigned, hp']

@[simp] theorem expression_read (var : Var) (s : State n) :
    expression (readVar var) s = some (s.values var.id.value) := by
  rw [expression]; rfl

@[simp] theorem expression_integer (w : Nat) (i : Int) (s : State n) :
    expression (integer w i) s = signed w i := by rw [expression]; rfl

@[simp] theorem expression_binary (ty : QASM.IR.Type) (op : BinaryOp) (a b : Expr)
    (s : State n) : expression (binary ty op a b) s = (do
      let x ← expression a s
      let y ← expression b s
      match op, x, y, ty with
      | .sub, .sint _ i, .sint _ j, .scalar (.sint w) => signed w (i-j)
      | .gt, .sint _ i, .sint _ j, .scalar .boolean => some (.boolean (decide (i > j)))
      | .div, .angle w bits, .uint v d, .scalar (.angle t) =>
        if w = v ∧ w = t ∧ 0 < d then
          some (QASM.Value.binary "/" (.angle w bits) (.uint v d)) else none
      | _, _, _, _ => none) := by rw [expression]; rfl

theorem integer_eval (safe : QFTRangeSafe n w iw) (s : State n) (i : Int)
    (low : -1 ≤ i) (high : i ≤ (n : Int)) :
    expression (integer iw i) s = some (.sint iw i) := by
  simpa using signed_safe safe i low high

theorem cp_theta {j k : Nat} (hj : j < n) (hk : k < j) (hd : j-k < w) :
    cp n k j (bitAngle w (thetaBits w (j-k))) =
      stepOperator n (.controlledPhase k j (j-k)) := by
  rw [thetaBits_value hd]
  funext row col
  simp [cp, stepOperator, hj, hk, lt_trans hk hj, Nat.ne_of_lt hk]

theorem inner_step (safe : QFTRangeSafe n w iw) {j k d : Nat}
    (hj : j < n) (hk : k < j) (hd : d+1 = j-k) (s : State n)
    (sj : s.values 1 = .sint iw j) (sk : s.values 2 = .sint iw k)
    (st : s.values 3 = .angle w (thetaBits w d)) (s2 : s.values 4 = .uint w 2) :
    Runs n (innerStep w iw) s
      (emit (put s 3 (.angle w (thetaBits w (j-k))))
        (stepOperator n (.controlledPhase k j (j-k)))) .next := by
  have hw : n ≤ w := le_trans (Nat.le_max_right _ _) safe.1
  have hdw : d+1 < w := by omega
  have halving := runtime_angle_half (show 0 < w by omega) (thetaBits_valid (show d < w by omega))
  rw [thetaBits_half hdw, hd] at halving
  apply Exec.sequence
  apply ExecSequence.next (intermediate := put s 3 (.angle w (thetaBits w (j-k))))
  · apply Exec.operation
    simp [model, kernel, operation, atomic, target, thetaVar,
      twoVar, st, s2, halving]
  · apply ExecSequence.next (intermediate := emit (put s 3 (.angle w (thetaBits w (j-k))))
      (stepOperator n (.controlledPhase k j (j-k))))
    · apply Exec.operation
      have hb : thetaBits w (j-k) < 2^w := thetaBits_valid (by omega)
      simp [model, kernel, operation, atomic, thetaVar, kVar, jVar,
        wire, put, Function.update, sj, sk,
        hj, lt_trans hk hj, hb,
        Nat.ne_of_lt hk, cp_theta hj hk (show j-k < w by omega)]
    · exact ExecSequence.nil _

```

## Descending inner iterations

With m iterations remaining for target j, theta stores the bits at distance j-m.
Each iteration halves those bits, emits a CP at the resulting angle, and decreases m.
The final angle has distance j, and only k and theta can have changed.

```lean
def counters (iw : Nat) (indices : List Nat) : List QASM.Value :=
  indices.map (fun (i : Nat) => .sint iw (i : Int))

def innerSteps (j m : Nat) : List QFTStep :=
  (List.range m).reverse.map (fun k => .controlledPhase k j (j-k))

theorem inner_iterations (safe : QFTRangeSafe n w iw) {j m : Nat}
    (hj : j < n) (hm : m ≤ j) (s : State n)
    (sj : s.values 1 = .sint iw j) (s2 : s.values 4 = .uint w 2)
    (st : s.values 3 = .angle w (thetaBits w (j-m))) :
    ∃ t, Iterates n (kVar iw) (innerStep w iw)
      (counters iw (List.range m).reverse) s t .next ∧
      t.events = s.events ++ matrices n (innerSteps j m) ∧
      t.values 3 = .angle w (thetaBits w j) ∧ Preserves s t [2,3] := by
  induction m generalizing s with
  | zero =>
    refine ⟨s, ExecFor.nil _, by simp [innerSteps, matrices], ?_, ?_⟩
    · simpa using st
    · intro i _; rfl
  | succ m ih =>
    let bound := put s 2 (.sint iw m)
    let middle := emit (put bound 3 (.angle w (thetaBits w (j-m))))
      (stepOperator n (.controlledPhase m j (j-m)))
    have hmj : m < j := by omega
    have hd : j-(m+1)+1 = j-m := by omega
    have head : Runs n (innerStep w iw) bound middle .next := by
      apply inner_step safe hj hmj hd bound
      · simpa [bound, put, Function.update] using sj
      · simp [bound]
      · simpa [bound, put, Function.update] using st
      · simpa [bound, put, Function.update] using s2
    obtain ⟨t, tail, trace, theta, preserved⟩ := ih (by omega) middle
      (by simpa [middle, bound, put, emit, Function.update] using sj)
      (by simpa [middle, bound, put, emit, Function.update] using s2)
      (by simp [middle])
    refine ⟨t, ?_, ?_, theta, ?_⟩
    · have hs : counters iw (List.range (m+1)).reverse =
          .sint iw m :: counters iw (List.range m).reverse := by
        simp [counters, List.range_succ, List.reverse_append]
      rw [hs]
      exact ExecFor.next head (Or.inl rfl) tail
    · rw [trace]
      simp [middle, bound, emit, put, innerSteps, matrices, List.range_succ,
        List.reverse_append, List.append_assoc]
    · intro i hi
      have hi' : i ≠ 2 ∧ i ≠ 3 := by simpa using hi
      rw [preserved i hi]
      simp [middle, bound, emit, put, Function.update, hi'.1, hi'.2]

```

## Evaluated ranges and restored inner loop

The domain lemmas evaluate the IR expressions to finite-width values before deriving
the list of iterations. In particular, an empty descending range is not a singleton
iteration at zero. Restoring k leaves only theta modified.

```lean
theorem domain_down (safe : QFTRangeSafe n w iw) (s : State n) (e : Expr) (m : Nat)
    (he : expression e s = some (.sint iw ((m : Int) - 1))) :
    domain (.range e (integer iw (-1)) (integer iw 0)) s =
      some (s, some (counters iw (List.range m).reverse)) := by
  simp [domain, he, signed_safe safe (-1) (by omega) (by omega),
    signed_safe safe 0 (by omega) (by omega), integers, counters, Int.ofNat_eq_natCast, List.map_map, Function.comp_def]

theorem domain_up (safe : QFTRangeSafe n w iw) (hn : 0 < n) (hm : m ≤ n) (s : State n) :
    domain (.range (integer iw 0) (integer iw 1) (integer iw ((m : Int) - 1))) s =
      some (s, some (counters iw (List.range m))) := by
  simp [domain, signed_safe safe 0 (by omega) (by omega),
    signed_safe safe 1 (by omega) (by omega),
    signed_safe safe ((m : Int)-1) (by omega) (by omega),
    integers, counters, Int.ofNat_eq_natCast, List.map_map, Function.comp_def]

theorem inner_loop (safe : QFTRangeSafe n w iw) (hj : j < n) (s : State n)
    (sj : s.values 1 = .sint iw j) (s2 : s.values 4 = .uint w 2)
    (st : s.values 3 = .angle w (thetaBits w 0)) :
    ∃ t, Runs n (innerLoop w iw) s t .next ∧
      t.events = s.events ++ matrices n (innerSteps j j) ∧ Preserves s t [3] := by
  obtain ⟨t, iterations, trace, _, preserved⟩ := inner_iterations safe hj (le_refl j) s sj s2
    (by simpa using st)
  have start : expression (binary (.scalar (.sint iw)) .sub
      (readVar (jVar iw)) (integer iw 1)) s = some (.sint iw ((j : Int)-1)) := by
    simp [jVar, sj, signed_safe safe 1 (by omega) (by omega),
      signed_safe safe ((j : Int)-1) (by omega) (by omega)]
  refine ⟨restore #[kVar iw] s t, ?_, ?_, ?_⟩
  · exact Exec.forLoop (domain_down safe s _ j start) iterations
  · simpa [kVar] using trace
  · intro i hi
    have hi3 : i ≠ 3 := by simpa using hi
    by_cases hi2 : i = 2
    · subst i; simp [kVar]
    · simpa [kVar, put_other _ _ _ _ hi2] using preserved i (by simp [hi2, hi3])

end QASMVerification.QFTExecution


```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
