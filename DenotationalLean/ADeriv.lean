
import DenotationalLean.Imp
import DenotationalLean.State

/-! # 2.2 The evaluation of arithmetic expressions -/

inductive a_deriv : Aexp -> State -> Nat -> Prop
  | num {n σ} : a_deriv (Aexp.Nat n) σ n
  | loc {l σ} : a_deriv (Aexp.Loc l) σ (State.lookup σ l)
  | add {a0 n0 a1 n1 σ} : a_deriv a0 σ n0 -> a_deriv a1 σ n1 -> a_deriv (Aexp.Add a0 a1) σ (n0+n1)
  | sub {a0 n0 a1 n1 σ} : a_deriv a0 σ n0 -> a_deriv a1 σ n1 -> a_deriv (Aexp.Sub a0 a1) σ (n0-n1)
  | mul {a0 n0 a1 n1 σ} : a_deriv a0 σ n0 -> a_deriv a1 σ n1 -> a_deriv (Aexp.Mul a0 a1) σ (n0*n1)


/- example : ⟨(Init + 5) + (7 + 9), σ_0⟩ -> 21 -/
example : a_deriv
    ((#"Init" + |5|) + (|7| + |9|))
    [("Init",0)]
    21 := by
  let σ := [("Init",0)]
  have h0 : State.lookup σ "Init" = 0 := by rfl
  have hi := @a_deriv.loc "Init" σ
  simp [h0] at hi
  have h5 := @a_deriv.num 5 σ
  have h7 := @a_deriv.num 7 σ
  have h9 := @a_deriv.num 9 σ
  have hi5 := a_deriv.add hi h5
  have h79 := a_deriv.add h7 h9
  have h := a_deriv.add hi5 h79
  assumption

def a_equiv (a0 a1 : Aexp) : Prop :=
  ∀ (n : Nat) (σ : State) , (a_deriv a0 σ n) <-> (a_deriv a1 σ n)

/- Proposition 3.3 -/

theorem a_unique (a : Aexp) (σ : State) :
    ∀ (n0 n1 : Nat) , a_deriv a σ n0 ∧ a_deriv a σ n1 -> n0 = n1 := by
  induction a <;>
  intro n0 n1 <;> intro ⟨h0,h1⟩ <;>
  cases h0 <;> cases h1 <;> grind

/- Exercise 3.4 -/

def a_eval (a : Aexp) (σ : State) : Nat :=
  match a with
  | .Nat n => n
  | .Loc l => State.lookup σ l
  | .Add a0 a1 => a_eval a0 σ + a_eval a1 σ
  | .Sub a0 a1 => a_eval a0 σ - a_eval a1 σ
  | .Mul a0 a1 => a_eval a0 σ * a_eval a1 σ

theorem a_eval_deriv (a : Aexp) (σ : State) : a_deriv a σ (a_eval a σ) :=
  match a with
  | .Nat _ => a_deriv.num
  | .Loc _ => a_deriv.loc
  | .Add a0 a1 => a_deriv.add (a_eval_deriv a0 σ) (a_eval_deriv a1 σ)
  | .Sub a0 a1 => a_deriv.sub (a_eval_deriv a0 σ) (a_eval_deriv a1 σ)
  | .Mul a0 a1 => a_deriv.mul (a_eval_deriv a0 σ) (a_eval_deriv a1 σ)
