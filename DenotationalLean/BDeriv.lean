
import DenotationalLean.Imp
import DenotationalLean.ADeriv
import DenotationalLean.State

/-! # 2.3 The evaluation of boolean expressions -/

@[grind]
inductive b_deriv : Bexp -> State -> Bool -> Prop
  | bool {t σ} : b_deriv (|t|) σ t
  | eq {a0 n0 a1 n1 σ} : ⟨a0,σ⟩ ~~> n0 -> ⟨a1,σ⟩ ~~> n1 -> b_deriv (a0 == a1) σ (n0 == n1)
  | le {a0 n0 a1 n1 σ} : ⟨a0,σ⟩ ~~> n0 -> ⟨a1,σ⟩ ~~> n1 -> b_deriv (a0 <= a1) σ (n0 <= n1)
  | not {b t σ} : b_deriv b σ t -> b_deriv (¬ b) σ (!t)
  | and {b0 t0 b1 t1 σ} : b_deriv b0 σ t0 -> b_deriv b1 σ t1 -> b_deriv (b0 and b1) σ (t0 && t1)
  | or  {b0 t0 b1 t1 σ} : b_deriv b0 σ t0 -> b_deriv b1 σ t1 -> b_deriv (b0 or  b1) σ (t0 || t1)

notation:40 "⟨" b:40 "," σ:40 "⟩" " ~~> " σ':40 => b_deriv b σ σ'

def b_equiv (b0 b1 : Bexp) : Prop :=
  ∀ (t : Bool) (σ : State) , ⟨b0,σ⟩ ~~> t <-> ⟨b1,σ⟩ ~~> t

/- Exercise 3.5 -/

@[simp, grind]
theorem b_unique (b : Bexp) (σ : State) :
    ∀ (t0 t1 : Bool) , ⟨b,σ⟩ ~~> t0 ∧ ⟨b,σ⟩ ~~> t1 -> t0 = t1 := by
  induction b <;>
  intro t0 t1 <;> intro ⟨h0,h1⟩ <;>
  cases h0 <;> cases h1 <;> grind

@[simp, grind]
def b_eval (b : Bexp) (σ : State) : Bool :=
  match b with
  | .Bool t => t
  | .Eq a0 a1 => a_eval a0 σ == a_eval a1 σ
  | .Le a0 a1 => a_eval a0 σ <= a_eval a1 σ
  | .Not b => !(b_eval b σ)
  | .And b0 b1 => b_eval b0 σ && b_eval b1 σ
  | .Or  b0 b1 => b_eval b0 σ || b_eval b1 σ

@[simp, grind]
theorem b_eval_deriv (b : Bexp) (σ : State) : ⟨b,σ⟩ ~~> b_eval b σ :=
  match b with
  | .Bool _ => b_deriv.bool
  | .Eq a0 a1 => b_deriv.eq (a_eval_deriv a0 σ) (a_eval_deriv a1 σ)
  | .Le a0 a1 => b_deriv.le (a_eval_deriv a0 σ) (a_eval_deriv a1 σ)
  | .Not b => b_deriv.not (b_eval_deriv b σ)
  | .And b0 b1 => b_deriv.and (b_eval_deriv b0 σ) (b_eval_deriv b1 σ)
  | .Or  b0 b1 => b_deriv.or  (b_eval_deriv b0 σ) (b_eval_deriv b1 σ)
