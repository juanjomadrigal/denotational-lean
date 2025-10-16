
import DenotationalLean.Imp
import DenotationalLean.ADeriv

abbrev BConfig := Bexp × State

inductive b_deriv : BConfig -> Bool -> Prop
  | bool {t σ} : b_deriv (Bexp.Bool t, σ) t
  | eq {a0 n0 a1 n1 σ} : a_deriv (a0, σ) n0 -> a_deriv (a1, σ) n1 -> b_deriv (Bexp.Eq a0 a1, σ) (n0 == n1)
  | le {a0 n0 a1 n1 σ} : a_deriv (a0, σ) n0 -> a_deriv (a1, σ) n1 -> b_deriv (Bexp.Le a0 a1, σ) (n0 <= n1)
  | not {b t σ} : b_deriv (b, σ) t -> b_deriv (Bexp.Not b, σ) (!t)
  | and {b0 t0 b1 t1 σ} : b_deriv (b0, σ) t0 -> b_deriv (b1, σ) t1 -> b_deriv (Bexp.And b0 b1, σ) (t0 && t1)
  | or  {b0 t0 b1 t1 σ} : b_deriv (b0, σ) t0 -> b_deriv (b1, σ) t1 -> b_deriv (Bexp.Or  b0 b1, σ) (t0 || t1)

def b_equiv (b0 b1 : Bexp) : Prop :=
  ∀ (t : Bool) (σ : State) , (b_deriv (b0,σ) t) <-> (b_deriv (b1,σ) t)
