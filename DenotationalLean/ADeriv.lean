
import DenotationalLean.Imp

abbrev State := Loc -> Nat
abbrev Config := Aexp × State

inductive a_deriv : Config -> Nat -> Prop
  | num {n σ} : a_deriv (Aexp.Nat n, σ) n
  | loc {l σ} : a_deriv (Aexp.Loc l, σ) (σ l)
  | add {a0 n0 a1 n1 σ} : a_deriv (a0,σ) n0 -> a_deriv (a1,σ) n1 -> a_deriv (Aexp.Add a0 a1,σ) (n0+n1)
  | sub {a0 n0 a1 n1 σ} : a_deriv (a0,σ) n0 -> a_deriv (a1,σ) n1 -> a_deriv (Aexp.Sub a0 a1,σ) (n0-n1)
  | mul {a0 n0 a1 n1 σ} : a_deriv (a0,σ) n0 -> a_deriv (a1,σ) n1 -> a_deriv (Aexp.Mul a0 a1,σ) (n0*n1)

example : a_deriv
    (Aexp.Add
      (Aexp.Add (Aexp.Loc "Init") (Aexp.Nat 5))
      (Aexp.Add (Aexp.Nat 7) (Aexp.Nat 9)),
    fun x => match x with | "Init" => 0 | _ => /- anything -/ 0)
    21 := by
  let σ := fun x => match x with | "Init" => 0 | _ => 0
  have h0 : σ "Init" = 0 := by rfl
  have hi := @a_deriv.loc "Init" σ
  simp [h0] at hi
  have h5 := @a_deriv.num 5 σ
  have h7 := @a_deriv.num 7 σ
  have h9 := @a_deriv.num 9 σ
  have hi5 := a_deriv.add hi h5
  have h79 := a_deriv.add h7 h9
  have h := a_deriv.add hi5 h79
  assumption

def a_equiv (a b : Aexp) : Prop :=
  ∀ (n : Nat) (σ : State) , (a_deriv (a,σ) n) <-> (a_deriv (b,σ) n)
