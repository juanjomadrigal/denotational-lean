
import DenotationalLean.Imp
import DenotationalLean.State

/-! # 2.2 The evaluation of arithmetic expressions -/

abbrev Config := Aexp × State

inductive a_deriv : Config -> Nat -> Prop
  | num {n σ} : a_deriv (Aexp.Nat n, σ) n
  | loc {l σ} : a_deriv (Aexp.Loc l, σ) (State.lookup σ l)
  | add {a0 n0 a1 n1 σ} : a_deriv (a0,σ) n0 -> a_deriv (a1,σ) n1 -> a_deriv (Aexp.Add a0 a1,σ) (n0+n1)
  | sub {a0 n0 a1 n1 σ} : a_deriv (a0,σ) n0 -> a_deriv (a1,σ) n1 -> a_deriv (Aexp.Sub a0 a1,σ) (n0-n1)
  | mul {a0 n0 a1 n1 σ} : a_deriv (a0,σ) n0 -> a_deriv (a1,σ) n1 -> a_deriv (Aexp.Mul a0 a1,σ) (n0*n1)


/- example : ⟨(Init + 5) + (7 + 9), σ_0⟩ -> 21 -/
example : a_deriv
    (Aexp.Add
      (Aexp.Add (Aexp.Loc "Init") (Aexp.Nat 5))
      (Aexp.Add (Aexp.Nat 7) (Aexp.Nat 9)),
    [("Init",0)])
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
  ∀ (n : Nat) (σ : State) , (a_deriv (a0,σ) n) <-> (a_deriv (a1,σ) n)

/- Proposition 3.3 -/

-- fixme : simplify
def a_unique (a : Aexp) (σ : State) : a_deriv (a,σ) n0 ∧ a_deriv (a,σ) n1 -> n0 = n1 := by
  intro ⟨h0,h1⟩
  cases a with
  | Nat n => cases h0; cases h1; trivial
  | Loc l => cases h0; cases h1; trivial
  | Add a0 a1 => cases h0 with
    | add h00 h01 => cases h1 with
      | add h10 h11 =>
        have f0 := a_unique a0 σ ⟨h00,h10⟩
        have f1 := a_unique a1 σ ⟨h01,h11⟩
        grind;
  | Sub a0 a1 => cases h0 with
    | sub h00 h01 => cases h1 with
      | sub h10 h11 =>
        have f0 := a_unique a0 σ ⟨h00,h10⟩
        have f1 := a_unique a1 σ ⟨h01,h11⟩
        grind;
  | Mul a0 a1 => cases h0 with
    | mul h00 h01 => cases h1 with
      | mul h10 h11 =>
        have f0 := a_unique a0 σ ⟨h00,h10⟩
        have f1 := a_unique a1 σ ⟨h01,h11⟩
        grind;
