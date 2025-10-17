
import DenotationalLean.Imp
import DenotationalLean.ADeriv
import DenotationalLean.BDeriv
import DenotationalLean.State

/-! # 2.4 The execution of commands -/

abbrev CConfig := Com × State

-- fixme : target should be Prop, but it then fails to show termination in the example below
inductive c_deriv : CConfig -> State -> Type
  | skip {σ} : c_deriv (Com.Skip, σ) σ
  | assign {a n l σ} : a_deriv (a, σ) n -> c_deriv (Com.Assing l a, σ) ((l,n)::σ)
  | seq {c0 c1 σ σ' σ''} : c_deriv (c0,σ) σ'' -> c_deriv (c1,σ'') σ' -> c_deriv (Com.Seq c0 c1, σ) σ'
  | ite_true  {b c0 c1 σ σ'} : b_deriv (b,σ) true  -> c_deriv (c0,σ) σ' -> c_deriv (Com.Ite b c0 c1, σ) σ'
  | ite_false {b c0 c1 σ σ'} : b_deriv (b,σ) false -> c_deriv (c1,σ) σ' -> c_deriv (Com.Ite b c0 c1, σ) σ'
  | while_false {b c σ} : b_deriv (b,σ) false -> c_deriv (Com.While b c, σ) σ
  | while_true {b c σ σ' σ''} : b_deriv (b,σ) true -> c_deriv (c, σ) σ'' -> c_deriv (Com.While b c, σ'') σ' -> c_deriv (Com.While b c, σ) σ'

-- fixme : remove Nonempty when c_deriv is Prop
def c_equiv (c0 c1 : Com) : Prop :=
  ∀ (σ σ': State) , Nonempty (c_deriv (c0,σ) σ') <-> Nonempty (c_deriv (c1,σ) σ')
-- def c_equiv (c0 c1 : Com) : Prop :=
--   ∀ (σ σ': State) , (c_deriv (c0,σ) σ') <-> (c_deriv (c1,σ) σ')

/- example: ⟨while true do skip, σ⟩ -> σ' is not achievable  -/

-- fixme : this definition should be inside the example below,
-- but then it's tricky to make the recursive definition
def aux (σ σ' : State) (hh : c_deriv (Com.While (Bexp.Bool true) Com.Skip, σ) σ') : False :=
  match hh with
    | c_deriv.while_false bd => by cases bd
    | @c_deriv.while_true _ _ σ σ' σ'' _ cd wcd => by
      have h : σ = σ'' := by cases cd; grind
      simp [<-h] at wcd
      exact aux σ σ' wcd

example : ¬ ∃ (σ σ' : State) , Nonempty (c_deriv (Com.While (Bexp.Bool true) Com.Skip, σ) σ') := by
  intro ⟨σ,σ',⟨h⟩⟩
  exact aux σ σ' h

/-! # 2.5 A simple proof -/

/- Proposition 2.8 -/

example : c_equiv (Com.While b c) (Com.Ite b (Com.Seq c (Com.While b c)) Com.Skip) := by
  let w := Com.While b c
  intro σ σ'
  apply Iff.intro
  . intro ⟨d⟩
    apply Nonempty.intro
    cases d with
    | while_false bd => exact c_deriv.ite_false bd c_deriv.skip
    | while_true bd cd wcd =>
      let h : c_deriv (Com.Seq c (Com.While b c), σ) σ' := c_deriv.seq cd wcd
      exact c_deriv.ite_true bd h
  . intro ⟨d⟩
    apply Nonempty.intro
    cases d with
    | ite_false bd cd =>
      have h : σ = σ' := by cases cd; grind
      simp [<-h]
      exact c_deriv.while_false bd
    | ite_true bd cd =>
      cases cd with
      | seq cd0 cd1 => exact c_deriv.while_true bd cd0 cd1
