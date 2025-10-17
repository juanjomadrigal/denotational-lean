
import DenotationalLean.Imp
import DenotationalLean.ADeriv
import DenotationalLean.BDeriv
import DenotationalLean.State

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
