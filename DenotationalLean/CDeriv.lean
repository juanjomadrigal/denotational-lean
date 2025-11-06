
import DenotationalLean.Imp
import DenotationalLean.ADeriv
import DenotationalLean.BDeriv
import DenotationalLean.State

/-! # 2.4 The execution of commands -/

abbrev CConfig := Com × State

inductive c_deriv : CConfig -> State -> Prop
  | skip {σ} : c_deriv (Com.Skip, σ) σ
  | assign {a n l σ} : a_deriv (a, σ) n -> c_deriv (Com.Assing l a, σ) ((l,n)::σ)
  | seq {c0 c1 σ σ' σ''} : c_deriv (c0,σ) σ'' -> c_deriv (c1,σ'') σ' -> c_deriv (Com.Seq c0 c1, σ) σ'
  | ite_true  {b c0 c1 σ σ'} : b_deriv (b,σ) true  -> c_deriv (c0,σ) σ' -> c_deriv (Com.Ite b c0 c1, σ) σ'
  | ite_false {b c0 c1 σ σ'} : b_deriv (b,σ) false -> c_deriv (c1,σ) σ' -> c_deriv (Com.Ite b c0 c1, σ) σ'
  | while_false {b c σ} : b_deriv (b,σ) false -> c_deriv (Com.While b c, σ) σ
  | while_true {b c σ σ' σ''} : b_deriv (b,σ) true -> c_deriv (c, σ) σ'' -> c_deriv (Com.While b c, σ'') σ' -> c_deriv (Com.While b c, σ) σ'

def c_equiv (c0 c1 : Com) : Prop :=
  ∀ (σ σ': State) , c_deriv (c0,σ) σ' <-> c_deriv (c1,σ) σ'

/- example: ⟨while true do skip, σ⟩ -> σ' is not achievable  -/

example : ¬ ∃ (σ σ' : State) , c_deriv (Com.While (Bexp.Bool true) Com.Skip, σ) σ' := by
  intro ⟨σ,σ',h⟩
  generalize hcfg : (Com.While (Bexp.Bool true) Com.Skip, σ) = cfg
  rw [hcfg] at h
  induction h with
  | skip | assign | seq | ite_true | ite_false => grind
  | while_false bd =>
    simp only [Prod.mk.injEq, Com.While.injEq] at hcfg
    simp only [<-hcfg] at bd
    nomatch bd
  | @while_true _ _ _ _ σ'' _ cd _ _ ih =>
    have h' : σ = σ'' := by cases cd <;> grind
    simp only [Prod.mk.injEq, Com.While.injEq] at hcfg
    simp [<-hcfg, h'] at ih

/-! # 2.5 A simple proof -/

/- Proposition 2.8 -/

example : c_equiv (Com.While b c) (Com.Ite b (Com.Seq c (Com.While b c)) Com.Skip) := by
  let w := Com.While b c
  intro σ σ'
  apply Iff.intro
  . intro d
    cases d with
    | while_false bd => exact c_deriv.ite_false bd c_deriv.skip
    | while_true bd cd wcd =>
      let h : c_deriv (Com.Seq c (Com.While b c), σ) σ' := c_deriv.seq cd wcd
      exact c_deriv.ite_true bd h
  . intro d
    cases d with
    | ite_false bd cd =>
      have h : σ = σ' := by cases cd; grind
      simp [<-h]
      exact c_deriv.while_false bd
    | ite_true bd cd =>
      cases cd with
      | seq cd0 cd1 => exact c_deriv.while_true bd cd0 cd1
