
import DenotationalLean.Imp
import DenotationalLean.ADeriv
import DenotationalLean.BDeriv
import DenotationalLean.State

import Mathlib.Tactic

/-! # 2.4 The execution of commands -/

inductive c_deriv : Com -> State -> State -> Prop
  | skip {σ} : c_deriv Skip σ σ
  | assign {a n l σ} : a_deriv a σ n -> c_deriv (l ::= a) σ ((l,n)::σ)
  | seq {c0 c1 σ σ' σ''} : c_deriv c0 σ σ'' -> c_deriv c1 σ'' σ' -> c_deriv (c0 ;; c1) σ σ'
  | ite_true  {b c0 c1 σ σ'} : ⟨b,σ⟩ ~~> true  -> c_deriv c0 σ σ' -> c_deriv (If b Then c0 Else c1) σ σ'
  | ite_false {b c0 c1 σ σ'} : ⟨b,σ⟩ ~~> false -> c_deriv c1 σ σ' -> c_deriv (If b Then c0 Else c1) σ σ'
  | while_false {b c σ} : ⟨b,σ⟩ ~~> false -> c_deriv (While b Do c) σ σ
  | while_true {b c σ σ' σ''} : ⟨b,σ⟩ ~~> true -> c_deriv c σ σ'' -> c_deriv (While b Do c) σ'' σ' -> c_deriv (While b Do c) σ σ'

notation:40 "⟨" c:40 "," σ:40 "⟩" " ~~> " σ':40 => c_deriv c σ σ'

def c_equiv (c0 c1 : Com) : Prop :=
  ∀ (σ σ': State) , ⟨c0,σ⟩ ~~> σ' <-> ⟨c1,σ⟩ ~~> σ'

/- example: ⟨while true do skip, σ⟩ -> σ' is not achievable  -/

example : ¬ ∃ (σ σ' : State) , ⟨While |true| Do Skip,σ⟩ ~~> σ' := by
  intro ⟨σ,σ',h⟩
  generalize hcom : While |true| Do Skip = com
  rw [hcom] at h
  induction h with
  | skip | assign | seq | ite_true | ite_false => grind
  | while_false bd =>
    simp only [Com.Wh.injEq] at hcom
    simp only [<-hcom] at bd
    nomatch bd
  | @while_true _ _ _ _ σ'' _ cd _ _ ih =>
    have h' : σ = σ'' := by cases cd <;> grind
    simp only [Com.Wh.injEq] at hcom
    simp [<-hcom] at ih

/-! # 2.5 A simple proof -/

/- Proposition 2.8 -/

example : c_equiv (While b Do c) (If b Then c ;; While b Do c Else Skip) := by
  let w := While b Do c
  intro σ σ'
  apply Iff.intro
  . intro d
    cases d with
    | while_false bd => exact c_deriv.ite_false bd c_deriv.skip
    | while_true bd cd wcd =>
      let h : ⟨c ;; While b Do c, σ⟩ ~~> σ' := c_deriv.seq cd wcd
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

/-! # 3.3 Well-founded induction -/

/- Theorem 3.10 -/

/- euclid := while ¬(M=N) do if M < N then N:=N-M else M:=M-N -/
def euclid : Com :=
  While ¬ #"M" == #"N"
  Do (If (#"M" <= #"N") Then ("N" ::= #"N" - #"M") Else ("M" ::= #"M" - #"N"))

-- fixme : to simplify a lot
theorem euclid_deriv :
    ∀ (σ : State) ,
    σ{"M"} >= 1 ∧ σ{"N"} >= 1
    -> ∃ (σ' : State) , ⟨euclid,σ⟩ ~~> σ'
:= by
  intro σ h

  let M := "M"
  let N := "N"
  let m := σ{M}
  let n := σ{N}

  let MsubN := #M - #N
  let NsubM := #N - #M
  let MeqN := #M == #N
  let MleN := #M <= #N

  let heq := m = n
  by_cases heq
  . have ev := b_eval_deriv (¬ MeqN) σ
    have h1 : (m == n) = true := by grind
    simp [b_eval,a_eval,m,n,h1,MeqN] at ev
    use σ
    exact .while_false ev
  . have ev := b_eval_deriv (¬ MeqN) σ
    have h1 : (m == n) = false := by grind
    simp [b_eval,a_eval,m,n,h1,MeqN] at ev
    let hlt := m <= n
    by_cases hlt
    . have h2 : (m <= n) = true := by grind
      let σ'' := (N,n-m)::σ
      have c1 : ⟨N ::= NsubM, σ⟩ ~~> σ'' := by
        apply c_deriv.assign
        apply a_eval_deriv
      have c : ⟨If MleN Then N ::= NsubM Else M ::= MsubN, σ⟩ ~~> σ'' := by
        apply c_deriv.ite_true
        have hhh : (b_eval MleN σ) = true := by rw [b_eval,a_eval,a_eval]; grind
        have lll := b_eval_deriv MleN σ
        simp [hhh] at lll
        trivial
        exact c1
      have q1 : σ''{M} = m := by rw [State.lookup]; grind
      have q2 : σ''{N} = n-m := by rw [State.lookup]; grind
      have q : σ''{M} >= 1 ∧ σ''{N} >= 1 := by grind
      have t : ((N, n-m) :: σ){N} < n := by grind
      have ⟨σ',p⟩ := euclid_deriv σ'' q
      use σ'
      exact .while_true ev c p
    . have h2 : (m <= n) = false := by grind
      let σ'' := (M,m-n)::σ
      have c1 : ⟨M ::= MsubN, σ⟩ ~~> σ'' := by
        apply c_deriv.assign
        apply a_eval_deriv
      have c : ⟨If MleN Then N ::= NsubM Else M ::= MsubN, σ⟩ ~~> σ'' := by
        apply c_deriv.ite_false
        have hhh : (b_eval MleN σ) = false := by rw [b_eval,a_eval,a_eval]; grind
        have lll := b_eval_deriv MleN σ
        simp [hhh] at lll
        trivial
        exact c1
      have q1 : σ''{M} = m-n := by rw [State.lookup]; grind
      have q2 : σ''{N} = n := by rw [State.lookup]; grind
      have q : σ''{M} >= 1 ∧ (σ''{N}) >= 1 := by grind
      have t : ((M, m-n) :: σ){M} < m := by grind
      have ⟨σ',p⟩ := euclid_deriv σ'' q
      use σ'
      exact .while_true ev c p
  termination_by σ => (σ{"M"} , σ{"N"})

/- Theorem 3.11 -/

theorem c_unique (c : Com) (σ : State) :
  ∀ (σ0 σ1 : State) , ⟨c,σ⟩ ~~> σ0 ∧ ⟨c,σ⟩ ~~> σ1 -> σ0 = σ1
:= by
  intro σ0 σ1 ⟨h0,h1⟩
  induction h0 generalizing σ1 <;> cases h1 <;> grind [a_unique, b_unique]

/- Proposition 4.7 -/

def loc (c : Com) : Set Loc :=
  match c with
  | .Skp => ∅
  | .Assign l _ => {l}
  | .Seq c0 c1 => loc c0 ∪ loc c1
  | .Ite _ c0 c1 => loc c0 ∪ loc c1
  | .Wh _ c => loc c

theorem loc_irrelev :
  ∀ (Y : Loc) (c : Com) (σ σ' : State) ,
  Y ∉ loc c ∧ ⟨c,σ⟩ ~~> σ' -> σ{Y} = σ'{Y}
:= by
  intro Y c
  induction c with
  | Skp | Assign | Seq | Ite =>
    intro σ σ' ⟨h0,h1⟩ ; simp [loc] at h0 ; cases h1 <;> grind [State.lookup]
  | Wh b c =>
    intro σ σ' ⟨h0,h1⟩ ; simp [loc] at h0
    generalize hcom : While b Do c = com
    rw [hcom] at h1
    induction h1 <;> grind
