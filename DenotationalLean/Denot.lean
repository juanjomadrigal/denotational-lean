import DenotationalLean.ADeriv
import DenotationalLean.BDeriv
import DenotationalLean.CDeriv

import Mathlib.Data.Part

open Classical

def a_denot : Aexp -> State -> Nat :=
  fun a => fun σ => a_eval a σ

def b_denot : Bexp -> State -> Bool :=
  fun b => fun σ => b_eval b σ

noncomputable def c_denot : Com -> State -> Option State :=
  fun c => fun σ => if h : ∃ (σ' : State) , ⟨c,σ⟩ ~~> σ'
    then some (choose h)
    else none

theorem c_denot_correct :
  ∀ (c : Com) (σ σ' : State) , c_denot c σ = some σ' <-> ⟨c,σ⟩ ~~> σ'
:= by
  intro c σ σ'
  simp [c_denot]
  apply Iff.intro
  . intro h
    by_cases hh : ∃ σ', ⟨c,σ⟩ ~~> σ' <;> simp [hh] at h ; grind [choose_spec]
  . intro h
    have ex : ∃ σ', ⟨c,σ⟩ ~~> σ' := ⟨σ', h⟩
    have _ := choose_spec ex
    grind [c_unique]
