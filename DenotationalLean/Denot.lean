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

def a_denot_set (a : Aexp) : Set (State × Nat) :=
  match a with
  | .Nat n => {(σ,n) | σ : State}
  | .Loc l => {(σ,σ{l}) | σ : State}
  | .Add a0 a1 => {(σ,n) | ∃ (n0 n1 : Nat) , n0 + n1 = n ∧ (σ,n0) ∈ a_denot_set a0 ∧ (σ,n1) ∈ a_denot_set a1}
  | .Sub a0 a1 => {(σ,n) | ∃ (n0 n1 : Nat) , n0 - n1 = n ∧ (σ,n0) ∈ a_denot_set a0 ∧ (σ,n1) ∈ a_denot_set a1}
  | .Mul a0 a1 => {(σ,n) | ∃ (n0 n1 : Nat) , n0 * n1 = n ∧ (σ,n0) ∈ a_denot_set a0 ∧ (σ,n1) ∈ a_denot_set a1}

theorem a_denot_equiv :
  ∀ (a : Aexp) (σ : State) (n : Nat) , a_denot a σ = n <-> (σ,n) ∈ a_denot_set a
:= by
  intro a σ
  induction a with
  | Nat | Loc =>
    simp [a_denot_set, a_denot, a_eval]
  | Add a0 a1 | Sub a0 a1 | Mul a0 a1 =>
    simp [a_denot_set, a_denot, a_eval]
    intro n
    apply Iff.intro
    . intro h
      use a_denot a0 σ
      use a_denot a1 σ
      grind [a_denot]
    . grind [a_denot]

def b_denot_set (b : Bexp) : Set (State × Bool) :=
  match b with
  | .Bool t => {(σ,t) | σ : State}
  | .Eq a0 a1 => {(σ,a_eval a0 σ == a_eval a1 σ) | σ : State}
  | .Le a0 a1 => {(σ,decide (a_eval a0 σ <= a_eval a1 σ)) | σ : State}
  | .Not b => {(σ,t) | ∃ (t' : Bool) , (t = !t') ∧ (σ,t') ∈ b_denot_set b}
  | .And b0 b1 => {(σ,t) | ∃ (t0 t1 : Bool) , t = (t0 && t1) ∧ (σ,t0) ∈ b_denot_set b0 ∧ (σ,t1) ∈ b_denot_set b1}
  | .Or  b0 b1 => {(σ,t) | ∃ (t0 t1 : Bool) , t = (t0 || t1) ∧ (σ,t0) ∈ b_denot_set b0 ∧ (σ,t1) ∈ b_denot_set b1}

theorem b_denot_equiv :
  ∀ (b : Bexp) (σ : State) (t : Bool) , b_denot b σ = t <-> (σ,t) ∈ b_denot_set b
:= by
  intro b
  induction b <;> simp [b_denot_set, b_denot, b_eval] <;> grind [b_denot]
