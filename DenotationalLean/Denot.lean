import DenotationalLean.ADeriv
import DenotationalLean.BDeriv
import DenotationalLean.CDeriv

import Mathlib.Data.Part

open Classical

@[simp, grind]
def a_denot : Aexp -> State -> Nat :=
  fun a => fun σ => a_eval a σ

@[simp, grind]
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
    grind

@[simp, grind]
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
    simp
  | Add a0 a1 | Sub a0 a1 | Mul a0 a1 =>
    simp
    intro n
    apply Iff.intro
    . intro h
      use a_denot a0 σ
      use a_denot a1 σ
      grind
    . grind

@[simp, grind]
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
  induction b <;> simp <;> grind

def fix (Γ : Set α -> Set α) : Set α := ⋃ n:Nat , n.iterate Γ ∅

@[simp, grind]
def c_denot_set (c : Com) : Set (State × State) :=
  match c with
  | .Skp => {(σ,σ) | σ : State}
  | .Assign l a => {(σ,(l,a_eval a σ)::σ) | σ : State}
  | .Seq c0 c1 => {(σ,σ') | ∃ (σ'' : State) , (σ,σ'') ∈ c_denot_set c0 ∧ (σ'',σ') ∈ c_denot_set c1}
  | .Ite b c0 c1 => {(σ,σ') | (b_eval b σ = true) ∧ (σ,σ') ∈ c_denot_set c0} ∪ {(σ,σ') | (b_eval b σ = false) ∧ (σ,σ') ∈ c_denot_set c1}
  | .Wh b c => fix (fun φ => {(σ,σ') | (b_eval b σ = true) ∧ ∃ (σ'' : State) , (σ,σ'') ∈ c_denot_set c ∧ (σ'',σ') ∈ φ} ∪ {(σ,σ') | (b_eval b σ = false) ∧ σ' = σ})

def fix_wh (b : Bexp) (c : Com) : Set (State × State) -> Set (State × State) :=
  fun φ => {(σ,σ') | (b_eval b σ = true) ∧ ∃ (σ'' : State) , (σ,σ'') ∈ c_denot_set c ∧ (σ'',σ') ∈ φ} ∪ {(σ,σ') | (b_eval b σ = false) ∧ σ' = σ}

theorem c_denot_equiv :
  ∀ (c : Com) (σ σ' : State) , ⟨c,σ⟩ ~~> σ' <-> (σ,σ') ∈ c_denot_set c
:= by
  intro c σ σ'
  apply Iff.intro
  . intro h
    induction h with
    | skip | assign | seq | ite_true | ite_false => simp [c_denot_set] <;> grind
    | while_false =>
      simp [c_denot_set, fix]
      use 1
      simp ; grind
    | while_true hb hc whc h1 h2 =>
      simp [c_denot_set, fix] at h2
      let ⟨n,_⟩ := h2
      simp [c_denot_set, fix]
      use n + 1
      rw [Function.iterate_succ']
      grind
  . revert σ σ'
    induction c with
    | Skp | Assign | Seq | Ite => grind
    | Wh b c ih =>
      have aux : ∀ (n : Nat) (σ σ' : State) ,
          (σ,σ') ∈ (fix_wh b c)^[n] ∅ -> ⟨While b Do c,σ⟩ ~~> σ' := by
        intro n
        induction n with
        | zero => simp [Nat.iterate]
        | succ m ihh =>
          intro σ σ' h
          rw [Function.iterate_succ'] at h
          simp [fix_wh] at h
          cases h <;> grind
      intro σ σ' hh
      simp [c_denot_set, fix] at hh
      let ⟨n,_⟩ := hh
      apply aux n σ σ'
      grind
