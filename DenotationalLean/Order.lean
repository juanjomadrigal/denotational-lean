import Mathlib.Tactic

open Classical

class PO (P : Type u) where
  ple : P → P → Prop
  po_ref : ∀ (p : P) , ple p p
  po_trans : ∀ (p q r : P) , ple p q -> ple q r -> ple p r
  po_antisym : ∀ (p q : P) , ple p q -> ple q p -> p = q

notation:50 p:50 "⊑" q:50 => PO.ple p q

def upper_bound {P : Type u} [PO P] (X : Set P) (p : P) : Prop :=
  ∀ (q : P) , q ∈ X -> q ⊑ p

def least_upper_bound {P : Type u} [PO P] (X : Set P) (p : P) : Prop :=
  upper_bound X p ∧ ∀ (q : P) , upper_bound X q -> p ⊑ q

def omega_chain {P : Type u} [PO P] (d : Nat -> P) : Prop :=
  ∀ (n : Nat) , d n ⊑ d (n+1)

def OmegaChain (P : Type u) [PO P] :=
  {d : Nat -> P // omega_chain d}

instance [PO P] : CoeFun (OmegaChain P) (fun _ => Nat -> P) where
  coe | ⟨d, _⟩ => d

class CPO (P : Type u) extends PO P where
  chain_lub : ∀ (d : Nat -> P) , omega_chain d ->
    ∃ (p : P) , least_upper_bound {d n | n : Nat} p

noncomputable def lub {P : Type u} [CPO P] (d : OmegaChain P) : P :=
  choose (CPO.chain_lub d.val d.prop)
notation:60 "⨆" d:60 => lub d

class CPOB (P : Type u) extends CPO P where
  bot : P
  is_bot : ∀ (p : P) , bot ⊑ p

notation "⊥" => CPOB.bot

/- Exercise 5.10 -/

def flatCPO : CPO P where
  ple p q := p = q
  po_ref := by grind
  po_trans := by grind
  po_antisym := by grind
  chain_lub := by
    intro d h
    have h1 : ∀ (n : Nat) , d n = d 0 := by
      intro n
      induction n <;> grind [omega_chain]
    simp [h1]
    exists d 0
    simp [least_upper_bound, upper_bound]

instance powCPOB : CPOB (Set P) where
  ple p q := p ⊆ q
  po_ref := by grind
  po_trans := by grind
  po_antisym := by
    intro p q h1 h2
    apply Set.ext
    grind
  chain_lub := by
    intro d h
    exists ⋃ n:Nat , d n
    simp [least_upper_bound, upper_bound]
    intro n
    apply Set.subset_iUnion
  bot := ∅
  is_bot := by grind

instance partCPOB : CPOB (X -> Option X) where
  ple p q := ∀ (x : X) , p x = none ∨ p x = q x
  po_ref := by grind
  po_trans := by grind
  po_antisym := by
    intro p q h1 h2
    apply funext
    grind
  chain_lub := by
    intro d h
    let p : X -> Option X := fun x =>
      let ns := {n : Nat | d n x ≠ none}
      if h : ns.Nonempty then
        d (Nat.find h) x
      else
        none
    exists p
    have aux1 :
      ∀ (m n : Nat) (x : X) , m >= n -> d n x = none ∨ d m x = d n x
    := by
      intro m
      induction m with
      | zero => grind
      | succ mm =>
        intro n x
        have _ : d mm x = none ∨ d mm x = d (mm + 1) x := by grind [omega_chain]
        grind
    have aux2 :
      ∀ (m n : Nat) (x : X) , d m x ≠ none ∧ d n x ≠ none -> d m x = d n x
    := by grind
    have aux3 :
      ∀ (n : Nat) (x : X) , d n x = none ∨ d n x = p x
    := by
      intro n x
      cases _ : d n x with
      | none => grind
      | some y =>
        simp [p]
        exists ⟨n, by grind⟩
        grind
    simp [least_upper_bound, upper_bound]
    grind
  bot := fun _ => none
  is_bot := by grind

def monotonic {P Q : Type u} [CPO P] [CPO Q] (f : P -> Q) : Prop :=
  ∀ (p p' : P) , p ⊑ p' -> f p ⊑ f p'

def Monotonic (P Q : Type u) [CPO P] [CPO Q] :=
  {f : P -> Q // monotonic f}

instance [CPO P] [CPO Q] : CoeFun (Monotonic P Q) (fun _ => P -> Q) where
  coe | ⟨f, _⟩ => f

def map {P Q : Type u} [CPO P] [CPO Q]
  (f : Monotonic P Q) (d : OmegaChain P) : OmegaChain Q
:= ⟨
  fun n => f (d n),
  by
    simp [omega_chain]
    intro n
    apply f.prop
    apply d.prop
⟩

def cont {P Q : Type u} [CPO P] [CPO Q] (f : Monotonic P Q) : Prop :=
  ∀ (d : OmegaChain P) , ⨆ (map f d) = f (⨆ d)

def Cont (P Q : Type u) [CPO P] [CPO Q] :=
  {f : Monotonic P Q // cont f}

instance [CPO P] [CPO Q] : Coe (Cont P Q) (Monotonic P Q) where
  coe | ⟨f, _⟩ => f

instance [CPO P] [CPO Q] : CoeFun (Cont P Q) (fun _ => P -> Q) where
  coe | f => (f : Monotonic P Q)
