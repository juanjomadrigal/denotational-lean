
import Mathlib.Tactic

open Classical

section Definitions

class PO (P : Type u) where
  ple : P → P → Prop
  po_ref : ∀ (p : P) , ple p p
  po_trans : ∀ (p q r : P) , ple p q -> ple q r -> ple p r
  po_antisym : ∀ (p q : P) , ple p q -> ple q p -> p = q

notation:50 p:50 "⊑" q:50 => PO.ple p q

def upper_bound {P : Type u} [PO P] (X : Set P) (p : P) : Prop :=
  ∀ (q : P) , q ∈ X -> q ⊑ p

@[simp, grind]
def least_upper_bound {P : Type u} [PO P] (X : Set P) (p : P) : Prop :=
  upper_bound X p ∧ ∀ (q : P) , upper_bound X q -> p ⊑ q

@[simp, grind]
def omega_chain {P : Type u} [PO P] (d : Nat -> P) : Prop :=
  ∀ (n : Nat) , d n ⊑ d (n+1)

def OmegaChain (P : Type u) [PO P] :=
  {d : Nat -> P // omega_chain d}

instance [PO P] : CoeFun (OmegaChain P) (fun _ => Nat -> P) where
  coe | ⟨d, _⟩ => d

namespace OmegaChain
@[simp, grind]
def set {P : Type u} [PO P] (d : OmegaChain P) : Set P := {d n | n : Nat}
end OmegaChain

class CPO (P : Type u) extends PO P where
  chain_lub : ∀ (d : Nat -> P) , omega_chain d ->
    ∃ (p : P) , least_upper_bound {d n | n : Nat} p

class CPOB (P : Type u) extends CPO P where
  bot : P
  is_bot : ∀ (p : P) , bot ⊑ p

notation "⊥" => CPOB.bot

end Definitions

section Instances

/- Exercise 5.10 -/

local instance flatCPO : CPO P where
  ple p q := p = q
  po_ref := by grind
  po_trans := by grind
  po_antisym := by grind
  chain_lub := by
    intro d h
    have h1 : ∀ (n : Nat) , d n = d 0 := by
      intro n
      induction n <;> grind
    simp [h1]
    exists d 0
    simp [upper_bound]

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
    simp [upper_bound]
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
        have _ : d mm x = none ∨ d mm x = d (mm + 1) x := by grind
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
    simp [upper_bound]
    grind
  bot := fun _ => none
  is_bot := by grind

end Instances

section LeastUpperBound

section Set

variable {P : Type u} [PO P] (X : Set P)

theorem unique_lub :
  ∀ (p q : P) , least_upper_bound X p ∧ least_upper_bound X q -> p = q
:= by
  grind [PO.po_antisym]

@[simp, grind]
noncomputable def lub_set : Option P :=
  if h : ∃ (p : P) , least_upper_bound X p
    then some (choose h)
    else none

@[simp, grind]
theorem lub_set_correct :
  ∀ (p : P) , least_upper_bound X p <-> lub_set X = some p
:= by
  intro p
  apply Iff.intro
  . intro h
    simp
    use ⟨p,h⟩
    grind [choose_spec, unique_lub]
  . simp
    grind [choose_spec, unique_lub]

end Set

section Chain

variable {P : Type u} [CPO P] (d : OmegaChain P)

noncomputable def lub_chain : P :=
  choose (CPO.chain_lub d.val d.prop)
notation:60 "⨆" d:60 => lub_chain d

@[simp, grind]
theorem lub_set_chain :
  lub_set d.set = some (lub_chain d)
:= by
  simp only [lub_set]
  grind [lub_chain]

end Chain

section Bottom

variable {P : Type u} [CPOB P]

lemma bottom_least_upper_bound (X : Set P) (p : P) :
  least_upper_bound X p <-> least_upper_bound (insert CPOB.bot X) p
:= by
  apply Iff.intro
  . intro h
    simp
    apply And.intro
    . grind [upper_bound, CPOB.is_bot]
    . intro q h
      have _ : upper_bound X q := by grind [upper_bound]
      grind
  . intro h
    simp
    apply And.intro
    . grind [upper_bound]
    . intro q h
      have _ : upper_bound (insert CPOB.bot X) q := by grind [upper_bound, CPOB.is_bot]
      grind

@[simp, grind]
theorem bottom_lub_set (X : Set P) :
  lub_set (insert CPOB.bot X) = lub_set X
:= by
  cases h1 : lub_set X with
  | none => cases h2 : lub_set (insert CPOB.bot X) with
    | none => rfl
    | some q =>
      have _ : least_upper_bound (insert CPOB.bot X) q := by grind
      have _ : least_upper_bound X q := by grind [bottom_least_upper_bound]
      have _ : lub_set X = q := by grind
      grind
  | some p =>
    have _ : least_upper_bound X p := by grind
    have _ : least_upper_bound (insert CPOB.bot X) p := by grind [bottom_least_upper_bound]
    have _ : lub_set (insert CPOB.bot X) = p := by grind
    grind

def insert_bottom_chain (d : OmegaChain P) : OmegaChain P
:= ⟨
  fun n => match n with | .zero => ⊥ | .succ m => d m,
  by
    simp
    intro n
    cases n
    . simp [CPOB.is_bot]
    . apply d.prop
⟩

lemma insert_bottom_chain_set (d : OmegaChain P) :
  insert CPOB.bot d.set = (insert_bottom_chain d).set
:= by
  simp [insert_bottom_chain]
  apply Set.ext
  intro p
  apply Iff.intro
  . simp
    intro h
    cases h with
    | inl => use 0; grind
    | inr h => let ⟨n,hh⟩ := h ; use n+1
  . simp
    intro n
    cases n <;> grind

lemma insert_bottom_chain_lub (d : OmegaChain P) : ⨆ insert_bottom_chain d = ⨆ d := by
  have _ : some (⨆ insert_bottom_chain d) = some (⨆ d) := by
    calc
      some (⨆ insert_bottom_chain d)
      _ = lub_set (insert_bottom_chain d).set := by grind
      _ = lub_set (insert CPOB.bot d.set) := by have _ := insert_bottom_chain_set d ; grind
      _ = lub_set d.set := by grind
      _ = some (⨆ d) := by grind
  grind

end Bottom

end LeastUpperBound

section GreatestLowerBound

variable {P : Type u} [PO P] (X : Set P)

def lower_bound (p : P) : Prop :=
  ∀ (q : P) , q ∈ X -> p ⊑ q

@[simp, grind]
def greatest_lower_bound (p : P) : Prop :=
  lower_bound X p ∧ ∀ (q : P) , lower_bound X q -> q ⊑ p

theorem unique_glb :
  ∀ (p q : P) , greatest_lower_bound X p ∧ greatest_lower_bound X q -> p = q
:= by
  grind [PO.po_antisym]

@[simp, grind]
noncomputable def glb_set : Option P :=
  if h : ∃ (p : P) , greatest_lower_bound X p
    then some (choose h)
    else none

@[simp, grind]
theorem glb_set_correct :
  ∀ (p : P) , greatest_lower_bound X p <-> glb_set X = some p
:= by
  intro p
  apply Iff.intro
  . intro h
    simp
    use ⟨p,h⟩
    grind [choose_spec, unique_glb]
  . simp
    grind [choose_spec, unique_glb]

-- complete lattice
class CL (P : Type u) extends PO P where
  glb : ∀ (X : Set P) , ∃ (p : P) , greatest_lower_bound X p
  lub : ∀ (X : Set P) , ∃ (p : P) , least_upper_bound X p

end GreatestLowerBound

section Dual

def Dual (P : Type*) : Type _ := P

instance dualPO (P : Type*) [inst : PO P] : PO (Dual P) where
  ple p q := inst.ple q p
  po_ref := inst.po_ref
  po_trans := by intro p q r h1 h2 ; exact inst.po_trans r q p h2 h1
  po_antisym := by intro p q h1 h2 ; exact inst.po_antisym p q h2 h1

lemma dual_ub_lb {P : Type u} [inst : PO P] (X : Set P) (p : P) :
  @upper_bound P inst X p <-> @lower_bound P (dualPO P) X p
:= by
  apply Iff.intro <;> exact id

lemma dual_lb_ub {P : Type u} [inst : PO P] (X : Set P) (p : P) :
  @lower_bound P inst X p <-> @upper_bound P (dualPO P) X p
:= by
  apply Iff.intro <;> exact id

lemma dual_lub_glb {P : Type u} [inst : PO P] (X : Set P) (p : P) :
  @least_upper_bound P inst X p <-> @greatest_lower_bound P (dualPO P) X p
:= by
  apply Iff.intro <;> exact id

lemma dual_glb_lub {P : Type u} [inst : PO P] (X : Set P) (p : P) :
  @greatest_lower_bound P inst X p <-> @least_upper_bound P (dualPO P) X p
:= by
  apply Iff.intro <;> exact id

instance dualCL [inst : CL P] : CL (Dual P) where
  glb := inst.lub
  lub := inst.glb

end Dual
