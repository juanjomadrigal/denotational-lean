import DenotationalLean.Order.PartialOrder

section Definitions

def monotonic {P Q : Type u} [PO P] [PO Q] (f : P -> Q) : Prop :=
  ∀ (p p' : P) , p ⊑ p' -> f p ⊑ f p'

def Monotonic (P Q : Type u) [PO P] [PO Q] :=
  {f : P -> Q // monotonic f}

instance [PO P] [PO Q] : CoeFun (Monotonic P Q) (fun _ => P -> Q) where
  coe | ⟨f, _⟩ => f

def dual_mon {P Q : Type u} [PO P] [PO Q]
  (f : Monotonic P Q) : @Monotonic P Q dualPO dualPO
:= ⟨
  f.val,
  by intro p q ; exact f.prop q p
⟩

def map {P Q : Type u} [PO P] [PO Q]
  (f : Monotonic P Q) (d : OmegaChain P) : OmegaChain Q
:= ⟨
  fun n => f (d n),
  by
    simp
    intro n
    apply f.prop
    apply d.prop
⟩

def cont [CPO P] [CPO Q] (f : Monotonic P Q) : Prop :=
  ∀ (d : OmegaChain P) , ⨆ (map f d) = f (⨆ d)

def Cont (P Q : Type u) [CPO P] [CPO Q] :=
  {f : Monotonic P Q // cont f}

instance [CPO P] [CPO Q] : Coe (Cont P Q) (Monotonic P Q) where
  coe | ⟨f, _⟩ => f

instance [CPO P] [CPO Q] : CoeFun (Cont P Q) (fun _ => P -> Q) where
  coe | f => (f : Monotonic P Q)

end Definitions

section fix

variable {P : Type u}

@[simp, grind] def prefixed  [PO P] (f : P -> P) (p : P) : Prop := f p ⊑ p
@[simp, grind] def postfixed [PO P] (f : P -> P) (p : P) : Prop := p ⊑ f p
@[simp, grind] def fixed     [PO P] (f : P -> P) (p : P) : Prop := f p = p

def iter_bottom_chain [CPOB P] (f : Monotonic P P) : OmegaChain P
:= ⟨
  fun n => f^[n] ⊥,
  by
    simp
    intro n
    induction n
    . simp [CPOB.is_bot]
    . rw [Function.iterate_succ']
      apply f.prop
      assumption
⟩

noncomputable def fix_chain [CPOB P] (f : Monotonic P P) : P :=
  ⨆ iter_bottom_chain f

lemma insert_iter_bottom [CPOB P] (f : Monotonic P P) :
  (insert_bottom_chain (map f (iter_bottom_chain f))).val = (iter_bottom_chain f).val
:= by
  simp [insert_bottom_chain, iter_bottom_chain]
  apply funext
  intro n
  cases _ : n with
  | zero => simp
  | succ m => rw [Function.iterate_succ'] ; simp ; rfl

theorem fixed_point [CPOB P] (f : Cont P P) : fixed f (fix_chain f) := by
  let fc := iter_bottom_chain (f : Monotonic P P)
  simp [fixed]
  calc
    f (fix_chain f)
    _ = f (fix_chain f) := by rfl
    _ = f (⨆ fc) := by rfl
    _ = ⨆ (map f fc) := by have _ := f.prop fc ; grind
    _ = ⨆ insert_bottom_chain (map f fc) := by grind [insert_bottom_chain_lub]
    _ = ⨆ fc := by grind [insert_iter_bottom, Subtype.ext]
    _ = fix_chain f := by rfl

theorem least_prefixed_point [CPOB P] (f : Cont P P) :
  ∀ (p : P) , prefixed f p -> fix_chain f ⊑ p
:= by
  intro p h
  have _ : ∀ (n : Nat) , f^[n] ⊥ ⊑ p := by
    intro n
    induction n with
    | zero => grind [Nat.iterate, CPOB.is_bot]
    | succ m h =>
      rw [Function.iterate_succ']
      have _ : f (f^[m] ⊥) ⊑ f p := by apply f.val.prop ; grind
      have _ : f p ⊑ p := by grind [prefixed]
      grind [PO.po_trans]
  have _ : upper_bound (iter_bottom_chain f).set p :=
    by grind [upper_bound, iter_bottom_chain]
  have _ : lub_chain (iter_bottom_chain f) ⊑ p := by grind [lub_chain]
  grind [fix_chain]

end fix

section KnasterTarski

variable {L : Type u} [CL L] (f : Monotonic L L)

@[simp, grind]
def prefixed_set := { x | prefixed f x }
@[simp, grind]
noncomputable def min_prefixed := CL.glb <| prefixed_set f

@[simp, grind]
def postfixed_set := { x | postfixed f x }
@[simp, grind]
noncomputable def max_postfixed := CL.lub <| postfixed_set f

theorem knaster_tarski_minimum_fixed : fixed f (min_prefixed f) := by
  generalize g1 : prefixed_set f = X
  generalize g2 : min_prefixed f = m
  generalize g3 : f m = fm
  have _ : m = CL.glb X := by grind
  have _ : lower_bound X m := by grind [CL.glb]
  have _ : ∀ (x : L) , x ∈ X -> m ⊑ x := by grind
  have _ : ∀ (x : L) , x ∈ X -> fm ⊑ f x := by
    intro x _
    rw [<-g3]
    apply f.prop
    grind
  have _ : ∀ (x : L) , x ∈ X -> f x ⊑ x := by
    intro x _
    have _ : prefixed f x := by grind
    grind
  have _ : ∀ (x : L) , x ∈ X -> fm ⊑ x := by grind [PO.po_trans]
  have _ : lower_bound X fm := by grind
  have _ : fm ⊑ m := by
    rw [<-g2, min_prefixed, CL.glb]
    grind
  have _ : f fm ⊑ fm := by rw [<-g3] ; apply f.prop ; grind
  have _ : prefixed f fm := by grind
  have _ : fm ∈ X := by grind
  have _ : m ⊑ fm := by grind
  have _ : fm = m := by grind [PO.po_antisym]
  grind

theorem knaster_tarski_maximum_fixed : fixed f (max_postfixed f) := by
  exact @knaster_tarski_minimum_fixed (Dual L) dualCL (@dual_mon L L _ _ f)

end KnasterTarski
