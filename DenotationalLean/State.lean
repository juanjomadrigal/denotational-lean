
import DenotationalLean.Imp

abbrev State := List (Loc × Nat)

namespace State

def lookup(σ : State) : Loc -> Nat := fun l => match σ with
  | [] => 0
  | ((l',n)::xs) => if l == l' then n else lookup xs l

end State

notation:70 σ:70 "{" l:70 "}" => State.lookup σ l
