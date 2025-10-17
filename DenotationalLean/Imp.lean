
abbrev Loc := String

inductive Aexp : Type where
  | Nat : Nat -> Aexp
  | Loc : Loc -> Aexp
  | Add : Aexp -> Aexp -> Aexp
  | Sub : Aexp -> Aexp -> Aexp
  | Mul : Aexp -> Aexp -> Aexp

inductive Bexp : Type where
  | Bool : Bool -> Bexp
  | Eq : Aexp -> Aexp -> Bexp
  | Le : Aexp -> Aexp -> Bexp
  | Not : Bexp -> Bexp
  | And : Bexp -> Bexp -> Bexp
  | Or  : Bexp -> Bexp -> Bexp

inductive Com : Type where
  | Skip : Com
  | Assing : Loc -> Aexp -> Com
  | Seq : Com -> Com -> Com
  | Ite : Bexp -> Com -> Com -> Com
  | While : Bexp -> Com -> Com
