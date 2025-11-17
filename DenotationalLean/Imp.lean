
/-! # 2.1 IMP - a simple imperative language -/

abbrev Loc := String

inductive Aexp : Type where
  | Nat : Nat -> Aexp
  | Loc : Loc -> Aexp
  | Add : Aexp -> Aexp -> Aexp
  | Sub : Aexp -> Aexp -> Aexp
  | Mul : Aexp -> Aexp -> Aexp
deriving Repr

notation:80 "|" n:80 "|" => Aexp.Nat n
notation:80 "#" l:80 => Aexp.Loc l
notation:75 a1:75 "+" a2:75 => Aexp.Add a1 a2
notation:75 a1:75 "-" a2:75 => Aexp.Sub a1 a2
notation:75 a1:75 "*" a2:75 => Aexp.Mul a1 a2

inductive Bexp : Type where
  | Bool : Bool -> Bexp
  | Eq : Aexp -> Aexp -> Bexp
  | Le : Aexp -> Aexp -> Bexp
  | Not : Bexp -> Bexp
  | And : Bexp -> Bexp -> Bexp
  | Or  : Bexp -> Bexp -> Bexp
deriving Repr

notation:80 "|" t:80 "|" => Bexp.Bool t
notation:75 a1:75 "==" a2:75 => Bexp.Eq a1 a2
notation:75 a1:75 "<=" a2:75 => Bexp.Le a1 a2
notation:70 "¬" b:70 => Bexp.Not b
notation:70 b1:70 " and " b2:70 => Bexp.And b1 b2
notation:70 b1:70 " or " b2:70 => Bexp.Or b1 b2

inductive Com : Type where
  | Skp : Com
  | Assign : Loc -> Aexp -> Com
  | Seq : Com -> Com -> Com
  | Ite : Bexp -> Com -> Com -> Com
  | Wh : Bexp -> Com -> Com
deriving Repr

notation "Skip" => Com.Skp
notation:60 l:60 "::=" a:60 => Com.Assign l a
notation:60 c1:60 ";;" c2:60 => Com.Seq c1 c2
notation:60 "If " b:60 " Then " c1:60 " Else " c2:60 => Com.Ite b c1 c2
notation:60 "While " b:60 " Do " c:60 => Com.Wh b c
