import Denote.PCF.Stx

namespace PCF

def letters : List String := ["a", "b", "c", "d", "e", "f", "g"]

def natToLetter (i : Nat) : String := letters.getD i "z"

def Ty.show (ty : Ty) : String :=
  match ty with
  | .arr t1 t2 => "(" ++ Ty.show t1 ++ " → " ++ Ty.show t2 ++ ")"
  | .bool => "bool"
  | .nat => "nat"

def Term'.show {ty : Ty} (expr : Term' (fun _ => String) ty) (level : Nat := 0) : String :=
  match ty, expr with
  | _, .var s => s
  | _, .app t1 t2 => "(" ++ Term'.show t1 level ++ " " ++ Term'.show t2 level ++ ")"
  | .arr ty _, .lam f => "(λ" ++ natToLetter level ++ " : " ++ ty.show ++ ". " ++ Term'.show (f (natToLetter level)) (level + 1) ++ ")"

  | _, .true => "true"
  | _, .false => "false"

  | _, .zero => "0"
  | _, .succ t => "(succ " ++ Term'.show t level ++ ")"
  | _, .pred t => "(pred " ++ Term'.show t level ++ ")"
  | _, .z? t => "(z? " ++ Term'.show t level ++ ")"
  | _, .fix t => "(fix " ++ Term'.show t level ++ ")"
  | _, .ite c t f => s!"if {Term'.show c level} then {Term'.show t level} {Term'.show f level}"

end PCF
