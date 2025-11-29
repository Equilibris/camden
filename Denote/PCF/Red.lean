import Denote.PCF.Stx

namespace PCF

inductive ITerm.Val : ITerm Γ t → Prop
  | zero : Val .zero
  | succ : Val v → Val (.succ v)
  | true : Val .true
  | false : Val .false
  | lam : Val (.lam l)

inductive Red : ITerm [] t → ITerm [] t → Prop
  | val : v.Val → Red v v
  | succ : Red x v → Red (.succ x) (.succ v)
  | pred : Red x (.succ v) → Red (.pred x) v
  | z?z : Red x .zero → Red (.z? x) .true
  | z?s : Red x (.succ _) → Red (.z? x) .false
  | itet : Red c .true → Red t v → Red (.ite c t f) v
  | itef : Red c .false → Red f v → Red (.ite c t f) v
  | app : Red t (.lam f) → Red (f.parSubst <| .cons u .nil) v → Red (.app t u) v
  | fix : Red (.app t (.fix t)) v → Red (.fix t) v

theorem Red.rhs_Val (h : Red a b) : b.Val := by
  induction h
  any_goals assumption
  case succ ih => exact .succ ih
  case pred ih => cases ih; assumption
  case z?z => exact .true
  case z?s => exact .false

def Ω Γ t : ITerm Γ t := .fix <| .lam <| .var .hd

