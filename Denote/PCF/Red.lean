import Denote.PCF.Stx

namespace PCF

def Term'.subst : Term' (Term' A) t → Term' A t
  | .lam l => .lam fun v => (l (.var v)).subst
  | .var v => v
  | .app a b => .app a.subst b.subst

  | .zero => .zero
  | .false => .false
  | .true => .true

  | .succ v => .succ v.subst
  | .fix v => .fix v.subst
  | .z? v => .z? v.subst
  | .pred v => .pred v.subst

  | .ite c t f => .ite c.subst t.subst f.subst

inductive Term'.Val : Term' A t → Prop
  | zero : Val .zero
  | succ : Val v → Val (.succ v)
  | true : Val .true
  | false : Val .false
  | lam : Val (.lam l)

def Term.Val (v : Term t) : Prop := 
  Term'.Val (A := fun _ => PUnit) v

inductive Red : Term t → Term t → Prop
  | val : Term.Val v → Red v v
  | succ : Red x v → Red (Term.succ x) (Term.succ v)
  | pred : Red x (Term.succ v) → Red (Term.pred x) v
  | z?z : Red x .zero → Red (Term.z? x) .true
  | z?s : Red x (Term.succ _) → Red (Term.z? x) .false
  | itet : Red c .true → Red t v → Red (Term.ite c t f) v
  | itef : Red c .false → Red f v → Red (Term.ite c t f) v
  | app {t : Term (.arr A B)} {u : Term A} {v : Term B} {f : {rep : Ty → Type} → rep A → Term B}
      : Red t (Term.lam f) → Red (f u).subst v → Red (Term.app t u) v
  | fix : Red (Term.app t (Term.fix t)) v → Red (Term.fix t) v

theorem Red.rhs_Val (h : Red a b) : Term.Val b := by
  induction h
  any_goals assumption
  case succ ih => exact .succ ih
  case pred ih => cases ih; assumption
  case z?z => exact .true
  case z?s => exact .false

def Ω (t : Ty) : Term t := .fix <| .lam fun x => .var x

