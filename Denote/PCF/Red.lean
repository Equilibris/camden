import Denote.PCF.Stx

namespace PCF

namespace ITerm

@[grind]
inductive Val : ITerm Γ t → Prop
  | zero : Val .zero
  | succ : Val v → Val (.succ v)
  | true : Val .true
  | false : Val .false
  | lam : Val (.lam l)

@[grind]
def ofNat : (n : Nat) → ITerm Γ .nat
  | 0 => .zero
  | n+1 => .succ <|.ofNat n

@[grind]
def ofBool : (n : Bool) → ITerm Γ .bool
  | .true => .true
  | .false => .false

theorem Val_imp_ex {e : ITerm Γ .nat} : Val e → ∃ n, e = ITerm.ofNat n
  | .zero => ⟨0, rfl⟩
  | .succ h => by
    obtain ⟨w, rfl⟩ := Val_imp_ex h
    refine ⟨w.succ, rfl⟩
theorem Val_nat_iff {e : ITerm Γ .nat} : Val e = ∃ n, e = ITerm.ofNat n := by 
  ext; constructor
  · exact fun a ↦ Val_imp_ex a
  · rintro ⟨w, rfl⟩
    induction w
    · exact .zero
    · exact .succ ‹_›
theorem Val_bool_iff {e : ITerm Γ .bool} : Val e = ∃ n, e = ITerm.ofBool n := by
  ext; constructor
  · rintro (_|_)
    · refine ⟨.true,  rfl⟩
    · refine ⟨.false, rfl⟩
  · rintro ⟨(_|_), rfl⟩
    · grind
    · grind
theorem Val_arr_iff {e : ITerm Γ (.arr A B)} : Val e = ∃ e', e = .lam e' := by grind

theorem Val_iff {e : ITerm Γ t} : Val e = (match t with
    | .nat => ∃ n, e = .ofNat n
    | .bool => ∃ b, e = .ofBool b
    | .arr _ _ => ∃ e', e = .lam e') := by
  split
  · exact Val_nat_iff
  · exact Val_bool_iff
  · exact Val_arr_iff

end ITerm

instance {Γ} {n : Nat} : OfNat (ITerm Γ .nat) n where
  ofNat := ITerm.ofNat n

inductive Red : ITerm [] t → ITerm [] t → Prop
  | val : v.Val → Red v v
  | succ : Red x v → Red (.succ x) (.succ v)
  | pred : Red x (.succ v) → Red (.pred x) v
  | z?z : Red x .zero → Red (.z? x) .true
  | z?s : Red x (.succ _) → Red (.z? x) .false
  | itet : Red c .true → Red t v → Red (.ite c t f) v
  | itef : Red c .false → Red f v → Red (.ite c t f) v
  | app : Red t' (.lam f) → Red (f.parSubst <| .cons u .nil) v → Red (.app t' u) v
  | fix : Red (.app t' (.fix t')) v → Red (.fix t') v

theorem Red.rhs_Val (h : Red a b) : b.Val := by
  induction h
  any_goals assumption
  case succ ih => exact .succ ih
  case pred ih => cases ih; assumption
  case z?z => exact .true
  case z?s => exact .false

def Ω Γ t : ITerm Γ t := .fix <| .lam <| .var .hd

