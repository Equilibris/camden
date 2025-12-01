import Denote.PCF.Stx
import Mathlib.Logic.Relation

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

def CtxEquiv {ty} (t t' : ITerm Γ ty) (γ : Ty) : Prop := 
  ∀ C : ECtx Γ ty [] γ, ∀ v, Red (C t) v ↔ Red (C t') v

theorem Red.rhs_Val (h : Red a b) : b.Val := by
  induction h
  any_goals assumption
  case succ ih => exact .succ ih
  case pred ih => cases ih; assumption
  case z?z => exact .true
  case z?s => exact .false

def Ω Γ t : ITerm Γ t := .fix <| .lam <| .var .hd

theorem Ω.Div {t v} : Red (Ω [] t) v → False := sorry

inductive SRed : ITerm [] t → ITerm [] t → Prop
  | succ : SRed x y → SRed (.succ x) (.succ y)
  | pred : v.Val → SRed x (.succ v) → SRed (.pred x) v
  | predc : SRed x x' → SRed (.pred x) (.pred x')
  | z?z : SRed (.z? .zero) .true
  | z?s : v.Val → SRed (.z? (.succ v)) .true
  | z?c : SRed x y → SRed (.z? x) (.z? y)
  | itet : SRed (.ite .true t f) t
  | itef : SRed (.ite .false t f) f
  | itec : SRed c c' → SRed (.ite c t f) (.ite c' t f)
  | appc : SRed e e' → SRed (.app e u) (.app e' u)
  | app : SRed (.app (.lam v) u) (v.parSubst <| .cons u .nil)
  | fix : SRed (.fix t') (.app t' (.fix t'))


def RedStar {t} := Relation.ReflTransGen (SRed (t := t))
def BRed (a b : ITerm [] t) : Prop := RedStar a b ∧ b.Val

/- #check Relation.Comp -/

#check Relation.ReflTransGen.rec

theorem SRed_Val : {a b : ITerm [] t} → SRed a b → b.Val → Red a b
  | _,_, .succ hs, .succ h => Red.succ <| SRed_Val hs h
  | _,_, .pred _ _, .succ _ => .pred sorry
  | _,_, .pred _ _, .zero => .pred sorry
  | _,_, .predc _, _ => sorry
  | _,_, .z?z, _ => sorry
  | _,_, .z?s v, _ => sorry
  | _,_, .z?c _, _ => sorry
  | _,_, .itet, _ => sorry
  | _,_, .itef, _ => sorry
  | _,_, .itec _, _ => sorry
  | _,_, .appc _, _ => sorry
  | _,_, .app, _ => sorry
  | _,_, .fix, _ => sorry
theorem Red_SRed {a b c : ITerm [] t} : SRed a b → Red b c → Red a c := by
  intro s r
  induction s
  case succ => 
    sorry
  case pred => 
    sorry
  case predc => 
    sorry
  case z?z => 
    sorry
  case z?s => 
    sorry
  case z?c => 
    sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

theorem BRed_Red {a b : ITerm [] t} (h : RedStar a b) (hv : b.Val) : Red a b := by
  dsimp [RedStar] at h
  rw [Relation.reflTransGen_swap] at h
  induction h
  · exact .val hv
  case tail b' c v s ih =>
    clear v hv a
    induction s
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry

end PCF


