import Denote.PCF.Stx
import Mathlib.Logic.Relation
import Mathlib.Tactic.ClearExcept

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
  | pred : v.Val → SRed (.pred (.succ v)) v
  | predc : SRed x x' → SRed (.pred x) (.pred x')
  | z?z : SRed (.z? .zero) .true
  | z?s : v.Val → SRed (.z? (.succ v)) .false
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
  | _,_, .pred h , _ => .pred <| .val <| .succ h
  | _,_, .itec _, hs
  | _,_, .z?c _, hs
  | _,_, .fix, hs
  | _,_, .appc _, hs
  | _,_, .predc _, hs => by cases hs
  | _,_, .z?z, .true => .z?z <| .val .zero
  | _,_, .z?s v, .false => .z?s <| .val <| .succ v
  | _,_, .itet, hs => .itet (.val .true) (.val hs)
  | _,_, .itef, hs => .itef (.val .false) (.val hs)
  | _,_, .app, hs => .app (.val .lam) (.val hs)

theorem Red_SRed {a b c : ITerm [] t} : SRed a b → Red b c → Red a c := by
  intro s r
  induction s
  case succ v ih =>
    cases r
    <;> rename_i h
    · cases h; rename_i h
      exact .succ (SRed_Val  v h)
    · exact .succ (ih h)
  case pred ih =>
    exact .pred <| .succ r
  case predc ih =>
    cases r
    <;> rename_i h
    · cases h
    · exact .pred (ih h)
  case z?z =>
    cases r
    exact .z?z <| .val .zero
  case z?s =>
    cases r
    exact .z?s <| .val <| .succ <| ‹_›
  case z?c ih =>
    cases r
    <;> rename_i h
    · cases h
    · apply Red.z?z (ih h)
    · apply Red.z?s (ih h)
  · exact .itet (.val .true) r
  · exact .itef (.val .false) r
  case itec ih =>
    cases r
    <;> rename_i h' h
    · cases h
    · apply Red.itet (ih h') h
    · apply Red.itef (ih h') h
  case appc ih =>
    cases r
    <;> rename_i h' h
    · cases h
    · exact .app (ih h') h
  case app =>
    exact .app (.val .lam) r
  · exact .fix r

theorem Val_SRed : {a b : ITerm [] t} → a.Val → SRed a b → False
  | _, _, .true
  | _, _, .false
  | _, _, .zero
  | _, _, .lam => by intro v; cases v
  | _, _, .succ h => fun | .succ v => Val_SRed h v

theorem SRed_Red {a b c : ITerm [] t} : Red a c → SRed a b → Red b c := by
  intro r s
  induction s
  case succ ih =>
    cases r <;> rename_i r
    · cases r
      apply False.elim (Val_SRed ‹_› ‹_›)
    · exact .succ (ih r)
  case pred ih =>
    cases r <;> rename_i r <;> cases r
    · exact .val ‹_›
    · assumption
  case predc ih =>
    cases r <;> rename_i r
    · cases r
    · exact .pred (ih r)
  case z?z =>
    cases r <;> rename_i r
    any_goals (cases r; done)
    exact .val .true
  case z?s =>
    cases r <;> rename_i r
    any_goals (cases r; done)
    exact .val .false
  case z?c ih =>
    cases r <;> rename_i r
    · cases r
    · exact .z?z (ih r)
    · exact .z?s (ih r)
  case itet =>
    cases r <;> rename_i r
    · cases r
    · assumption
    · rename_i v; cases v
  case itef =>
    cases r <;> rename_i r
    · cases r
    · rename_i v; cases v
    · assumption
  case itec ih =>
    cases r <;> rename_i r
    · cases r
    · exact .itet (ih ‹_›) r
    · exact .itef (ih ‹_›) r
  case appc ih =>
    cases r <;> rename_i r
    · cases r
    · exact .app (ih ‹_›) r
  · cases r <;> rename_i r
    · cases r
    · rename_i v'
      cases v'
      assumption
  · cases r <;> rename_i r
    · cases r
    · assumption

theorem BRed_Red {a b : ITerm [] t} (h : RedStar a b) (hv : b.Val) : Red a b := by
  dsimp [RedStar] at h
  rw [Relation.reflTransGen_swap] at h
  induction h
  · exact .val hv
  case tail b' c v s ih => exact Red_SRed s ih

theorem BRed'_Red {a b : ITerm [] t} (h : Relation.TransGen SRed a b) (hv : b.Val) : Red a b := by
  rw [Relation.transGen_swap] at h
  induction h
  case single h => 
    exact SRed_Val h hv
  case tail b' c v s ih => 
    exact Red_SRed s ih

theorem Red_BRed {a b : ITerm [] t} (h : Red a b) : RedStar a b := by 
  dsimp [RedStar]
  rw [Relation.reflTransGen_swap]
  induction h
  · exact .refl
  case succ v ih =>
    clear v
    induction ih
    · exact .refl
    case tail h ih =>
      exact .tail ih (.succ h)
  case pred v' ih =>
    have v := (Red.rhs_Val v')
    clear v'
    cases v; rename_i v
    induction ih
    · exact .single (.pred v)
    case tail s ih =>
      exact .tail ih (.predc s)
  case z?z v ih =>
    clear v
    induction ih
    · exact .single .z?z
    case tail h ih =>
      exact .tail ih (.z?c h)
  case z?s v' ih =>
    have v := (Red.rhs_Val v')
    clear v'; cases v; rename_i v
    induction ih
    · exact .single (.z?s v)
    case tail h ih =>
      exact .tail ih (.z?c h)
  case itet x ihc ihv =>
    apply Relation.ReflTransGen.trans ihv
    clear ihv x
    induction ihc
    · exact .single .itet
    case tail s ih v =>
      specialize ih (SRed_Red v s)
      exact .tail ih (SRed.itec s)
  case itef x ihc ihv =>
    apply Relation.ReflTransGen.trans ihv
    clear ihv x
    induction ihc
    · exact .single .itef
    case tail s ih v =>
      specialize ih (SRed_Red v s)
      exact .tail ih (SRed.itec s)
  case app x' x ihf iha =>
    apply Relation.ReflTransGen.trans iha
    clear iha x x'
    induction ihf
    · exact .single .app
    · exact .tail ‹_› (.appc ‹_›)
  case fix ih =>
    exact .tail ih (.fix)

/- theorem ECtx.subst_SRed {a b : ITerm [] t'} : {t : _} → {C : ECtx [] t' [] t} → SRed a b → Red (C a) v → Red (C b) v -/
/-   | _, .succ hs => sorry -/
/-   | _, .pred h => sorry -/
/-   | _, .itec _ => sorry -/
/-   | _, .z?c _ => sorry -/
/-   | _, .fix => sorry -/
/-   | _, .appc _ => sorry -/
/-   | _, .predc _ => sorry -/
/-   | _, .z?z => sorry -/
/-   | _, .z?s v => sorry -/
/-   | _, .itet => sorry -/
/-   | _, .itef => sorry -/
/-   | _, .app => sorry -/

end PCF
