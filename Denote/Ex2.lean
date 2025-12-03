import Denote.PCF.Denote
import Denote.PCF.Red
import Denote.PCF.Subst
import Denote.Domain.Scott
import Denote.Domain.Kleenes

/- ii) P (Topic 5-8): 2, 6, 8;  -/
/-     L: 15, 17, 19 -/

open PCF Dom

section Ex2

def F (n m : ITerm [] .nat) : ITerm [] ((Ty.nat.arr .nat).arr (Ty.nat.arr .nat)) :=
  .lam <| .lam <|
    .ite (.z? (.var .hd)) (m.shift [_, _])
    <| .ite (.z? (.pred (.var .hd)))
      (n.shift [_, _])
      <| .succ
        <| .app (.var <| .tl .hd) (.pred <| .var .hd)

def FixF (n m : ITerm [] .nat) : ITerm [] (Ty.nat.arr .nat) := .fix (F n m)

def FixF' (n m : Flat Nat) : CFunc (Flat Nat) (Flat Nat) :=
  .fbind fun
    | 0 => m
    | v+1 => n.bind (pure <| · + v)

theorem FixF.eq {n m} : (FixF n m).denote .unit = FixF' (n.denote .unit) (m.denote .unit) := by 
  apply CFunc.ext
  funext i
  rcases i with (_|⟨w⟩)
  · dsimp [FixF, ITerm.denote, CFunc.fix, CFunc.comp]
    rw [←kleenes _ 1]
    change ⊥ = ⊥
    rfl
  · dsimp [FixF, ITerm.denote, CFunc.fix, CFunc.comp, ]
    rw [←kleenes _ w]
    induction w
    · dsimp [FixF', CFunc.fbind, Flat.bind, FixF, ITerm.denote, CFunc.comp, CFunc.fix]
      rw [←kleenes _ 1]
      change (ITerm.shift [[ty|nat], [ty|nat → nat]] m).denote.f
          ((PUnit.unit, ((F n m).denote.f PUnit.unit).fix'), Flat.obj 0) =
        m.denote.f PUnit.unit
      have := PCF.shift_denote
        (a := m)
        (Δ := (show ctx_denote [] from .unit))
        [.nat, .arr .nat .nat] 
        ⟨⟨.unit, ((F n m).denote.f PUnit.unit).fix'⟩, .obj 0⟩
      dsimp [ctx_denote.concat] at this
      rw [this]
    case h.h.obj.succ w ih =>
      dsimp [Nat.repeat]
      conv =>
        lhs; lhs; lhs;
        simp only [F, ITerm.denote, CFunc.curry, Ty.denote'.eq_1, Ty.denote'.eq_3, Ty.denote.eq_1,
          Function.comp_apply, CFunc.comp, ite.denote, CFunc.corecP, z?.denote, proj, CFunc.snd,
          pred.denote, succ.denote, CFunc.mp, CFunc.fst, ite.denote', Prod.corec, z?.denote',
          pred.denote', succ.denote', CFunc.mp', Nat.succ_eq_add_one]
      dsimp [Nat.repeat]
      rw [ih]; clear ih
      cases w
      · simp [FixF', CFunc.fbind, Flat.bind, Nat.repeat]
        have := PCF.shift_denote
          (a := n)
          (Δ := (show ctx_denote [] from .unit))
          [.nat, .arr .nat .nat] 
          ⟨⟨.unit, ((F n m).denote.f PUnit.unit).fix'⟩, .obj 1⟩
        dsimp [ctx_denote.concat] at this
        rw [this]
        cases n.denote.f PUnit.unit <;> rfl
      · simp [FixF', CFunc.fbind, Flat.bind]
        cases n.denote.f PUnit.unit <;> rfl

end Ex2

section Ex6

variable (M₁ M₂ : ITerm Γ t)

def s1 {ty} (t t' : ITerm Γ ty) : Prop :=
  ∀ C : ECtx Γ ty [] .bool, (∃ v, Red (C t) v) ↔ (∃ v, Red (C t') v)

def s2 {ty} (t t' : ITerm Γ ty) : Prop := 
  ∀ C : ECtx Γ ty [] .bool, (Red (C t) .true) ↔ Red (C t') .true

def s2' {ty} (t t' : ITerm Γ ty) : Prop :=
  ∀ C : ECtx Γ ty [] .bool, (Red (C t) .false) ↔ Red (C t') .false

theorem s1_imp_s2 (h : s1 M₁ M₂) : s2 M₁ M₂ := by
  intro C
  specialize h (.itec C .true (Ω _ _))
  simp [ECtx.subst] at h
  constructor
  · intro h'
    obtain ⟨w,r⟩ := h.mp ⟨.true, .itet h' <| .val .true⟩
    cases r
    <;> rename_i h
    · cases h
    · assumption
    · exact False.elim (Ω.Div h)
  · intro h'
    obtain ⟨w,r⟩ := h.mpr ⟨.true, .itet h' <| .val .true⟩
    cases r
    <;> rename_i h
    · cases h
    · assumption
    · exact False.elim (Ω.Div h)

theorem s1_imp_s2' (h : s1 M₁ M₂) : s2' M₁ M₂ := by
  intro C
  specialize h (.itec C (Ω _ _) .true)
  simp [ECtx.subst] at h ⊢
  constructor
  <;> intro h'
  · obtain ⟨w,r⟩ := h.mp ⟨.true, .itef h' <| .val .true⟩
    cases r
    <;> rename_i h
    · cases h
    · exact False.elim (Ω.Div h)
    · assumption
  · obtain ⟨w,r⟩ := h.mpr ⟨.true, .itef h' <| .val .true⟩
    cases r
    <;> rename_i h
    · cases h
    · exact False.elim (Ω.Div h)
    · assumption

theorem s2_imp_CtxEquiv (h : s2 M₁ M₂) : CtxEquiv M₁ M₂ t := by
  intro C v
  dsimp
  specialize h
  constructor
  <;> intro h'
  · sorry
  · sorry

end Ex6

section Ex8

/-

This generalisies from a binary por to a complete por.

-/

end Ex8

section Ex15

theorem Nat.repeat.id {x : Nat} : x.repeat id = (id : A → A) := by 
  induction x
  · rfl
  · simp_all only [Nat.repeat]; rfl

theorem ex15 {Γ Δ} : (Ω Γ t).denote Δ = ⊥ := by
  change complete (Nat.repeat id · ⊥) _ = ⊥
  conv => lhs; lhs; intro x; rw [Nat.repeat.id]; dsimp
  rw [complete_const]

example {Γ Δ arg t} : (ITerm.lam (Ω (arg :: Γ) t)).denote Δ = (Ω _ _).denote Δ := by
  dsimp [ITerm.denote, CFunc.curry]
  conv => lhs; lhs; intro x; rw [ex15]
  rw [ex15]
  rfl

end Ex15

section Ex17

example {t₁ t₂ : ITerm [] t} : ∀ v, (Red t₁ v ↔ Red t₂ v) → CtxEquiv t₁ t₂ τ := by
  intro v h' C v'
  dsimp
  refine ⟨fun h => ?_, fun h => ?_⟩
  · sorry
  · sorry

end Ex17

section Ex19

-- We can prove it for ground types using adequecy, 
-- function types dont hold. Consider λ x ↦ x and λ x ↦ (λ x ↦ x) x

end Ex19

