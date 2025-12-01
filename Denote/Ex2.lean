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
  stop
  apply le_antisymm
  · change ∀ v : Flat Nat, _
    apply Ccss.scott
      (Φ := fun (x : CFunc (Flat Nat) (Flat Nat)) =>
        ∀ v, x.f v ≤ (FixF' (n.denote.f PUnit.unit) (m.denote.f PUnit.unit)).f v)
    constructor
    · intro v
      exact .bot
    · rintro f ih (_|⟨(_|⟨(_|⟨n⟩)⟩)⟩)
      <;> simp [Ty.denote.eq_1, Function.comp_apply, Ty.denote'.eq_1, Ty.denote'.eq_3, F,
        ITerm.denote, CFunc.curry, CFunc.comp, ite.denote, z?.denote, proj, CFunc.snd, CFunc.fst,
        CFunc.corecP, Prod.corec, z?.denote', ite.denote', pred.denote, pred.denote',
        FixF', CFunc.fbind, Flat.bind, succ.denote, succ.denote', CFunc.mp, CFunc.mp']
      · have := PCF.shift_denote
          (a := m)
          (Δ := (show ctx_denote [] from .unit))
          [.nat, .arr .nat .nat] 
          ⟨⟨.unit, f⟩, .obj 0⟩
        dsimp [ctx_denote.concat] at this
        rw [this]
      · have := PCF.shift_denote
          (a := n)
          (Δ := (show ctx_denote [] from .unit))
          [.nat, .arr .nat .nat] 
          ⟨⟨.unit, f⟩, .obj 1⟩
        dsimp [ctx_denote.concat] at this
        rw [this]; clear this
        cases n.denote.f PUnit.unit <;> rfl
      · split
        · rename_i v heq
          specialize ih (.obj (n + 1))
          rw [heq] at ih
          dsimp [FixF', CFunc.fbind, Flat.bind] at ih
          split at ih
          <;> cases ih
          rw [Nat.add_assoc]
          rfl
        · exact .bot
    · exact fun c hc ih v => complete_least _ (ih · v)
  · change ∀ v : Flat Nat, _
    rintro (_|⟨w⟩)
    · exact .bot
    · induction w
      · dsimp [FixF', CFunc.fbind, Flat.bind, FixF, ITerm.denote, CFunc.comp, CFunc.fix]
        rw [←kleenes _ 1]
        conv =>
          rhs
          lhs
          dsimp [Nat.repeat]
          lhs
          simp only [F, ITerm.denote, CFunc.curry, Ty.denote'.eq_1, Ty.denote'.eq_3, Ty.denote.eq_1,
            Function.comp_apply, CFunc.comp, ite.denote, CFunc.corecP, z?.denote, proj, CFunc.snd,
            pred.denote, succ.denote, CFunc.mp, CFunc.fst, ite.denote', Prod.corec, z?.denote',
            pred.denote', succ.denote', CFunc.mp', Nat.succ_eq_add_one]
        dsimp
        have := PCF.shift_denote
          (a := m)
          (Δ := (show ctx_denote [] from .unit))
          [.nat, .arr .nat .nat] 
          ⟨⟨.unit, ((F n m).denote.f PUnit.unit).fix'⟩, .obj 0⟩
        dsimp [ctx_denote.concat] at this
        rw [this]
      case a.obj.succ ih => sorry

end Ex2

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



end Ex17


