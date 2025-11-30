import Denote.PCF.Red
import Denote.PCF.Denote
import Denote.Domain.Scott

namespace PCF

def ITerm.Approx : {t : Ty} → t.denote → ITerm [] t → Prop
  | .bool, .bot, _ | .nat, .bot, _ => True
  | .nat, .obj n, t => Red t (.ofNat n)
  | .bool, .obj .true, t => Red t .true
  | .bool, .obj .false, t => Red t .false
  | .arr _ _, d, t => ∀ e u, Approx e u → Approx (d.f (e)) (.app t u)

def CtxApprox : {Γ : _} → ctx_denote Γ → (HList (ITerm []) Γ) → Prop
  | [], .unit, .nil => True
  | _ :: _, ⟨td, hd⟩, .cons ht tt => ht.Approx hd ∧ CtxApprox td tt

namespace ITerm.Approx

def bot : {t : _} → {e : ITerm [] t} → ITerm.Approx ⊥ e
  | .nat, _ => .intro
  | .bool, _ => .intro
  | .arr _ _, _ => fun _ _ _ => bot

theorem le_respects
    : {t : _}
    → {d' d : t.denote}
    → {e : ITerm [] t}
    → d' ≤ d
    → ITerm.Approx d e
    → ITerm.Approx d' e
  | .nat, .obj _, .obj _, _, .obj_obj, h
  | .bool, .obj _, .obj _, _, .obj_obj, h => h
  | .bool, .bot, .bot, _, .bot_bot, _
  | .bool, .bot, .obj _, _, .bot_obj, _
  | .nat, .bot, .bot, _, .bot_bot, _
  | .nat, .bot, .obj _, _, .bot_obj, _ => .bot
  | .arr _ _, _, _, _, le, h => fun dx' dx v =>
      le_respects (le dx') (h dx' dx v)

theorem red_respects
    : {t : _}
    → {d : t.denote}
    → {e e' : ITerm [] t}
    → (∀ v, Red e v → Red e' v)
    → ITerm.Approx d e
    → ITerm.Approx d e'
  | .bool, .bot, _, _, map, _
  | .nat, .bot, _, _, map, _ => .bot
  | .bool, .obj .true, _, _, map, h
  | .bool, .obj .false, _, _, map, h
  | .nat, .obj _, _, _, map, h => map _ h
  | .arr Dom Ren, d, e, e', map, h =>
    fun d' ex h' => red_respects (by
        intro v h
        rcases h with ((_|_)|_)
        rename_i f h h'
        refine .app (map _ h) h'
      ) (h d' ex h')

#check Dom.Ccss

end ITerm.Approx

open Dom in
theorem fund : (e : ITerm Γ t) → (ρ σ : _) → CtxApprox ρ σ → (e.parSubst σ).Approx (e.denote ρ)
  | .false, _, _, _ | .true, _, _, _ | .zero, _, _,_ => by
    dsimp [ITerm.Approx, ITerm.denote, CFunc.const, ITerm.parSubst]
    apply Red.val
    grind
  | .var _, _, _, _=> sorry
  | .fix _, _, _, _ => sorry
  | .z? e, ctx, _, h => by 
    dsimp [z?.denote, CFunc.comp, ITerm.Approx, ITerm.denote, CFunc.const, ITerm.parSubst]
    have := fund e ‹_› ‹_› h
    generalize e.denote.f ctx = v at this
    rcases v with (_|(_|⟨w⟩))
    <;> dsimp [ITerm.Approx] at this
    · exact .bot
    · exact Red.z?z this
    · exact Red.z?s this
  | .pred e, ctx, _, h => by
    dsimp [pred.denote, CFunc.comp, ITerm.Approx, ITerm.denote, CFunc.const, ITerm.parSubst]
    have := fund e ‹_› ‹_› h
    generalize e.denote.f ctx = v at this
    rcases v with (_|(_|⟨v⟩))
    any_goals exact .bot
    exact Red.pred this
  | .succ e, ctx, _, h => by
    dsimp [succ.denote, CFunc.comp, ITerm.Approx, ITerm.denote, CFunc.const, ITerm.parSubst]
    have := fund e ‹_› ‹_› h
    generalize e.denote.f ctx = v at this
    cases v
    · exact .bot
    · exact Red.succ this
  | .ite e _ _, ctx, _, h => by
    dsimp [Prod.corec, CFunc.corecP, ite.denote, CFunc.comp, ITerm.Approx, ITerm.denote, CFunc.const, ITerm.parSubst]
    have := fund e ‹_› ‹_› h
    generalize e.denote.f ctx = v at this
    rcases v with (_|_|_)
    <;> dsimp [ITerm.Approx, ite.denote'] at this ⊢
    · exact .bot
    · unfold ITerm.Approx
      sorry
    · sorry
  | .app _ _, _, _, _ => sorry
  | .lam _, _, _, _ => sorry

theorem adeq_n {t : ITerm [] .nat}
    (h : t.denote .unit = (ITerm.ofNat (Γ := []) n).denote .unit)
    : Red t (ITerm.ofNat n) := by
  have := fund t .unit .nil .intro
  simpa [h, ITerm.ofNat_denote, ITerm.parSubst.closed, Dom.CFunc.const, ITerm.Approx] using this

theorem adeq_b {t : ITerm [] .bool}
    (h : t.denote .unit = (ITerm.ofBool (Γ := []) n).denote .unit)
    : Red t (ITerm.ofBool n) := by
  have := fund t .unit .nil .intro
  cases n <;>
  simpa [h, ITerm.ofBool_denote, ITerm.parSubst.closed, Dom.CFunc.const, ITerm.Approx] using this

end PCF


