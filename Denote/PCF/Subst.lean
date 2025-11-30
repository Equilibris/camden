import Denote.PCF.Stx
import Denote.PCF.Red
import Denote.PCF.Denote
import Denote.PCF.DenoteDefs
import Denote.Domain.Flat
import Denote.Domain.FuncDom
import Denote.Domain.DomConstructs

namespace PCF

open Dom

noncomputable section
def deepApply (h : ctx_denote Γ₂) : {Γ : _}
    → HList (ITerm Γ₂) Γ
    → ctx_denote Γ
  | _, .nil => .unit
  | _, .cons hd tl => ⟨deepApply h tl, hd.denote h⟩

def ctx_denote.concat
    : {a b : _}
    → (ha : ctx_denote a)
    → (hb : ctx_denote b)
    → ctx_denote (a ++ b)
  | [], _, _, hb => hb
  | _ :: _, _, ⟨htl, hhd⟩, hb => ⟨htl.concat hb, hhd⟩

theorem shift {Δ₁ : ctx_denote Γ₁}
    : {Γ : _}
    → {Δ : ctx_denote Γ}
    → (v : List.MemT t (Γ₁))
    → (proj v.shift).f (Δ.concat Δ₁) = (proj v).f Δ₁ 
  | [], _, h => rfl
  | _ :: _, ⟨Δ, _⟩, h => by 
    change (proj h.shift).f (Δ.concat Δ₁) = (proj h).f Δ₁
    exact shift h

theorem sshift {Δ₁ : ctx_denote Γ₁}
    : {Γ Γ₂ : _}
    → {Δ : ctx_denote Γ}
    → {Δ₂ : ctx_denote Γ₂}
    → (v : List.MemT t (Γ ++ Γ₁))
    → (proj v.sandwitch_shift).f (Δ.concat (Δ₂.concat Δ₁)) = (proj v).f (Δ.concat Δ₁)
  | [], _, .unit, _, v => shift v
  | _ :: _, _, ⟨_, _⟩, _, .hd => rfl
  | _ :: _, _, ⟨_, _⟩, _, .tl h => sshift h

theorem gshift {Γ Γ₁ Γ₂} {Δ Δ₁ Δ₂ : ctx_denote _}
    : {a : ITerm (Γ ++ Γ₁) t} 
    → (ITerm.gshift (Γ₂ := Γ₂) a).denote.f (.concat Δ (.concat Δ₂ Δ₁)) = a.denote (.concat Δ Δ₁)
  | .var v => by
    simp only [Ty.denote, Function.comp_apply, ITerm.gshift, ITerm.denote]
    exact sshift v
  | .z? v
  | .pred v
  | .succ v
  | .ite c t f
  | .app a b
  | .fix v => by
    unfold ITerm.gshift
    dsimp [ITerm.denote, CFunc.comp, CFunc.corecP, Prod.corec]
    repeat rw [gshift]
  | .false | .zero | .true => by simp [ITerm.gshift, ITerm.denote, CFunc.const]
  | .lam (dom := dom) a => by
    unfold ITerm.gshift
    apply CFunc.ext
    funext v
    exact gshift (Γ := dom :: Γ) (Δ := ⟨Δ,v⟩)

theorem shift1 {Γ₁} {Δ : ctx_denote _}
    {a : ITerm Γ₁ t}
    : (ITerm.shift [t₂] a).denote.f (Δ, v) = a.denote Δ :=
  @gshift t [] Γ₁ [t₂] .unit Δ ⟨.unit, v⟩ a

theorem deepApply_denote
    (Δ : ctx_denote Γ₂)
    : {Γ : _}
    → (Δ' : HList (ITerm Γ₂) Γ)
    → (h : List.MemT t₂ Γ)
    → Δ'[h].denote.f Δ = (proj h).f (deepApply Δ Δ')
  | _ :: _, .cons _ _, .hd => rfl
  | _ :: _, .cons _ tl, .tl h => 
    deepApply_denote Δ tl h

theorem subst
    {Δ' : HList (ITerm Γ₂) Γ}
    : {t : ITerm Γ t₂} → (t.parSubst Δ').denote Δ = t.denote (deepApply Δ Δ')
  | .var h => by
    dsimp [ITerm.parSubst, ITerm.denote]
    apply deepApply_denote
  | .false | .true | .zero => rfl
  | .fix v => by
    change ((v.parSubst _).denote Δ).fix' = (v.denote.f _).fix'
    rw [subst]
  | .z? v => by
    change z?.denote ((v.parSubst _).denote Δ) = z?.denote _
    rw [subst]
  | .pred v => by
    change pred.denote ((v.parSubst _).denote Δ) = pred.denote _
    rw [subst]
  | .succ v => by
    change succ.denote ((v.parSubst _).denote Δ) = succ.denote _
    rw [subst]
  | .ite c t f => by
    change ite.denote ⟨
      (c.parSubst _).denote Δ,
      (t.parSubst _).denote Δ,
      (f.parSubst _).denote Δ
    ⟩ = ite.denote ⟨_,_,_⟩
    rw [subst, subst, subst]
  | .app a b => by
    change CFunc.mp ⟨
      (a.parSubst _).denote Δ,
      (b.parSubst _).denote Δ
    ⟩ = CFunc.mp ⟨a.denote _, b.denote _⟩
    rw [subst, subst]
  | .lam l => by
    apply CFunc.ext
    funext v
    change (ITerm.parSubst (HList.cons (ITerm.var List.MemT.hd) _) l).denote.f (Δ, v) = 
      l.denote.f (deepApply Δ Δ', v)
    rw [subst]
    congr
    refine Prod.ext ?_ rfl
    dsimp [deepApply, ITerm.denote, proj]
    clear *-
    induction Δ'
    · rfl
    case cons ih =>
      dsimp [deepApply, HList.map]
      apply Prod.ext
      · exact ih
      · rw [shift1]

/- theorem shift1 {dom v} : {a : ITerm Γ t} → (ITerm.shift [dom] a).denote.f (Δ, v) = a.denote Δ -/
/-   | .var _ => sorry -/
/-   | .fix _ => sorry -/
/-   | .z? _ => sorry -/
/-   | .pred _ => sorry -/
/-   | .succ _ => sorry -/
/-   | .zero => sorry -/
/-   | .ite _ _ _ => sorry -/
/-   | .false => sorry -/
/-   | .true => sorry -/
/-   | .app _ _ => sorry -/
/-   | .lam _ => sorry -/

end

end PCF

