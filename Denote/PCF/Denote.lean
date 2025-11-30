import Denote.PCF.Stx
import Denote.PCF.Red
import Denote.PCF.DenoteDefs
import Denote.Domain.Flat
import Denote.Domain.FuncDom
import Denote.Domain.DomConstructs

namespace PCF

open Dom

instance {x : Sigma Dom} : Dom x.fst := x.snd

noncomputable section

@[simp]
def Ty.denote' : Ty → Sigma Dom
  | .arr t1 t2 => ⟨Dom.CFunc t1.denote'.fst t2.denote'.fst, inferInstance⟩
  | .bool => ⟨Dom.Flat Bool, inferInstance⟩
  | .nat => ⟨Dom.Flat Nat, inferInstance⟩

@[simp]
def Ty.denote : Ty → Type 0 := Sigma.fst ∘ Ty.denote'

instance {ty : Ty} : Dom ty.denote := ty.denote'.snd

def ctx_denote : List Ty → Type 0
  | [] => PUnit
  | hd :: tl => ctx_denote tl × hd.denote

instance ctx_denote.isDom : {ls : List Ty} → Dom (ctx_denote ls)
  | [] => (inferInstance : Dom PUnit)
  | _ :: tl => 
    have : Dom (ctx_denote tl) := isDom
    (inferInstance : Dom (_ × _))

def proj {ty} : {ctx : List _} → List.MemT ty ctx → CFunc (ctx_denote ctx) ty.denote
  | _, .hd => .snd
  | _, .tl h => .comp (proj h) .fst

def ITerm.denote {ctx ty} : ITerm ctx ty → CFunc (ctx_denote ctx) ty.denote
  | .var v => proj v
  | .app t1 t2 => .comp .mp (.corecP t1.denote t2.denote)
  | .lam f => .curry f.denote
  | .true => .const (.obj .true)
  | .false => .const (.obj .false)
  | .zero => .const (.obj .zero)
  | .succ v => succ.denote.comp v.denote
  | .pred v => pred.denote.comp v.denote
  | .fix v => .comp .fix v.denote
  | .z? v => z?.denote.comp v.denote
  | .ite c t f => ite.denote.comp
      <| .corecP c.denote
      <| .corecP t.denote f.denote

end

theorem ITerm.ofNat_denote Γ : {n : _} → (ITerm.ofNat (Γ := Γ) n).denote = CFunc.const (.obj n)
  | 0 => rfl
  | n+1 => by
    change succ.denote.comp (ofNat n).denote = _
    rw [ITerm.ofNat_denote]
    rfl

theorem ITerm.ofBool_denote Γ : {n : _} → (ITerm.ofBool (Γ := Γ) n).denote = CFunc.const (.obj n)
  | .false | .true => rfl


end PCF

