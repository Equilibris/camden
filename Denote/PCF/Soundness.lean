import Denote.PCF.Subst
import Denote.PCF.Red

namespace PCF

open Dom

theorem ITerm.ofNat_denote Γ : {n : _} → (ITerm.ofNat (Γ := Γ) n).denote = CFunc.const (.obj n)
  | 0 => rfl
  | n+1 => by
    change succ.denote.comp (ofNat n).denote = _
    rw [ITerm.ofNat_denote]
    rfl

theorem ITerm.ofBool_denote Γ : {n : _} → (ITerm.ofBool (Γ := Γ) n).denote = CFunc.const (.obj n)
  | .false | .true => rfl

theorem sound (e : ITerm [] t) : Red e v → e.denote .unit = v.denote .unit
  | .val _ => rfl
  | .fix (t' := t') h => by
    rw [←sound _ h]
    change complete _ _ = (t'.denote.f PUnit.unit).f (complete _ _)
    rw [(t'.denote.f PUnit.unit).continous.preserves_lubs]
    exact complete_contR (a := 1) fun n => rfl
  | .z?s (x := v) h => by
    change z?.denote.f (v.denote.f PUnit.unit) = Flat.obj Bool.false
    rw [sound _ h]
    obtain ⟨(_|⟨w⟩),p⟩ := Red.rhs_Val h |> ITerm.Val_nat_iff.mp
    <;> simp only [ITerm.ofNat, reduceCtorEq, ITerm.succ.injEq] at p
    subst p
    change z?.denote.f (ITerm.denote (ITerm.ofNat w.succ) _) = Flat.obj Bool.false
    rw [ITerm.ofNat_denote]
    rfl
  | .z?z (x := x) h => by 
    change z?.denote.f (x.denote.f PUnit.unit) = _
    rw [sound _ h]
    rfl
  | .pred (x := x) h => by
    change pred.denote.f (x.denote.f PUnit.unit) = _
    rw [sound _ h]
    obtain ⟨(_|⟨w⟩),p⟩ := Red.rhs_Val h |> ITerm.Val_nat_iff.mp
    <;> simp only [ITerm.ofNat, reduceCtorEq, ITerm.succ.injEq] at p
    subst p
    change pred.denote ((ITerm.ofNat w.succ).denote _) = _
    rw [ITerm.ofNat_denote, ITerm.ofNat_denote]
    rfl
  | .succ h => by
    change succ.denote.f _ = succ.denote.f _
    rw [sound _ h]
  | .itef h v | .itet h v => by
    change ite.denote.f ⟨_,_,_⟩ = _
    rw [sound _ h]
    simp only [ite.denote, Ty.denote.eq_1, Function.comp_apply, Ty.denote'.eq_2, ITerm.denote,
      CFunc.const, Function.const_apply, ite.denote']
    rw [sound _ v]
  | .app (t' := t') (f := f) (u := u) flam val => by
    change (t'.denote.f PUnit.unit).f (u.denote.f PUnit.unit) = v.denote.f PUnit.unit
    rw [sound _ flam, (sound _ val).symm.trans subst]
    rfl

end PCF

