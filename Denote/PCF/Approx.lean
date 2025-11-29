import Denote.PCF.Red
import Denote.PCF.Denote

namespace PCF

def ITerm.ofNat : (n : Nat) → ITerm Γ .nat
  | 0 => .zero
  | n+1 => .succ <|.ofNat n

instance {Γ} {n : Nat} : OfNat (ITerm Γ .nat) n where
  ofNat := ITerm.ofNat n

def Approx : {t : Ty} → t.denote → ITerm [] t → Prop
  | .bool, .bot, _ | .nat, .bot, _ => True
  | .nat, .obj n, t => Red t (.ofNat n)
  | .bool, .obj .true, t => Red t .true
  | .bool, .obj .false, t => Red t .false
  | .arr _ _, d, t => ∀ e u, Approx e u → Approx (d.f (e)) (.app t u)



end PCF

