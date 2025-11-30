import Denote.PCF.Denote
import Denote.PCF.Red

/- ii) P (Topic 5-8): 2, 6, 8;  -/
/-     L: 15, 17, 19 -/

open PCF Dom

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

