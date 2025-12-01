import Denote.Domain.Finite
import Denote.Domain.FuncDom

namespace Dom

variable {A B C : _} [da : Dom A] [db : Dom B] [dc : Dom C]


theorem kleenes
    (f : CFunc A A) n
    : Nat.repeat f.f n f.fix' = f.fix' := by
  dsimp [CFunc.fix']
  induction n
  · rfl
  case succ ih => 
    dsimp [Nat.repeat]
    rw [ih]
    rw [f.continous.preserves_lubs]
    change complete ((fun x ↦ Nat.repeat f.f x.succ ⊥)) _ = complete (fun x ↦ Nat.repeat f.f x ⊥) _
    symm
    apply complete_contR (a := 1)
    intro _
    rfl

theorem flatConv
    [FiniteDom A]
    (f : CFunc (CFunc A A) (CFunc A A))
    (h : f.fix' x = v)
    : ∃ n, Nat.repeat f.f n ⊥ x = v := by
  subst h
  dsimp [CFunc.fix', complete]
  generalize_proofs hc
  rw [FiniteDom.complete_eq_chain_fin]
  generalize_proofs neq
  exact Dom.C.Finite.memAll (FiniteDom.chain_fin _ hc) _ (List.getLast_mem neq)

theorem flatConv'
    (f : CFunc (CFunc A A) (CFunc A A))
    (h : ∃ n, Nat.repeat f.f n ⊥ x = v)
    : f.fix' x = v
    := by
  rcases h with ⟨w, rfl⟩
  rw [←kleenes _ w]
  induction w
  · dsimp [Nat.repeat]
    sorry
  · sorry

end Dom

