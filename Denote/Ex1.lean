import Denote.Domain.Basic
import Mathlib.Data.ENat.Defs

/- P (Topic 1-4): 2, 3, 6; -/
/-     L: 6, 7, 8 -/
/- ii) P (Topic 5-8): 2, 6, 8;  -/
/-     L: 15, 17, 19 -/

open Dom

section P

section Ex2

variable {P Q : Type _} [PartialOrder P]

instance [PartialOrder Q] : PartialOrder ((f : P → Q) ×' Monotone f) where
  le := fun ⟨f, _⟩ ⟨g, _⟩ => ∀ a, f a ≤ g a
  le_antisymm := fun ⟨f, _⟩ ⟨g, _⟩ hf hg =>
    PSigma.ext (funext fun v => le_antisymm (hf v) (hg v)) (proof_irrel_heq _ _)
  le_refl f v := le_refl (f.1 v)
  le_trans f g h hfg hgh v := le_trans (hfg v) (hgh v)

instance domMono [dq : Dom Q] : Dom ((f : P → Q) ×' Monotone f) where
  bot := ⟨fun _ => ⊥, monotone_const⟩
  bot_le _f _v := bot_le
  complete c hc := ⟨
    fun v => dq.complete (c.map (·.1 v)) (hc.map <| fun ⦃_a _b⦄ f ↦ f v),
    fun _a _b h => complete_mono fun n => (c n).snd h
  ⟩
  complete_lub c hc := {
    lub_bound n v :=
      (dq.complete_lub (c.map (·.1 v)) (hc.map <| fun ⦃_a _b⦄ f ↦ f v)).lub_bound n
    lub_least f h v :=
      (dq.complete_lub (c.map (·.1 v)) (hc.map <| fun ⦃_a _b⦄ f ↦ f v)).lub_least (f.1 v)
        fun n => h n v
  }

end Ex2

section Ex3

variable {Q}

def chain_equiv [PartialOrder Q]
    : ((f : Nat → Q) ×' Monotone f) ≃ ((x : C Q) ×' Chain x) where
  toFun := fun ⟨f, mono⟩ => ⟨f, ⟨(mono <| Nat.le_succ ·)⟩⟩
  invFun := fun ⟨c, hc⟩ => ⟨c, fun a b => Chain.le_lift c⟩

variable [Dom Q]

-- Using this isomorphism we can see that we get it for free from the previous definition
/-- info: domMono -/
#guard_msgs in
#synth Dom <| (f : Nat → Q) ×' Monotone f

end Ex3

section Ex6

inductive ENat.Le : ℕ∞ → ℕ∞ → Prop
  | top {a} : Le a ⊤
  | nn {a b} : a ≤ b → Le (.some a) (.some b)

instance : LE ℕ∞ := ⟨ENat.Le⟩
section simps

attribute [simp] ENat.Le.top
attribute [simp] ENat.Le.nn

@[simp]
theorem some_a_le_some_b_eq {a b : ℕ} : ((Nat.cast a : ℕ∞) ≤ (Nat.cast b : ℕ∞)) = (a ≤ b) := by
  apply propext
  constructor
  · rintro ⟨_⟩; assumption
  · intro h; exact .nn h

@[simp]
theorem some_le_top {a : ENat} : (a ≤ ⊤) = True := by
  apply propext
  constructor
  · intro; trivial
  · intro; exact .top

@[simp]
theorem top_le_some {a : ENat} : (⊤ ≤ a) = (a = ⊤) := by
  apply propext
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact .top

end simps

instance : DecidableLE ℕ∞ := fun
  | _, ⊤ => .isTrue .top
  | ⊤, .some _ => .isFalse (fun h => Option.noConfusion <| top_le_some.mp h)
  | .some a, .some b =>
    if h : a ≤ b then
      .isTrue (.nn h)
    else .isFalse (fun h' => h (some_a_le_some_b_eq.mp h'))

instance : PartialOrder ℕ∞ where
  le_refl := fun
    | .some _ => .nn (Nat.le_refl _ )
    | ⊤       => .top
  le_trans := fun
    | _, _, ⊤, _, _ => .top
    | .some a , .some b, .some c, .nn hab, .nn hbc => .nn (Nat.le_trans hab hbc)
  le_antisymm := fun
    | ⊤, ⊤, .top, .top => rfl
    | .some _, .some _, .nn hab, .nn hbc => (Option.some.injEq _ _).mpr <| Nat.le_antisymm hab hbc

instance : OfNat ℕ∞ n := ⟨Nat.cast n⟩

-- Cursed nonsense
private noncomputable instance (priority := low)
    : ∀ c : C ℕ∞, Decidable (∃ k : Nat, ∀ n, c n ≤ k) :=
  fun c => Classical.propDecidable (∃ k : Nat, ∀ n, c n ≤ k)
private noncomputable instance (priority := low)
      : ∀ c : C ℕ∞, ∀ k : Nat, Decidable (∀ n, c n ≤ .some k) := 
  fun c => (Classical.propDecidable <| ∀ (n : ℕ), c n ≤ ·)

noncomputable instance : Dom ℕ∞ where
  bot := 0
  bot_le := fun | .some _ => .nn (Nat.zero_le _) | .none => .top
  complete c hc :=
    if h : ∃ k : Nat, ∀ n, c n ≤ k then .some (Nat.find h)
    else ⊤
  complete_lub c hc := by
    split <;> rename_i h
    · constructor
      · exact Nat.find_spec h
      · intro x h'
        rcases x with (_|⟨x⟩)
        · exact .top
        exact .nn <| Nat.find_min' h h'
    · push_neg at h
      refine ⟨fun _ => .top, fun x h' => ?_⟩
      rcases x with (_|⟨x⟩)
      · exact .top
      rcases h x with ⟨w, h⟩
      exact False.elim <| h <| h' w

def non_ex : ℕ∞ → ℕ∞
  | ⊤ => ⊤
  | .some _ => .some 0

theorem non_ex.mono : Monotone non_ex := fun
    | _, _, .top => .top
    | _, _, .nn _ => .nn (Nat.le_refl _)

-- Theres a much easier proof for this,
-- using a lemma about domains where chains are eventually constant.

theorem f (h : {f : ℕ∞ → ℕ∞} → Monotone f → Continous f) : False := by
  specialize h non_ex.mono
  have : _ = complete (fun val => (0 : ENat)) _ :=
    h.preserves_lubs (fun n => n) ⟨fun n => .nn <| Nat.le_succ _⟩
  rw [complete_const] at this
  dsimp [complete] at this
  split at this
  case isFalse => exact Option.noConfusion this
  rename_i h'
  rcases h' with ⟨w, h'⟩
  specialize h' w.succ
  simp only [Nat.succ_eq_add_one, some_a_le_some_b_eq] at h'
  omega

theorem ENat.complete_eq
    (c : Dom.C ℕ∞)
    (hc : Dom.Chain c)
    : Dom.complete c hc = ⊤ ∨ ∃ n, Dom.complete c hc = c n := by
  dsimp [Dom.complete]
  split
  · right; rename_i h
    have := Nat.find_spec h
    have := Nat.find_min h (m := (Classical.choose h))
    sorry
  · simp


end Ex6

end P

section L

section Ex6

instance : Equiv (CFunc ℕ∞ (Flat Unit)) ℕ∞ where
  toFun := sorry -- Is exacly what you expect
  invFun := fun
    | ⊤ => ⊥
    | .some n => {
      f := fun
        | .some v => if v ≤ n then .bot
            else .obj .unit
        | .none => .obj .unit
      continous := {
        mono := fun
          | ⊤, _, .top => le_refl _
          | .some v, _, .top => by 
            dsimp; split
            · exact .bot
            · exact le_refl _
          | _, _, .nn h => by 
            dsimp
            split
            · split <;> exact .bot
            simp only [obj_le_eq, right_eq_ite_iff, reduceCtorEq, imp_false, not_le]
            omega
        preserves_lubs c hc := by 
          have := FiniteDom.complete_map 
          rcases ENat.complete_eq _ hc with h|⟨w, h⟩
          <;> simp [h]
          · rw [FiniteDom.complete_eq_chain_fin]
            sorry
          · rw [FiniteDom.complete_eq_chain_fin]
            sorry

      }
    }
      

end Ex6

section Ex7

/--
info: Dom.CFunc.curry.{u_1, u_2, u_3} {A : Type u_1} {B : Type u_2} {C : Type u_3} [da : Dom A] [db : Dom B] [dc : Dom C]
  (f : CFunc (A × B) C) : CFunc A (CFunc B C)
-/
#guard_msgs in
#check Dom.CFunc.curry

/- def curry' (f : A × B → C) [hcf : Continous f] : CFunc A (CFunc B C) where -/
/-   f a := ⟨(f ⟨a, ·⟩), { -/
/-     mono := fun x y h => Continous.mono <| Prod.le_def.mpr ⟨le_refl _, h⟩, -/
/-     preserves_lubs := fun c hc => by -/
/-       change _ = complete (fun n => f (a, c n)) _ -/
/-       let mapper := (Prod.corec (Function.const B a) id) -/
/-       have mapperCont : Continous mapper := by infer_instance -/
/-       have := hcf.preserves_lubs (c.map mapper) (hc.map mapperCont.mono) -/
/-       change _ = complete ((c.map mapper).map f) _ -/
/-       rw [←this] -/
/-       change _ = f (complete (Function.const _ a) _, complete c _) -/
/-       congr 2 -/
/-       exact complete_const.symm -/
/-   }⟩ -/
/-   continous := { -/
/-     mono := fun a b h v => hcf.mono <| Prod.le_def.mpr ⟨h, le_refl (a, v).2⟩, -/
/-     preserves_lubs := fun c hc => by -/
/-       apply (CFunc.mk.injEq _ _ _ _).mpr -/
/-       funext a -/
/-       let mapper : A → A × B := Prod.corec id (Function.const _ a) -/
/-       have mapperCont : Continous mapper := by infer_instance -/
/-       have := hcf.preserves_lubs (c.map mapper) (hc.map mapperCont.mono) -/
/-       change _ = complete ((c.map mapper).map f) _ -/
/-       rw [←this] -/
/-       change _ = f (complete c _, complete (Function.const _ a) _) -/
/-       congr -/
/-       exact complete_const.symm, -/
/-   } -/

end Ex7

section Ex8

#check Dom.Ccss.inter

end Ex8

end L


