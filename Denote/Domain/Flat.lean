import Mathlib.Order.Lattice
import Denote.Domain.ChainTrellis
import Denote.Domain.Dom
import Denote.Domain.PartialFunc
import Denote.Domain.Continous
import Denote.Domain.Finite

namespace Dom

@[grind]
inductive Flat (α : Type _) | bot | obj (v : α)
deriving DecidableEq

@[grind]
inductive Flat.Le : Flat α → Flat α → Prop
  | bot_bot : Le .bot .bot
  | bot_obj : Le .bot <| .obj _
  | obj_obj : Le (.obj a) (.obj a)

def Flat.Le.bot : {a : Flat α} → Le .bot a
  | .bot => .bot_bot | .obj _ => .bot_obj

inductive Flat.Lt : Flat α → Flat α → Prop
  | bot_obj : Lt .bot <| .obj _

instance : LE (Flat α) := ⟨Flat.Le⟩
instance : LT (Flat α) := ⟨Flat.Lt⟩
instance : PartialOrder (Flat α) where
  lt_iff_le_not_ge _ _ := ⟨
    fun | .bot_obj => ⟨.bot, fun h => by cases h⟩,
    fun
      | ⟨.bot_obj, _⟩ => .bot_obj
      | ⟨.bot_bot, h⟩ | ⟨.obj_obj, h⟩ => False.elim <| h (by solve_by_elim)
  ⟩
  le_refl | .bot => .bot_bot | .obj _ => .obj_obj
  le_trans
    | .bot, _, _, _, _ => .bot
    | .obj _, .obj _, .obj _, .obj_obj, .obj_obj => .obj_obj
  le_antisymm : ∀ (a b : Flat α), a ≤ b → b ≤ a → a = b
    | .bot, .bot, .bot_bot, .bot_bot => rfl
    | .obj _, .obj _, .obj_obj, .obj_obj => rfl

section simps

attribute [simp] Flat.Lt.bot_obj
attribute [simp] Flat.Le.bot_obj
attribute [simp] Flat.Le.bot_bot
attribute [simp] Flat.Le.bot

@[simp, grind =]
theorem obj_a_le_obj_b_eq {a b : α} : (Flat.obj a ≤ .obj b) = (a = b) := by
  apply propext
  constructor
  · rintro (_|_); rfl
  · rintro rfl; rfl

@[simp]
theorem obj_a_le_bot {a : α} : (Flat.obj a ≤ .bot) = False := by
  apply propext
  constructor
  · rintro (_|_)
  · exact False.elim

@[simp]
theorem obj_le_eq {v} : {f : Flat α} → (.obj v ≤ f) = (.obj v = f)
  | .obj _  => by simp
  | .bot    => by simp
end simps

theorem Flat.finite (c : C <| Flat α) (hc : Chain c) : Nonempty c.Finite' := by
  cases h : c 0
  case obj v =>
    refine ⟨⟨[obj v], ?_, fun n => ?_, fun x mem => ?_⟩⟩
    · simp
    · have := h ▸ hc.le_lift _ (Nat.zero_le n)
      simp_all
    · obtain rfl := List.mem_singleton.mp mem
      exact ⟨0, h⟩
  by_cases x : ∃ n w, c n = .obj w
  · rcases x with ⟨nw, w,p⟩
    refine ⟨⟨[.bot, .obj w], ?_, fun n => ?_, fun  x mem => ?_⟩⟩
    all_goals simp_all only [List.sorted_cons, List.mem_cons, or_false, forall_eq,
      List.mem_cons, or_false,List.mem_cons, forall_eq, List.mem_nil_iff, or_false,
      IsEmpty.forall_iff, implies_true, List.sorted_nil, and_self, and_true]
    · exact .bot_obj
    · induction n
      · exact .inl h
      next n ih =>
        rcases ih with ih|ih
        · refine match h : c n, h' : c n.succ, hc.chain n with
            | .obj _, .obj _, .obj_obj => Flat.noConfusion <| ih.symm.trans h
            | .bot, .obj _, .bot_obj => ?_
            | .bot, .bot, .bot_bot => .inl rfl
          simp_all only [Nat.succ_eq_add_one, obj.injEq]
          have := hc.rel _ (n+1) nw
          rw [h', p] at this
          simp at this ⊢
          rcases this with (rfl | rfl) <;> rfl
        · have := hc.chain n
          generalize c n.succ = n1, c n = n2 at this ih
          cases this <;> simp_all
    · rcases mem with rfl|rfl
      · exact ⟨0, h⟩
      · exact ⟨nw, p⟩
  · simp only [not_exists] at x
    have : ∀ n, c n = .bot := fun n =>
      match h : c n with
      | .obj v => False.elim <| x n v h
      | .bot => rfl
    refine ⟨⟨[.bot], ?_, ?_, ?_⟩⟩
    <;> simp_all

instance : OrderBot (Flat A) where
  bot := .bot
  bot_le | .bot => .bot_bot | .obj _ => .bot_obj

noncomputable instance : FiniteDom (Flat α) where
  chain_fin c hc := .ofFinite' <| Classical.choice <| Flat.finite c hc

def Flat.domainLift (f : PFun A B) : Flat A → Flat B
  | .bot => .bot
  | .obj x => if let .some x := f x then .obj x else .bot

theorem Flat.domainLift.mono : Monotone (domainLift f)
  | .obj _, .obj _, .obj_obj => by
    dsimp [Flat.domainLift]
    split
    · exact .obj_obj
    · exact .bot_bot
  | .bot,   .obj _,  .bot_obj => by
    dsimp [Flat.domainLift]
    split
    · exact .bot_obj
    · exact .bot_bot
  | .bot,   .bot,    .bot_bot => .bot_bot

variable [DecidableEq B]

noncomputable instance : Continous (Flat.domainLift f : Flat A → Flat B) :=
  Continous.finite Flat.domainLift.mono

noncomputable instance : StrictContinous (Flat.domainLift f : Flat A → Flat B) := ⟨rfl⟩

namespace Flat

section FlatMonad

@[grind]
def bind (v : Flat A) (f : (A → Flat B)) : Flat B :=
  match v with
  | .obj v => f v
  | .bot => .bot

theorem bind.mono : Monotone (domainLift f)
  | .obj _, .obj _, .obj_obj => by
    dsimp [Flat.domainLift]
    split
    · exact .obj_obj
    · exact .bot_bot
  | .bot,   .obj _,  .bot_obj => by
    dsimp [Flat.domainLift]
    split
    · exact .bot_obj
    · exact .bot_bot
  | .bot,   .bot,    .bot_bot => .bot_bot

noncomputable instance : Continous (Flat.domainLift f : Flat A → Flat B) :=
  Continous.finite Flat.domainLift.mono

instance : Monad Flat where
  bind := bind
  pure := .obj

instance : LawfulMonad Flat where
  bind_assoc {A B C} := by rintro (_|_) f g <;> rfl
  map_const := rfl
  id_map := fun | .bot | .obj _ => rfl
  seqLeft_eq := fun | .bot, .bot | .bot, .obj _ | .obj _, .bot | .obj _, .obj _ => rfl
  seqRight_eq := fun | .bot, .bot | .bot, .obj _ | .obj _, .bot | .obj _, .obj _ => rfl
  pure_seq g := fun | .bot | .obj _ => rfl
  bind_pure_comp f := fun | .bot | .obj _ => rfl
  bind_map v := fun | .bot | .obj _ => rfl
  pure_bind x f := rfl

end FlatMonad

end Flat

end Dom

