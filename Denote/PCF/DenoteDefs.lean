import Denote.PCF.Stx
import Denote.Domain.Flat
import Denote.Domain.FuncDom

namespace PCF

open Dom

def succ.denote' : Flat Nat → Flat Nat
  | .obj v => .obj v.succ
  | .bot => .bot
def succ.denote'.mono : Monotone succ.denote' := fun
  | .obj _, .obj _, .obj_obj => .obj_obj
  | .bot,   .obj _, _        => .bot_obj
  | .bot,   .bot,   _        => .bot_bot
instance succ.denote'.cont : Continous succ.denote' :=
  Continous.finite succ.denote'.mono 
def succ.denote : CFunc (Flat Nat) (Flat Nat) where
  f := succ.denote'
  continous := succ.denote'.cont 

def pred.denote' : Flat Nat → Flat Nat
  | .obj (.succ v) => .obj v
  | .obj 0 => .bot
  | .bot => .bot
def pred.denote'.mono : Monotone pred.denote' := fun
  | .obj (_+1), .obj _, .obj_obj => .obj_obj
  | .bot, .obj (.succ _), _ => .bot_obj
  | .bot, .obj 0, _
  | .obj 0, .obj _, .obj_obj
  | .bot, .bot, _ => .bot_bot
instance pred.denote'.cont : Continous pred.denote' :=
  Continous.finite pred.denote'.mono
def pred.denote : CFunc (Flat Nat) (Flat Nat) where
  f := pred.denote'
  continous := pred.denote'.cont 

def z?.denote' : Flat Nat → Flat Bool
  | .obj (.succ _) => .obj .false
  | .obj 0 => .obj .true
  | .bot => .bot
def z?.denote'.mono : Monotone z?.denote' := fun
  | .obj 0, .obj _, .obj_obj | .obj (_+1), .obj _, .obj_obj => .obj_obj
  | .bot, .obj 0, .bot_obj   | .bot,   .obj (_+1), .bot_obj => .bot_obj
  | .bot, .bot, .bot_bot => .bot_bot
instance z?.denote'.cont : Continous z?.denote' :=
  Continous.finite z?.denote'.mono
def z?.denote : CFunc (Flat Nat) (Flat Bool) where
  f := z?.denote'
  continous := z?.denote'.cont

def ite.denote' [Bot τ] : Flat Bool × τ × τ → τ
  | ⟨.obj .true,  v⟩ => Prod.fst v
  | ⟨.obj .false, v⟩ => Prod.snd v
  | ⟨.bot, _, _⟩ => ⊥

def ite.denote'.mono [Preorder τ] [OrderBot τ] : Monotone (ite.denote' : _ → τ) := fun
  | ⟨.bot, _⟩, ⟨.obj .true,  _⟩, ⟨.bot_obj, _⟩
  | ⟨.bot, _⟩, ⟨.obj .false, _⟩, ⟨.bot_obj, _⟩ => bot_le

  | ⟨.obj .true,  _⟩, ⟨.obj .true,  _⟩, ⟨.obj_obj, o, _⟩
  | ⟨.obj .false, _⟩, ⟨.obj .false, _⟩, ⟨.obj_obj, _, o⟩ => o

  | ⟨.bot, _⟩, ⟨.bot, _⟩, ⟨.bot_bot, _⟩ => le_refl _
instance [Dom τ] : Continous (ite.denote' : _ → τ) :=
  Continous.sep_args ite.denote'.mono
    (fun en hen d => by
      have : DecidableEq τ := Classical.typeDecidableEq τ
      rw [FiniteDom.complete_last]
      have m : Monotone (ite.denote' ⟨·, d⟩) :=
        (two_arg_mono.mpr ite.denote'.mono).1 d
      let enFin := FiniteDom.chain_fin en hen
      let map := C.Finite.map (f := (ite.denote' ⟨·, d⟩)) m enFin
      have := C.Finite.complete_last _ (hen.map m) <| map
      rw [this]
      have := C.Finite.ls_map _ m map enFin
      rw [List.getLast_writer this]
      dsimp [List.dedup]
      rw [pw_filter_last, List.getLast_map]
    )
    (fun
      | .bot, en, h => complete_const.symm
      | .obj .true, en, h | .obj .false, en, h => rfl)
def ite.denote [Dom τ] : CFunc (Flat Bool × τ × τ) τ where
  f := ite.denote'
  continous := by infer_instance

end PCF
