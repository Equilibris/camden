import Denote.Utils

namespace PCF

universe u v

inductive Ty : Type where
  | arr   : Ty → Ty → Ty
  | nat  : Ty
  | bool : Ty
deriving DecidableEq

declare_syntax_cat stlc_ty

syntax ident : stlc_ty
syntax "!(" term ")" : stlc_ty
syntax "(" stlc_ty ")" : stlc_ty
syntax stlc_ty ppSpace "→" ppSpace stlc_ty : stlc_ty

syntax "[ty|" stlc_ty "]" : term

macro_rules
  | `([ty| nat ]) => `(Ty.nat)
  | `([ty| bool ]) => `(Ty.bool)
  | `([ty| $id:ident ]) => `($id)
  | `([ty| !($t) ]) => `($t)
  | `([ty| ($v) ]) => `([ty| $v])
  | `([ty| $a → $b ]) => `(Ty.arr [ty| $a] [ty| $b])

open Lean in
def Ty.uex_inner : Syntax.Term → PrettyPrinter.UnexpandM (TSyntax `stlc_ty)
  | `([ty|$b]) => `(stlc_ty|$b)
  | `($t) => `(stlc_ty|!($t))

@[app_unexpander Ty.bool]
def Ty.bool.uex : Lean.PrettyPrinter.Unexpander
  | `($_p) => `([ty| bool])

@[app_unexpander Ty.nat]
def Ty.nat.uex : Lean.PrettyPrinter.Unexpander
  | `($_p) => `([ty| nat])

@[app_unexpander Ty.arr]
def Ty.arr.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do
    let a ← uex_inner a
    let b ← uex_inner b
    let perenify : Lean.TSyntax `stlc_ty → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `stlc_ty)
      | `(stlc_ty|$c → $d) => `(stlc_ty|($c → $d))
      | v => `(stlc_ty|$v)
    let a ← perenify a
    `([ty| $a → $b])
  | _ => throw ()

inductive ITerm : List Ty → Ty → Type
  | var {ctx ty} : ctx.MemT ty → ITerm ctx ty

  | lam {dom ctx ran} : ITerm (dom :: ctx) ran → ITerm ctx (.arr dom ran)
  | app {ctx dom ran} : ITerm ctx (.arr dom ran) → ITerm ctx dom → ITerm ctx ran

  | true  {ctx} : ITerm ctx .bool
  | false {ctx} : ITerm ctx .bool
  | ite {ctx ty} : ITerm ctx .bool → ITerm ctx ty → ITerm ctx ty → ITerm ctx ty

  | zero {ctx} : ITerm ctx .nat
  | succ {ctx} : ITerm ctx .nat → ITerm ctx .nat
  | pred {ctx} : ITerm ctx .nat → ITerm ctx .nat

  | z? {ctx} : ITerm ctx .nat → ITerm ctx .bool

  | fix {ctx ty} : ITerm ctx (.arr ty ty) → ITerm ctx ty

namespace ITerm

def gshift {Γ Γ₁ Γ₂} : ITerm (Γ ++ Γ₁) t → ITerm (Γ ++ (Γ₂ ++ Γ₁)) t
  | .var h => .var h.sandwitch_shift

  | .pred v => .pred v.gshift
  | .succ v => .succ v.gshift
  | .zero => .zero

  | .false => .false | .true => .true

  | .fix v => .fix v.gshift
  | .z? v => .z? v.gshift
  | .ite c t f => .ite c.gshift t.gshift f.gshift
  | .app a b => .app a.gshift b.gshift
  | .lam (dom := dom) v => .lam (v.gshift (Γ := dom :: Γ))

def shift {Γ₁} Γ₂ : ITerm Γ₁ t → ITerm (Γ₂ ++ Γ₁) t := gshift (Γ := [])

def parSubst (hList : HList (ITerm Γ') Γ) : ITerm Γ t → ITerm Γ' t
  | .var h => hList[h]

  | .pred v => .pred <| v.parSubst hList
  | .succ v => .succ <| v.parSubst hList
  | .zero => .zero

  | .false => .false | .true => .true

  | .fix v => .fix <| v.parSubst hList
  | .z? v => .z? <| v.parSubst hList
  | .ite c t f => .ite (c.parSubst hList) (t.parSubst hList) (f.parSubst hList)
  | .app a b => .app (a.parSubst hList) (b.parSubst hList)
  | .lam (dom := dom) v => .lam
      <| v.parSubst
      <| .cons (.var .hd)
      <| hList.map
      <| shift [dom]

def parSubst.noopL : {Γ : _} → HList (ITerm Γ) Γ
  | [] => .nil
  | _ :: _ => .cons (.var .hd) <| noopL.map <| shift [_]

theorem parSubst.noopL_get
    : {Γ : _}
    → (h : List.MemT t Γ)
    → (parSubst.noopL (Γ := Γ))[h] = var h 
  | _ :: _, .hd => rfl
  | _ :: _, .tl h => by 
    change HList.get h (HList.map _ noopL) = var h.tl
    rw [HList.get_map', parSubst.noopL_get]
    cases h
    · simp only [shift, gshift, List.cons_append, List.nil_append, List.MemT.sandwitch_shift, var.injEq]
      rename_i as
      cases as <;> rfl
    · simp [shift, gshift, List.MemT.sandwitch_shift, List.MemT.shift]

theorem parSubst.noop : {e : ITerm Γ t} → e.parSubst parSubst.noopL = e
  | .var h => noopL_get h
  | .app _ _
  | .ite _ _ _ | .fix _ | .z? _ | .pred _ | .succ _ => by
    dsimp [parSubst]
    repeat rw [parSubst.noop]
  | .zero | .false | .true => rfl
  | .lam _ => by
    change ITerm.lam (parSubst noopL _) = .lam _
    rw [parSubst.noop]

theorem parSubst.closed : {e : ITerm [] t} → e.parSubst .nil = e := parSubst.noop

