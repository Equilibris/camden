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

inductive Term' (rep : Ty → Type) : Ty → Type where
  | var {t} : rep t → Term' rep t

  | lam {A B} : (rep A → Term' rep B) → Term' rep (Ty.arr A B)
  | app {A B} : Term' rep (.arr A B) → Term' rep A → Term' rep B

  | true : Term' rep .bool
  | false : Term' rep .bool
  | ite {A}
      : Term' rep .bool
      → Term' rep A
      → Term' rep A
      → Term' rep A

  | zero : Term' rep .nat
  | succ : Term' rep .nat → Term' rep .nat 
  | pred : Term' rep .nat → Term' rep .nat 

  | z? : Term' rep .nat → Term' rep .bool

  | fix {A} : Term' rep (.arr A A) → Term' rep A

def Term (t : Ty) : Type 1 :=
  {rep : Ty → Type} → Term' rep t

namespace Term

def var {t} : {rep : Ty → Type} → rep t → Term' rep t
  | _, r => .var r

def lam {A B} : (∀ {rep : Ty → Type}, rep A → Term B) → Term (.arr A B)
  | f, _ => .lam (fun r => f r)

def app {A B} : Term (.arr A B) → Term A → Term B
  | f, v, _ => .app f v

def true : Term .bool
  | _ => .true

def false : Term .bool
  | _ => .false

def ite {A} : Term .bool → Term A → Term A → Term A
  | c, t, e, _ => .ite c t e

def zero : Term .nat
  | _ => .zero

def succ : Term .nat → Term .nat
  | v, _ => .succ v

def pred : Term .nat → Term .nat
  | v, _ => .pred v

def z? : Term .nat → Term .bool
  | v, _ => .z? v

def fix {A} : Term (.arr A A) → Term A
  | f, _ => .fix f

end Term

inductive _root_.List.MemT {A} : A → List A → Type
  | hd {a as} : MemT a (a :: as)
  | tl {bs a b} : MemT a bs → MemT a (b :: bs)

def _root_.List.MemT.shift {l₁}
    : {l₂ : List A}
    → l₁.MemT a
    → (l₂ ++ l₁).MemT a
  | [], h => h
  | _ :: _, h => .tl (shift h)

def _root_.List.MemT.sandwitch_shift {l₁}
    : {l l₂ : List A}
    → (l ++ l₁).MemT a
    → (l ++ (l₂ ++ l₁)).MemT a
  | [],_, h => h.shift
  | _ :: _, _, .hd => .hd
  | _ :: _, _, .tl v => .tl v.sandwitch_shift

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

inductive HList (f : A → Type) : List A → Type
  | nil : HList f []
  | cons {hd tl} : f hd → HList f tl → HList f (hd :: tl)

def HList.get : {t Γ : _} → List.MemT t Γ → HList f Γ → f t 
  | _, _ :: _, .hd, .cons h _ => h
  | _, _ :: _, .tl v, .cons _ tl => tl.get v

def HList.map {f g} (h : ∀ v, f v → g v) : HList f Γ → HList g Γ
  | .nil => .nil
  | .cons hd tl => .cons (h _ hd) $ tl.map h

def parSubst (hList : HList (ITerm Γ') Γ) : ITerm Γ t → ITerm Γ' t
  | .var h => hList.get h

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
      <| fun _ => shift [dom]

-- Instantiate var with depth-tracking
-- At each lambda, pass the current depth as the "variable"
def Wf (depth : Nat) (ctx : List Ty) {ty : _} : Term' (fun _ => Nat) ty → Prop
  | .var n => ctx[depth - n - 1]? = some ty  -- level → index lookup
  | .true | .false | .zero => True
  | .succ v | .z? v | .fix v | .pred v => Wf depth ctx v
  | .lam (A := dom) body => Wf (depth + 1) (dom :: ctx) (body depth)
  | .app f a       => Wf depth ctx f ∧ Wf depth ctx a
  | .ite c t e => Wf depth ctx c ∧ Wf depth ctx t ∧ Wf depth ctx e

instance Wf.dec {depth ctx ty} : {term : Term' _ ty} → Decidable (Wf depth ctx term)
  | .var n => if h : _ = _ then .isTrue h else .isFalse h
  | .true | .false | .zero => .isTrue .intro
  | .succ v | .z? v | .fix v | .pred v => (Wf.dec : Decidable (Wf depth ctx v))
  | .lam (A := dom) body => (Wf.dec : Decidable (Wf (depth+1) _ _))
  | .app _ _ =>
    match Wf.dec, Wf.dec with
    | .isTrue h₁, .isTrue h₂ => .isTrue ⟨h₁, h₂⟩
    | .isFalse h, _=> .isFalse <| not_and_of_not_or_not <| .inl h 
    | _, .isFalse h => .isFalse <| not_and_of_not_or_not <| .inr h 
  | .ite _ _ _ =>
    match Wf.dec, Wf.dec, Wf.dec with
    | .isTrue h₁, .isTrue h₂, .isTrue h₃ => .isTrue ⟨h₁, h₂, h₃⟩
    | .isFalse h, _, _=> .isFalse <| not_and_of_not_or_not <| .inl h 
    | _, .isFalse h, _ => .isFalse <| not_and_of_not_or_not <| .inr <| not_and_of_not_or_not <| .inl h
    | _, _, .isFalse h => .isFalse <| not_and_of_not_or_not <| .inr <| not_and_of_not_or_not <| .inr h

def listGetToMember : {ctx : List Ty} → {ty : Ty} → (n : Nat) → ctx[n]? = some ty → ctx.MemT ty
  | [], _, n, h => by simp at h
  | t :: ts, x, 0, h => cast (congr (congr rfl (by simpa using h)) rfl) .hd
  | t :: ts, ty, n + 1, h => .tl (listGetToMember n h)

-- The actual transformation
def ofWfTerm'
    : {ctx : List Ty}
    → {ty : Ty}
    → (depth : Nat)
    → (t : Term' (fun _ => Nat) ty)
    → Wf depth ctx t
    → ITerm ctx ty
  | _, _, depth, .var n, h => .var (listGetToMember (depth - n - 1) h)
  | _, _, depth, .lam body, h =>
    .lam (ofWfTerm' (depth + 1) (body depth) h)
  | _, _, depth, .app f a, h =>
    .app (ofWfTerm' depth f h.1) (ofWfTerm' depth a h.2)
  | _, _, _, .true, _ => .true
  | _, _, _, .false, _ => .false
  | _, _, depth, .ite c t e, h =>
    .ite (ofWfTerm' depth c h.1) (ofWfTerm' depth t h.2.1) (ofWfTerm' depth e h.2.2)
  | _, _, _, .zero, _ => .zero
  | _, _, depth, .succ n, h => .succ (ofWfTerm' depth n h)
  | _, _, depth, .pred n, h => .pred (ofWfTerm' depth n h)
  | _, _, depth, .z? n, h => .z? (ofWfTerm' depth n h)
  | _, _, depth, .fix f, h => .fix (ofWfTerm' depth f h)

