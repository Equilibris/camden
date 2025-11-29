namespace List

inductive MemT {A} : A → List A → Type
  | hd {a as} : MemT a (a :: as)
  | tl {bs a b} : MemT a bs → MemT a (b :: bs)

namespace MemT

def shift {l₁}
    : {l₂ : List A}
    → l₁.MemT a
    → (l₂ ++ l₁).MemT a
  | [], h => h
  | _ :: _, h => .tl (shift h)

def sandwitch_shift {l₁}
    : {l l₂ : List A}
    → (l ++ l₁).MemT a
    → (l ++ (l₂ ++ l₁)).MemT a
  | [], _, h => h.shift
  | _ :: _, _, .hd => .hd
  | _ :: _, _, .tl v => .tl v.sandwitch_shift

def remove
    : {l : List A}
    → l.MemT v
    → List A 
  | _ :: t, .hd => t
  | h :: _, .tl h' => h :: remove h'

end List.MemT

inductive HList (f : A → Type) : List A → Type
  | nil : HList f []
  | cons {hd tl} : f hd → HList f tl → HList f (hd :: tl)

namespace HList

def get : {t Γ : _} → List.MemT t Γ → HList f Γ → f t
  | _, _ :: _, .hd, .cons h _ => h
  | _, _ :: _, .tl v, .cons _ tl => tl.get v

instance : GetElem (HList f Γ) (List.MemT t Γ) (f t) (fun _ _ => True) where
  getElem h v _ := h.get v

def map {f g} (h : ∀ {v}, f v → g v) : HList f Γ → HList g Γ
  | .nil => .nil
  | .cons hd tl => .cons (h hd) <| tl.map h

end HList
