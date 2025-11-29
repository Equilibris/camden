import Types.STLCHOAS.Stx
import Types.STLCHOAS.Denote
import Types.STLCHOAS.Show

namespace STLCHOAS

universe u

-- Identity function: (A → A) → A → A
def id_type : Ty := Ty.arr Ty.unit Ty.unit

-- λ x. x
def identity : Term (Ty.arr Ty.unit Ty.unit) :=
  Term'.lam (fun x => Term'.var x)

-- Boolean type encoded as sum: Unit ⊕ Unit
def bool_type : Ty := Ty.cpd Ty.unit Ty.unit

-- true = inl ()
def true_term : Term bool_type :=
  Term'.inl Term'.unit

-- false = inr ()
def false_term : Term bool_type :=
  Term'.inr Term'.unit

-- Boolean conditional: (Unit ⊕ Unit) → A → A → A
def if_then_else_type (A : Ty) : Ty :=
  Ty.arr bool_type (Ty.arr A (Ty.arr A A))

def if_then_else (A : Ty) : Term (if_then_else_type A) :=
  Term'.lam (fun b =>
    Term'.lam (fun t =>
      Term'.lam (fun f =>
        Term'.case (Term'.var b)
          (fun _ => Term'.var t)
          (fun _ => Term'.var f))))

-- Pair operations
def pair_type (A B : Ty) : Ty := Ty.prod A B

def make_pair (A B : Ty) : Term (Ty.arr A (Ty.arr B (pair_type A B))) :=
  Term'.lam (fun a =>
    Term'.lam (fun b =>
      Term'.mkP (Term'.var a) (Term'.var b)))

def first_proj (A B : Ty) : Term (Ty.arr (pair_type A B) A) :=
  Term'.lam (fun p => Term'.fst (Term'.var p))

def second_proj (A B : Ty) : Term (Ty.arr (pair_type A B) B) :=
  Term'.lam (fun p => Term'.snd (Term'.var p))

-- Swap a pair: (A × B) → (B × A)
def swap (A B : Ty) : Term (Ty.arr (pair_type A B) (pair_type B A)) :=
  Term'.lam (fun p =>
    Term'.mkP
      (Term'.snd (Term'.var p))
      (Term'.fst (Term'.var p)))

-- Composition: (B → C) → (A → B) → (A → C)
def compose (A B C : Ty) : Term (Ty.arr (Ty.arr B C) (Ty.arr (Ty.arr A B) (Ty.arr A C))) :=
  Term'.lam (fun g =>
    Term'.lam (fun f =>
      Term'.lam (fun x =>
        Term'.app (Term'.var g) (Term'.app (Term'.var f) (Term'.var x)))))

-- Either operations
def either_type (A B : Ty) : Ty := Ty.cpd A B

def left_inject (A B : Ty) : Term (Ty.arr A (either_type A B)) :=
  Term'.lam (fun a => Term'.inl (Term'.var a))

def right_inject (A B : Ty) : Term (Ty.arr B (either_type A B)) :=
  Term'.lam (fun b => Term'.inr (Term'.var b))

-- Case analysis: (A ⊕ B) → (A → C) → (B → C) → C
def case_analysis (A B C : Ty) : Term (Ty.arr (either_type A B) (Ty.arr (Ty.arr A C) (Ty.arr (Ty.arr B C) C))) :=
  Term'.lam (fun sum =>
    Term'.lam (fun f =>
      Term'.lam (fun g =>
        Term'.case (Term'.var sum)
          (fun a => Term'.app (Term'.var f) (Term'.var a))
          (fun b => Term'.app (Term'.var g) (Term'.var b)))))

-- Absurd elimination: Empty → A
def absurd_elim (A : Ty) : Term (Ty.arr Ty.empty A) :=
  Term'.lam (fun x => Term'.empty (Term'.var x))

-- Examples of denotational semantics
example : Ty.denote Ty.unit = PUnit := rfl
example : Ty.denote Ty.empty = PEmpty := rfl
example : Ty.denote bool_type = (PUnit ⊕ PUnit) := rfl
example : Ty.denote (pair_type Ty.unit Ty.unit) = (PUnit × PUnit) := rfl

example : Term'.denote identity = (fun x : PUnit => x) := rfl
example : Term'.denote true_term = Sum.inl PUnit.unit := rfl
example : Term'.denote false_term = Sum.inr PUnit.unit := rfl

-- Show examples
/-- info: "((1 ⊕ 1) → (1 → (1 → 1)))" -/
#guard_msgs in
#eval Ty.show (if_then_else_type Ty.unit)

/-- info: "(λa : (1 ⊕ 1). (λb : 1. (λc : 1. (case a of inl d => b | inr e => c))))" -/
#guard_msgs in
#eval Term'.show (if_then_else Ty.unit)

/-- info: "(inl ())" -/
#guard_msgs in
#eval Term'.show true_term

/-- info: "(inr ())" -/
#guard_msgs in
#eval Term'.show false_term

/-- info: "(λa : (1 × 1). ⟨(a.2), (a.1)⟩)" -/
#guard_msgs in
#eval Term'.show (swap Ty.unit Ty.unit)

/-- info: "(λa.(λb.(λc.(a (b c)))))" -/
#guard_msgs in
#eval Term'.show (compose Ty.unit Ty.unit Ty.unit)

-- Correctness properties
@[simp]
theorem if_true {A : Ty} (t f : A.denote) :
    Term'.denote (if_then_else A) (Sum.inl PUnit.unit) t f = t := rfl

@[simp]
theorem if_false {A : Ty} (t f : A.denote) :
    Term'.denote (if_then_else A) (Sum.inr PUnit.unit) t f = f := rfl

@[simp]
theorem fst_pair {A B : Ty} (a : A.denote) (b : B.denote) :
    Term'.denote (first_proj A B) ⟨a, b⟩ = a := rfl

@[simp]
theorem snd_pair {A B : Ty} (a : A.denote) (b : B.denote) :
    Term'.denote (second_proj A B) ⟨a, b⟩ = b := rfl

-- Denotational equivalence examples
def swap_involution (A B : Ty) : Term (Ty.arr (pair_type A B) (pair_type A B)) :=
  Term'.lam (fun p => Term'.app (swap B A) (Term'.app (swap A B) (Term'.var p)))

theorem swap_is_involution (A B : Ty) : same (swap_involution A B) (identity) := by
  ext p
  simp [Term'.denote, swap, swap_involution, identity]
  cases p with
  | mk a b => simp

end STLCHOAS
