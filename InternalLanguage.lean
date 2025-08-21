import Aesop
import Qq

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Qq

/- # Abstract Syntax of the STLC -/

inductive Ty  where
  | unit : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq

notation "⊤" => Ty.unit
infixr : 50 "⇒" => Ty.arr

inductive Tm where
  | var : Nat → Tm
  | tt : Tm
  | lam : Ty → Tm → Tm
  | app : Tm → Tm → Tm

notation "()" => Tm.tt
notation "Λ " T ", " t => Tm.lam T t
infixl : 60 "@" => Tm.app

instance : Coe Nat Tm where
  coe := .var

instance : OfNat Tm n where
  ofNat := n

abbrev Ctx := List Ty

/- # Typing Rules -/

@[aesop safe (transparency! := default) constructors]
inductive VarHasType : Ctx → Nat → Ty → Prop where
  | zero : VarHasType (T :: Γ) 0 T
  | succ : VarHasType Γ n T → VarHasType (U :: Γ) (n + 1) T

notation : 10 Γ " ⊢ᵥ " n " ∶ " T => VarHasType Γ n T

@[aesop safe (transparency! := default) constructors]
inductive HasType : Ctx → Tm → Ty → Prop where
  | var : (Γ ⊢ᵥ n ∶ T) → HasType Γ (.var n) T
  | tt : HasType Γ () ⊤
  | lam : HasType (T :: Γ) t U → HasType Γ (Λ T, t) (T ⇒ U)
  | app : HasType Γ t (T ⇒ U) → HasType Γ u T → HasType Γ (t @ u) U

notation : 10 Γ " ⊢ " t " ∶ " T => HasType Γ t T

example : [] ⊢ Λ ⊤, Λ ⊤, 0 ∶ ⊤ ⇒ ⊤ ⇒ ⊤ := by
  aesop

/- # Typechecker (Bidirectional for Fun) -/

mutual
  def check (Γ : Ctx) : (t : Tm) → (T : Ty) → Option (PLift (Γ ⊢ t ∶ T))
    | .var n, T => do
      let ⟨T', p⟩ ← inferVar Γ n
      if eq : T = T' then
        return ⟨.var (eq ▸ p)⟩
      else
        failure
    | (), ⊤ => return ⟨.tt⟩
    | (), _ => failure
    | .app t u, U => do
      let ⟨T ⇒ U', pt⟩ ← infer Γ t
        | failure
      if eq : U = U' then
        let ⟨pu⟩ ← check Γ u T
        return ⟨.app (eq ▸ pt) pu⟩
      else
        failure
    | .lam T t, T' ⇒ U => do
      if eq : T = T' then
        let ⟨p⟩ ← check (T :: Γ) t U
        return ⟨eq ▸ .lam p⟩
      else
        none
    | .lam T t, _ => failure

  def inferVar : (Γ : Ctx) → (n : Nat) → Option (Σ' T, Γ ⊢ᵥ n ∶ T)
    | [], _ => failure
    | T :: _, .zero => return ⟨T, .zero⟩
    | _ :: Γ, .succ n => do
      let ⟨T, p⟩ ← inferVar Γ n
      return ⟨T, .succ p⟩

  def infer (Γ : Ctx) : (t : Tm) → Option (Σ' T, Γ ⊢ t ∶ T)
    | .var n => do
      let ⟨T, p⟩ ← inferVar Γ n
      return ⟨T, .var p⟩
    | () => return ⟨⊤, .tt⟩
    | Λ T, t => do
      let ⟨U, p⟩ ← infer (T :: Γ) t
      return ⟨T ⇒ U, .lam p⟩
    | .app t u => do
      let ⟨T ⇒ U, pt⟩ ← infer Γ t
        | failure
      let ⟨pu⟩ ← check Γ u T
      return ⟨U, .app pt pu⟩
end

/- # Parser -/

declare_syntax_cat ty (behavior := both)

syntax &"Unit" : ty
syntax ty "→" ty : ty
syntax "(" ty ")" : ty

declare_syntax_cat tm (behavior := both)

syntax ident : tm
syntax "()" : tm
syntax &"λ " ident " : " ty ". " tm : tm
syntax tm tm : tm
syntax "(" tm ")" : tm

/- # Elaborator -/

partial def elabTy : TSyntax `ty → TermElabM Q(Ty)
  | `(ty| Unit) => return q(Ty.unit)
  | `(ty| $T:ty → $U:ty) => return q(Ty.arr $(← elabTy T) $(← elabTy U))
  | `(ty| ($T:ty)) => elabTy T
  | _ => throwUnsupportedSyntax

abbrev ElabCtx := List Name

namespace ElabCtx

protected def empty : ElabCtx := []

def extend (Γ : ElabCtx) (name : Name) : ElabCtx :=
  name :: Γ

def getIdx? (ctx : ElabCtx) (name : Name) : Option Nat :=
  go 0 ctx
where
  go (i : Nat) : ElabCtx → Option Nat
    | [] => none
    | n :: ctx =>
      if n == name then
        some i
      else
        go (i + 1) ctx

end ElabCtx

abbrev TmElabM := ReaderT ElabCtx TermElabM

protected def TmElabM.run (x : TmElabM α) : TermElabM α :=
  ReaderT.run x .empty

def getCtx : TmElabM ElabCtx :=
  read

partial def elabTm : TSyntax `tm → TmElabM Q(Tm)
  | `(tm| $id:ident) => do
    let id := id.getId
    if let some i := (← getCtx).getIdx? id then
      return q(Tm.var $i)
    else
      throwError "unknown identifier: {id}"
  | `(tm| ()) =>
    return q(Tm.tt)
  | `(tm| λ $id:ident : $T:ty. $t:tm) => do
    let id := id.getId
    let T ← elabTy T
    let t ← withReader (·.extend id) $ elabTm t
    return q(Tm.lam $T $t)
  | `(tm| $t:tm $u:tm) =>
    return q(Tm.app $(← elabTm t) $(← elabTm u))
  | `(tm| ($t:tm)) =>
    elabTm t
  | _ => throwUnsupportedSyntax

elab "tm%⟨ " t:tm " ⟩" : term =>
  elabTm t |>.run

structure TTm where
  Γ : Ctx
  t : Tm
  T : Ty
  hasType : Γ ⊢ t ∶ T

def elabTTm (stx : TSyntax `tm) : TmElabM Q(TTm) := do
  let t ← elabTm stx
  let ttm? := q(infer [] $t)
  let ttm? : Q(Option (Σ' T, [] ⊢ $t ∶ T)) ← whnf ttm?
  match ttm? with
  | ~q(Option.some $p) =>
    let p : Q(Σ' T, [] ⊢ $t ∶ T) ← whnf p
    match p with
    | ~q(⟨$T, $p'⟩) =>
      return q({ Γ := [], t := $t, T := $T, hasType := $p'})
  | _ => throwError "type-incorrect!"

elab "ttm%⟨ " t:tm " ⟩" : term =>
  elabTTm t |>.run

/- # Tests -/

section Tests

open Tm Ty

example : Tm := tm%⟨ (λ x : Unit. x x) (λ x : Unit. x x) ⟩

example : tm%⟨ λ x : Unit. λ x : Unit. x ⟩ = lam unit (lam unit (var 0)) := rfl

example : tm%⟨ λ x : Unit. λ y : Unit. x ⟩ = lam unit (lam unit (var 1)) := rfl

example : TTm :=
  ttm%⟨ () ⟩

example : TTm :=
  ttm%⟨ λ x : Unit. λ x : Unit. x ⟩

example : TTm :=
  ttm%⟨ λ x : Unit. λ y : Unit. x ⟩

example : TTm :=
  ttm%⟨ λ f : Unit → Unit. λ x : Unit. f x ⟩

example : TTm :=
  ttm%⟨ λ f : Unit → Unit → Unit. λ x : Unit. f x ⟩

example : TTm :=
  ttm%⟨ λ x : Unit. y ⟩

example : TTm :=
  ttm%⟨ λ x : Unit. λ y : Unit. x y ⟩

example : TTm :=
  ttm%⟨ λ f : (Unit → Unit) → Unit. λ x : Unit. f x ⟩

end Tests
