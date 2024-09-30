import Lean
import equational_theories.FreeMagma
import Mathlib.Order.Basic


open Lean Elab Parser Meta

declare_syntax_cat magma_term

syntax ident:magma_term
syntax "(" magma_term ")" : magma_term
syntax:44 magma_term:45 " ∘ " magma_term:43 : magma_term

syntax "magmaterm{" magma_term "}" : term
syntax "magmalaw{" magma_term " ≃ " magma_term "}" : term

macro_rules
  | `(magmaterm{$x:ident}) => `(FreeMagma.Leaf $(Lean.quote (toString x.getId)))
  | `(magmaterm{$l:magma_term ∘ $r:magma_term}) =>
    `(FreeMagma.Fork magmaterm{$l} magmaterm{$r})
  | `(magmaterm{($t:magma_term)}) => `(magmaterm{$t})


structure MagmaLaw (α : Type) where
  mk :: (lhs : FreeMagma α) (rhs : FreeMagma α)
deriving DecidableEq, Repr

macro_rules
  | `(magmalaw{$l:magma_term ≃ $r:magma_term}) => `(MagmaLaw.mk magmaterm{$l} magmaterm{$r})

#check magmaterm{x ∘ y ∘ z ∘ zks}
#check magmalaw{x ∘ y ∘ z ≃ z}

def reduce_magma_term {α :Type} [BEq α] (x : FreeMagma α) : StateM (List α) (FreeMagma Nat) :=
  match x with
    | .Leaf a => do
      let l ← get
      let i := l.indexOf a
      if i = l.length then
        set (l ++ [a])
      return .Leaf i
    | .Fork l r => do
      let left ← reduce_magma_term l
      let right ← reduce_magma_term r
      return .Fork left right

def reduce_law {α :Type} [DecidableEq α] (law : MagmaLaw α) : MagmaLaw Nat := match law with
  | .mk l r => (MagmaLaw.mk <$> reduce_magma_term l <*> reduce_magma_term r).run' []

#reduce reduce_law magmalaw{x ∘ y ≃ y ∘ x}


open Lean PrettyPrinter Delaborator SubExpr

def get_variable_name (n:Nat) : String := match ["x","y","z","u","v","w"][n]? with
  | .some s => s
  | .none => "x_" ++ (n - 6).repr

@[app_unexpander FreeMagma.Leaf]
def unexpandLeaf : Unexpander
  | `($(_) $x:str) => do
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `(magmaterm{ $(⟨name.raw⟩) }) -- note the coercion from Ident to TSyntax
  | `($(_) $n:num) => do
    let str := get_variable_name n.getNat
    let name := mkIdent $ Name.mkSimple str
    `(magmaterm{ $(⟨name.raw⟩) })
  | _ => throw ()

@[app_unexpander FreeMagma.Fork]
def unexpandFork : Unexpander
  | `($(_) magmaterm{$l:magma_term} magmaterm{$r:magma_term}) =>
    `(term| magmaterm{$l ∘ $r})
  | _ => throw ()

@[app_unexpander MagmaLaw.mk]
def unexpandMagmaLaw : Unexpander
  | `(term|$(_) magmaterm{$l:magma_term} magmaterm{$r:magma_term}) => do
    `(term|magmalaw{$l ≃ $r})
  | _ => throw ()

-- magmaterm{(x ∘ (y ∘ (z ∘ zks)))} : FreeMagma String
#check magmaterm{x ∘ y ∘ (z ∘ zks)}

-- magmalaw{x ∘ y ∘ z ≃ z} : MagmaLaw String
#check magmalaw{x ∘ y ∘ z ≃ z}

-- magmalaw{x ∘ y ≃ y ∘ x} : MagmaLaw Nat
#reduce reduce_law magmalaw{x ∘ y ≃ y ∘ x}

-- magmalaw{x ∘ y ≃ y ∘ x} : MagmaLaw Nat
#check MagmaLaw.mk
  (FreeMagma.Fork (FreeMagma.Leaf 0) (FreeMagma.Leaf 1))
  (FreeMagma.Fork (FreeMagma.Leaf 1) (FreeMagma.Leaf 0))

def MagmaLaw.holdsInMagma {α:Type} (G:Type) [Magma G] (law:MagmaLaw α) : Prop :=
  ∀ (f: α → G), law.lhs.evalInMagma f = law.rhs.evalInMagma f

infix:50 " ⊧ " => MagmaLaw.holdsInMagma

instance {α :Type}: Preorder (MagmaLaw α) where
  le l r := ∀ (G:Type) [Magma G], G ⊧ l → G ⊧ r
  le_refl a := by
    intro G _
    exact id
  le_trans := by
    intro a b c hab hbc
    intro G _ h
    apply hbc G
    exact hab G h

example :∀ law, magmalaw{x ≃ y} ≤ law := by
  intro right G _
  dsimp [MagmaLaw.holdsInMagma, FreeMagma.evalInMagma]
  intro h f
  generalize right.lhs.evalInMagma f = a
  generalize right.rhs.evalInMagma f = b
  specialize h (fun x => if x = "x" then a else b)
  simp only [↓reduceIte, String.reduceEq] at h
  exact h

example : ∀ law, law ≤ magmalaw{x ≃ x} := by
  intro left G _
  intro _ f
  rfl
