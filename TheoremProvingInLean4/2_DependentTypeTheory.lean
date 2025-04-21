--------------------------------------------------------------------------
---Simple Type Theory-----------------------------------------------------
--------------------------------------------------------------------------

/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false

#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9

#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type

#check List α    -- Type
#check List Nat  -- Type

#check Type      -- Type 1

#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5

#check Type
#check Type 0

#check List    -- List.{u} (α : Type u) : Type u

#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)

universe u

def H (α : Type u) : Type u := Prod α α

#check H    -- Type u → Type u

def I.{v} (α : Type v) : Type v := Prod α α

#check I    -- Type v → Type v

--------------------------------------------------------------------------
--Function Abstraction and Evaluation-------------------------------------
--------------------------------------------------------------------------

#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x => x + 5     -- Nat inferred
#check λ x => x + 5       -- Nat inferred

#eval (λ x : Nat => x + 5) 10    -- 15

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun _ : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool

#check fun (α β : Type) (γ : Type 5) (g : β → γ) (f : α → β) (x : α) => g (f x)

#check (fun x : Nat => x) 1     -- Nat
#check (fun _ : Nat => true) 1  -- Bool

def h (n : Nat) : String := toString n
def i (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool i h
  -- Nat → Bool

#eval
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool i h 0
  -- true

#eval (fun x : Nat => x) 1     -- 1
#eval (fun _ : Nat => true) 1  -- true

--------------------------------------------------------------------------
--Definitions-------------------------------------------------------------
--------------------------------------------------------------------------

def double (x : Nat) : Nat :=
  x + x

#eval double 3    -- 6

def doubleLambda : Nat → Nat :=
  fun x => x + x

#eval doubleLambda 3    -- 6

def doubleLambdaInferred :=
  fun (x : Nat) => x + x

#eval doubleLambda 3    -- 6

def pi := 3.141592654

def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5

def doubleAgain (x : Nat) : Nat :=
 x + x

def addAgain (x : Nat) (y : Nat) :=
  x + y

#eval addAgain (doubleAgain 3) (7 + 9)  -- 22

def greater (x y : Nat) :=
  if x > y then x
  else y

def doubleAgainAgain (x : Nat) : Nat :=
 x + x

def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice doubleAgainAgain 2   -- 8

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doubleAgainAgainAgain (x : Nat) : Nat :=
 x + x
def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat doubleAgainAgainAgain square 3  -- 18

--------------------------------------------------------------------------
--Local Definitions-------------------------------------------------------
--------------------------------------------------------------------------

#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16

#check let y := 2 + 2; let z := y + y; z * z   -- Nat
-- ((2 + 2) + (2 + 2)) * ((2 + 2) + (2 + 2)) ?
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64

-- multi line
def t (x : Nat) : Nat :=
  let y := x + x
  y * y

-- This typechecks
def foo := let a := Nat; fun x : a => x + 2
-- This does not typecheck because we can't lock down the fact that "a" will
-- be the type "Nat". So this let construct lets us do more specific
-- declarations.
-- def bar := (fun a => fun x : a => x + 2) Nat
--

--------------------------------------------------------------------------
--Variables and Sections--------------------------------------------------
--------------------------------------------------------------------------

-- Variables make for nice and compact definitions.

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def composeCompact := g (f x)
def doTwiceCompact := h (h x)
def doThrice := h (h (h x))

#print composeCompact
#print doTwiceCompact
#print doThrice

section UsefulForVariables
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def composeCompactAgain := g (f x)
  def doTwiceAgain := h (h x)
  def doThriceAgain := h (h (h x))
end UsefulForVariables

--------------------------------------------------------------------------
--Namespaces--------------------------------------------------------------
--------------------------------------------------------------------------

namespace Foo
  def a : Nat := 5
  def b (x : Nat) : Nat := x + 7

  def ba : Nat := b a
  def bba : Nat := b (b a)

  #check a
  #check b
  #check ba
  #check bba
  #check Foo.ba
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.b
#check Foo.ba
#check Foo.bba

open Foo

#check a
#check b
#check ba
#check Foo.ba

#check List.nil
#check List.cons
#check List.map

open List

#check nil
#check cons
#check map

namespace FooAgain
  def c : Nat := 5
  def d (x : Nat) : Nat := x + 7

  def dc : Nat := d c

  namespace Bar
    def ddc : Nat := d (d c)

    #check dc
    #check ddc
  end Bar

  #check dc
  #check Bar.ddc
end FooAgain

#check FooAgain.dc
#check FooAgain.Bar.ddc

open FooAgain

#check dc
#check Bar.ddc

namespace FooAgainAgain
  def j : Nat := 5
  def k (x : Nat) : Nat := x + 7

  def kj : Nat := k j
end FooAgainAgain

#check FooAgainAgain.j
#check FooAgainAgain.kj

namespace FooAgainAgain
  def kkj : Nat := k (k j)
end FooAgainAgain

--------------------------------------------------------------------------
---What makes dependent type theory dependent?----------------------------
--------------------------------------------------------------------------

def consDef (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check consDef Nat        -- Nat → List Nat → List Nat
#check consDef Bool       -- Bool → List Bool → List Bool
#check consDef            -- (α : Type) → α → List α → List α
