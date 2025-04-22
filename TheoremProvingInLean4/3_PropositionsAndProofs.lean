
--------------------------------------------------------------------------
--Propositions as Types---------------------------------------------------
--------------------------------------------------------------------------
namespace Example0

def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop

end Example0

namespace Example1

def Implies (p q : Prop) : Prop := p → q
-- Structure hasn't been introduced at this point, so I'm just gonna take this
-- as black magic for now :).
structure Proof (p : Prop) : Type where
  proof : p
#check Proof   -- Proof : Prop → Type

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm p q     -- Proof (Implies (And p q) (And q p))

axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q

axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)

end Example1

namespace Example10

variable {p : Prop}
variable {q : Prop}

-- I'm guessing hp stands for "hypothesis p"?
theorem t1 : p → q → p :=
  λ (hp : p) => λ (_ : q) => hp

#print t1

end Example10

namespace Example11

variable {p : Prop}
variable {q : Prop}
theorem t1 (hp : p) (_ : q) : p := hp
#print t1

axiom hp : p

theorem t2 : q → p := t1 hp

end Example11

namespace Example100

axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound

end Example100

namespace Example101

theorem t1 (p q : Prop) (hp : p) (_ : q) : p := hp

#print t1


end Example101

namespace Example110

-- I prefer this syntax.
theorem t1 : ∀ (p q : Prop), p → q → p :=
  λ (p q : Prop) => λ (hp : p) => λ (_ : q) => hp

#print t1

variable (p q r s : Prop)

#check t1 p q                -- p → q → p
#check t1 r s                -- r → s → r
#check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
variable (i : s → r)
variable (j : r)
#check t1 (r → s) (s → r) h  -- (s → r) → r → s
#check t1 (r → s) (s → r) h i -- r → s
#check t1 (r → s) (s → r) h i j -- s

theorem t2 : ∀ (p q r : Prop), (q → r) → (p → q) → p → r :=
  λ (p q r : Prop) =>
  λ (hqr: q → r) =>
  λ (hqp: p → q) =>
  λ (hp: p) =>
  hqr (hqp hp)

#print t2

end Example110

namespace Example111

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p


end Example111

namespace Example1000

example : ∀ (p q : Prop), p → q → p ∧ q :=
  λ (p q : Prop) (hp : p) (hq : q) => And.intro hp hq

#check λ (p q : Prop) (hp : p) (hq : q) => And.intro hp hq

end Example1000
