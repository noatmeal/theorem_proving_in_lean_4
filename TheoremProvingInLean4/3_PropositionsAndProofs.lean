
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

--------------------------------------------------------------------------
--Working with Propositions as Types--------------------------------------
--------------------------------------------------------------------------

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

--------------------------------------------------------------------------
--Conjunction-------------------------------------------------------------
--------------------------------------------------------------------------

namespace Example1000

  variable (p q : Prop)

  example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
  example (h : p ∧ q) : p := And.left h
  example (h : p ∧ q) : q := And.right h
  example (h : p ∧ q) : q ∧ p :=
    And.intro (And.right h) (And.left h)

end Example1000

namespace Example1001

  variable (p q : Prop)
  variable (hp : p) (hq : q)

  #check (⟨hp, hq⟩ : p ∧ q)

end Example1001

namespace Example1010

  variable (xs : List Nat)

  #check List.length xs
  #check xs.length

  variable (p q : Prop)

  example (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left⟩

  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, ⟨h.left, h.right⟩⟩

  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, h.left, h.right⟩

end Example1010

--------------------------------------------------------------------------
--Disjunction-------------------------------------------------------------
--------------------------------------------------------------------------

namespace Example1011

  variable (p q : Prop)
  example (hp : p) : p ∨ q := Or.intro_left q hp
  example (hq : q) : p ∨ q := Or.intro_right p hq

end Example1011

namespace Example1100

  variable (p q r : Prop)

  example (h : p ∨ q) : q ∨ p :=
    Or.elim
      h
      (λ hp : p =>
        show q ∨ p from Or.intro_right q hp)
      (λ hq : q =>
        show q ∨ p from Or.intro_left p hq)

  -- less boilerplate

  example (h : p ∨ q) : q ∨ p :=
    h.elim (λ hp : p => Or.inr hp) (λ hq : q => Or.inl hq)

end Example1100

--------------------------------------------------------------------------
--Negation and Falsity----------------------------------------------------
--------------------------------------------------------------------------

namespace Example1101

  variable (p q r : Prop)

  example (hpq : p → q) (hnq : ¬q) : ¬p :=
    λ hp : p =>
    show False from hnq (hpq hp)

  example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

  -- brevity

  example (hp : p) (hnp : ¬p) : q := absurd hp hnp

  example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp

end Example1101

--------------------------------------------------------------------------
--Logical Equivalence-----------------------------------------------------
--------------------------------------------------------------------------

namespace Example1110

  variable (p q : Prop)

  theorem and_swap : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (λ h : p ∧ q =>
       show q ∧ p from And.intro (And.right h) (And.left h))
      (λ h : q ∧ p =>
       show p ∧ q from And.intro (And.right h) (And.left h))

  variable ( s t : Prop)

  #check and_swap s t    -- s ∧ t ↔ t ∧ s

  variable (h : p ∧ q)
  example : q ∧ p := Iff.mp (and_swap p q) h

end Example1110


-- more concisely

namespace Example1111

  variable (p q : Prop)

  theorem and_swap : p ∧ q ↔ q ∧ p :=
    ⟨ λ h : p ∧ q => ⟨h.right, h.left⟩, λ h : q ∧ p => ⟨h.right, h.left⟩ ⟩

  example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

end Example1111

--------------------------------------------------------------------------
--Introducing Auxiliary Subgoals------------------------------------------
--------------------------------------------------------------------------

namespace Example10000

  variable (p q : Prop)

  -- Starting to feel a lot like doing math :).

  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    have hq : q := h.right
    show q ∧ p from And.intro hq hp

  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    suffices hq : q from And.intro hq hp
    show q from And.right h

end Example10000

--------------------------------------------------------------------------
--Classical Logic---------------------------------------------------------
--------------------------------------------------------------------------

namespace Example10001

  open Classical

  variable (p : Prop)
  #check em p

  theorem dne {p : Prop} (h : ¬¬p) : p :=
    Or.elim
      (em p)
      (λ hp : p => hp)
      (λ hnp : ¬p => absurd hnp h)

end Example10001

namespace Exercise0
-- Show excluded middle from double negation.

  -- I totally ripped this from
  -- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Proving.20double.20negation.20elimination.20implies.20LEM/near/362946379
  theorem demorgan {p q: Prop} : ¬(p ∨ q) → ¬p ∧ ¬q :=
    λ h : ¬(p ∨ q) => ⟨λ hp : p => h (Or.inl hp), λ hq : q => h (Or.inr hq)⟩

  theorem dne {p : Prop} (h : ¬¬p) : p := sorry

  theorem em2 {p : Prop} : p ∨ ¬p :=
    suffices hnn : ¬¬(p ∨ ¬ p) from dne hnn
    λ hn : ¬(p ∨ ¬p) =>
      let h := demorgan hn
      have hp : p := dne (h.right)
      have hnp : ¬p := h.left
      hnp hp

end Exercise0
