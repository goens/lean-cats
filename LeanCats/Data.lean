import Mathlib.Data.Rel

namespace Data

inductive Thread : Type where
  | mk: Nat -> Thread
deriving Inhabited, BEq, Repr, DecidableEq

inductive Op : Type where
  | write : Op
  | read : Op
  | fence : Op
  | branch : Op
deriving Inhabited, BEq, Repr, DecidableEq

abbrev Location := String

structure Effect : Type where
  op : Op
  location : Location
  -- For read, the value can not be determined at the begining.
  value : Option Nat
  isFirstWrite : Bool
  isFinalWrite : Bool
deriving Inhabited, BEq, Repr, DecidableEq

class Tag (t : Type) where

structure Event where
  (id : Nat)   -- Unique identifier, consistent with program order for a given thread
  (t_id : Nat)      -- Thread ID
  (t : Thread)    -- Associated thread
  (effect : Effect) -- Action performed
  [tag {tagType} [Tag tagType] : tagType]

@[simp] def reads : Set Event :=
  λ e ↦ e.effect.op = Op.read

@[simp] def writes : Set Event :=
  λ e ↦ e.effect.op = Op.write

@[simp] def modifications : Set Event :=
  reads ∪ writes

-- Events can be (for brevity this is not an exhaustive list):
-- writes, gathered in the set W, including the the set IW of initial writes coming from the prelude of the program;
-- reads, gathered in the set R;
-- branch events, gathered in the set B;
-- fences, gathered in the set F.
structure Events where
  (all : Set Event)
  (Acquire : Set Event)
  (Release : Set Event)
  (IW : Set Event)
  (R : Set Event)
  (W : Set Event)
  (B : Set Event)
  (F : Set Event)
  (RMW : Set Event)

instance : Membership Event Events where
  mem evts evt := evt ∈ evts.all

/-
In the definition of the cat specification, we know that the tag is just an id.
Basically it's a event.

What we want is a:
  enum A = 'z | 'a
  enum B = 'z | 'a
  etc

-/

end Data
