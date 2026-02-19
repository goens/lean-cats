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

class Event where
  (id : Nat)   -- Unique identifier, consistent with program order for a given thread
  (t_id : Nat)      -- Thread ID
  (t : Thread)    -- Associated thread
  (effect : Effect) -- Action performed
  (tagType : Type) -- We attach a type to it.
  (tag : tagType)

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
  (Read : Set Event)
  (Write : Set Event)
  (Branch : Set Event)
  (Fence : Set Event)
  (RMW : Set Event)
  (M : Set Event)

  -- Assumptions
  (uniqueId : ∀e₁ e₂ : Event, e₁ = e₂ ↔ e₁.id = e₂.id)
  (writeEqOrNotEq : ∀w₁ w₂ : Write, w₁ = w₂ ∨ w₁ ≠ w₂)
  (readEqOrNotEq : ∀r₁ r₂ : Read, r₁ = r₂ ∨ r₁ ≠ r₂)
  (fenceEqOrNotEq : ∀f₁ f₂ : Fence, f₁ = f₂ ∨ f₁ ≠ f₂)
  (readDef : ∀ r ∈ Read, r.effect.op = Op.read)
  (writeDef : ∀ w ∈ Write, w.effect.op = Op.write)
  (mDef : ∀ m ∈ M, m.effect.op = Op.read ∨ m.effect.op = Op.write)
  (mFence : ∀ f ∈ Fence, f.effect.op = Op.fence)
  (mBranch : ∀ b ∈ Branch, b.effect.op = Op.branch)
  (allIn : Acquire ∪ Release ∪ IW ∪ Read ∪ Write ∪ Branch ∪ Fence ∪ RMW ∪ M ⊆ all)

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

-- By default it's Event, every time we use it, we should use (Tag Event) to know it's an event tag.
class Tag (t : Type) where

end Data
