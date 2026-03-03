import LeanCats.Data
import Mathlib.Data.Rel

namespace CatRel
open Data

variable {tagType : Type} [DecidableEq tagType] [Inhabited tagType]

-- Not sure if this is the correct definition of cartesian product.
def prod (s₁ s₂ : Set <| Event tagType) : SetRel (Event tagType) (Event tagType) := s₁.prod s₂

#check SetRel.inv

@[simp] def R : Set (Event tagType) :=
  λ e ↦ e.effect.op = Op.read

@[simp] def W : Set (Event tagType) :=
  λ e ↦ e.effect.op = Op.write

@[simp] def M : Set (Event tagType) :=
  R ∪ W

@[simp] def Rel.prod (lhs rhs : Event tagType -> Prop) : Rel (Event tagType) (Event tagType) :=
  λ e₁ e₂ ↦ lhs e₁ ∧ rhs e₂

omit [DecidableEq tagType] [Inhabited tagType] in
theorem RelProdIsSetProd (s₁ s₂ : Event tagType -> Prop) (e₁ e₂ : Event tagType) :
  Rel.prod s₁ s₂ e₁ e₂ = ((e₁, e₂) ∈ Set.prod s₁ s₂) :=
  by
    simp
    apply Iff.intro
    {
      intro hrel
      unfold Set.prod
      aesop
    }
    {
      intro hset
      aesop
    }

abbrev Acyclic (r : Rel (Event tagType) (Event tagType)) := ∀a : Event tagType, ¬ Relation.TransGen r a a

@[simp] def Rel.internal (e₁ e₂ : Event tagType) : Prop :=
  e₁.t_id = e₂.t_id

@[simp] def Rel.external (e₁ e₂ : Event tagType) : Prop :=
  ¬ (Rel.internal e₁ e₂)

@[simp] def Rel.empty (_ _ : Event tagType) : Prop :=
  False

@[simp] def Rel.loc (e₁ e₂ : Event tagType) : Prop :=
  e₁.effect.location = e₂.effect.location

@[simp] def Rel.ext (e₁ e₂ : Event tagType) : Prop :=
  e₁.t_id ≠ e₂.t_id

@[simp] def isWrite (e : Event tagType) : Prop :=
  e.effect.op = Op.write

structure rf (evts : Events tagType) (e₁ e₂ : Event tagType) : Prop where
  -- left one in the evts.
  lIn : e₁ ∈ evts
  rIn : e₂ ∈ evts
  lWrite : e₁.effect.op = Op.write
  rRead : e₂.effect.op = Op.read
  sameTarget : e₁.effect.location = e₂.effect.location

@[simp] def internal (evts : Events tagType) : Rel (Event tagType) (Event tagType) :=
  λ e₁ e₂ ↦ e₁ ∈ evts ∧ e₂ ∈ evts ∧ e₁.t_id = e₂.t_id

@[simp] def external (evts : Events tagType) : Rel (Event tagType) (Event tagType) :=
  λ e₁ e₂ ↦ ¬(internal evts e₁ e₂)

@[simp] def isWriteSameLoc (l : Location) (e : Event tagType) :=
  e.effect.op = Op.write ∧ e.effect.location = l

def po (evts : Events tagType) (e₁ e₂ : Event tagType) : Prop :=
  internal evts e₁ e₂ ∧ e₁.id < e₂.id

instance (evts : Events tagType) : IsStrictOrder (Event tagType) (rf evts) where
  irrefl :=
  by
    intro e hin
    have h₁ : e.effect.op = Op.write := by apply hin.lWrite
    have h₂ : e.effect.op = Op.read := by apply hin.rRead
    rw [h₁] at h₂
    contradiction
  trans :=
  by
    intro a b c hrfab hrfbc
    have lIn : a ∈ evts := by apply hrfab.lIn
    have rIn : c ∈ evts := by apply hrfbc.rIn
    have lWrite : a.effect.op = Op.write := by apply hrfab.lWrite
    have rRead : c.effect.op = Op.read := by apply hrfbc.rRead
    have sameTarget : a.effect.location = c.effect.location :=
    by
      have abSameTarget : a.effect.location = b.effect.location := by apply hrfab.sameTarget
      have bcSameTarget : b.effect.location = c.effect.location := by apply hrfbc.sameTarget
      rw [abSameTarget]
      rw [bcSameTarget]

    exact ⟨lIn, rIn, lWrite, rRead, sameTarget⟩

omit [DecidableEq tagType] [Inhabited tagType] in
theorem rfIsTransitive {evts : Events tagType} : Transitive (rf evts) :=
  by
    intro a b c rab rbc
    obtain ⟨lInab, rInab, lWriteab, rReadab, sameTargetab⟩ := rab
    obtain ⟨lInbc, rInbc, lWritebc, rReadbc, sameTargetbc⟩ := rbc
    rw [<-sameTargetab] at sameTargetbc
    exact ⟨lInab, rInbc, lWriteab, rReadbc, sameTargetbc⟩

-- This defines:
-- Write event must exists
-- Write equlity (If the two write events write to the same read event, then these two writes are the same)
structure rf.wellformed (evts : Events tagType) (e₁ e₂ : Event tagType) extends rf evts e₁ e₂ where
  wExtAndUnique {r} : r.effect.op = Op.read ->
    (∃w, isWrite w ∧ rf evts w r)
    ∧ (∀ w₁ w₂, rf evts w₁ r -> rf evts w₂ r -> w₁ = w₂)

structure preCo (evts : Events tagType) (e₁ e₂ : Event tagType) : Prop where
  lIn : e₁ ∈ evts
  rIn : e₂ ∈ evts
  lWrite : isWrite e₁
  rWrite : isWrite e₂

-- TODO: Check if this definition follows the Coq definition in diy7.
structure co.wellformed
  (evts : Events tagType)
  [IsStrictTotalOrder (Event tagType) (preCo evts)]
  (e₁ e₂ : Event tagType)
  extends preCo evts e₁ e₂

@[simp] def fr
  (evts : Events tagType)
  [IsStrictTotalOrder (Event tagType) (preCo evts)]
  (e1 e2 : Event tagType)
  : Prop :=
  ∃w, isWrite w ∧ rf evts w e1 ∧ co.wellformed evts w e2


def com
  (evts : Events tagType)
  [IsStrictTotalOrder (Event tagType) (preCo evts)]
  (e₁ e₂ : Event tagType) :=
  rf.wellformed evts e₁ e₂ ∨ co.wellformed evts e₁ e₂ ∨ fr evts e₁ e₂

#check Rel.prod

end CatRel
