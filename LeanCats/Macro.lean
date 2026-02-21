import LeanCats.Syntax
import Lean
import LeanCats.Relations
import LeanCats.Data
import LeanCats.Basic

open Lean Elab Command Term Meta
open Data

syntax "[model|" ident inst* "]" : command
syntax "[expr|" expr "," cat_ident "," cat_ident "]" : term
syntax "[keyword|" keyword "]" : term
syntax "[assertion|" assertion "]" : term
syntax "[inst|" inst "," cat_ident "," cat_ident "]" : command
syntax "[annotable-events|" annotable_events "," cat_ident "," cat_ident "]" : term -- Set
syntax "[predefined-events|" predefined_events "," cat_ident "," cat_ident "]" : term
syntax "[reserved|" reserved "," cat_ident "," cat_ident "]" : term
syntax "[predefined-relations|" predefined_relations "]" : term
syntax "[dsl-term|" dsl_term "," cat_ident "," cat_ident "]" : term

-- Walk any cat_ident syntax tree, collect all ident leaves, and join with "_".
-- This handles plain idents, tick-prefixed ('ONCE), and multi-hyphen (rcu-lock, after-unlock-lock).
partial def catIdentToName (stx : Syntax) : Name :=
  let rec go (s : Syntax) : Array String :=
    if s.isIdent then #[s.getId.toString]
    else if s.isAtom then #[]  -- skip punctuation atoms like "'" and "-"
    else s.getArgs.foldl (fun acc a => acc ++ go a) #[]
  let parts := go stx
  match parts with
  | #[] => `_unknown
  | _   =>
    let joined := parts[1:].foldl (fun acc s => acc ++ "_" ++ s) parts[0]!
    joined.toName

instance : Coe (TSyntax `cat_ident) (TSyntax `ident) where
  coe s := mkIdent (catIdentToName s.raw)

instance : Coe (TSyntax `ident) (TSyntax `cat_ident) where
  coe s := mkNode `cat_ident #[s]

macro_rules
  | `([expr| $e₁:expr | $e₂:expr, $evts, $X]) =>
    `(CatRel.union ([expr| $e₁, $evts, $X]) ([expr| $e₂, $evts, $X]))

  | `([expr| $e₁:expr & $e₂:expr, $evts, $X]) =>
    `(CatRel.inter ([expr| $e₁, $evts, $X]) ([expr| $e₂, $evts, $X]))

  | `([expr| $e₁:expr ; $e₂:expr, $evts, $X]) =>
    `(Rel.comp ([expr| $e₁, $evts, $X]) ([expr| $e₂, $evts, $X]))

  | `([expr| $e₁:expr * $e₂:expr, $evts, $X]) =>
    `(CatRel.prod ([expr| $e₁, $evts, $X]) ([expr| $e₂, $evts, $X]))

  | `([expr| $e^-1, $evts, $X]) =>
    `(Rel.inv ([expr| $e, $evts, $X]))

  | `([expr| $r:reserved, $evts, $X]) =>
    `([reserved| $r, $evts, $X])

  | `([expr| ($e:expr), $evts, $X]) =>
    `([expr| $e, $evts, $X])

  | `([expr| $t:dsl_term, $evts, $X]) =>
    `(([dsl-term| $t, $evts, $X]))

  | `([expr| $i:cat_ident ($e:expr), $evts, $X]) => do
    `(($i $evts $X) ([expr| $e, $evts, $X]))

macro_rules
  | `([dsl-term| $i:cat_ident, $evts, $X]) =>
      `($i $evts $X)

macro_rules
  | `([reserved| $r:predefined_relations, $evts, $X]) =>
    `([predefined-relations| $r])
  | `([reserved| $e:predefined_events, $evts, $X]) => `([predefined-events| $e, $evts, $X])

macro_rules
  | `([predefined-relations| fr]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      X._fr)

  | `([predefined-relations| po]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      X._po)

  | `([predefined-relations| rf]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      X._rf)

  | `([predefined-relations| rfe]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.external X.evts X._rf)

  | `([predefined-relations| co]) =>
    `(fun (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo (evts))] (X : CandidateExecution evts) =>
      CatRel.co.wellformed evts)

macro_rules
  | `([keyword| and]) => Lean.Macro.throwUnsupported
  | `([keyword| as]) => Lean.Macro.throwUnsupported
  | `([keyword| begin]) => Lean.Macro.throwUnsupported
  | `([keyword| call]) => Lean.Macro.throwUnsupported
  | `([keyword| do]) => Lean.Macro.throwUnsupported
  | `([keyword| end]) => Lean.Macro.throwUnsupported
  | `([keyword| enum]) => Lean.Macro.throwUnsupported
  | `([keyword| flag]) => Lean.Macro.throwUnsupported
  | `([keyword| forall]) => Lean.Macro.throwUnsupported
  | `([keyword| from]) => Lean.Macro.throwUnsupported
  | `([keyword| fun]) => Lean.Macro.throwUnsupported
  | `([keyword| in]) => Lean.Macro.throwUnsupported
  | `([keyword| let]) => Lean.Macro.throwUnsupported
  | `([keyword| match]) => Lean.Macro.throwUnsupported
  | `([keyword| procedure]) => Lean.Macro.throwUnsupported
  | `([keyword| rec]) => Lean.Macro.throwUnsupported
  | `([keyword| scopes]) => Lean.Macro.throwUnsupported
  | `([keyword| with]) => Lean.Macro.throwUnsupported
  | `([keyword| $a:assertion]) => `([assertion| $a])

macro_rules
  | `([assertion| irreflexive]) => `(CatRel.Irreflexive)
  | `([assertion| acyclic]) => `(CatRel.Acyclic)
  | `([assertion| empty]) => `(CatRel.IsEmpty)

macro_rules
  | `([annotable-events| W, $evts, $X]) =>
    let nm := mkIdent "W".toName
    `(($X.$evts.$nm : Set Event))
  | `([annotable-events| R, $evts, $X]) =>
    let nm := mkIdent "R".toName
    `(($X.$evts.$nm : Set Event))
  | `([annotable-events| B, $evts, $X]) =>
    let nm := mkIdent "B".toName
    `(($X.$evts.$nm : Set Event))
  | `([annotable-events| F, $evts, $X]) =>
    let nm := mkIdent "F".toName
    `(($X.$evts.$nm : Set Event))
  | `([annotable-events| RMW, $evts, $X]) =>
    let nm := mkIdent "RMW".toName
    `(($X.$evts.$nm : Set Event))

namespace TestAnnotableEvents
variable (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts)
def a := [annotable-events| R, evts, X]
#reduce a
end TestAnnotableEvents

macro_rules
  -- | `([predefined-events| ___]) => __ TODO!(figure all the definiations of all the events. (⋃?))
  | `([predefined-events| IW, $evts, $X]) =>
    let nm := mkIdent "IW".toName
    `($X.$evts.$nm)

  | `([predefined-events| M, $evts, $X]) =>
    let nm := mkIdent "M".toName
    `($X.$evts.$nm)

  | `([predefined-events| $a:annotable_events, $evts, $X]) =>
    `([annotable-events| $a, $evts, $X])

namespace TestPredefinedEvents
variable (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts)
def a := [predefined-events| R, evts, X]
#reduce a
end TestPredefinedEvents

macro_rules
  -- We just ignore the include inst.
  | `([inst| include $_filename:str , $_ , $_]) => return mkNullNode

  -- TODO(Don't know how the coe works here, maybe ask others? Like the coe works, okay, but how do I know it's value?)
  | `([inst| let $nm:cat_ident = $e, $evts, $X]) =>
    `(@[simp] def $nm := [expr|$e, $evts, $X])

  | `([inst| $a:assertion $e as $nm:cat_ident, $evts, $X]) => do
    `([assertion| $a] ([expr| $e, $evts, $X]))

  | `([inst| ~$a:assertion $e as $nm:cat_ident, $evts, $X]) => do
    `([assertion| $a] (¬[expr| $e, $evts, $X]))

  | `([inst| enum $nm:cat_ident = $[ $tags:cat_ident ]||*, $_, $_]) => do
    let nmIdent : TSyntax `ident := nm
    -- Convert each cat_ident tag to a plain Lean ident (handles multi-hyphen names like rcu-lock → rcu_lock, and adds trailing ').
    let tagIdents : Array (TSyntax `ident) := tags.map (fun t =>
      mkIdent (Name.mkSimple ((catIdentToName t.raw).toString ++ "'")))
    let indef <- `(
      inductive $nmIdent where $[| $tagIdents:ident ]*
    )
    -- Derive DecidableEq so we can state and decide `e.tag = Accesses.ONCE` in proofs.
    let decEq <- `(deriving instance DecidableEq for $nmIdent)
    -- Register as a Tag type so the vm knows this is used for event tagging.
    let tagName := mkIdent `Data.Tag
    let tagInst <- `(instance : $tagName $nmIdent where)
    -- Create unqualified aliases, e.g. `ONCE` → `Accesses.ONCE`.
    let aliases <- tagIdents.mapM fun (tagId : TSyntax `ident) => do
      let qualName := mkIdent (nmIdent.getId ++ tagId.getId)
      `(def $tagId := $qualName)
    let ret := #[indef, decEq, tagInst] ++ aliases
    return mkNullNode ret

  | `([inst| flag $_:assertion $_:expr as $_:expr, $_, $_]) => do
    -- We ignore the flag for now, since it doesn't change the states of the execution, it's just used to witness the assertion.
    return mkNullNode #[]

/--
Processes `instructions A[EnumType]` by generating a definition for each constructor of `EnumType`.
Specifically, for each constructor `C` of `EnumType`, we generate:
  `def C : Set Event := { e | e.tag = EnumType.C } ∩ A`

For example, given `enum Accesses = ONCE || RELEASE || ...` and `instructions R[Accesses]`,
we generate:
  `def ONCE : Set Event := { e | e.tag = Accesses.ONCE } ∩ R`
  `def RELEASE : Set Event := { e | e.tag = Accesses.RELEASE } ∩ R`
  ...
-/
elab "instructions" a:annotable_events "[" c:cat_ident "]" "," evts:cat_ident "," X:cat_ident : command => do
  let currNamespace <- getCurrNamespace
  -- This is used to get the full name with namespace.
  let typeName := Name.updatePrefix c.getId currNamespace

  let info <- getConstInfoInduct typeName
  dbg_trace typeName

  let commands <- info.ctors.mapM (
    fun ctor => do
      -- Make the constructors name correct by removing the end tick.
      let ctorName : Name := ctor.lastComponentAsString.dropEnd 1 |>.toName
      -- TODO(Nekolas): Make this part `∩ [annotable-events| $a]` work.
      let ctorDef <-
      `(
        abbrev $(mkIdent ctorName) :
          Set Event := {e | e.tag = $(mkIdent ctor) } ∩ ([annotable-events| $a, $evts, $X])
      )
      return ctorDef
  )
  -- A hack to return the commands, the mkNullNode create a SyntaxTree and we use the elabCommand to execute it.
  elabCommand $ mkNullNode commands.toArray

macro_rules
  -- Create the model.
  | `([model| $n:ident $x:inst*]) => do
    let nstart <- `(namespace $n)
    let evts := mkIdent `evts
    let X := mkIdent `X
    let vars <- `(variable ($evts : Events) [IsStrictTotalOrder Event (CatRel.preCo $evts)] ($X : CandidateExecution $evts))
    let nend <- `(end $n)
    let insts <- x.mapM (fun ins => `([inst| $ins, $evts, $X]))

    -- let insts : Array (TSyntax `command) := #[]
    let ret := #[nstart] ++ #[vars] ++ insts ++ #[nend]
    return mkNullNode ret

-- Linux-kernel memory consistency model  ("linux.bell" excerpt)
-- Comments (*...*) and tick-prefixes (') are stripped by the preprocessor
-- before these lines reach the Lean syntax; we write the cleaned form here.

namespace TestInstructions
variable (evts : Events) [IsStrictTotalOrder Event (CatRel.preCo evts)] (X : CandidateExecution evts)
[inst| enum Accesses = ONCE || RELEASE || ACQUIRE || NORETURN || MB, evts, X]
#check Accesses
instructions R[Accesses] , evts, X

#reduce ONCE
end TestInstructions

#check TestInstructions.ONCE

[model| t
  enum Barriers =
    wmb || rmb || barrier || rcu_read_lock || rcu_read_unlock ||
    rcu_lock || rcu_unlock || sync_rcu ||
    before_atomic || after_atomic ||
    after_spinlock || after_unlock_lock ||
    after_srcu_read_unlock
]

-- Spot-check generated names
-- This tags used as the event tags, we don't refer them directly.
#check t.Barriers.wmb'

-- [model| linux
--
-- enum Accesses = ONCE  ||
--   RELEASE  ||
--   ACQUIRE  ||
--   NORETURN  ||
--   MB
-- instructions R[Accesses]
-- instructions W[Accesses]
-- instructions RMW[Accesses]
--
-- enum Barriers = wmb  ||
--   rmb  ||
--   barrier  ||
--   rcu-lock   ||
--   rcu-unlock  ||
--   sync-rcu  ||
--   before-atomic  ||
--   after-atomic  ||
--   after-spinlock  ||
--   after-unlock-lock  ||
--   after-srcu-read-unlock
-- instructions F[Barriers]
--
-- let FailedRMW = RMW \ (domain(rmw) | range(rmw))
--
-- let Acquire = ACQUIRE \ W \ FailedRMW
-- let Release = RELEASE \ R \ FailedRMW
-- let Mb = MB \ FailedRMW
-- let Noreturn = NORETURN \ W]
-- -- Check the instruction sets
