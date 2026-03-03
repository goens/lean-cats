import LeanCats.Data
import LeanCats.Relations

open Data
open CatRel

/-- Each execution is abstracted to a candidate execution 〈evts , po, rf, co, IW, sr〉 providing
This definination is different with the formal semantics, because the `co` is defined in [stdlib.cat](https://github.com/herd/herdtools7/blob/2a7599f8ecdbde0ed67925daf6534c1a0c26d535/herd-www/cat_includes/stdlib.cat) and
by computation, so should declare it as the base relation. -/
structure CandidateExecution
  (evts : Events tagType)
  [IsStrictTotalOrder (Event tagType) (preCo evts)]
  where
  (evts : Events tagType)
  (_po : SetRel (Event tagType) (Event tagType))
  (_rf : SetRel (Event tagType) (Event tagType))
  (_fr : SetRel (Event tagType) (Event tagType))
  (_rmw : SetRel (Event tagType) (Event tagType))
