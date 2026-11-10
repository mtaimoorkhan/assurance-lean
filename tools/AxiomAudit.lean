/-
  Axiom-footprint gate.

  Every declaration the project defines is audited for its transitive axiom
  dependencies. The build fails if any axiom outside `allowed` appears, which
  catches `sorry` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`), and any
  home-rolled axiom -- including one reaching in through an import.

  Run:  lake env lean tools/AxiomAudit.lean
-/
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import CalibrePilot

open Lean Elab Command

/-- The only axioms this project is permitted to depend on. Note the absence of
    `Classical.choice`: nothing here needs it. -/
def allowed : List Name := [`propext, `Quot.sound]

/-- Declarations are audited when their name begins with this component. -/
def auditedRoots : List String := ["Calibre"]

run_cmd do
  let env ← getEnv
  let mut audited := 0
  let mut offences : List (Name × Name) := []
  let mut seen : List Name := []
  for (nm, _) in env.constants.toList do
    if !nm.isInternal && auditedRoots.any (fun r => nm.getRoot.toString.startsWith r) then
      audited := audited + 1
      for a in (← collectAxioms nm) do
        if !seen.contains a then seen := a :: seen
        if !allowed.contains a then offences := (nm, a) :: offences
  logInfo s!"declarations audited : {audited}"
  logInfo s!"axioms observed      : {seen}"
  logInfo s!"axioms permitted     : {allowed}"
  if audited == 0 then
    throwError "axiom audit matched no declarations -- the audit itself is vacuous, \
      which is precisely the failure mode this project is about. Check `auditedRoots`."
  unless offences.isEmpty do
    throwError "axiom audit FAILED. Disallowed dependencies:\n{offences}"
  logInfo "axiom audit passed"
