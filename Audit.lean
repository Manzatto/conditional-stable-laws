import ConditionedStableLaws
import Lean.Util.CollectAxioms

open Lean Elab Command

def citedAxioms : Array Name := #[
  ``ConditionedStableLaws.Cited.castro_qProcess_stationary_ergodic]

def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  let mut axiomFree : Nat := 0
  let mut dependents : Std.HashMap Name Nat := {}
  for (name, info) in env.constants.toList do
    if (`ConditionedStableLaws).isPrefixOf name ||
        name.toString.startsWith "_private.ConditionedStableLaws." then
      match info with
      | .axiomInfo _ =>
          unless citedAxioms.contains name do
            throwError "Unregistered project axiom is forbidden: {name}"
      | .thmInfo _ => theorems := theorems + 1
      | _ => pure ()
      let axioms ← collectAxioms name
      let mut usesCited := false
      for ax in axioms do
        if citedAxioms.contains ax then
          usesCited := true
          unless ax == name do
            dependents := dependents.insert ax (dependents.getD ax 0 + 1)
        else unless standardAxioms.contains ax do
          throwError "{name} depends on forbidden axiom {ax}"
      unless usesCited do axiomFree := axiomFree + 1
      checked := checked + 1
  if theorems == 0 then
    throwError "No project theorems found; an empty build is not a verification."
  for ax in citedAxioms do
    unless env.contains ax do
      throwError "Registered cited axiom is missing: {ax}"
  let report := citedAxioms.toList.map fun ax =>
    m!"\n  {ax}: {dependents.getD ax 0} dependent declarations"
  logInfo m!"Axiom audit passed: {checked} declarations, including {theorems} theorems; \
    {axiomFree} use no cited axiom.{MessageData.joinSep report ""}"
