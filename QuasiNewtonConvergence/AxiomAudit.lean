import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! An enforcing axiom audit for public convergence results. -/

open Lean Elab Command

/-- Reject every transitive axiom dependency except Lean's three standard
logical axioms. In particular, unfinished proofs using `sorryAx` fail the audit.
Unlike `#print axioms`, this command makes the Lean process fail on a violation. -/
elab "assert_standard_axioms " decl:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo decl
  let axioms ← Lean.collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := axioms.filter fun axiomName => !allowed.contains axiomName
  unless forbidden.isEmpty do
    throwError "{decl} depends on forbidden axioms: {forbidden.toList}"

