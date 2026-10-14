import QuasiNewtonConvergence.AxiomAudit
import Lean.Elab.GuardMsgs

/-! Regression checks for the audit command. Deliberately untrusted declarations
live only in this test file, which is never imported by the library. -/

namespace ProofAuditTests

theorem constructive : True := True.intro
assert_standard_axioms constructive

theorem standard (p : Prop) : p ∨ ¬p := Classical.em p
assert_standard_axioms standard

axiom unexpected : False
theorem indirect : True := unexpected.elim

/-- error: indirect depends on forbidden axioms: [ProofAuditTests.unexpected] -/
#guard_msgs in
assert_standard_axioms indirect

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem unfinished : True := sorryAx True false

/-- error: unfinished depends on forbidden axioms: [sorryAx] -/
#guard_msgs in
assert_standard_axioms unfinished

end ProofAuditTests
