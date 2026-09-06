/- Test-only module, compiled under a temporary package root by check_axioms.py.
   Origin-module selection must include names outside the RequestProject namespace. -/
import AuditForeign

namespace OutsideProjectNamespace

axiom directUnexpected : True

private theorem hiddenViolation : False := auditUnexpected

theorem publicViolation : False := hiddenViolation

end OutsideProjectNamespace
