import IsingModel.ComplexAnalyticity.VitaliPorter.Theorem

/-!
# Function-theory results formerly axiomatized (now proved)

This module historically isolated the **Vitali–Porter convergence theorem** as a deliberately
unproven scope-excluded `axiom`. That axiom has since been **discharged**: the theorem is now
**proved** from Mathlib in `ComplexAnalyticity/VitaliPorter/Theorem.lean`
(`vitaliPorter_tendstoLocallyUniformlyOn`), via the complex Montel theorem
(`VitaliPorter/MontelExtraction.lean`) and the identity-theorem uniqueness core
(`VitaliPorter/Uniqueness.lean`). This file now merely re-exports the proved theorem so existing
consumers (`IsingModel.FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn`) keep resolving.

The project no longer carries the Vitali–Porter axiom. (Issue #4280.)

References: e.g. Conway, *Functions of One Complex Variable I*, VII.§2–3 (Montel's theorem and
Vitali's theorem); the Vitali–Porter theorem.
-/

namespace IsingModel

namespace FunctionTheory

-- The Vitali–Porter convergence theorem is proved in `VitaliPorter/Theorem.lean`
-- (`IsingModel.FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn`), imported above.

end FunctionTheory

end IsingModel
