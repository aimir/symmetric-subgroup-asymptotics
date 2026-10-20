import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1086SchreierData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairBinding16T1086
local instance pilotSchreierCheck000Group : Group SourceTop := BinaryTopSource056.group

theorem nextTop_checked000 : ∀ q : SourceTop,
    0≤q.index.val → q.index.val<16 → ∀ j,
    q*images j=nextTop q j := by
  simp only [BinaryKernelAxes097.row_mul_eq_iff]
  decide +kernel
theorem schreier_mem000 : ∀ q : SourceTop,
    0≤q.index.val → q.index.val<16 → ∀ j,
    schreierBits q j∈BinaryKernelAxes097.kernelChart.space := by decide +kernel
theorem schreier_action000 : ∀ q : SourceTop,
    0≤q.index.val → q.index.val<16 → ∀ j (p : Fin 8 × ZMod 2),
    frame.symm ((schreierElement q j : Equiv.Perm (Fin 16)) (frame p))=
      (p.1,p.2+schreierBits q j p.1) := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryPairBinding16T1086
