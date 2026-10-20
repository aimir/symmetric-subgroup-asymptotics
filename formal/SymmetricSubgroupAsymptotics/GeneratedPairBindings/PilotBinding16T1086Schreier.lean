import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1086SchreierCheck000

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairBinding16T1086
local instance pilotSchreierGroup : Group SourceTop := BinaryTopSource056.group

theorem nextTop_checked : ∀ q j,q*images j=nextTop q j := by
  intro q
  exact nextTop_checked000 q (Nat.zero_le _) q.index.isLt

theorem schreier_mem : ∀ q j,schreierBits q j∈BinaryKernelAxes097.kernelChart.space := by
  intro q
  exact schreier_mem000 q (Nat.zero_le _) q.index.isLt

theorem schreier_action : ∀ q j (p : Fin 8 × ZMod 2),
    frame.symm ((schreierElement q j : Equiv.Perm (Fin 16)) (frame p))=
      (p.1,p.2+schreierBits q j p.1) := by
  intro q
  exact schreier_action000 q (Nat.zero_le _) q.index.isLt

end SymmetricSubgroupAsymptotics.BinaryPairBinding16T1086
