import SymmetricSubgroupAsymptotics.CFSGGeckIntegralMatrices
import SymmetricSubgroupAsymptotics.CFSGGeckOppositionAlgEquiv

/-! The actual Geck opposition has an integral permutation matrix.
Consequently conjugating an integral second coefficient stays integral. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGeckIntegralMatrices
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsCrystallographic] (b : P.Base)

def Omega : IntegralTarget b :=
  .fromBlocks 1 0 0 (.of fun i j=>if i=P.reflectionPerm j j then 1 else 0)

theorem map_Omega : (Int.castRingHom ℚ).mapMatrix (Omega b)=RootPairing.GeckConstruction.ω b := by
  classical
  ext (j|j) (k|k) <;>
    simp [Omega,RootPairing.GeckConstruction.ω,RootPairing.indexNeg_neg,Matrix.one_apply]

theorem map_opposition (x : IntegralTarget b) :
    (Int.castRingHom ℚ).mapMatrix (Omega b*x*Omega b)=
      CFSGGeckOppositionAlgEquiv.opposition b ((Int.castRingHom ℚ).mapMatrix x) := by
  change (Int.castRingHom ℚ).mapMatrix (Omega b*x*Omega b)=
    RootPairing.GeckConstruction.ω b*((Int.castRingHom ℚ).mapMatrix x)*
      RootPairing.GeckConstruction.ω b
  rw [map_mul,map_mul,map_Omega]

end SymmetricSubgroupAsymptotics.CFSGGeckIntegralMatrices
