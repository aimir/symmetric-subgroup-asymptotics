import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic

/-! Literal integer coefficient lifts of Geck's rational matrices. This is
only coefficient compatibility, not divided-power integrality or a group
recognition assertion. Root strings and their coefficients remain those of
the same actual rational root pairing. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGeckIntegralMatrices
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsCrystallographic] (b : P.Base)

abbrev IntegralTarget := Matrix (b.support⊕ι) (b.support⊕ι) ℤ

def H (i : b.support) : IntegralTarget b :=
  open scoped Classical in
  .fromBlocks 0 0 0 (.diagonal (P.pairingIn ℤ · i))

def E (i : b.support) : IntegralTarget b :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j=>if i'=i ∧ j= -i then 1 else 0)
    (.of fun i' j=>if i'=i then |b.cartanMatrix i j| else 0)
    (.of fun i' j=>if P.root i'=P.root i+P.root j then (P.chainBotCoeff i j+1:ℕ) else 0)

def F (i : b.support) : IntegralTarget b :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j=>if i'=i ∧ j=i then 1 else 0)
    (.of fun i' j=>if i'= -i then |b.cartanMatrix i j| else 0)
    (.of fun i' j=>if P.root i'=P.root j-P.root i then (P.chainTopCoeff i j+1:ℕ) else 0)

theorem map_H (i : b.support) :
    (Int.castRingHom ℚ).mapMatrix (H b i)=RootPairing.GeckConstruction.h i := by
  classical
  ext (j|j) (k|k) <;>
    simp [H,RootPairing.GeckConstruction.h,Matrix.diagonal_apply]

theorem map_E (i : b.support) :
    (Int.castRingHom ℚ).mapMatrix (E b i)=RootPairing.GeckConstruction.e i := by
  classical
  letI := P.indexNeg
  ext (j|j) (k|k) <;>
    simp [E,RootPairing.GeckConstruction.e]

theorem map_F (i : b.support) :
    (Int.castRingHom ℚ).mapMatrix (F b i)=RootPairing.GeckConstruction.f i := by
  classical
  letI := P.indexNeg
  ext (j|j) (k|k) <;>
    simp [F,RootPairing.GeckConstruction.f]

end SymmetricSubgroupAsymptotics.CFSGGeckIntegralMatrices
