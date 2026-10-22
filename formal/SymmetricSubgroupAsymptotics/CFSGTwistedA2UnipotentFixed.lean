import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentNatural
import SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestFixedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnitRootTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedAPairedFixedRoots

/-! Norm-constrained adjacent A2 unipotent words are elements of the SAME
original fixed Serre subgroup. Only explicit natural units and the checked
converse fixed-image theorem are used; full SU equality is not assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGTwistedA2HighestRootUnits
open CFSGTwistedA2OriginalRelations
variable (K : Type) [Field K] (σ : K ≃+* K)

theorem upperNatural_fixed (hσ : Function.Involutive σ) (a b : K)
    (hab : NormCondition σ a b) :
    diagramFieldUnitHom K 2 σ.toRingHom (upperNatural K σ a b).val =
      (upperNatural K σ a b).val := by
  have hc : -(σ (b - a * σ a)) = b := by
    change b + σ b = a * σ a at hab
    rw [map_sub, map_mul, hσ]
    linear_combination -hab
  change diagramFieldUnitHom K 2 σ.toRingHom
    (naturalRootUnit K 2 false 0 a * naturalRootUnit K 2 false 1 (σ a) *
      (highest K (b - a * σ a)).val) = _
  simp only [map_mul]
  rw [CFSGTwistedA2UnitRootTwist.simpleUnit_twist,
    CFSGTwistedA2UnitRootTwist.simpleUnit_twist]
  change naturalRootUnit K 2 false 1 (σ a) * naturalRootUnit K 2 false 0 (σ (σ a)) *
    diagramFieldUnitHom K 2 σ.toRingHom (highest K (b - a * σ a)).val = _
  rw [hσ, highest_val, diagramField_highest_entry, hc]
  apply Units.ext
  change ((naturalRootUnit K 2 false 1 (σ a) : Mat K 2) *
      (naturalRootUnit K 2 false 0 a : Mat K 2)) *
    (entryUnit K (show (0 : Fin 3) ≠ 2 by decide) b : Mat K 2) = _
  rw [upperNatural_val, naturalRootUnit_positive_one, naturalRootUnit_positive_zero]
  simp only [entryUnit_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperArray, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single,
      Matrix.one_apply] <;> (try simp only [Fin.ext_iff]) <;> (try norm_num) <;> ring

def originalUpper (q : CFSG.PrimePower) (a b : q.Extension 2)
    (hab : NormCondition (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) a b) :
    CFSG.Models.Chevalley.fixedSubgroup A (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order) :=
  fixedElementOfNaturalUnit q
    (upperNatural (q.Extension 2) (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) a b)
    (upperNatural_fixed (q.Extension 2) (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2)
      (fun x => extension_two_pow_twice q x) a b hab)

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
