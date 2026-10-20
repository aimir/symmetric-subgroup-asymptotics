import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicTwelveSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T57ClassPilotGroup

/-! Two literal point identities bind the unchanged T57 generators to an
actual affine subgroup with cyclic-twelve projection. The resulting bound
does not import the older native-decide normal or conjugacy census. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T57AffineSocles
open BinaryPlaneCyclicTwelveSocles
open PrimitiveAffineDegreeTwoNonbinary16T57ClassPilot (generators)

abbrev Original : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range generators)

def points : Fin 16 ≃ Fin 16 where
  toFun := ![0,10,1,11,15,12,14,13,4,7,5,6,3,9,2,8]
  invFun := ![0,2,14,12,8,10,11,9,15,13,1,3,5,7,6,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lifts : Fin 2 → Model :=
  ![⟨Multiplicative.ofAdd (0 : Vector),Multiplicative.ofAdd 1⟩,
    ⟨Multiplicative.ofAdd (fun _ => BinaryThreeQuartetLiteralSocles.planeLabel.symm 2),
      Multiplicative.ofAdd 11⟩]

theorem bindings (i : Fin 2) : literalAction points (lifts i) = generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem quotientSocle (N : Subgroup Original) [N.Normal] :
    SocleNormalGeneratorBound (Original ⧸ N) 2 :=
  BinaryPlaneCyclicTwelveSocles.quotientSocle points lifts generators bindings 0 rfl N

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T57AffineSocles
end
