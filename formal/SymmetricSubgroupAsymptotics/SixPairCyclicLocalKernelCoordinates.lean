import SymmetricSubgroupAsymptotics.CyclicExponentFourCoordinates
import SymmetricSubgroupAsymptotics.C4CoordinateHomCount
import SymmetricSubgroupAsymptotics.SixPairThreePairKernelExponent

/-! Actual cyclic local projections yield three full C4 coordinates on
the SAME original coarse kernel. Local cyclicity is a structural condition,
not metadata, normal-source coverage, or a count bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairCyclicLocalKernelCoordinates
variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

abbrev localRange (i : Fin 3) :=
  ((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate i).range

 theorem exists_coordinates (hcyc : ∀ i,IsCyclic (localRange F E i)) :
    ∃ j : (SixPairNestedTopFrames.nestedFrame F E).top.ker →*
      (Fin 3 → C4CoordinateHomCount.C4),Function.Injective j := by
  have hf (i : Fin 3) (g : localRange F E i) : g^4=1 := by
    obtain ⟨k,hk⟩ := g.property
    apply Subtype.ext
    change g.val^4=1
    rw [←hk,←map_pow,SixPairThreePairKernelExponent.fourth_power F E,map_one]
  choose e he using fun i => CyclicExponentFourCoordinates.exists_embedding
    (localRange F E i) (hcyc i) (hf i)
  let j : (SixPairNestedTopFrames.nestedFrame F E).top.ker →*
      (Fin 3 → C4CoordinateHomCount.C4) :=
    Pi.monoidHom (fun i => (e i).comp
      ((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate i).rangeRestrict)
  refine ⟨j,?_⟩
  intro a b h
  apply (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinates_joint_injective
  funext i
  have hh : e i (((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate i).rangeRestrict a)=
      e i (((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate i).rangeRestrict b) := congrFun h i
  exact congrArg Subtype.val (he i hh)

end SymmetricSubgroupAsymptotics.SixPairCyclicLocalKernelCoordinates
