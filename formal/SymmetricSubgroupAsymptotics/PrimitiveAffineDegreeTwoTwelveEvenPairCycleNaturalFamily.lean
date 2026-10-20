import SymmetricSubgroupAsymptotics.BinaryPairEvenCycleGenerators
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Six original capacity-one fields from the even-pair kernel theorem.
Rows145,196,235 use actual adjacent double flips, not independent single
flips. The other three form a double flip from one single flip and its
cycle conjugate. All group and offset certificates are literal point data. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def pointChart : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := if p.2 = 0 then ![0, 1, 3, 5, 7, 9] p.1 else ![11, 2, 4, 6, 8, 10] p.1
  invFun x := (![0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 0] x,
    ![0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def topPermutation (j : Fin 9) : Equiv.Perm (Fin 6) where
  toFun x := ((#[
    #[0, 1, 2, 3, 4, 5], #[1, 2, 3, 4, 5, 0], #[5, 4, 3, 2, 1, 0],
    #[2, 1, 4, 3, 0, 5], #[0, 1, 4, 5, 2, 3], #[0, 3, 2, 5, 4, 1],
    #[0, 3, 4, 1, 2, 5], #[0, 1, 2, 5, 4, 3], #[1, 0, 2, 3, 4, 5]
    ] : Array (Array (Fin 6)))[j.val]!)[x.val]!
  invFun x := ((#[
    #[0, 1, 2, 3, 4, 5], #[5, 0, 1, 2, 3, 4], #[5, 4, 3, 2, 1, 0],
    #[4, 1, 0, 3, 2, 5], #[0, 1, 4, 5, 2, 3], #[0, 5, 2, 1, 4, 3],
    #[0, 3, 4, 1, 2, 5], #[0, 1, 2, 5, 4, 3], #[1, 0, 2, 3, 4, 5]
    ] : Array (Array (Fin 6)))[j.val]!)[x.val]!
  left_inv := by revert j; decide +kernel
  right_inv := by revert j; decide +kernel

theorem uniform_of_generators {m : ℕ}
    (gs : Fin m → Equiv.Perm (Fin 12)) (tops : Fin m → Equiv.Perm (Fin 6))
    (ci ki oi : Fin m) (single : Bool)
    (hp : ∀ j, BinaryPairFrame.Preserves pointChart (gs j) (tops j))
    (hc : tops ci = BinaryPairEvenCycleGenerators.pairCycle)
    (hk : tops ki = 1)
    (hb : (fun j : Fin 6 ↦ (pointChart.symm
      ((if single then gs ki * (gs ci * gs ki * (gs ci)⁻¹) else gs ki)
        (pointChart (j, 0)))).2) =
          Pi.single 0 (1 : ZMod 2) + Pi.single 1 (1 : ZMod 2))
    (ho : ∑ j : Fin 6, (pointChart.symm (gs oi (pointChart (j, 0)))).2 = 1) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2)
        (Subgroup.closure (Set.range gs)) (Fin 12)) 1 := by
  let F := BinaryPairFrame.ofGenerators pointChart gs tops hp
  let c : Subgroup.closure (Set.range gs) := closureGenerators gs ci
  let k : F.top.ker := ⟨closureGenerators gs ki, by
    change F.top (closureGenerators gs ki) = 1
    exact (BinaryPairFrame.ofGenerators_top_generator pointChart gs tops hp ki).trans hk⟩
  let a : F.top.ker := if single then k * MulAut.conjNormal c k else k
  have hca : F.top c = BinaryPairEvenCycleGenerators.pairCycle :=
    (BinaryPairFrame.ofGenerators_top_generator pointChart gs tops hp ci).trans hc
  have ha : F.bits a = Pi.single 0 (1 : ZMod 2) + Pi.single 1 (1 : ZMod 2) := by
    cases single <;> exact hb
  apply BinaryPairEvenCycleGenerators.uniform F c a hca ha
  exact ⟨closureGenerators gs oi, ho⟩

theorem row134Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row134Interface.top (Fin 12)) 1 := by
  apply uniform_of_generators row134Generators
    ![topPermutation 0, topPermutation 1] 1 0 0 true
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row145Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row145Interface.top (Fin 12)) 1 := by
  apply uniform_of_generators row145Generators
    ![topPermutation 0, topPermutation 1, topPermutation 2] 1 0 2 false
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row193Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row193Interface.top (Fin 12)) 1 := by
  apply uniform_of_generators row193Generators
    ![topPermutation 0, topPermutation 1, topPermutation 2] 1 0 0 true
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row196Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row196Interface.top (Fin 12)) 1 := by
  apply uniform_of_generators row196Generators
    ![topPermutation 0, topPermutation 3, topPermutation 1, topPermutation 4] 2 0 3 false
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row235Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row235Interface.top (Fin 12)) 1 := by
  apply uniform_of_generators row235Generators
    ![topPermutation 0, topPermutation 5, topPermutation 1, topPermutation 6,
      topPermutation 7] 2 0 4 false
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row293Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row293Interface.top (Fin 12)) 1 := by
  apply uniform_of_generators row293Generators
    ![topPermutation 0, topPermutation 8, topPermutation 1] 2 0 0 true
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

end PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily
end SymmetricSubgroupAsymptotics

end
