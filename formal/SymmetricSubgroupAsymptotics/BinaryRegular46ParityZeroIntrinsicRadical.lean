import SymmetricSubgroupAsymptotics.BinaryRegularSixCanonicalGenerators
import SymmetricSubgroupAsymptotics.BinaryPairOriginalGraphRigidity
import SymmetricSubgroupAsymptotics.BinaryPairRadicalFromCanonicalGenerators

/-! Six actual original generators identify the entire regular K46
parity-zero intrinsic radical. Only48 state-basis displacement columns
are checked, rather than128 source elements. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroIntrinsicRadical
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open BinaryRegularSixCanonicalGenerators
private def inclusion : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
  (binaryRectangularMatrixOfColumnMasks 16 4
    (![135,75,45,30] : Fin 4 → ℕ)).mulVecLin
private def dualMasks : Fin 4 → ℕ := ![128,64,32,16]
private def coordinates : (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  (binaryRectangularMatrixOfColumnMasks 4 16
    (fun i => binaryVectorMask (fun j => binaryVectorOfMask 16 (dualMasks j) i))).mulVecLin
private theorem basis_left : ∀ i : Fin 4, coordinates (inclusion (Pi.single i 1)) = Pi.single i 1 := by decide +kernel
private theorem left_inverse (v : Fin 4 → ZMod 2) : coordinates (inclusion v) = v := by
  have he : coordinates.comp inclusion = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : (Pi.single i c : Fin 4 → ZMod 2) = c • Pi.single i 1 := by
      funext j;simp [Pi.single_apply,mul_ite]
    simp only [LinearMap.comp_apply,hs,map_smul,basis_left,LinearMap.id_apply]
  exact DFunLike.congr_fun he v

def radical : BinaryCoordinateSpace 16 4 := ⟨inclusion,coordinates,left_inverse⟩
private def actionSix (i : Fin 6) : (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
  (BinaryPairFrame.pairLayerFlatten (w := 8)).toLinearMap.comp
    ((BinaryPairFrame.affinePairLayerMap (topRows i) (binaryVectorOfMask 8 (offsetMasks i))).comp
      (BinaryPairFrame.pairLayerFlatten (w := 8)).symm.toLinearMap)
private theorem kill_basis : ∀ i : Fin 6, ∀ j : Fin 8,
    actionSix i ((BinaryRegular46GraphHeadRigidity.stateChart 0).inclusion (Pi.single j 1)) -
      (BinaryRegular46GraphHeadRigidity.stateChart 0).inclusion (Pi.single j 1) ∈ radical.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem top_rows_original : ∀ i : Fin 6, topRows i = 1 ∨
    ∃ j : Fin 3, topRows i = BinaryMenuCayley8T3.generators j := by decide +kernel
private theorem offsets_kernel : ∀ i : Fin 6,
    binaryVectorOfMask 8 (offsetMasks i) ∈ (BinaryRegularEightNaturalRegistry.charts 46).2.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)} (E : BinaryPairFrame U (Fin 8))

theorem original_radical_eq
    (hzero : U = E.splitAffineAction)
    (hH : E.top.range = BinaryRegularEightNaturalRegistry.H)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hW : (E.originalCoordinateSubrepresentation W).toSubmodule =
      (BinaryRegular46GraphHeadRigidity.stateChart 0).space)
    (hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 4) :
    ((Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype).map
      E.originalCoordinateEquiv.toLinearMap = radical.space := by
  have ht (i : Fin 6) : topRows i ∈ E.top.range := by
    rcases top_rows_original i with h | ⟨j,h⟩
    · rw [h];exact E.top.range.one_mem
    · rw [h,hH];exact Subgroup.subset_closure ⟨j,rfl⟩
  have ha (i : Fin 6) : binaryVectorOfMask 8 (offsetMasks i) ∈ E.kernelSpace := by
    rw [hK];exact offsets_kernel i
  exact E.original_radical_eq_of_canonical_affine_generators_basis hzero topRows
    (fun i => binaryVectorOfMask 8 (offsetMasks i)) ht ha
    (BinaryRegularSixCanonicalGenerators.BinaryPairFrame.canonical_regular_six_closure
      E hzero hH hK) W (BinaryRegular46GraphHeadRigidity.stateChart 0) radical hW
    kill_basis hcap (by decide : 8 = 4 + 4)

end SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroIntrinsicRadical
