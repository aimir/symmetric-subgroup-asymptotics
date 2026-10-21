import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerModelBound
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerDimension

/-! A joint finite head/dimension profile for the SAME two original pair
layers controls the full dimension of a high-head original submodule.
Arbitrary affine lift offsets are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem naturalModule_finrank_le_of_literal_pair_head_dimension_profile
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : F.top.range = H)
    (K : Submodule (ZMod 2) (Fin w → ZMod 2)) (hK : F.kernelSpace = K)
    (headCap dimCap : ℕ)
    (hprofile : ∀ S L : Subrepresentation ((binaryPermutationRepresentation w).comp H.subtype),
      binaryCoordinateProductSpan K S.toSubmodule ≤ L.toSubmodule →
      headCap ≤ Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
        Module.finrank (ZMod 2) (L.toSubmodule ⧸
          ((binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ⊔
            Representation.Coinvariants.ker L.toRepresentation)) →
      Module.finrank (ZMod 2) S.toSubmodule + Module.finrank (ZMod 2) L.toSubmodule ≤ dimCap)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hhead : headCap ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Module.finrank (ZMod 2) W.toSubmodule ≤ dimCap := by
  subst H
  let S := F.pairSumModuleLayer W
  let L := F.pairConstantModuleLayer W
  have hp : binaryCoordinateProductSpan K (F.descendPairLayer S).toSubmodule ≤
      (F.descendPairLayer L).toSubmodule := by
    change binaryCoordinateProductSpan K S.toSubmodule ≤ L.toSubmodule
    rw [← hK]
    exact F.actual_kernel_pairSum_product_le_constantLayer W
  have hprodEq := congrArg
    (fun A : Submodule (ZMod 2) (Fin w → ZMod 2) =>
      (binaryCoordinateProductSpan A S.toSubmodule).comap L.toSubmodule.subtype) hK.symm
  have hden := congrArg₂ (fun P R : Submodule (ZMod 2) L.toSubmodule => P ⊔ R)
    hprodEq (F.descendPairLayer_radical L).symm
  have hquotEq :
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker (F.descendPairLayer L).toRepresentation)) =
      Module.finrank (ZMod 2) (L.toSubmodule ⧸ F.pairLayerProductDenominator W) :=
    (Submodule.quotEquivOfEq _ _ hden).finrank_eq
  have hw := F.pairModuleHead_le_product_quotient_add W
  change Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
    Module.finrank (ZMod 2) (L.toSubmodule ⧸ F.pairLayerProductDenominator W) +
      Module.finrank (ZMod 2) S.toRepresentation.Coinvariants at hw
  have hh : headCap ≤ Module.finrank (ZMod 2) (F.descendPairLayer S).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker (F.descendPairLayer L).toRepresentation)) := by
    rw [← F.descendPairLayer_head S, hquotEq]
    omega
  have hd := hprofile (F.descendPairLayer S) (F.descendPairLayer L) hp hh
  exact (F.pairModuleLayers_finrank W).trans_le hd

end SymmetricSubgroupAsymptotics.BinaryPairFrame
