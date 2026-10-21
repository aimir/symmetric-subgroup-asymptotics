import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerHeadDimension

/-! A joint original-kernel and pair-layer profile controls their combined
dimension, retaining the same correlated kernel and arbitrary offsets. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem naturalModule_kernel_add_finrank_le_of_literal_joint_profile
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : F.top.range = H)
    (K : Subrepresentation ((binaryPermutationRepresentation w).comp H.subtype))
    (hK : F.kernelSpace = K.toSubmodule)
    (headCap dimCap : ℕ)
    (hprofile : ∀ S L : Subrepresentation ((binaryPermutationRepresentation w).comp H.subtype),
      binaryCoordinateProductSpan K.toSubmodule S.toSubmodule ≤ L.toSubmodule →
      headCap ≤ Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
        Module.finrank (ZMod 2) (L.toSubmodule ⧸
          ((binaryCoordinateProductSpan K.toSubmodule S.toSubmodule).comap L.toSubmodule.subtype ⊔
            Representation.Coinvariants.ker L.toRepresentation)) →
      Module.finrank (ZMod 2) K.toSubmodule + Module.finrank (ZMod 2) S.toSubmodule +
        Module.finrank (ZMod 2) L.toSubmodule ≤ dimCap)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hhead : headCap ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Module.finrank (ZMod 2) F.kernelSpace + Module.finrank (ZMod 2) W.toSubmodule ≤ dimCap := by
  subst H
  let S := F.pairSumModuleLayer W
  let L := F.pairConstantModuleLayer W
  have hp : binaryCoordinateProductSpan K.toSubmodule (F.descendPairLayer S).toSubmodule ≤
      (F.descendPairLayer L).toSubmodule := by
    change binaryCoordinateProductSpan K.toSubmodule S.toSubmodule ≤ L.toSubmodule
    rw [← hK]
    exact F.actual_kernel_pairSum_product_le_constantLayer W
  have hprodEq := congrArg
    (fun A : Submodule (ZMod 2) (Fin w → ZMod 2) =>
      (binaryCoordinateProductSpan A S.toSubmodule).comap L.toSubmodule.subtype) hK.symm
  have hden := congrArg₂ (fun P R : Submodule (ZMod 2) L.toSubmodule => P ⊔ R)
    hprodEq (F.descendPairLayer_radical L).symm
  have hquotEq :
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan K.toSubmodule S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker (F.descendPairLayer L).toRepresentation)) =
      Module.finrank (ZMod 2) (L.toSubmodule ⧸ F.pairLayerProductDenominator W) :=
    (Submodule.quotEquivOfEq _ _ hden).finrank_eq
  have hw := F.pairModuleHead_le_product_quotient_add W
  change Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
    Module.finrank (ZMod 2) (L.toSubmodule ⧸ F.pairLayerProductDenominator W) +
      Module.finrank (ZMod 2) S.toRepresentation.Coinvariants at hw
  have hh : headCap ≤ Module.finrank (ZMod 2) (F.descendPairLayer S).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan K.toSubmodule S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker (F.descendPairLayer L).toRepresentation)) := by
    rw [← F.descendPairLayer_head S, hquotEq]
    omega
  have hd := hprofile (F.descendPairLayer S) (F.descendPairLayer L) hp hh
  change Module.finrank (ZMod 2) K.toSubmodule + Module.finrank (ZMod 2) S.toSubmodule +
    Module.finrank (ZMod 2) L.toSubmodule ≤ dimCap at hd
  rw [← hK] at hd
  rw [F.pairModuleLayers_finrank W]
  change Module.finrank (ZMod 2) F.kernelSpace +
    (Module.finrank (ZMod 2) S.toSubmodule + Module.finrank (ZMod 2) L.toSubmodule) ≤ dimCap
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
