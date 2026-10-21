import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerTopTransport

/-! A proved literal-top pair-layer bound transfers to every submodule
of the original natural point module. It uses the actual kernel space and
surjective top action; all original affine lift offsets remain arbitrary. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w))

theorem naturalModuleHead_le_of_literal_pair_layer_bound
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : F.top.range = H)
    (K : Submodule (ZMod 2) (Fin w → ZMod 2)) (hK : F.kernelSpace = K)
    (cap : ℕ)
    (hbound : ∀ S L : Subrepresentation ((binaryPermutationRepresentation w).comp H.subtype),
      binaryCoordinateProductSpan K S.toSubmodule ≤ L.toSubmodule →
      Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
        Module.finrank (ZMod 2) (L.toSubmodule ⧸
          ((binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ⊔
            Representation.Coinvariants.ker L.toRepresentation)) ≤ cap)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ cap := by
  subst H
  let S := F.pairSumModuleLayer W
  let L := F.pairConstantModuleLayer W
  have hp : binaryCoordinateProductSpan K (F.descendPairLayer S).toSubmodule ≤
      (F.descendPairLayer L).toSubmodule := by
    change binaryCoordinateProductSpan K S.toSubmodule ≤ L.toSubmodule
    rw [← hK]
    exact F.actual_kernel_pairSum_product_le_constantLayer W
  have hb := hbound (F.descendPairLayer S) (F.descendPairLayer L) hp
  change Module.finrank (ZMod 2) (F.descendPairLayer S).toRepresentation.Coinvariants +
    Module.finrank (ZMod 2) (L.toSubmodule ⧸
      ((binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ⊔
        Representation.Coinvariants.ker (F.descendPairLayer L).toRepresentation)) ≤ cap at hb
  rw [← F.descendPairLayer_head S] at hb
  have hprodEq := congrArg
    (fun A : Submodule (ZMod 2) (Fin w → ZMod 2) =>
      (binaryCoordinateProductSpan A S.toSubmodule).comap L.toSubmodule.subtype) hK.symm
  have hden := congrArg₂
    (fun P R : Submodule (ZMod 2) L.toSubmodule => P ⊔ R)
      hprodEq (F.descendPairLayer_radical L).symm
  have hquotEq :
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker (F.descendPairLayer L).toRepresentation)) =
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan F.kernelSpace S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation)) :=
    (Submodule.quotEquivOfEq _ _ hden).finrank_eq
  have hw := F.pairModuleHead_le_product_quotient_add W
  change Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
    Module.finrank (ZMod 2) (L.toSubmodule ⧸
      ((binaryCoordinateProductSpan F.kernelSpace S.toSubmodule).comap L.toSubmodule.subtype ⊔
        Representation.Coinvariants.ker L.toRepresentation)) +
      Module.finrank (ZMod 2) S.toRepresentation.Coinvariants at hw
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
