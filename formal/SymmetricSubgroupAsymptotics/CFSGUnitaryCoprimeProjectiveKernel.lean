import SymmetricSubgroupAsymptotics.CFSGUnitaryMatrixCardinalityBounds
import Mathlib.Data.Int.GCD

/-! Coprime natural dimension and extension-field unit order force the
ACTUAL unitary projective cover kernel to be trivial. The proof uses its
existing injection into the literal SL centre, not a centre formula. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryCoprimeProjectiveKernel

/-- Shared scalar-centre fact, valid for every finite field. -/
theorem specialLinear_center_card_eq_one {F I : Type} [Field F] [Finite F]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (hc : (Fintype.card I).Coprime (Nat.card Fˣ)) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup I F)) = 1 := by
  let R := rootsOfUnity (Fintype.card I) F
  have hR : ∀ z : R, z = 1 := by
    intro z
    apply Subtype.ext
    exact (pow_eq_one_iff_of_coprime hc).mp
      ⟨z.property,pow_card_eq_one'⟩
  have hcard : Nat.card R = 1 := Nat.card_eq_one_iff_exists.mpr ⟨1,hR⟩
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
    (n := I) (R := F) (Classical.arbitrary I)).toEquiv]
  exact hcard

theorem unitaryProjectiveCover_kernel_card_eq_one (q : CFSG.PrimePower) (s : ℕ)
    (hc : (s+4).Coprime (q.order^2-1)) :
    Nat.card (CFSGTwistedAUnitaryCoordinates.unitaryProjectiveCover q s).ker = 1 := by
  have hc' : (Fintype.card (Fin (s+3+1))).Coprime (Nat.card (q.Extension 2)ˣ) := by
    simpa only [Fintype.card_fin,Nat.card_units,CFSGTwistedANaturalMatrices.extension_two_card]
      using hc
  have hcenter := specialLinear_center_card_eq_one (F := q.Extension 2) (I := Fin (s+3+1)) hc'
  have hh := Nat.card_le_card_of_injective
    (CFSGTwistedAUnitaryCoordinates.unitaryCoverKernelToSLCenter q s)
    (CFSGTwistedAUnitaryCoordinates.unitaryCoverKernelToSLCenter_injective q s)
  rw [hcenter] at hh
  have hp : 0 < Nat.card (CFSGTwistedAUnitaryCoordinates.unitaryProjectiveCover q s).ker := Nat.card_pos
  omega

end SymmetricSubgroupAsymptotics.CFSGUnitaryCoprimeProjectiveKernel
