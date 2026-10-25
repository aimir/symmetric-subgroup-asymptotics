import SymmetricSubgroupAsymptotics.PrimitiveSocleSelectedOrderDegree
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedWordOrder

/-! The actual supported Co3 simple factor cannot occur in a faithful
original action on at most10points. The complete socle/perfectness/order
proof is generic in the model type; this concrete installer supplies
only the SAME already checked selected14-order witness. No concrete
model simplicity or order table, new word or new vector is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleCoThreeSmallActionExclusion
open PrimitiveSocleRawStructure

-- This installer uses the model only as a group. Keep the literal raw
-- decoder and arrays opaque while comparing its existing group marking.
attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.Co3.rows1
  CFSG.Models.MatrixGroups.Co3.rows2

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X)

theorem not_co_three (hcard : Nat.card X ≤ 10)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Co3.Model) : False := by
  have h : 11 ≤ Nat.card X :=
    @PrimitiveSocleSelectedOrderDegree.prime_add_four_le_card
      G X ‹Group G› ‹Finite G› ‹Finite X› ‹MulAction G X› ‹FaithfulSMul G X› D
      CFSG.Models.MatrixGroups.Co3.Model
      (inferInstance : Group CFSG.Models.MatrixGroups.Co3.Model) e 7 (by decide) (by decide)
      CFSGCoThreeSelectedWordOrder.exists_fourteen_dvd_orderOf
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleCoThreeSmallActionExclusion
