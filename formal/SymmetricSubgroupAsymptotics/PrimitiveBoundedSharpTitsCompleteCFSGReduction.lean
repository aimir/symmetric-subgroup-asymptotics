import SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleTitsBoundedSharp

/-! The same actual primitive bounded-sharp reduction, with its Tits
branch paid by the literal Tits model packet. Only affine16 and actual
sporadic factor witnesses remain. No new model callback is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpTitsCompleteCFSGReduction
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics

theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (J : Subgroup (Equiv.Perm (Fin n))) (hprimitive : MulAction.IsPreprimitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (PrimitiveAffineProfile J (Fin n))) ∨
      ∃ D : NonaffineData J (Fin n), ∃ s : CFSG.Sporadic,
        Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  letI : MulAction.IsPreprimitive J (Fin n) := hprimitive
  rcases PrimitiveBoundedSharpCFSGReduction.genRank_le_sharpFloor_or_actual_residual
      hCFSG n hlo hhi J hprimitive with hpaid | haffine | ⟨D,j,hj,⟨e⟩⟩
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl haffine)
  · cases j <;> try exact hj.elim
    case tits =>
      have hpaid := PrimitiveSocleTitsBoundedSharp.genRank_le_sharpFloor D e
        (by simpa only [Nat.card_fin] using hhi)
      exact Or.inl (by simpa only [Nat.card_fin] using hpaid)
    case sporadic s => exact Or.inr (Or.inr ⟨D,s,⟨e⟩⟩)

theorem exists_generating_finset_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (J : Subgroup (Equiv.Perm (Fin n))) (hprimitive : MulAction.IsPreprimitive J (Fin n)) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      (n = 16 ∧ Nonempty (PrimitiveAffineProfile J (Fin n))) ∨
      ∃ D : NonaffineData J (Fin n), ∃ s : CFSG.Sporadic,
        Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) := by
  rcases genRank_le_sharpFloor_or_actual_residual hCFSG n hlo hhi J hprimitive with hpaid | hresidual
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr hresidual

end SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpTitsCompleteCFSGReduction
