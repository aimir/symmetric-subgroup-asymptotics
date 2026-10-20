import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex
import SymmetricSubgroupAsymptotics.PrimitiveTernaryThreeTenthsPublished
import Mathlib.GroupTheory.GroupAction.Quotient

/-! A second application of the same retained composition correspondence:
the actual least-index coset action of the simple socle is faithful and
primitive. This supplies an actual-order chart rather than an independent
simple-group classification premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {T : Type} [Group T] [Finite T] [IsSimpleGroup T]

theorem LeastProperIndex.isCoatom {ell : ℕ} (h : LeastProperIndex T ell)
    (H : Subgroup T) (hH : H≠⊤) (hi : H.index=ell) : IsCoatom H := by
  refine ⟨hH,?_⟩
  intro K hHK
  by_contra hK
  have hsmall := Subgroup.index_strictAnti hHK
  have hlarge := h.2 K hK
  omega

/-- A proper subgroup of a simple group has a faithful actual coset action. -/
theorem simple_cosetAction_injective (H : Subgroup T) (hH : H≠⊤) :
    Function.Injective (MulAction.toPermHom T (T⧸H)) := by
  have hcore : H.normalCore=⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore H.normalCore_normal with h|h
    · exact h
    · exact (hH (top_le_iff.mp (h ▸ H.normalCore_le))).elim
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [←Subgroup.normalCore_eq_ker H,hcore]

/-- The same336-row actual-order correspondence can be applied to the
least-index primitive coset action of the actual simple factor. -/
theorem compositionMatch_at_leastIndex
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hnc : ¬ IsMulCommutative T) {ell : ℕ}
    (hell : LeastProperIndex T ell) (hsmall : ell<45) :
    ∃ H : Subgroup T,H≠⊤ ∧ H.index=ell ∧
      Nonempty (PrimitiveCompositionCatalogueMatch T (T⧸H)) := by
  obtain ⟨H,hH,hi⟩ := hell.1
  have hi5 : 5≤ell := nonabelianSimple_leastProperIndex_five_le
    (fun hc => hnc (isMulCommutative_iff.mpr hc)) hell.1
  letI : FaithfulSMul T (T⧸H) :=
    ⟨fun {_ _} h => simple_cosetAction_injective H hH (Equiv.ext h)⟩
  letI : Nontrivial (T⧸H) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [←H.index_eq_card,hi]
    omega)
  letI : MulAction.IsPreprimitive T (T⧸H) := by
    apply (MulAction.isCoatom_stabilizer_iff_preprimitive T ((1 : T) : T⧸H)).mp
    rw [MulAction.stabilizer_quotient]
    exact hell.isCoatom H hH hi
  exact ⟨H,hH,hi,catalogue T (T⧸H) (by rw [←H.index_eq_card,hi]; exact hsmall)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
