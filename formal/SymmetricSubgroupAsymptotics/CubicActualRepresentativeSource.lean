import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairSourceCatalogue
import SymmetricSubgroupAsymptotics.CubicAllNormalB6Transport
import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport

/-! A structural source on an actual physical action determines a source
on its genuine preE7 action class through actual point conjugacy. This
constructs one actual source row, never a global catalogue or locator. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace CubicActualRepresentativeSource

/-- The actual representative and point correspondence remain visible. -/
theorem exists_actualRepresentativeSource
    {G : Type} [Group G] [Finite G]
    (H : Subgroup (Equiv.Perm (Fin 12)))
    (hH : ¬ IsPGroup 2 H) (htrans : MulAction.IsPretransitive H (Fin 12))
    (F : BinaryPairFrame H (Fin 6)) (modelEquiv : H ≃* G)
    (top : G →* CyclicThree) (htop : Function.Surjective top)
    (A : Rep (ZMod 2) CyclicThree) (E : OriginalKernelModuleChart top A)
    (D : CubicBinaryCoordinates A.ρ)
    (hscalar : ∃ j : Fin 2, ∃ q : top.ker,
      CubicElementaryKernelCoordinates.scalar top A.ρ E.equiv.symm D j q ≠ 1)
    (hKP : KovacsPraegerAbelianizationBound) :
    ∃ p : PreE7PairActionClass 6, ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c H = preE7PairAction 6 p ∧
      Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) := by
  obtain ⟨i,c,hc⟩ := Non2TransitiveActionClass.representative_cover H hH htrans
  have hr : relabelSubgroup c H = i.representative := by
    have he : relabelSubgroup c H = MulAut.conj c • H := by
      change H.map c.permCongrHom.toMonoidHom = _
      rw [Subgroup.pointwise_smul_def]
      congr 1
    exact he.trans hc
  have hpre : IsPreE7ActionClass 12 i := by
    intro d hd
    have hg := d.pairCount_ge_24
    change 2*d.pairCount=12 at hd
    omega
  have hframe : Nonempty (BinaryPairFrame i.representative (Fin 6)) := by
    rw [←hr]
    exact ⟨F.relabelPoints c⟩
  let p : PreE7PairActionClass 6 := ⟨⟨i,hpre⟩,hframe⟩
  let e : preE7PairAction 6 p ≃* G :=
    (actionConjugacyEquiv c hc).symm.trans modelEquiv
  exact ⟨p,c,hr,⟨CubicAllNormalB6Transport.originalActionCertificate
    (top := top) (A := A) (E := E) e htop D hscalar hKP
    (preE7PairFrame 6 p)⟩⟩

end CubicActualRepresentativeSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
