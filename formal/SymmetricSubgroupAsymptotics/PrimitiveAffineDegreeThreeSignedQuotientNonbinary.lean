import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientPairFrame

/-!
# Nonbinary signed quotients outside four blocks

The literal signed quotient is transitive on `2s` points.  A transitive
binary group has power-of-two degree, so at the residual block counts
`3, 6, 12, 18` the signed quotient cannot be a 2-group.  This supplies the
exact structural premise required by the nonbinary degree-two pair
catalogues, without replacing the actual quotient action by a representative.

Four blocks are deliberately excluded: a transitive binary action on eight
points is possible and needs its own binary row.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The literal signed quotient on `2s` points is nonbinary whenever three
divides the number of blocks. -/
theorem DegreeThreeSignedQuotientPairChart.not_isPGroup_of_three_dvd
    {s : ℕ} (C : DegreeThreeSignedQuotientPairChart block P s)
    (hspos : 0 < s) (hs3 : 3 ∣ s) :
    ¬ IsPGroup 2 C.action := by
  intro htwo
  letI : MulAction.IsPretransitive C.action (Fin (2 * s)) :=
    C.pretransitive
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp htwo
  let x : Fin (2 * s) := ⟨0, by omega⟩
  have hdvd : 2 * s ∣ Nat.card C.action := by
    have h := Subgroup.index_dvd_card (MulAction.stabilizer C.action x)
    rwa [MulAction.index_stabilizer_of_transitive C.action x,
      Nat.card_fin] at h
  rw [hk] at hdvd
  have hthree : 3 ∣ 2 ^ k := by
    exact (by omega : 3 ∣ 2 * s).trans hdvd
  have hthreeTwo : 3 ∣ 2 :=
    Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hthree
  omega

/-- Convenience form for the four nonbinary residual pair counts. -/
theorem DegreeThreeSignedQuotientPairChart.not_isPGroup_of_residual_count
    {s : ℕ} (C : DegreeThreeSignedQuotientPairChart block P s)
    (hs : s = 3 ∨ s = 6 ∨ s = 12 ∨ s = 18) :
    ¬ IsPGroup 2 C.action := by
  apply C.not_isPGroup_of_three_dvd block P
  · rcases hs with rfl | rfl | rfl | rfl <;> norm_num
  · rcases hs with rfl | rfl | rfl | rfl <;> norm_num

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
