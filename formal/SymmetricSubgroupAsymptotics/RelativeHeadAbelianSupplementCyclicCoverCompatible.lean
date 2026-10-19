import SymmetricSubgroupAsymptotics.AffineNormalGraphFibre
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralAbelianSupplement

/-! A full-image relative head uses two cyclic abelianization positions,
including cyclic-four positions. Their order is not charged as dimension. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

 theorem relativeHead_le_two_of_abelianSupplement_cyclicCover_compatible
    (p : ℕ) [Fact p.Prime]
    {G C D : Type} [Group G] [Finite G]
    [Group C] [Finite C] [IsCyclic C] [Group D] [Finite D] [IsCyclic D]
    (cover : C × D →* G ⧸ commutator G) (hcover : Function.Surjective cover)
    (K M : Subgroup G) [M.Normal] (hKM : K ⊔ M=⊤)
    (hK : IsMulCommutative K) :
    Module.finrank (ZMod p) (primeRelativeCharacters p M)≤2 := by
  let R := primeRelativeRadical p M
  have hcomm : IsMulCommutative (G ⧸ R) :=
    TwelvePointRemainingStructural.relativeRadicalQuotient_commutative p K M hKM hK
  have hder : commutator G≤R :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  let f : (G ⧸ commutator G) →* (G ⧸ R) :=
    QuotientGroup.lift (commutator G) (QuotientGroup.mk' R) (by
      rw [QuotientGroup.ker_mk']; exact hder)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective R y
    exact ⟨QuotientGroup.mk' (commutator G) g,rfl⟩
  have hCD : PrimeSectionalRankBound p (C × D) 2 :=
    PrimeSectionalRankBound.prod p (primeSectionalRankBound_cyclic p C)
      (primeSectionalRankBound_cyclic p D)
  have hT : PrimeSectionalRankBound p (G ⧸ R) 2 :=
    PrimeSectionalRankBound.of_surjective p
      (PrimeSectionalRankBound.of_surjective p hCD cover hcover) f hf
  rw [primeRelativeHead_radical_image_eq p M]
  exact (Submodule.finrank_le _).trans (hT (normalChainQuotient R M))

end SymmetricSubgroupAsymptotics
