import SymmetricSubgroupAsymptotics.CentralPrimeExponentSocle
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadNormalGenerators
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalImage
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! A socle bound for every actual quotient controls every original normal
relative head. First quotient by the original relative-character radical.
Then kill a maximal normal subgroup disjoint from its central elementary
image. The image becomes the entire socle without losing any retained
characters. The socle hypothesis is applied to the explicit composite
original epimorphism through its actual kernel. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem primeRelativeHead_le_of_all_quotient_socles (t : ℕ)
    (hall : ∀ K : {K : Subgroup G // K.Normal}, SocleNormalGeneratorBound (G ⧸ K.1) t)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ t := by
  let R : Subgroup G := primeRelativeRadical p N
  let q₁ : G →* G ⧸ R := QuotientGroup.mk' R
  let A : Subgroup (G ⧸ R) := normalChainQuotient R N
  letI : R.Normal := primeRelativeRadical_normal p N
  letI : A.Normal := normalChainQuotient_normal R N
  obtain ⟨B, hB, hd, hmax⟩ := NormalDisjointQuotientSocle.exists_maximal_disjoint_normal A
  letI : B.Normal := hB
  let q₂ : (G ⧸ R) →* (G ⧸ R) ⧸ B := QuotientGroup.mk' B
  let π : G →* (G ⧸ R) ⧸ B := q₂.comp q₁
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective B).comp (QuotientGroup.mk'_surjective R)
  have hsocle : finiteGroupSocle ((G ⧸ R) ⧸ B) = normalChainQuotient B A :=
    CentralPrimeExponentSocle.socle_eq_image p A B
      (primeRelativeRadical_image_le_center p N)
      (primeRelativeRadical_image_pow_eq_one p N) hd hmax
  have hbound : SocleNormalGeneratorBound ((G ⧸ R) ⧸ B) t :=
    CyclicSocleQuotientTools.socleBound_equiv
      (QuotientGroup.quotientKerEquivOfSurjective π hπ) (hall ⟨π.ker, inferInstance⟩)
  obtain ⟨x, hx⟩ := hbound
  have hhead : Module.finrank (ZMod p)
      (primeRelativeCharacters p (normalChainQuotient B A)) ≤ t :=
    primeRelativeHead_le_normal_generating_tuple p _ x (hx.trans hsocle)
  let e : A ≃* normalChainQuotient B A := MulEquiv.ofBijective (normalChainMap B A) ⟨by
    intro a b hab
    exact NormalDisjointQuotientSocle.quotientMap_injective_on A B hd
      (congrArg Subtype.val hab), normalChainMap_surjective B A⟩
  have he (g : G ⧸ R) (a : A) :
      e (MulAut.conjNormal g a) = MulAut.conjNormal (q₂ g) (e a) :=
    normalChainMap_equivariant B A g a
  have htransport := (relativeCharacterEquivariantCongr p q₂
    (QuotientGroup.mk'_surjective B) A (normalChainQuotient B A) e he).finrank_eq
  calc
    Module.finrank (ZMod p) (primeRelativeCharacters p N) =
        Module.finrank (ZMod p) (primeRelativeCharacters p A) :=
      primeRelativeHead_radical_image_eq p N
    _ = Module.finrank (ZMod p)
        (primeRelativeCharacters p (normalChainQuotient B A)) := htransport.symm
    _ ≤ t := hhead

end SymmetricSubgroupAsymptotics

end
