import SymmetricSubgroupAsymptotics.QuotientSocleRelativeHead
import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank

/-! A relative head can be bounded using retained original quotients and
sectional rank on the exact killed-kernel quotient. The maximal-disjoint
quotient is formed after the original relative radical, and the case split
uses the kernel of the explicit composite map from the original group. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

/-- Only quotients retaining `E` need the socle certificate. Quotients
killing `E` are controlled by the actual sectional rank of `G / E`. -/
theorem primeRelativeHead_le_of_retained_socles
    (E : Subgroup G) [E.Normal] (t r : ℕ)
    (hretained : ∀ K : {K : Subgroup G // K.Normal},
      ¬ E ≤ K.1 → SocleNormalGeneratorBound (G ⧸ K.1) t)
    (hkilled : PrimeSectionalRankBound p (G ⧸ E) r)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ max t r := by
  let R : Subgroup G := primeRelativeRadical p N
  letI : R.Normal := primeRelativeRadical_normal p N
  let q₁ : G →* G ⧸ R := QuotientGroup.mk' R
  let A : Subgroup (G ⧸ R) := normalChainQuotient R N
  letI : A.Normal := normalChainQuotient_normal R N
  obtain ⟨B, hB, hd, hmax⟩ := NormalDisjointQuotientSocle.exists_maximal_disjoint_normal A
  letI : B.Normal := hB
  let q₂ : (G ⧸ R) →* (G ⧸ R) ⧸ B := QuotientGroup.mk' B
  let π : G →* (G ⧸ R) ⧸ B := q₂.comp q₁
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective B).comp (QuotientGroup.mk'_surjective R)
  let S : Subgroup ((G ⧸ R) ⧸ B) := normalChainQuotient B A
  have hhead : Module.finrank (ZMod p) (primeRelativeCharacters p S) ≤ max t r := by
    by_cases hE : E ≤ π.ker
    · let f : (G ⧸ E) →* (G ⧸ R) ⧸ B := QuotientGroup.lift E π hE
      have hf : Function.Surjective f := QuotientGroup.lift_surjective_of_surjective E π hπ hE
      have hS : Module.finrank (ZMod p) (PrimeCharacters p S) ≤ r :=
        PrimeSectionalRankBound.quotient_rank_le p hkilled (S.comap f)
          (f.subgroupComap S) (f.subgroupComap_surjective_of_surjective S hf)
      exact ((Submodule.finrank_le _).trans hS).trans (le_max_right t r)
    · have hsocle : finiteGroupSocle ((G ⧸ R) ⧸ B) = S :=
        CentralPrimeExponentSocle.socle_eq_image p A B
          (primeRelativeRadical_image_le_center p N)
          (primeRelativeRadical_image_pow_eq_one p N) hd hmax
      have hbound : SocleNormalGeneratorBound ((G ⧸ R) ⧸ B) t :=
        CyclicSocleQuotientTools.socleBound_equiv
          (QuotientGroup.quotientKerEquivOfSurjective π hπ)
          (hretained ⟨π.ker, inferInstance⟩ hE)
      obtain ⟨x, hx⟩ := hbound
      exact (primeRelativeHead_le_normal_generating_tuple p S x
        (hx.trans hsocle)).trans (le_max_left t r)
  let e : A ≃* S := MulEquiv.ofBijective (normalChainMap B A) ⟨by
    intro a b hab
    exact NormalDisjointQuotientSocle.quotientMap_injective_on A B hd
      (congrArg Subtype.val hab), normalChainMap_surjective B A⟩
  have he (g : G ⧸ R) (a : A) :
      e (MulAut.conjNormal g a) = MulAut.conjNormal (q₂ g) (e a) :=
    normalChainMap_equivariant B A g a
  have htransport := (relativeCharacterEquivariantCongr p q₂
    (QuotientGroup.mk'_surjective B) A S e he).finrank_eq
  calc
    Module.finrank (ZMod p) (primeRelativeCharacters p N) =
        Module.finrank (ZMod p) (primeRelativeCharacters p A) :=
      primeRelativeHead_radical_image_eq p N
    _ = Module.finrank (ZMod p) (primeRelativeCharacters p S) := htransport.symm
    _ ≤ max t r := hhead

end SymmetricSubgroupAsymptotics

end
