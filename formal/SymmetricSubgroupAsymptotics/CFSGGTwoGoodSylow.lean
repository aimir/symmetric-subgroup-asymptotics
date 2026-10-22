import SymmetricSubgroupAsymptotics.CFSGGTwoSylowNormalizer
import SymmetricSubgroupAsymptotics.CFSGTwoPSubgroupsSylowGeneration
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime

/-! A literal defining-characteristic GoodSylowPrime witness for the
actual folded natural G2 matrix group, with no Sylow or BN premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoGoodSylow
open CFSGGTwoSerreMatrices CFSGGTwoPositivePGroup CFSGGTwoSylowNormalizer

theorem natural_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    CFSGReduction.GoodSylowPrime (naturalGroup K) p := by
  letI : Fintype K := Fintype.ofFinite K
  let H := naturalGroup K
  let U := rootGroup K false
  let V := rootGroup K true
  have hjoin : U ⊔ V = H := positive_sup_negative K
  have hU : U ≤ H := by rw [← hjoin]; exact le_sup_left
  have hV : V ≤ H := by rw [← hjoin]; exact le_sup_right
  have hUp : IsPGroup p (U.subgroupOf H) :=
    (rootGroup_isPGroup K false p).of_injective
      (Subgroup.subgroupOfEquivOfLe hU).toMonoidHom (Subgroup.subgroupOfEquivOfLe hU).injective
  have hVp : IsPGroup p (V.subgroupOf H) :=
    (rootGroup_isPGroup K true p).of_injective
      (Subgroup.subgroupOfEquivOfLe hV).toMonoidHom (Subgroup.subgroupOfEquivOfLe hV).injective
  have htop : U.subgroupOf H ⊔ V.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hU hV, hjoin, Subgroup.subgroupOf_self]
  obtain ⟨P, g, hUP, hg⟩ := CFSGTwoPSubgroupsSylowGeneration.exists_conjugate_sylows
    (U.subgroupOf H) (V.subgroupOf H) hUp hVp htop
  exact ⟨Fact.out, P, g, normalizer_soluble K p (P : Subgroup H) P.isPGroup' hUP, hg⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoGoodSylow
