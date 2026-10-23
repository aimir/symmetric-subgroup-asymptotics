import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoUpperFlag
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOriginalSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentPSubgroups

/-! The literal natural upper subgroup in dimension three is Sylow,
and every element of its full normalizer is triangular.  The latter
uses the same original-source normalizer theorem on the actual cover. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem rankTwoUpperSubgroup_map_original (q : CFSG.PrimePower) :
    (rankTwoUpperSubgroup q).map (naturalFixedToOriginal q 2) = originalUnipotent 2 q := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u.val, hu⟩, rfl⟩
  · rintro _ ⟨u, rfl⟩
    exact ⟨⟨u.val, u.property.2⟩, u.property, rfl⟩

theorem rankTwo_natural_normalizer_upper (q : CFSG.PrimePower) (g : naturalFixed 2 q)
    (hg : g ∈ Subgroup.normalizer (rankTwoUpperSubgroup q : Set (naturalFixed 2 q))) :
    (g.val.val : Mat (q.Extension 2) 2).BlockTriangular id := by
  have hm := (rankTwoUpperSubgroup q).le_normalizer_map (naturalFixedToOriginal q 2)
    ⟨g, hg, rfl⟩
  rw [rankTwoUpperSubgroup_map_original] at hm
  let p : fixedNaturalPullback 2 q :=
    ⟨(naturalFixedToOriginal q 2 g, g.val),
      CFSGTwistedAIntervalSource.elementaryToModel_action (q.Extension 2) 2 g.val⟩
  exact pullback_normalizer_upper q 2 (by decide) p hm

theorem rankTwoUpperSubgroup_isPGroup (q : CFSG.PrimePower) :
    IsPGroup q.prime (rankTwoUpperSubgroup q) := by
  let e : rankTwoUpperSubgroup q ≃* naturalUnipotent 2 q :=
    (naturalUnipotent 2 q).subgroupOfEquivOfLe inf_le_right
  exact (naturalUnipotent_isPGroup 2 q).of_injective e.toMonoidHom e.injective

theorem rankTwo_natural_normalizer_pSubgroups (q : CFSG.PrimePower)
    (R : Subgroup (naturalFixed 2 q)) (hR : IsPGroup q.prime R)
    (hRN : R ≤ Subgroup.normalizer (rankTwoUpperSubgroup q : Set (naturalFixed 2 q))) :
    R ≤ rankTwoUpperSubgroup q := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  let rho : R →* Mat (q.Extension 2) 2 :=
    (Units.coeHom _).comp ((fixedMatrixHom q 2).comp R.subtype)
  have hu (x : R) : (rho x).BlockTriangular id :=
    rankTwo_natural_normalizer_upper q x.val (hRN x.property)
  intro x hx
  have hd (i : Fin 3) : (x.val.val : Mat (q.Extension 2) 2) i i = 1 :=
    CFSGTwistedA2UnipotentArrays.pGroup_upper_diagonal_one q.prime hR rho hu ⟨x, hx⟩ i
  exact ⟨⟨hu ⟨x, hx⟩, hd⟩, x.property⟩

def rankTwoNaturalSylow (q : CFSG.PrimePower) : Sylow q.prime (naturalFixed 2 q) :=
  CFSGSylowNormalizerMaximality.sylowOfNormalizer (rankTwoUpperSubgroup q)
    (rankTwoUpperSubgroup_isPGroup q) (rankTwo_natural_normalizer_pSubgroups q)

theorem rankTwoNaturalSylow_coe (q : CFSG.PrimePower) :
    (rankTwoNaturalSylow q : Subgroup (naturalFixed 2 q)) = rankTwoUpperSubgroup q := rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
