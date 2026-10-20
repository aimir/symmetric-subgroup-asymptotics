import SymmetricSubgroupAsymptotics.FourPairY2TFImage
import SymmetricSubgroupAsymptotics.FourPairXgSocle
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsRetainedChain

/-! Existing TF Xg covers and the already proved literal cyclic socle
control every lower quotient. No third-line reconstruction or normal menu
is needed: nonbottom normals descend through the existing S4 projections. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TFXgExistingQuotientSocles
open Non2UnipotentPrefixFiniteMenu TwoFourDiagonal NaturalS4 SemidirectProduct
open FourPairY2TFImage

private def generatorLift : Fin 6 → W4 :=
  ![inl (c1,1),inl (c2,1),inl (1,c1),inl (1,c2),gA,gT*gS]

private theorem lift_pair_checked : ∀ (j : Fin 6) (i : Fin 3),
    pairFun (generatorLift j).left.1 i = pairFun (generatorLift j).left.2 i := by
  decide +kernel
private theorem lift_parity_checked : ∀ j : Fin 6,
    (generatorLift j).left.1 ∈ a4Set ↔ (generatorLift j).right = 1 := by
  decide +kernel
private theorem generator_points_checked : ∀ (j : Fin 6) (x : Fin 8),
    naturalEight (generatorLift j) x = FourPairXgCyclicKernelWords.generators j x := by
  decide +kernel
private theorem base_points_checked : ∀ (i j : Fin 4) (x : Fin 8),
    naturalEight (inl (localKlein i,localKlein j)) x =
      ((FourPairXgSocle.translation i j : FourPairXgCyclicKernelWords.Source) :
        Equiv.Perm (Fin 8)) x := by
  decide +kernel

private theorem localKlein_cases (p : Equiv.Perm (Fin 4)) (hp : p ∈ kleinSet) :
    ∃ i : Fin 4, p = localKlein i := by
  rcases kleinSet_cases hp with h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩

/-- The fixed literal Xg source is exactly the natural action of TF Xg. -/
theorem source_eq_range : FourPairXgCyclicKernelWords.Source =
    (naturalEight.comp Xg.subtype).range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have hm : generatorLift j ∈ Xg :=
      ⟨(pairing_eq_iff _ _).mpr (funext (lift_pair_checked j)),lift_parity_checked j⟩
    exact ⟨⟨generatorLift j,hm⟩,Equiv.ext (generator_points_checked j)⟩
  · have hX : Xg ≤ FourPairXgCyclicKernelWords.Source.comap naturalEight := by
      rw [Xg_eq_closure]
      apply (Subgroup.closure_le _).mpr
      intro x hx
      rcases hx with hb | hg
      · obtain ⟨i,hi⟩ := localKlein_cases x.left.1 hb.2.1
        obtain ⟨j,hj⟩ := localKlein_cases x.left.2 hb.2.2
        have he : x = inl (localKlein i,localKlein j) :=
          (eq_inl_of_right x hb.1).trans (congrArg inl (Prod.ext hi hj))
        change naturalEight x ∈ FourPairXgCyclicKernelWords.Source
        rw [he,show naturalEight (inl (localKlein i,localKlein j)) =
          ((FourPairXgSocle.translation i j : FourPairXgCyclicKernelWords.Source) :
            Equiv.Perm (Fin 8)) from Equiv.ext (base_points_checked i j)]
        exact (FourPairXgSocle.translation i j).property
      · rcases Set.mem_insert_iff.mp hg with h | h
        · subst x
          have he : naturalEight gA = FourPairXgCyclicKernelWords.generators 4 :=
            Equiv.ext (generator_points_checked 4)
          change naturalEight gA ∈ FourPairXgCyclicKernelWords.Source
          rw [he]
          exact Subgroup.subset_closure (Set.mem_range_self (4 : Fin 6))
        · have hx : x = gT*gS := Set.mem_singleton_iff.mp h
          subst x
          have he : naturalEight (gT*gS) = FourPairXgCyclicKernelWords.generators 5 :=
            Equiv.ext (generator_points_checked 5)
          change naturalEight (gT*gS) ∈ FourPairXgCyclicKernelWords.Source
          rw [he]
          exact Subgroup.subset_closure (Set.mem_range_self (5 : Fin 6))
    rintro _ ⟨x,rfl⟩
    exact hX x.property

private def toSource : Xg →* FourPairXgCyclicKernelWords.Source :=
  (naturalEight.comp Xg.subtype).codRestrict _ (by
    intro x
    rw [source_eq_range]
    exact ⟨x,rfl⟩)

private theorem toSource_bijective : Function.Bijective toSource := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply naturalEight_injective
    exact congrArg Subtype.val h
  · intro y
    have hm : (y : Equiv.Perm (Fin 8)) ∈ (naturalEight.comp Xg.subtype).range :=
      source_eq_range ▸ y.property
    obtain ⟨x,hx⟩ := hm
    exact ⟨x,Subtype.ext hx⟩

def sourceEquiv : Xg ≃* FourPairXgCyclicKernelWords.Source :=
  MulEquiv.ofBijective toSource toSource_bijective

/-- Reuse the existing original-coordinate cyclic socle proof. -/
theorem socle_one : SocleNormalGeneratorBound Xg 1 :=
  CyclicSocleQuotientTools.socleBound_equiv sourceEquiv.symm FourPairXgSocle.socle_one

/-- Existing TF projections handle every nonbottom lower denominator,
while the actual cyclic whole socle handles bottom. -/
theorem quotientSocle (M : Subgroup Xg) [M.Normal] :
    SocleNormalGeneratorBound (Xg ⧸ M) 1 := by
  by_cases hbot : M = ⊥
  · let e : (Xg ⧸ M) ≃* Xg :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    exact CyclicSocleQuotientTools.socleBound_equiv e.symm socle_one
  · obtain ⟨i,hi⟩ := projG_normal_cover M inferInstance hbot
    let L := M.map (projG i)
    letI : L.Normal := (inferInstance : M.Normal).map (projG i) (projG_surjective i)
    let e : (Xg ⧸ M) ≃* ((Equiv.Perm (Fin 4)) ⧸ L) :=
      quotientEquivOfKerLe (projG i) (projG_surjective i) M hi
    have hs : SocleNormalGeneratorBound (((Equiv.Perm (Fin 4))) ⧸ L) 1 :=
      socleNormalGeneratorBound_one_of_normal_total
        (normalSubgroups_total_of_surjective (QuotientGroup.mk' L)
          (QuotientGroup.mk'_surjective L) NaturalFourNormalChains.symmetric_normal_total)
    exact CyclicSocleQuotientTools.socleBound_equiv e.symm hs


/-- The final Xg comparator keeps the full V4² kernel via its actual pair
quotient. It is not collapsed to the original Y pair kernel. -/
def smallAction : Xg →* Equiv.Perm (Fin 3) :=
  pairHom.comp (Subgroup.inclusion Xg_le_Xs)

/-- Existing character-row interface from a concrete outer central cover.
All lower normal denominators are discharged by the proved quotientSocle,
using the existing TF covers rather than a new finite normal menu. -/
def characterModel {U : PreE7NonPairActionClass 8}
    (q : preE7NonPairAction 8 U →* Xg) (hq : Function.Surjective q)
    (hne : q.ker ≠ ⊥)
    (cover : ∀ N : Subgroup (preE7NonPairAction 8 U),
      N.Normal → N ≠ ⊥ → q.ker ≤ N) : CertifiedFourPairCharacterModel U where
  interval := {
    E := (smallAction.comp q).ker
    quotientDegree := 3
    quotientAction := (smallAction.comp q).range.subtype.comp
      (QuotientGroup.quotientKerEquivRange (smallAction.comp q)).toMonoidHom
    quotientAction_injective := Subtype.val_injective.comp
      (QuotientGroup.quotientKerEquivRange (smallAction.comp q)).injective
    slots := 1
    quotientSocleGenerators := by
      intro N hN
      letI : N.1.Normal := N.2
      apply FourPairRetainedChain.retained_socle q hq hne cover smallAction.ker
        (by
          intro M hM _hnot
          letI : M.Normal := hM
          exact quotientSocle M) N.1
      exact hN }
  quotientDegree_le_six := by norm_num
  slots_eq_one := rfl

end SymmetricSubgroupAsymptotics.TFXgExistingQuotientSocles

end
