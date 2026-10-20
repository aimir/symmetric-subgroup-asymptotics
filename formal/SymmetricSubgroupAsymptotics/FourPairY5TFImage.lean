import SymmetricSubgroupAsymptotics.FourPairY5CentralGraph
import SymmetricSubgroupAsymptotics.FourPairY2TFImage

/-! Exact recognition of the selected Y5 central quotient as the existing
TF Xs group. The original graph target generators and sixteen base vectors
are matched on the original eight coordinates; no normal census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairY5TFImage
open FourPairY5CentralGraph TwoFourDiagonal NaturalS4 SemidirectProduct

open FourPairY2TFImage

def generatorLift : Fin 6 → W4 :=
  ![inl (c1,c1)*gS,inl (c3,c3)*gS,gS,inl (c2,c2)*gS,inl (Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 2,Equiv.swap 0 1)*gS,inl (Equiv.swap 0 2,Equiv.swap 0 2)*gS]

private theorem lift_pair_checked : ∀ (j : Fin 6) (i : Fin 3),
    pairFun (generatorLift j).left.1 i = pairFun (generatorLift j).left.2 i := by
  decide +kernel
private theorem generator_points_checked : ∀ (j : Fin 6) (x : Fin 8),
    naturalEight (generatorLift j) x = targetGenerators j x := by
  decide +kernel

theorem generatorLift_mem (j : Fin 6) : generatorLift j ∈ Xs :=
  (pairing_eq_iff _ _).mpr (funext (lift_pair_checked j))

def baseIndex : Fin 4 → Fin 4 → Fin 384 :=
  ![![324,103,234,9],![110,333,0,227],![233,10,327,100],![3,224,109,334]]

private theorem base_points_checked : ∀ (i j : Fin 4) (x : Fin 8),
    naturalEight (inl (localKlein i,localKlein j)) x = targetState (baseIndex i j) x := by
  decide +kernel
private theorem a_points_checked : ∀ x : Fin 8,
    naturalEight (gA) x = targetState 29 x := by
  decide +kernel
private theorem t_points_checked : ∀ x : Fin 8,
    naturalEight (gT) x = targetState 117 x := by
  decide +kernel
private theorem s_points_checked : ∀ x : Fin 8,
    naturalEight (gS) x = targetState 332 x := by
  decide +kernel

private theorem targetState_mem (i : Fin 384) : targetState i ∈ Image := by
  have h := certificate.hom_sourceElement i
  change (projection (certificate.sourceElement i) : Equiv.Perm (Fin 8)) = targetState i at h
  rw [← h]
  exact (projection (certificate.sourceElement i)).property

private theorem localKlein_cases (p : Equiv.Perm (Fin 4)) (hp : p ∈ kleinSet) :
    ∃ i : Fin 4, p = localKlein i := by
  rcases kleinSet_cases hp with h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩

/-- Equality of the actual original target subgroup and the existing TF
natural action range, proved by the two finite generator inclusions. -/
theorem image_eq_range : Image = (naturalEight.comp Xs.subtype).range := by
  apply le_antisymm
  · change Subgroup.closure (Set.range targetGenerators) ≤ _
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨⟨generatorLift j,generatorLift_mem j⟩,
      Equiv.ext (generator_points_checked j)⟩
  · have hX : Xs ≤ Image.comap naturalEight := by
      rw [Xs_eq_closure]
      apply (Subgroup.closure_le _).mpr
      intro x hx
      rcases hx with hb | hg
      · obtain ⟨i,hi⟩ := localKlein_cases x.left.1 hb.2.1
        obtain ⟨j,hj⟩ := localKlein_cases x.left.2 hb.2.2
        have he : x = inl (localKlein i,localKlein j) :=
          (eq_inl_of_right x hb.1).trans (congrArg inl (Prod.ext hi hj))
        change naturalEight x ∈ Image
        rw [he, show naturalEight (inl (localKlein i,localKlein j)) =
          targetState (baseIndex i j) from Equiv.ext (base_points_checked i j)]
        exact targetState_mem _
      · rcases Set.mem_insert_iff.mp hg with h | h
        · subst x
          change naturalEight gA ∈ Image
          rw [show naturalEight gA = targetState 29 from Equiv.ext a_points_checked]
          exact targetState_mem _
        · rcases Set.mem_insert_iff.mp h with h | h
          · subst x
            change naturalEight gT ∈ Image
            rw [show naturalEight gT = targetState 117 from Equiv.ext t_points_checked]
            exact targetState_mem _
          · have hx : x = gS := Set.mem_singleton_iff.mp h
            subst x
            change naturalEight gS ∈ Image
            rw [show naturalEight gS = targetState 332 from Equiv.ext s_points_checked]
            exact targetState_mem _
    rintro _ ⟨x,rfl⟩
    exact hX x.property

def toImage : Xs →* Image :=
  (naturalEight.comp Xs.subtype).codRestrict Image (by
    intro x
    rw [image_eq_range]
    exact ⟨x,rfl⟩)

theorem toImage_bijective : Function.Bijective toImage := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply naturalEight_injective
    exact congrArg Subtype.val h
  · intro y
    have hm : (y : Equiv.Perm (Fin 8)) ∈ (naturalEight.comp Xs.subtype).range :=
      image_eq_range ▸ y.property
    obtain ⟨x,hx⟩ := hm
    exact ⟨x,Subtype.ext hx⟩

/-- Actual recognition, not a replacement of the original Y5 action by a
historical TF action-class label. -/
def imageEquiv : Image ≃* Xs := (MulEquiv.ofBijective toImage toImage_bijective).symm

end SymmetricSubgroupAsymptotics.FourPairY5TFImage

end
