import SymmetricSubgroupAsymptotics.BinaryPairCoordinateCenterCapacity

/-! Coordinate transport retaining the actual top-centre restriction for
zero-top-image denominators. The original kernel space remains exact. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

abbrev binaryCentralTrivialDisplacements {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (rho : Representation (ZMod 2) G V) (K A : Submodule (ZMod 2) V) :=
  {g : G // g∈Subgroup.center G ∧ ∀ v,v∈K → rho g v-v∈A}

def binaryCentralJointDisplacementCapacity {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (rho : Representation (ZMod 2) G V) (K A : Submodule (ZMod 2) V) : ℕ :=
  Nat.card (binaryFixedDisplacements rho K A)*Nat.card (binaryCentralTrivialDisplacements rho K A)

namespace BinaryPairFrame
variable {X : Type} [Finite X] {w r : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w)) (E : BinaryPairFrame F.top.range (Fin r))
include F E

theorem kernel_center_card_mul_le_original_coordinate_central_capacity
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker)
    (K A : Submodule (ZMod 2) (Fin (r+r) → ZMod 2))
    (hK : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=K)
    (hA : (F.ambientAxis N).map E.originalCoordinateEquiv.toLinearMap≤A) :
    Nat.card N*Nat.card (Subgroup.center (U ⧸ N))≤
      binaryCentralJointDisplacementCapacity E.originalCoordinateRepresentation K A := by
  let e := E.originalCoordinateEquiv
  have heact (t : F.top.range) (v : Fin w → ZMod 2) :
      E.originalCoordinateRepresentation t (e v)-e v=e (F.coordinateTopAction t v-v) := by
    change e (F.coordinateTopAction t (e.symm (e v)))-e v=e _
    rw [e.symm_apply_apply,map_sub]
  let f : {v : Fin w → ZMod 2 // v∈F.kernelSpace ∧
      ∀ t : F.top.range,F.coordinateTopAction t v-v∈F.ambientAxis N} →
      binaryFixedDisplacements E.originalCoordinateRepresentation K A := fun v =>
    ⟨e v.val,by
      constructor
      · rw [←hK];exact ⟨v.val,v.property.1,rfl⟩
      · intro t;rw [heact];exact hA ⟨_,v.property.2 t,rfl⟩⟩
  have hf : Function.Injective f := by
    intro v z he
    apply Subtype.ext
    exact e.injective (congrArg
      (fun z : binaryFixedDisplacements E.originalCoordinateRepresentation K A => z.val) he)
  let t : {g : F.top.range // g∈Subgroup.center F.top.range ∧
      ∀ v,v∈F.kernelSpace → F.coordinateTopAction g v-v∈F.ambientAxis N} →
      binaryCentralTrivialDisplacements E.originalCoordinateRepresentation K A := fun g =>
    ⟨g.val,g.property.1,by
      intro z hz
      rw [←hK] at hz
      obtain ⟨v,hv,rfl⟩ := hz
      change E.originalCoordinateRepresentation g.val (e v)-e v∈A
      rw [heact]
      exact hA ⟨_,g.property.2 v hv,rfl⟩⟩
  have ht : Function.Injective t := by
    intro a b he
    exact Subtype.ext (congrArg
      (fun z : binaryCentralTrivialDisplacements E.originalCoordinateRepresentation K A => z.val) he)
  exact (F.kernel_normal_center_card_mul_le N hN).trans
    (Nat.mul_le_mul (Nat.card_le_card_of_injective f hf) (Nat.card_le_card_of_injective t ht))

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
