import SymmetricSubgroupAsymptotics.BinaryPairArbitraryNormalCenter
import SymmetricSubgroupAsymptotics.BinaryPairOriginalCoordinateRepresentation

/-! Quotient-centre capacities may be evaluated after a reversible point
coordinate change. The kernel space is the exact original image; only the
SAME denominator's displacement space may be enlarged for an upper bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

abbrev binaryFixedDisplacements (rho : Representation (ZMod 2) G V)
    (K A : Submodule (ZMod 2) V) :=
  {v : V // v∈K ∧ ∀ g : G,rho g v-v∈A}

abbrev binaryTrivialDisplacements (rho : Representation (ZMod 2) G V)
    (K A : Submodule (ZMod 2) V) :=
  {g : G // ∀ v : V,v∈K → rho g v-v∈A}

def binaryJointDisplacementCapacity (rho : Representation (ZMod 2) G V)
    (K A : Submodule (ZMod 2) V) : ℕ :=
  Nat.card (binaryFixedDisplacements rho K A)*Nat.card (binaryTrivialDisplacements rho K A)

theorem binaryJointDisplacementCapacity_mono [Finite G] [Finite V]
    (rho : Representation (ZMod 2) G V) (K A B : Submodule (ZMod 2) V)
    (hAB : A≤B) :
    binaryJointDisplacementCapacity rho K A≤binaryJointDisplacementCapacity rho K B := by
  let f : binaryFixedDisplacements rho K A → binaryFixedDisplacements rho K B :=
    fun v => ⟨v.val,v.property.1,fun g => hAB (v.property.2 g)⟩
  let t : binaryTrivialDisplacements rho K A → binaryTrivialDisplacements rho K B :=
    fun g => ⟨g.val,fun v hv => hAB (g.property v hv)⟩
  have hf : Function.Injective f := fun _ _ he => Subtype.ext
    (congrArg (fun z : binaryFixedDisplacements rho K B => (z : V)) he)
  have ht : Function.Injective t := fun _ _ he => Subtype.ext
    (congrArg (fun z : binaryTrivialDisplacements rho K B => (z : G)) he)
  exact Nat.mul_le_mul (Nat.card_le_card_of_injective f hf)
    (Nat.card_le_card_of_injective t ht)

namespace BinaryPairFrame
variable {X : Type} [Finite X] {w r : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w)) (E : BinaryPairFrame F.top.range (Fin r))

include F E

/-- The centre bound retains arbitrary original lift offsets. No zero-row
or split-extension hypothesis is used in this transport. -/
theorem kernel_center_card_mul_le_original_coordinate_capacity
    (N : Subgroup U) [N.Normal]
    (K A : Submodule (ZMod 2) (Fin (r+r) → ZMod 2))
    (hK : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=K)
    (hA : (F.ambientAxis N).map E.originalCoordinateEquiv.toLinearMap≤A) :
    Nat.card N*Nat.card (Subgroup.center (U ⧸ N))≤
      binaryJointDisplacementCapacity E.originalCoordinateRepresentation K A := by
  let e := E.originalCoordinateEquiv
  have heact (t : F.top.range) (v : Fin w → ZMod 2) :
      E.originalCoordinateRepresentation t (e v)-e v=
        e (F.coordinateTopAction t v-v) := by
    change e (F.coordinateTopAction t (e.symm (e v)))-e v=e _
    rw [e.symm_apply_apply,map_sub]
  let f : {v : Fin w → ZMod 2 // v∈F.kernelSpace ∧
      ∀ t : F.top.range,F.coordinateTopAction t v-v∈F.ambientAxis N} →
      binaryFixedDisplacements E.originalCoordinateRepresentation K A := fun v =>
    ⟨e v.val,by
      constructor
      · rw [←hK]
        exact ⟨v.val,v.property.1,rfl⟩
      · intro t
        rw [heact]
        exact hA ⟨_,v.property.2 t,rfl⟩⟩
  have hf : Function.Injective f := by
    intro v z he
    apply Subtype.ext
    exact e.injective (congrArg
      (fun z : binaryFixedDisplacements E.originalCoordinateRepresentation K A => z.val) he)
  let t : {g : F.top.range // ∀ v,v∈F.kernelSpace →
      F.coordinateTopAction g v-v∈F.ambientAxis N} →
      binaryTrivialDisplacements E.originalCoordinateRepresentation K A := fun g =>
    ⟨g.val,by
      intro z hz
      rw [←hK] at hz
      obtain ⟨v,hv,rfl⟩ := hz
      change E.originalCoordinateRepresentation g.val (e v)-e v∈A
      rw [heact]
      exact hA ⟨_,g.property v hv,rfl⟩⟩
  have ht : Function.Injective t := by
    intro a b he
    exact Subtype.ext (congrArg
      (fun z : binaryTrivialDisplacements E.originalCoordinateRepresentation K A => z.val) he)
  exact (F.arbitrary_normal_center_card_mul_le N).trans
    (Nat.mul_le_mul (Nat.card_le_card_of_injective f hf)
      (Nat.card_le_card_of_injective t ht))

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
