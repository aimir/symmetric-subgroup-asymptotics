import SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-! A chosen physical block system is minimal when its actual local
component is primitive. This reverses the cover-to-fibre direction without
replacing the chosen block by an arbitrary minimal block. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A Ω]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (ω₀ : Ω)

/-- Local primitivity gives the exact cover of the original stabilizer. -/
theorem originalBlockStabilizer_covers_of_component_preprimitive
    [Nontrivial (originalBlockFibre b (b ω₀))]
    (hc : MulAction.IsPreprimitive
      (originalBlockComponent b hb (b ω₀)) (originalBlockFibre b (b ω₀))) :
    MulAction.stabilizer A ω₀ ⋖ MulAction.stabilizer A (b ω₀) := by
  let H := MulAction.stabilizer A (b ω₀)
  let F := originalBlockFibre b (b ω₀)
  letI := originalBlockStabilizerMulAction b hb (b ω₀)
  letI : MulAction.IsPretransitive H F :=
    originalBlockStabilizer_pretransitive b hb (b ω₀)
  letI : MulAction.IsPreprimitive
      (originalBlockComponent b hb (b ω₀)) F := hc
  let f : MulActionHom
      (fun h : H => (originalBlockFibreAction b hb (b ω₀)).rangeRestrict h) F F := {
    toFun := id
    map_smul' := fun _ _ => rfl }
  letI : MulAction.IsPreprimitive H F :=
    (MulAction.isPreprimitive_congr
      (f := f) (originalBlockFibreAction b hb (b ω₀)).rangeRestrict_surjective
      Function.bijective_id).mpr hc
  have hle : MulAction.stabilizer A ω₀ ≤ H := by
    intro a ha
    change a • b ω₀ = b ω₀
    have ha' : a • ω₀ = ω₀ := ha
    rw [← hb, ha']
  let z : F := ⟨ω₀,rfl⟩
  have hz : MulAction.stabilizer H z = (MulAction.stabilizer A ω₀).subgroupOf H := by
    ext a
    change a • z = z ↔ (a : A) • ω₀ = ω₀
    constructor
    · exact congrArg Subtype.val
    · intro he
      exact Subtype.ext he
  have hm : IsCoatom ((MulAction.stabilizer A ω₀).subgroupOf H) := by
    rw [← hz]
    exact (MulAction.isCoatom_stabilizer_iff_preprimitive H z).mpr inferInstance
  let e : Subgroup H ≃o Set.Iic H := Subgroup.MapSubtype.orderIso H
  have hi : IsCoatom (⟨MulAction.stabilizer A ω₀,hle⟩ : Set.Iic H) :=
    (e.symm.isCoatom_iff _).mp hm
  exact Set.Iic.isCoatom_iff.mp hi

/-- The chosen block stabilizer, with the cover proved from its local
primitive action. Properness is a geometric block-system obligation. -/
def OriginalMinimalBlock.ofPrimitiveFibre
    [Nontrivial (originalBlockFibre b (b ω₀))]
    (hc : MulAction.IsPreprimitive
      (originalBlockComponent b hb (b ω₀)) (originalBlockFibre b (b ω₀)))
    (hproper : MulAction.stabilizer A (b ω₀) < ⊤) :
    OriginalMinimalBlock (A := A) ω₀ where
  subgroup := MulAction.stabilizer A (b ω₀)
  covers := originalBlockStabilizer_covers_of_component_preprimitive b hb ω₀ hc
  proper := hproper

end SymmetricSubgroupAsymptotics
end
