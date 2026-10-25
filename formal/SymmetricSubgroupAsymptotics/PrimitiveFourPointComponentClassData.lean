import SymmetricSubgroupAsymptotics.FourPointSubnormalClassSaving
import SymmetricSubgroupAsymptotics.PrimitivePGroupDegree

/-! An actual primitive four-point component has either the all-subgroup
class budget four or an actual equivalence to S4. The recognition uses
the proved order/index argument and the impossibility of primitive
degree four for a two-group, without a subgroup/action catalogue. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveFourPointComponentClassData

theorem all_subgroup_cap_or_symmetric
    (Y : Type) [Finite Y] (B : Subgroup (Equiv.Perm Y))
    (hprimitive : MulAction.IsPreprimitive B Y) (hdegree : Nat.card Y = 4) :
    (∀ L : Subgroup B, Nat.card (ConjClasses L) ≤ 4) ∨
      Nonempty (B ≃* Equiv.Perm (Fin 4)) := by
  letI : MulAction.IsPreprimitive B Y := hprimitive
  let points : Y ≃ Fin 4 := Finite.equivFinOfCardEq hdegree
  let T : Subgroup (Equiv.Perm (Fin 4)) := B.map points.permCongrHom.toMonoidHom
  let eG : B ≃* T := points.permCongrHom.subgroupMap B
  let f : MulActionHom eG Y (Fin 4) := {
    toFun := points
    map_smul' := by
      intro g y
      change points (g.val y) = ((points.permCongrHom.subgroupMap B g).val) (points y)
      simp [Equiv.permCongr_apply] }
  letI : MulAction.IsPreprimitive T (Fin 4) :=
    MulAction.IsPreprimitive.of_surjective (f := f) points.surjective
  have hnon : ¬ IsPGroup 2 T := by
    intro hp
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := primitive_pGroup_degree hp (0 : Fin 4)
    norm_num only [Nat.card_fin] at h
  rcases TransitiveFourBinaryOrAlternating.binary_or_alternating T
    (MulAction.exists_smul_eq T) with hbinary | hA
  · exact (hnon hbinary).elim
  · rcases AlternatingTopImageNormalGenerators.above_alternating T hA with hT | hT
    · left
      let e : B ≃* alternatingGroup (Fin 4) := eG.trans (MulEquiv.subgroupCongr hT)
      intro L
      have h := FourPointSubnormalClassSaving.alternating_subgroup_class_card_le_four
        (L.map e.toMonoidHom)
      exact (conjugacyClass_card_congr (e.subgroupMap L)).le.trans h
    · right
      exact ⟨eG.trans ((MulEquiv.subgroupCongr hT).trans
        (Subgroup.topEquiv : (⊤ : Subgroup (Equiv.Perm (Fin 4))) ≃* Equiv.Perm (Fin 4)))⟩

end SymmetricSubgroupAsymptotics.PrimitiveFourPointComponentClassData
