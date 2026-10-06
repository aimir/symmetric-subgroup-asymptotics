import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLiteralBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTopStabilizerEpi

/-!
# Pointed matching for an eight-block finite-frame row

The finite rows use the stabilizer of one displayed point.  A top-only
classification supplies an ambient conjugator but does not initially say
which actual block is sent to that displayed point.  There is no additional
classification obligation: the actual point is simply the inverse image of
the displayed point under the relabelling followed by the conjugator.

This file records the resulting stabilizer equivalence and the exact square
which a generated local `C3` or `S3` row has to check.  In particular, the
stored stabilizer kernel is not selected from its order alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

namespace DegreeFourZeroCoreEightLiteralTopMatch

/-- The action equivalence before the generated Cayley model is applied. -/
noncomputable def actionEquiv
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup) :
    block.Top ≃* M.literalAction :=
  (M.pointEquiv.permCongrHom.subgroupMap block.Top).trans
    (actionConjugacyEquiv M.conjugator M.conjugated)

/-- The actual block which is carried to one fixed point of the literal
row.  The eight-frame data use `0 : Fin 8`. -/
def pointOver
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup)
    (literalPoint : Fin 8) : block.Points :=
  M.pointEquiv.symm (M.conjugator.symm literalPoint)

omit [Nontrivial block.Fibre] in
@[simp] theorem conjugator_pointEquiv_pointOver
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup)
    (literalPoint : Fin 8) :
    M.conjugator
      (M.pointEquiv (pointOver (block := block) M literalPoint)) =
        literalPoint := by
  simp only [pointOver, Equiv.apply_symm_apply]

omit [Nontrivial block.Fibre] in
/-- Naturality of the literal action equivalence on points. -/
theorem actionEquiv_apply_point
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup)
    (u : block.Top) (x : block.Points) :
    ((((actionEquiv (block := block) M) u : M.literalAction) : Equiv.Perm (Fin 8))
        (M.conjugator (M.pointEquiv x))) =
      M.conjugator (M.pointEquiv (u.1 x)) := by
  simp [actionEquiv, actionConjugacyEquiv, Equiv.permCongr_apply]

omit [Nontrivial block.Fibre] in
/-- The literal action selected by the top match is transitive.  This is
transported from the actual minimal-block top, so a selected row does not
need a separate transitivity certificate. -/
theorem literalAction_pretransitive
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup) :
    MulAction.IsPretransitive M.literalAction (Fin 8) := by
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  refine ⟨fun x y => ?_⟩
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq block.Top
    (pointOver (block := block) M x) (pointOver (block := block) M y)
  refine ⟨(actionEquiv (block := block) M) u, ?_⟩
  change ((((actionEquiv (block := block) M) u : M.literalAction) :
    Equiv.Perm (Fin 8)) x) = y
  calc
    ((((actionEquiv (block := block) M) u : M.literalAction) :
        Equiv.Perm (Fin 8)) x) =
        ((((actionEquiv (block := block) M) u : M.literalAction) :
          Equiv.Perm (Fin 8))
          (M.conjugator (M.pointEquiv (pointOver (block := block) M x)))) :=
      congrArg ((((actionEquiv (block := block) M) u : M.literalAction) :
        Equiv.Perm (Fin 8)))
        (conjugator_pointEquiv_pointOver (block := block) M x).symm
    _ = M.conjugator
        (M.pointEquiv (u.1 (pointOver (block := block) M x))) :=
      actionEquiv_apply_point (block := block) M u
        (pointOver (block := block) M x)
    _ = M.conjugator
        (M.pointEquiv (pointOver (block := block) M y)) := by
      change u.1.1 (pointOver (block := block) M x) =
        pointOver (block := block) M y at hu
      exact congrArg (fun z => M.conjugator (M.pointEquiv z)) hu
    _ = y := conjugator_pointEquiv_pointOver (block := block) M y

/-- The classifier's action equivalence restricts to the exact two point
stabilizers once the actual point is chosen by `pointOver`. -/
noncomputable def stabilizerEquiv
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup)
    (literalPoint : Fin 8) :
    MulAction.stabilizer block.Top (pointOver (block := block) M literalPoint) ≃*
      MulAction.stabilizer M.literalAction literalPoint where
  toFun u := ⟨(actionEquiv (block := block) M) u.1, by
    change ((((actionEquiv (block := block) M) u.1 : M.literalAction) :
      Equiv.Perm (Fin 8))
      literalPoint) = literalPoint
    calc
      ((((actionEquiv (block := block) M) u.1 : M.literalAction) :
          Equiv.Perm (Fin 8))
          literalPoint) =
          ((((actionEquiv (block := block) M) u.1 : M.literalAction) :
            Equiv.Perm (Fin 8))
            (M.conjugator (M.pointEquiv
              (pointOver (block := block) M literalPoint)))) :=
        congrArg
          ((((actionEquiv (block := block) M) u.1 : M.literalAction) :
            Equiv.Perm (Fin 8)))
          (conjugator_pointEquiv_pointOver (block := block) M literalPoint).symm
      _ = M.conjugator
          (M.pointEquiv
            (u.1.1 (pointOver (block := block) M literalPoint))) :=
        actionEquiv_apply_point (block := block) M u.1
          (pointOver (block := block) M literalPoint)
      _ = M.conjugator
          (M.pointEquiv (pointOver (block := block) M literalPoint)) := by
        have hu := u.2
        change u.1.1 (pointOver (block := block) M literalPoint) =
          pointOver (block := block) M literalPoint at hu
        rw [hu]
      _ = literalPoint :=
        conjugator_pointEquiv_pointOver (block := block) M literalPoint
  ⟩
  invFun v :=
    let e := actionEquiv (block := block) M
    ⟨e.symm v.1, by
    have hv := v.2
    change v.1.1 literalPoint = literalPoint at hv
    have haction := actionEquiv_apply_point (block := block) M
      (e.symm v.1)
      (pointOver (block := block) M literalPoint)
    apply (M.conjugator.injective.comp M.pointEquiv.injective)
    calc
      M.conjugator
          (M.pointEquiv ((e.symm v.1).1
            (pointOver (block := block) M literalPoint))) =
          (((e (e.symm v.1) : M.literalAction) : Equiv.Perm (Fin 8))
            (M.conjugator (M.pointEquiv
              (pointOver (block := block) M literalPoint)))) := haction.symm
      _ = (((e (e.symm v.1) : M.literalAction) : Equiv.Perm (Fin 8))
            literalPoint) :=
        congrArg
          (((e (e.symm v.1) : M.literalAction) : Equiv.Perm (Fin 8)))
          (conjugator_pointEquiv_pointOver
            (block := block) M literalPoint)
      _ = ((v.1 : M.literalAction) : Equiv.Perm (Fin 8)) literalPoint := by
        rw [e.apply_symm_apply]
      _ = literalPoint := hv
      _ = M.conjugator
          (M.pointEquiv (pointOver (block := block) M literalPoint)) :=
        (conjugator_pointEquiv_pointOver
          (block := block) M literalPoint).symm
    ⟩
  left_inv u := by
    apply Subtype.ext
    exact (actionEquiv (block := block) M).symm_apply_apply u.1
  right_inv v := by
    apply Subtype.ext
    exact (actionEquiv (block := block) M).apply_symm_apply v.1
  map_mul' u v := by
    apply Subtype.ext
    exact (actionEquiv (block := block) M).map_mul u.1 v.1

/-- The actual local epimorphism, transported to the literal point
stabilizer used by the selected finite row. -/
def transportedLocalMap
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (literalPoint : Fin 8) :
    MulAction.stabilizer M.literalAction literalPoint →*
      LocalQuotient block P :=
  (degreeFourZeroCoreTopStabilizerLocalMap block P hr hD
    (pointOver (block := block) M literalPoint)).comp
      (stabilizerEquiv (block := block) M literalPoint).symm.toMonoidHom

theorem transportedLocalMap_surjective
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (literalPoint : Fin 8) :
    Function.Surjective
      (transportedLocalMap (block := block) (P := P) M hr hD literalPoint) :=
  (degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD
    (pointOver (block := block) M literalPoint)).comp
      (stabilizerEquiv (block := block) M literalPoint).symm.surjective

end DegreeFourZeroCoreEightLiteralTopMatch

/-- The exact handwritten/generated interface for the stabilizer part of
one row.  The compatibility equation binds the stored kernel and local
images to the actual affine component.  Cardinalities are useful audit
fields, but they never substitute for this square. -/
structure DegreeFourZeroCoreEightPointedLocalMatch
    {ModelGroup : Type} [Group ModelGroup]
    (topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (literalPoint : Fin 8) : Type 1 where
  ModelLocalGroup : Type
  [modelLocalGroup : Group ModelLocalGroup]
  [modelLocalFinite : Finite ModelLocalGroup]
  literalLocalMap :
    MulAction.stabilizer topMatch.literalAction literalPoint →*
      ModelLocalGroup
  literalLocalMap_surjective : Function.Surjective literalLocalMap
  local_card : Nat.card ModelLocalGroup = 3 ∨
    Nat.card ModelLocalGroup = 6
  targetEquiv : LocalQuotient block P ≃* ModelLocalGroup
  compatible :
    targetEquiv.toMonoidHom.comp
        (DegreeFourZeroCoreEightLiteralTopMatch.transportedLocalMap
          (block := block) (P := P) topMatch hr hD literalPoint) =
      literalLocalMap

attribute [instance]
  DegreeFourZeroCoreEightPointedLocalMatch.modelLocalGroup
  DegreeFourZeroCoreEightPointedLocalMatch.modelLocalFinite

namespace DegreeFourZeroCoreEightPointedLocalMatch

/-- The compatibility square identifies the row's stored stabilizer kernel
with the kernel of the actual local component map. -/
theorem literalLocalMap_ker_eq
    {ModelGroup : Type} [Group ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    {literalPoint : Fin 8}
    (M : DegreeFourZeroCoreEightPointedLocalMatch
      block P topMatch hr hD literalPoint) :
    M.literalLocalMap.ker =
      (DegreeFourZeroCoreEightLiteralTopMatch.transportedLocalMap
        (block := block) (P := P) topMatch hr hD literalPoint).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  have hcompat := DFunLike.congr_fun M.compatible x
  constructor
  · intro hx
    apply M.targetEquiv.injective
    calc
      M.targetEquiv
          (DegreeFourZeroCoreEightLiteralTopMatch.transportedLocalMap
            (block := block) (P := P) topMatch hr hD literalPoint x) =
          M.literalLocalMap x := hcompat
      _ = 1 := hx
      _ = M.targetEquiv 1 := (map_one M.targetEquiv).symm
  · intro hx
    calc
      M.literalLocalMap x =
          M.targetEquiv
            (DegreeFourZeroCoreEightLiteralTopMatch.transportedLocalMap
              (block := block) (P := P) topMatch hr hD literalPoint x) :=
        hcompat.symm
      _ = M.targetEquiv 1 := congrArg M.targetEquiv hx
      _ = 1 := map_one M.targetEquiv

end DegreeFourZeroCoreEightPointedLocalMatch

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
