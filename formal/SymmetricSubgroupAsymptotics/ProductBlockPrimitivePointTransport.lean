import SymmetricSubgroupAsymptotics.ProductBlockFramePointTransport
import SymmetricSubgroupAsymptotics.ProductBlockFrameOriginalBlocks

/-! Actual point conjugacy transports local primitivity of the chosen
physical block system. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame

variable {X Y I F : Type} {U : Subgroup (Equiv.Perm X)}
    {V : Subgroup (Equiv.Perm Y)}
    (C : ProductBlockFrame U I F) (e : U ≃* V) (points : X ≃ Y)
    (he : ∀ (u : U) (x : X),
      points ((u : Equiv.Perm X) x) = (e u : Equiv.Perm Y) (points x))

local notation "D" => ofPointEquiv C e points he

@[simp] theorem ofPointEquiv_blockMap (x : X) :
    (ofPointEquiv C e points he).blockMap (points x) = C.blockMap x := by
  simp [blockMap,ofPointEquiv]

/-- The component acts on the same chosen physical fibre after relabelling. -/
theorem ofPointEquiv_component_preprimitive (i : I) :
    letI : MulAction U I := C.topMulAction
    letI : MulAction V I := (ofPointEquiv C e points he).topMulAction
    (hc : MulAction.IsPreprimitive
      (originalBlockComponent C.blockMap C.blockMap_equivariant i)
      (originalBlockFibre C.blockMap i)) →
    MulAction.IsPreprimitive
      (originalBlockComponent (ofPointEquiv C e points he).blockMap (ofPointEquiv C e points he).blockMap_equivariant i)
      (originalBlockFibre (ofPointEquiv C e points he).blockMap i) := by
  letI : MulAction U I := C.topMulAction
  letI : MulAction V I := (ofPointEquiv C e points he).topMulAction
  intro hc
  let H := MulAction.stabilizer U i
  let FX := originalBlockFibre C.blockMap i
  let FY := originalBlockFibre (ofPointEquiv C e points he).blockMap i
  letI := originalBlockStabilizerMulAction C.blockMap C.blockMap_equivariant i
  let f0 : MulActionHom
      (fun h : H => (originalBlockFibreAction C.blockMap C.blockMap_equivariant i).rangeRestrict h)
      FX FX := { toFun := id, map_smul' := fun _ _ => rfl }
  letI : MulAction.IsPreprimitive H FX :=
    (MulAction.isPreprimitive_congr (f := f0)
      (originalBlockFibreAction C.blockMap C.blockMap_equivariant i).rangeRestrict_surjective
      Function.bijective_id).mpr hc
  let phi : H → originalBlockComponent (ofPointEquiv C e points he).blockMap (ofPointEquiv C e points he).blockMap_equivariant i :=
    fun h => (originalBlockFibreAction (ofPointEquiv C e points he).blockMap (ofPointEquiv C e points he).blockMap_equivariant i).rangeRestrict
      ⟨e h.1,by
        change (ofPointEquiv C e points he).top (e h.1) i = i
        simpa only [ofPointEquiv,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
          e.symm_apply_apply] using h.2⟩
  let f : MulActionHom phi FX FY := {
    toFun := fun x => ⟨points x.1,by
      rw [ofPointEquiv_blockMap]
      exact x.2⟩
    map_smul' := by
      intro h x
      apply Subtype.ext
      exact he h.1 x.1 }
  have hs : Function.Surjective f := by
    intro y
    let x : FX := ⟨points.symm y.1,by
      have hx := ofPointEquiv_blockMap C e points he (points.symm y.1)
      rw [points.apply_symm_apply] at hx
      exact hx.symm.trans y.2⟩
    refine ⟨x,?_⟩
    apply Subtype.ext
    exact points.apply_symm_apply y.1
  exact MulAction.IsPreprimitive.of_surjective (f := f) hs

end SymmetricSubgroupAsymptotics.ProductBlockFrame
end
