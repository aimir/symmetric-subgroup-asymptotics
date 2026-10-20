import SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalAbelianOrder
import SymmetricSubgroupAsymptotics.BinaryVectorOrderFourCoordinates
import SymmetricSubgroupAsymptotics.SixPairThreePairKernelClassTwo
import SymmetricSubgroupAsymptotics.Non2LiftBound

/-! Two binary observations on one actual physical local range of an
elementary coarse kernel. No transitivity of the local range is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics.SixPairElementaryLocalObservation
variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))
  (A : Rep (ZMod 2) (SixPairNestedTopFrames.nestedFrame F E).top.range)
  (D : OriginalKernelModuleChart
    (SixPairNestedTopFrames.nestedFrame F E).top.rangeRestrict A)

 theorem exists_observation
    (hsquare : ∀ k : (SixPairNestedTopFrames.nestedFrame F E).top.rangeRestrict.ker,k^2=1) :
    ∃ q : A →ₗ[ZMod 2] (Fin 2 → ZMod 2),∀ v : A,
      q v=0 ↔ (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate 0
        ((MulEquiv.subgroupCongr (show
          (SixPairNestedTopFrames.nestedFrame F E).top.rangeRestrict.ker=
            (SixPairNestedTopFrames.nestedFrame F E).top.ker by
            ext g; constructor
            · intro h; exact congrArg Subtype.val h
            · intro h; exact Subtype.ext h))
          (D.equiv (Multiplicative.ofAdd v)))=1 := by
  classical
  let C := SixPairNestedTopFrames.nestedFrame F E
  have hk : C.top.rangeRestrict.ker=C.top.ker := by
    ext g
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  let kmap : C.top.rangeRestrict.ker →* C.top.ker := (MulEquiv.subgroupCongr hk).toMonoidHom
  let f := (C.kernelCoordinate 0).comp kmap
  let L := f.range
  have hcomm (a b : C.top.rangeRestrict.ker) : a*b=b*a := by
    apply D.equiv.symm.injective
    rw [map_mul,map_mul,mul_comm]
  have hc (a b : L) : a*b=b*a := by
    apply Subtype.ext
    obtain ⟨x,hx⟩ := a.property
    obtain ⟨y,hy⟩ := b.property
    change a.val*b.val=b.val*a.val
    rw [←hx,←hy,←map_mul,←map_mul,hcomm]
  letI : IsMulCommutative L := IsMulCommutative.of_comm hc
  have hs (a : L) : a^2=1 := by
    apply Subtype.ext
    obtain ⟨k,hk⟩ := a.property
    change a.val^2=1
    rw [←hk,←map_pow,hsquare,map_one]
  letI : Module (ZMod 2) (Additive L) := AddCommGroup.zmodModule (n := 2) (fun x => by
    apply Additive.toMul.injective
    exact hs x.toMul)
  have hp (a : L) : BinaryTwoLayerLocalClassTwo.Preserves a.val := by
    obtain ⟨k,hk⟩ := a.property
    rw [←hk]
    exact SixPairThreePairKernelClassTwo.coordinate_preserves F E 0 (kmap k)
  have hcard : Nat.card (Additive L)≤4 :=
    (Nat.card_congr Additive.toMul).le.trans (BinaryTwoLayerLocalAbelianOrder.card_le_four L hp hc)
  obtain ⟨q,hq⟩ := BinaryVectorOrderFourCoordinates.exists_injective (Additive L) hcard
  let obs : A →ₗ[ZMod 2] (Additive L) :=
    ((f.rangeRestrict.comp D.equiv.toMonoidHom).toAdditiveRight).toZModLinearMap 2
  refine ⟨q.comp obs,?_⟩
  intro v
  change q (obs v)=0 ↔ _
  rw [q.map_eq_zero_iff hq]
  change Additive.ofMul (f.rangeRestrict (D.equiv (Multiplicative.ofAdd v)))=0 ↔ _
  constructor
  · intro h
    exact congrArg Subtype.val (congrArg Additive.toMul h)
  · intro h
    apply Additive.toMul.injective
    exact Subtype.ext h

end SymmetricSubgroupAsymptotics.SixPairElementaryLocalObservation
