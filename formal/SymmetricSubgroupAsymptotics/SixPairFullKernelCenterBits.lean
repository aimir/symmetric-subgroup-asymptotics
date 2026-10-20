import SymmetricSubgroupAsymptotics.SixPairFullKernelCenter

/-! Literal binary coordinates on the original coarse center. The map
records the second coordinate at the original (0,0) point of each fibre;
full independence supplies surjectivity, not an abstract dimension claim. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelCenterBits
open SixPairFullKernelCenter SixPairCoarseCenterTransport
open BinaryTwoLayerLocalClassTwo BinaryTwoLayerLocalCommutators

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

abbrev K := (SixPairNestedTopFrames.nestedFrame F E).top.ker

def kernel : centerImage F E →* K F E where
  toFun z := ⟨z.val,centerImage_le_kernel F E z.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def bits (z : centerImage F E) (j : Fin 3) : ZMod 2 :=
  (((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j (kernel F E z)) (0,0)).2

theorem hasBits
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (z : centerImage F E) : HasBits F E (kernel F E z) (bits F E z) := by
  have hz : kernel F E z∈Subgroup.center (K F E) :=
    (mem_centerImage F E (kernel F E z)).mp z.property
  obtain ⟨s,hs⟩ := (hasBits_iff_center F E hfull (kernel F E z)).mpr hz
  have he : bits F E z=s := by
    funext j
    change (((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j
      (kernel F E z)) (0,0)).2=s j
    rw [hs j 0 0]
    exact zero_add _
  rw [he]
  exact hs

def bitsHom (hfull : SixPairIndependentKernelNormalCommutators.Independent F E) :
    centerImage F E →* Multiplicative (Fin 3 → ZMod 2) where
  toFun z := Multiplicative.ofAdd (bits F E z)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext j
    change (((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j 1) (0,0)).2=0
    rw [map_one]
    rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext j
    change (((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j
      (kernel F E (a*b))) (0,0)).2=bits F E a j+bits F E b j
    rw [(kernel F E).map_mul,map_mul,Equiv.Perm.mul_apply,
      hasBits F E hfull b j 0 0,hasBits F E hfull a j 0 (0+bits F E b j)]
    simp only [zero_add]
    exact add_comm _ _

theorem bitsHom_injective
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E) :
    Function.Injective (bitsHom F E hfull) := by
  intro a b h
  apply Subtype.ext
  have hk : kernel F E a=kernel F E b := by
    apply (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinates_joint_injective
    funext j
    apply Equiv.ext
    rintro ⟨x,y⟩
    rw [hasBits F E hfull a j x y,hasBits F E hfull b j x y]
    have hj := congrArg (fun v : Multiplicative (Fin 3 → ZMod 2) => v.toAdd j) h
    change bits F E a j=bits F E b j at hj
    rw [hj]
  exact congrArg (fun z : K F E => (z : U)) hk

theorem bitsHom_surjective
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E) :
    Function.Surjective (bitsHom F E hfull) := by
  intro s
  let v : Fin 3 → Equiv.Perm Points := fun j => if s.toAdd j=0 then 1 else diagonal
  have hv : ∀ j,Preserves (v j) := by
    intro j
    by_cases hj : s.toAdd j=0
    · simp only [v,if_pos hj]
      intro a b hab
      exact hab
    · simpa only [v,if_neg hj] using diagonal_preserves
  obtain ⟨x,hx⟩ := hfull v hv
  have hs : HasBits F E x s.toAdd := by
    intro j a b
    rw [hx j]
    have hb : ∀ t : ZMod 2,t=0 ∨ t=1 := by decide +kernel
    rcases hb (s.toAdd j) with h0 | h1
    · simp [v,h0]
    · simp [v,h1,diagonal]
  have hc := (hasBits_iff_center F E hfull x).mp ⟨s.toAdd,hs⟩
  let z : centerImage F E := ⟨x.val,(mem_centerImage F E x).mpr hc⟩
  refine ⟨z,?_⟩
  apply Multiplicative.toAdd.injective
  funext j
  change ((SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j x (0,0)).2=s.toAdd j
  rw [hs j 0 0]
  exact zero_add _

def equiv (hfull : SixPairIndependentKernelNormalCommutators.Independent F E) :
    centerImage F E ≃* Multiplicative (Fin 3 → ZMod 2) :=
  MulEquiv.ofBijective (bitsHom F E hfull)
    ⟨bitsHom_injective F E hfull,bitsHom_surjective F E hfull⟩

end SymmetricSubgroupAsymptotics.SixPairFullKernelCenterBits
