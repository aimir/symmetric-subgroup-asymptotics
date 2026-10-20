import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralTernarySplitJointData
import SymmetricSubgroupAsymptotics.QuaternionEightNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryKleinNaturalFamily

/-! Selected original row47; actual signed complement, original words and gauge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow47TernaryPilot
open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
abbrev H := QuaternionGroup 2

def rotation : Equiv.Perm (Fin 8) where
  toFun i := (![3,2,0,1,6,7,5,4] : Fin 8 → Fin 8) i
  invFun i := (![2,3,1,0,7,6,4,5] : Fin 8 → Fin 8) i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def reflection : Equiv.Perm (Fin 8) where
  toFun i := (![6,7,5,4,2,3,1,0] : Fin 8 → Fin 8) i
  invFun i := (![7,6,4,5,3,2,0,1] : Fin 8 → Fin 8) i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def signed : H →* Equiv.Perm (Fin 8) where
  toFun
    | .a i => rotation ^ i.val
    | .xa i => reflection * rotation ^ i.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def blocks : H →* Equiv.Perm (Fin 4) where
  toFun h :=
    { toFun := fun i => ⟨(signed h ⟨2*i.val,by omega⟩).val / 2,by omega⟩
      invFun := fun i => ⟨(signed h⁻¹ ⟨2*i.val,by omega⟩).val / 2,by omega⟩
      left_inv := by revert h; decide +kernel
      right_inv := by revert h; decide +kernel }
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def signs (h : H) (i : Fin 4) : ZMod 3 :=
  if (signed h ⟨2*(blocks h⁻¹ i).val,by omega⟩).val % 2=0 then 1 else 2

theorem signs_one : ∀ i, signs 1 i=1 := by decide +kernel
theorem signs_mul : ∀ g h i, signs (g*h) i=signs g i*signs h (blocks g⁻¹ i) := by
  decide +kernel
abbrev Model := TernaryMonomialCocycle.Model blocks signs signs_one signs_mul

def gauge : Fin 4 → ZMod 3 := ![0,0,1,2]
def points : Fin 4 × ZMod 3 ≃ Fin 12 where
  toFun p := ⟨p.1.val+4*(p.2+gauge p.1).val,by have := (p.2+gauge p.1).val_lt; omega⟩
  invFun x := (⟨x.val%4,by omega⟩,((x.val / 4 : ℕ) : ZMod 3)-gauge ⟨x.val%4,by omega⟩)
  left_inv := by decide +kernel
  right_inv := by decide +kernel


def sourceH : Fin 4 → H := ![1,QuaternionGroup.a 2,QuaternionGroup.a 1,QuaternionGroup.xa 0]
def offsets : Fin 4 → Fin 4 → ZMod 3 := ![![0,1,1,1],![1,2,0,1],![1,0,2,2],![1,1,1,0]]
def lifts (j : Fin 4) : Model :=
  ⟨Multiplicative.ofAdd (fun i => offsets j i + signs (sourceH j) i *
    gauge (blocks (sourceH j)⁻¹ i)-gauge i), sourceH j⟩
theorem binding : ∀ j,
    TwelvePointRemainingStructuralTernarySplitJointData.literalAction
      blocks signs signs_one signs_mul points (lifts j)=row47Generators j := by
  intro j
  apply Equiv.ext
  revert j
  decide +kernel

def sectionWords : Fin 8 → List (Fin 4) := ![[],[1],[1,2],[2],[3,2],[2,3],[3],[1,3]]
def coefficients : Fin 8 → Fin 2 → ℕ := ![![0,0],![2,2],![2,0],![0,2],![1,2],![1,0],![2,1],![0,1]]
def word (w : List (Fin 4)) : Model := (w.map lifts).prod
def basis0 : Model := word [] * lifts 0 * (word [])⁻¹
def basis1 : Model := word [1,2] * lifts 0 * (word [1,2])⁻¹
theorem complement_identity (h : H) :
    (basis0 ^ coefficients (signed h 0) 0 * basis1 ^ coefficients (signed h 0) 1)⁻¹ * word (sectionWords (signed h 0)) = (inr h : Model) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    revert h i
    decide +kernel
  · revert h
    decide +kernel

theorem word_mem (w : List (Fin 4)) : word w ∈ Subgroup.closure (Set.range lifts) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure (Set.mem_range_self j)

theorem complement_mem (h : H) : (inr h : Model) ∈ Subgroup.closure (Set.range lifts) := by
  let D := Subgroup.closure (Set.range lifts)
  have hg (j : Fin 4) : lifts j ∈ D := Subgroup.subset_closure (Set.mem_range_self j)

  have hb0 : basis0 ∈ D :=
    D.mul_mem (D.mul_mem (word_mem []) (hg 0)) (D.inv_mem (word_mem []))
  have hb1 : basis1 ∈ D :=
    D.mul_mem (D.mul_mem (word_mem [1,2]) (hg 0)) (D.inv_mem (word_mem [1,2]))
  rw [← complement_identity h]
  exact D.mul_mem (D.inv_mem (D.mul_mem (D.pow_mem hb0 _) (D.pow_mem hb1 _))) (word_mem _)
theorem block_transitive : ∀ i : Fin 4, ∃ h : H, blocks h 0=i := by decide +kernel
theorem normal_tuples (L : Subgroup H) (hL : L.Normal) :
    ∃ x : Fin 2 → H, Subgroup.normalClosure (Set.range x)=L := by
  exact QuaternionEightNormalGenerators.normal_generating_pairs L hL
def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row47Interface :=
  TwelvePointRemainingStructuralTernarySplitJointData.jointDataAtTwo
    blocks signs signs_one signs_mul points lifts row47Generators binding complement_mem
    (QuaternionEightNormalGenerators.coprime_three) 0 block_transitive normal_tuples
    row47Interface rfl PrimitiveAffineDegreeTwoTwelveTernaryKleinNaturalFamily.row47Natural
end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow47TernaryPilot
end
