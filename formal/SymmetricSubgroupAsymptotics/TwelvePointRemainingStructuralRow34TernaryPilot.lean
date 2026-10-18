import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralTernarySplitJointData
import SymmetricSubgroupAsymptotics.TernaryFourBlockMetacyclicModel
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSharedNaturalWitnesses

/-! Selected row34: actual coordinate-dependent D8 complement, with two
retained Schreier translations. No original-group or normal enumeration. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow34TernaryPilot
open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
abbrev H := TernaryFourBlockMetacyclicModel.Complement true

def rotation : Equiv.Perm (Fin 8) where
  toFun i := (![3,2,0,1,6,7,5,4] : Fin 8 → Fin 8) i
  invFun i := (![2,3,1,0,7,6,4,5] : Fin 8 → Fin 8) i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def reflection : Equiv.Perm (Fin 8) where
  toFun i := (![4,5,6,7,0,1,2,3] : Fin 8 → Fin 8) i
  invFun i := (![4,5,6,7,0,1,2,3] : Fin 8 → Fin 8) i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def signed : H →* Equiv.Perm (Fin 8) where
  toFun h := rotation ^ h.left.toAdd.val * reflection ^ h.right.toAdd.val
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

def gauge : Fin 4 → ZMod 3 := ![0,0,0,2]
def points : Fin 4 × ZMod 3 ≃ Fin 12 where
  toFun p := ⟨p.1.val+4*(p.2+gauge p.1).val,by have := (p.2+gauge p.1).val_lt; omega⟩
  invFun x := (⟨x.val%4,by omega⟩,((x.val / 4 : ℕ) : ZMod 3)-gauge ⟨x.val%4,by omega⟩)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sourceH : Fin 2 → H := ![inr (Multiplicative.ofAdd 1),
  inl (Multiplicative.ofAdd (-1)) * inr (Multiplicative.ofAdd 1)]
def offsets : Fin 2 → Fin 4 → ZMod 3 := ![![1,1,0,0],![1,0,0,1]]
def lifts (j : Fin 2) : Model :=
  ⟨Multiplicative.ofAdd (fun i => offsets j i + signs (sourceH j) i *
    gauge (blocks (sourceH j)⁻¹ i)-gauge i), sourceH j⟩

theorem binding : ∀ j,
    TwelvePointRemainingStructuralTernarySplitJointData.literalAction
      blocks signs signs_one signs_mul points (lifts j)=row34Generators j := by
  intro j
  apply Equiv.ext
  revert j
  decide +kernel

def sectionWords : Fin 8 → List (Fin 2) :=
  ![[],[0,1,0,1],[1,0],[0,1],[0],[1,0,1],[0,1,0],[1]]
def coefficients : Fin 8 → Fin 2 → ℕ :=
  ![![0,0],![1,2],![2,2],![1,0],![2,2],![1,0],![0,1],![1,1]]
def word (w : List (Fin 2)) : Model := (w.map lifts).prod
def basis0 : Model := word [0,1,0,1] * lifts 0 * (word [1,0,1])⁻¹
def basis1 : Model := lifts 0 * lifts 0

theorem complement_identity (h : H) :
    (basis0 ^ coefficients (signed h 0) 0 * basis1 ^ coefficients (signed h 0) 1)⁻¹ *
      word (sectionWords (signed h 0)) = (inr h : Model) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    revert h i
    decide +kernel
  · revert h
    decide +kernel

theorem word_mem (w : List (Fin 2)) : word w ∈ Subgroup.closure (Set.range lifts) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure (Set.mem_range_self j)

theorem complement_mem (h : H) : (inr h : Model) ∈ Subgroup.closure (Set.range lifts) := by
  let D := Subgroup.closure (Set.range lifts)
  have h0 : lifts 0 ∈ D := Subgroup.subset_closure (Set.mem_range_self 0)
  have hb0 : basis0 ∈ D :=
    D.mul_mem (D.mul_mem (word_mem _) h0) (D.inv_mem (word_mem _))
  have hb1 : basis1 ∈ D := D.mul_mem h0 h0
  rw [← complement_identity h]
  exact D.mul_mem (D.inv_mem (D.mul_mem (D.pow_mem hb0 _) (D.pow_mem hb1 _)))
    (word_mem _)

theorem block_transitive : ∀ i : Fin 4, ∃ h : H, blocks h 0=i := by decide +kernel

theorem normal_tuples (L : Subgroup H) (hL : L.Normal) :
    ∃ x : Fin 2 → H, Subgroup.normalClosure (Set.range x)=L := by
  letI := hL
  exact exists_normal_generating_tuple_of_normalGen_le L
    (TernaryFourBlockMetacyclicModel.complement_normalGen true L hL)

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row34Interface :=
  TwelvePointRemainingStructuralTernarySplitJointData.jointDataAtTwo
    blocks signs signs_one signs_mul points lifts row34Generators binding complement_mem
    (TernaryFourBlockMetacyclicModel.complement_coprime true) 0 block_transitive normal_tuples
    row34Interface rfl DegreeTwoTwelveSharedNaturalWitnesses.row34Natural
end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow34TernaryPilot
