import SymmetricSubgroupAsymptotics.Selected1542QuotientStructurePackets
import SymmetricSubgroupAsymptotics.FiniteGeneratedKernelTable

/-! The two exact original subgroups N and L, from original source words.
Neither subgroup is assumed central in the original16-point group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

def Original : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range sourceGenerators)

def source (j : Fin 3) : Original :=
  ⟨sourceGenerators j,Subgroup.subset_closure ⟨j,rfl⟩⟩

private theorem signed_mem (j : Fin 6) : signedSource j∈Original := by
  unfold signedSource
  split
  · exact (source _).property
  · exact Original.inv_mem (source _).property

private theorem source_word_mem (w : List (Fin 6)) : (w.map signedSource).prod∈Original := by
  apply Original.list_prod_mem
  intro p hp
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
  exact signed_mem j

theorem normal_mem_original (i : Fin 8) : normalElements i∈Original := by
  have he : normalWordElement i=normalElements i := by
    apply Equiv.ext
    exact all_normal_word i
  exact he ▸ source_word_mem (normalWord i)

theorem preimage_mem_original (i : Fin 64) : preimageElements i∈Original := by
  have he : preimageWordElement i=preimageElements i := by
    apply Equiv.ext
    exact all_preimage_word i
  exact he ▸ source_word_mem (preimageWord i)

def normalOriginal (i : Fin 8) : Original := ⟨normalElements i,normal_mem_original i⟩
def preimageOriginal (i : Fin 64) : Original := ⟨preimageElements i,preimage_mem_original i⟩

theorem source_generates : Subgroup.closure (Set.range source)=⊤ := by
  apply Subgroup.map_injective (f := Original.subtype) Subtype.val_injective
  rw [MonoidHom.map_closure,←Set.range_comp]
  change Subgroup.closure (Set.range sourceGenerators)=(⊤ : Subgroup Original).map Original.subtype
  rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
  rfl

private theorem normalOriginal_injective : Function.Injective normalOriginal := by
  intro i j h
  have hh := congrArg (fun z : Original => pointCode z.val) h
  change pointCode (normalElements i)=pointCode (normalElements j) at hh
  rw [all_normal_code i,all_normal_code j] at hh
  exact all_normal_code_injective i j hh

private theorem preimageOriginal_injective : Function.Injective preimageOriginal := by
  intro i j h
  have hh := congrArg (fun z : Original => pointCode z.val) h
  change pointCode (preimageElements i)=pointCode (preimageElements j) at hh
  rw [all_preimage_code i,all_preimage_code j] at hh
  exact all_preimage_code_injective i j hh

def normalTable : FiniteGeneratedKernelTable (I := Fin 8) source where
  element := normalOriginal
  element_injective := normalOriginal_injective
  identity := 0
  identity_eq := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change normalElements 0 x=x
    revert x
    decide +kernel
  multiply := normalMul
  multiply_eq i j := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact (all_normal_mul i j x).symm
  inverse := normalInv
  inverse_eq i := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact (all_normal_inverse i x).symm
  conjugate j :=
    { toFun := normalConj j
      invFun := normalInvConj j
      left_inv := fun i => (all_normal_conj_inverse i j).2
      right_inv := fun i => (all_normal_conj_inverse i j).1 }
  conjugate_eq j i := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact (all_normal_conjugation i j x).symm

def preimageTable : FiniteGeneratedKernelTable (I := Fin 64) source where
  element := preimageOriginal
  element_injective := preimageOriginal_injective
  identity := 0
  identity_eq := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change preimageElements 0 x=x
    revert x
    decide +kernel
  multiply := preimageMul
  multiply_eq i j := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact (all_preimage_mul i j x).symm
  inverse := preimageInv
  inverse_eq i := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact (all_preimage_inverse i x).symm
  conjugate j :=
    { toFun := preimageConj j
      invFun := preimageInvConj j
      left_inv := fun i => (all_preimage_conj_inverse i j).2
      right_inv := fun i => (all_preimage_conj_inverse i j).1 }
  conjugate_eq j i := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact (all_preimage_conjugation i j x).symm

abbrev originalNormal : Subgroup Original := normalTable.subgroup
abbrev originalPreimage : Subgroup Original := preimageTable.subgroup
instance : originalNormal.Normal := normalTable.normal source_generates
instance : originalPreimage.Normal := preimageTable.normal source_generates

theorem normal_le_preimage : originalNormal≤originalPreimage := by
  rintro g ⟨i,hi⟩
  refine ⟨normalInPreimage i,?_⟩
  apply Subtype.ext
  change preimageElements (normalInPreimage i)=g.val
  rw [←congrArg Subtype.val hi]
  apply Equiv.ext
  intro x
  exact (all_normal_in_preimage i x).symm

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
