import SymmetricSubgroupAsymptotics.CFSGSuzukiBorelPSubgroups
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality

/-! Exact conditional assembly inside the pinned actual Suzuki group.
The normalizer premise is intersected with that original group: scalar
matrices in the ambient GL normalizer are not silently discarded. This
helper does not assert that the pending Bruhat/normalizer premise has
already been proved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiSylowOfNormalizer
open CFSGSuzukiUnipotent CFSGSuzukiBorelPSubgroups

abbrev ActualGroup (m : ℕ) := CFSG.Models.SuzukiConstruction.Model m

def modelUnipotent (m : ℕ) : Subgroup (ActualGroup m) :=
  (unipotentSubgroup m).subgroupOf (CFSG.Models.SuzukiConstruction.subgroup m)

def modelBorel (m : ℕ) : Subgroup (ActualGroup m) :=
  (borelEnvelope m).subgroupOf (CFSG.Models.SuzukiConstruction.subgroup m)

theorem modelUnipotent_map (m : ℕ) :
    (modelUnipotent m).map (CFSG.Models.SuzukiConstruction.subgroup m).subtype=
      unipotentSubgroup m := by
  change ((unipotentSubgroup m).subgroupOf _).map _=unipotentSubgroup m
  rw [Subgroup.subgroupOf_map_subtype,inf_of_le_left (unipotentSubgroup_le_model m)]

theorem modelUnipotent_isPGroup (m : ℕ) : IsPGroup 2 (modelUnipotent m) :=
  (unipotentSubgroup_isPGroup m).comap_of_injective
    (CFSG.Models.SuzukiConstruction.subgroup m).subtype Subtype.val_injective

theorem modelBorel_soluble (m : ℕ) : IsSolvable (modelBorel m) := by
  letI : IsSolvable (borelEnvelope m) := borelEnvelope_soluble m
  let f : modelBorel m →* borelEnvelope m :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      map_one' := Subtype.ext rfl
      map_mul' _ _ := Subtype.ext rfl }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : borelEnvelope m => z.val) he
  exact solvable_of_solvable_injective (f := f) hf

theorem model_binary_subgroup_le_unipotent (m : ℕ)
    (P : Subgroup (ActualGroup m)) (hP : IsPGroup 2 P) (hPB : P≤modelBorel m) :
    P≤modelUnipotent m := by
  let f := (CFSG.Models.SuzukiConstruction.subgroup m).subtype
  have hPB' : P.map f≤borelEnvelope m := by
    rintro _ ⟨x,hx,rfl⟩
    exact hPB hx
  have hPU := binary_subgroup_le_unipotent m (P.map f) (hP.map f) hPB'
  intro x hx
  exact hPU ⟨x,hx,rfl⟩

variable (m : ℕ)
    (hN : Subgroup.normalizer (unipotentSubgroup m : Set (Ambient m)) ⊓
      CFSG.Models.SuzukiConstruction.subgroup m≤borelEnvelope m)

include hN

theorem model_normalizer_le_borel :
    Subgroup.normalizer (modelUnipotent m : Set (ActualGroup m))≤modelBorel m := by
  intro g hg
  have hmap := (modelUnipotent m).le_normalizer_map
    (CFSG.Models.SuzukiConstruction.subgroup m).subtype
  rw [modelUnipotent_map] at hmap
  have hn : g.val∈Subgroup.normalizer (unipotentSubgroup m : Set (Ambient m)) :=
    hmap ⟨g,hg,rfl⟩
  exact hN ⟨hn,g.property⟩

def modelSylow : Sylow 2 (ActualGroup m) :=
  CFSGSylowNormalizerMaximality.sylowOfNormalizer (modelUnipotent m)
    (modelUnipotent_isPGroup m)
    (fun P hP hPN => model_binary_subgroup_le_unipotent m P hP
      (hPN.trans (model_normalizer_le_borel m hN)))

@[simp] theorem modelSylow_coe :
    (modelSylow m hN : Subgroup (ActualGroup m))=modelUnipotent m := rfl

theorem modelSylow_normalizer_soluble :
    IsSolvable (Subgroup.normalizer (modelSylow m hN : Set (ActualGroup m))) := by
  letI : IsSolvable (modelBorel m) := modelBorel_soluble m
  exact solvable_of_solvable_injective
    (f := Subgroup.inclusion (model_normalizer_le_borel m hN))
    (Subgroup.inclusion_injective _)

end SymmetricSubgroupAsymptotics.CFSGSuzukiSylowOfNormalizer
