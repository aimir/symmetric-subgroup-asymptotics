import SymmetricSubgroupAsymptotics.FourBlockBinarySignGeneration
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Original quotient-socle bounds for the shared signed-block family.
The five literal tops are the exact ranges of the displayed affine
actions; every normal quotient is reached by its original quotient map.
The sign space and block complement are retained throughout. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveBinarySignSocles

open SemidirectProduct BinarySignTernaryLinear FourBlockBinarySignSpaces
open TernaryFourBlockPermutationGenerators FourBlockBinarySignGeneration
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev CyclicModel (even : Bool) := FourBlockBinarySignGeneration.AffineModel (R := Cyclic) even
abbrev DihedralModel (even : Bool) := FourBlockBinarySignGeneration.AffineModel (R := Dihedral) even
abbrev SymmetricModel := FourBlockBinarySignGeneration.AffineModel (R := Equiv.Perm (Fin 4)) false

abbrev cyclicAction (even : Bool) := BinarySignTernaryPointAction.action (space (R := Cyclic) even)
abbrev dihedralAction (even : Bool) := BinarySignTernaryPointAction.action (space (R := Dihedral) even)
abbrev symmetricAction := BinarySignTernaryPointAction.action (space (R := Equiv.Perm (Fin 4)) false)

def cyclicLifts (even : Bool) : Fin 3 → CyclicModel even :=
  ![inl (Multiplicative.ofAdd (Pi.single 0 1)),
    inr (inl (Multiplicative.ofAdd (signSeed even))),inr (inr cyclicGenerator)]

def dihedralLifts (even : Bool) : Fin 4 → DihedralModel even :=
  ![inl (Multiplicative.ofAdd (Pi.single 0 1)),
    inr (inl (Multiplicative.ofAdd (signSeed even))),
    inr (inr dihedralRotation),inr (inr dihedralReflection)]

def symmetricLifts : Fin 4 → SymmetricModel :=
  ![inl (Multiplicative.ofAdd (Pi.single 0 1)),
    inr (inl (Multiplicative.ofAdd (signSeed false))),inr (inr c),inr (inr s)]

theorem cyclic_range (even : Bool) (generators : Fin 3 → Equiv.Perm (Fin 12))
    (hbind : ∀ i, cyclicAction even (cyclicLifts even i) = generators i) :
    (cyclicAction even).range = Subgroup.closure (Set.range generators) := by
  have hm (i : Fin 3) : cyclicAction even (cyclicLifts even i) ∈
      Subgroup.closure (Set.range generators) := by
    rw [hbind]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  apply action_range_eq even cyclicGenerator (fun _ => rfl) generators (cyclicLifts even)
    hbind (hm 0) (hm 1) (hm 2)
  · intro K hc _
    apply top_unique
    intro g _
    exact cyclic_mem K hc g
  · intro i
    fin_cases i
    · change cyclicAction even 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · change cyclicAction even 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · exact hm 2

theorem dihedral_range (even : Bool) (generators : Fin 4 → Equiv.Perm (Fin 12))
    (hbind : ∀ i, dihedralAction even (dihedralLifts even i) = generators i) :
    (dihedralAction even).range = Subgroup.closure (Set.range generators) := by
  have hm (i : Fin 4) : dihedralAction even (dihedralLifts even i) ∈
      Subgroup.closure (Set.range generators) := by
    rw [hbind]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  apply action_range_eq even dihedralRotation (fun _ => rfl) generators (dihedralLifts even)
    hbind (hm 0) (hm 1) (hm 2)
  · intro K hc hg
    apply top_unique
    intro g _
    exact dihedral_mem K hc (hg 3) g
  · intro i
    fin_cases i
    · change dihedralAction even 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · change dihedralAction even 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · exact hm 2
    · exact hm 3

theorem symmetric_range (generators : Fin 4 → Equiv.Perm (Fin 12))
    (hbind : ∀ i, symmetricAction (symmetricLifts i) = generators i) :
    symmetricAction.range = Subgroup.closure (Set.range generators) := by
  have hm (i : Fin 4) : symmetricAction (symmetricLifts i) ∈
      Subgroup.closure (Set.range generators) := by
    rw [hbind]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  apply action_range_eq false c (fun _ => rfl) generators symmetricLifts
    hbind (hm 0) (hm 1) (hm 2)
  · intro K hc hg
    apply top_unique
    intro g _
    exact symmetric_mem K hc (hg 3) g
  · intro i
    fin_cases i
    · change symmetricAction 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · change symmetricAction 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · exact hm 2
    · exact hm 3

theorem row245_bindings (i : Fin 3) : cyclicAction true (cyclicLifts true i) = row245Generators i := by
  fin_cases i <;> apply Equiv.ext <;> intro j <;> revert j <;> decide +kernel

theorem row264_bindings (i : Fin 3) : cyclicAction false (cyclicLifts false i) = row264Generators i := by
  fin_cases i <;> apply Equiv.ext <;> intro j <;> revert j <;> decide +kernel

theorem row267_bindings (i : Fin 4) : dihedralAction true (dihedralLifts true i) = row267Generators i := by
  fin_cases i <;> apply Equiv.ext <;> intro j <;> revert j <;> decide +kernel

theorem row274_bindings (i : Fin 4) : dihedralAction false (dihedralLifts false i) = row274Generators i := by
  fin_cases i <;> apply Equiv.ext <;> intro j <;> revert j <;> decide +kernel

theorem row289_bindings (i : Fin 4) : symmetricAction (symmetricLifts i) = row289Generators i := by
  fin_cases i <;> apply Equiv.ext <;> intro j <;> revert j <;> decide +kernel

theorem row245_range : (cyclicAction true).range = Row245Top := cyclic_range true _ row245_bindings
theorem row264_range : (cyclicAction false).range = Row264Top := cyclic_range false _ row264_bindings
theorem row267_range : (dihedralAction true).range = Row267Top := dihedral_range true _ row267_bindings
theorem row274_range : (dihedralAction false).range = Row274Top := dihedral_range false _ row274_bindings
theorem row289_range : symmetricAction.range = Row289Top := symmetric_range _ row289_bindings

def row245Map : CyclicModel true →* Row245Top :=
  (MulEquiv.subgroupCongr row245_range).toMonoidHom.comp (cyclicAction true).rangeRestrict
def row264Map : CyclicModel false →* Row264Top :=
  (MulEquiv.subgroupCongr row264_range).toMonoidHom.comp (cyclicAction false).rangeRestrict
def row267Map : DihedralModel true →* Row267Top :=
  (MulEquiv.subgroupCongr row267_range).toMonoidHom.comp (dihedralAction true).rangeRestrict
def row274Map : DihedralModel false →* Row274Top :=
  (MulEquiv.subgroupCongr row274_range).toMonoidHom.comp (dihedralAction false).rangeRestrict
def row289Map : SymmetricModel →* Row289Top :=
  (MulEquiv.subgroupCongr row289_range).toMonoidHom.comp symmetricAction.rangeRestrict

theorem row245Map_surjective : Function.Surjective row245Map :=
  (MulEquiv.subgroupCongr row245_range).surjective.comp (cyclicAction true).rangeRestrict_surjective
theorem row264Map_surjective : Function.Surjective row264Map :=
  (MulEquiv.subgroupCongr row264_range).surjective.comp (cyclicAction false).rangeRestrict_surjective
theorem row267Map_surjective : Function.Surjective row267Map :=
  (MulEquiv.subgroupCongr row267_range).surjective.comp (dihedralAction true).rangeRestrict_surjective
theorem row274Map_surjective : Function.Surjective row274Map :=
  (MulEquiv.subgroupCongr row274_range).surjective.comp (dihedralAction false).rangeRestrict_surjective
theorem row289Map_surjective : Function.Surjective row289Map :=
  (MulEquiv.subgroupCongr row289_range).surjective.comp symmetricAction.rangeRestrict_surjective

theorem row245_quotientSocle (N : Subgroup Row245Top) [N.Normal] :
    SocleNormalGeneratorBound (Row245Top ⧸ N) 2 :=
  BinarySignTernaryAffineSocles.socle_of_surjective (space true)
    cyclicGenerator cyclic_orbit (pair_mem true 0 1) (pair_mem true 0 2)
    1 cyclic_normalGen ((QuotientGroup.mk' N).comp row245Map)
    ((QuotientGroup.mk'_surjective N).comp row245Map_surjective)

theorem row264_quotientSocle (N : Subgroup Row264Top) [N.Normal] :
    SocleNormalGeneratorBound (Row264Top ⧸ N) 2 :=
  BinarySignTernaryAffineSocles.socle_of_surjective (space false)
    cyclicGenerator cyclic_orbit (pair_mem false 0 1) (pair_mem false 0 2)
    1 cyclic_normalGen ((QuotientGroup.mk' N).comp row264Map)
    ((QuotientGroup.mk'_surjective N).comp row264Map_surjective)

theorem row267_quotientSocle (N : Subgroup Row267Top) [N.Normal] :
    SocleNormalGeneratorBound (Row267Top ⧸ N) 3 :=
  BinarySignTernaryAffineSocles.socle_of_surjective (space true)
    dihedralRotation dihedral_orbit (pair_mem true 0 1) (pair_mem true 0 2)
    2 dihedral_normalGen ((QuotientGroup.mk' N).comp row267Map)
    ((QuotientGroup.mk'_surjective N).comp row267Map_surjective)

theorem row274_quotientSocle (N : Subgroup Row274Top) [N.Normal] :
    SocleNormalGeneratorBound (Row274Top ⧸ N) 3 :=
  BinarySignTernaryAffineSocles.socle_of_surjective (space false)
    dihedralRotation dihedral_orbit (pair_mem false 0 1) (pair_mem false 0 2)
    2 dihedral_normalGen ((QuotientGroup.mk' N).comp row274Map)
    ((QuotientGroup.mk'_surjective N).comp row274Map_surjective)

theorem row289_quotientSocle (N : Subgroup Row289Top) [N.Normal] :
    SocleNormalGeneratorBound (Row289Top ⧸ N) 2 :=
  BinarySignTernaryAffineSocles.socle_of_surjective (space false)
    c symmetric_orbit (pair_mem false 0 1) (pair_mem false 0 2)
    1 symmetric_normalGen ((QuotientGroup.mk' N).comp row289Map)
    ((QuotientGroup.mk'_surjective N).comp row289Map_surjective)

def row245_family : row245Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row245Interface.normalRegistry (fun N => by letI := N.2; exact row245_quotientSocle N.1)
def row264_family : row264Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row264Interface.normalRegistry (fun N => by letI := N.2; exact row264_quotientSocle N.1)
def row267_family : row267Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row267Interface.normalRegistry (fun N => by letI := N.2; exact row267_quotientSocle N.1)
def row274_family : row274Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row274Interface.normalRegistry (fun N => by letI := N.2; exact row274_quotientSocle N.1)
def row289_family : row289Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row289Interface.normalRegistry (fun N => by letI := N.2; exact row289_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveBinarySignSocles

end
